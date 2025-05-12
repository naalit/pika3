use crate::{common::*, elab_file, find_crate_root, ElabModule};
use std::error::Error;

use lsp_server as lsp;
use lsp_types::notification::{Notification, PublishDiagnostics};
use lsp_types::request::GotoDefinition;
use lsp_types::request::Request;
use lsp_types::*;
use rustc_hash::FxHashSet;

pub struct Server {
    io_threads: lsp::IoThreads,
    connection: lsp::Connection,
    initialization_params: InitializeParams,
    files: FxHashSet<ElabModule>,
    db: DB,
}
impl Server {
    pub fn start(db: DB) -> Self {
        // Note that  we must have our logging only write out to stderr.
        eprintln!("starting generic LSP server");

        // Create the transport. Includes the stdio (stdin and stdout) versions but this could
        // also be implemented to use sockets or HTTP.
        let (connection, io_threads) = lsp::Connection::stdio();

        // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
        let server_capabilities = serde_json::to_value(&ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(
                TextDocumentSyncKind::INCREMENTAL,
            )),
            definition_provider: Some(OneOf::Left(true)),
            hover_provider: Some(HoverProviderCapability::Simple(true)),
            ..Default::default()
        })
        .unwrap();
        let initialization_params = connection.initialize(server_capabilities).unwrap();
        let initialization_params: InitializeParams =
            serde_json::from_value(initialization_params).unwrap();
        eprintln!("started language server");

        Server {
            io_threads,
            connection,
            initialization_params,
            files: default(),
            db,
        }
    }

    pub fn shutdown(self) {
        self.io_threads.join().unwrap();
    }

    pub fn main_loop(&mut self) {
        while let Ok(msg) = self.connection.receiver.recv() {
            eprintln!("Got message!");
            match msg {
                lsp::Message::Request(msg) => self.handle_request(msg),
                lsp::Message::Response(msg) => self.handle_response(msg),
                lsp::Message::Notification(msg) => self.handle_notification(msg),
            }
            .unwrap_or_else(|e| {
                eprintln!("WARNING: error in handling message: {}", e);
            })
        }
    }

    fn handle_response(&mut self, msg: lsp::Response) -> Result<(), Box<dyn Error>> {
        eprintln!("Ignoring response");
        Ok(())
    }

    fn handle_request(&mut self, msg: lsp::Request) -> Result<(), Box<dyn Error>> {
        if self.connection.handle_shutdown(&msg).unwrap() {
            eprintln!("Shutdown request received");
            return Ok(());
        }

        match &*msg.method {
            request::HoverRequest::METHOD => {
                let (id, params): (_, lsp_types::HoverParams) =
                    msg.extract(request::HoverRequest::METHOD)?;
                let file = self.db.ifiles.intern(&FileLoc::File(
                    params
                        .text_document_position_params
                        .text_document
                        .uri
                        .to_file_path()
                        .map_err(|_| "not a file uri")?,
                ));
                let pos = params.text_document_position_params.position;
                let source = self.db.file_rope(file);

                let (pos_, line) = line_to_byte(&source, pos.line as _);
                let pos = (pos_ + char_to_byte(&line, pos.character as _)) as u32;
                // TODO hover types
                // if let Some(split) = self.db.split_at(file, pos) {
                //     let aspan = self.db.split_span(file, split).unwrap();
                //     if let Some((ty, span)) = crate::elab::ide_support::hover_type(
                //         &self.db,
                //         file,
                //         split,
                //         pos - aspan.1.start,
                //     ) {
                //         let range = aspan.add(span).lsp_range(&self.source);
                //         let result = Hover {
                //             contents: HoverContents::Scalar(MarkedString::LanguageString(
                //                 LanguageString {
                //                     language: "pika".into(),
                //                     value: ty.to_string(false),
                //                 },
                //             )),
                //             range: Some(range),
                //         };
                //         let result = serde_json::to_value(&result)?;
                //         let resp = lsp::Response {
                //             id,
                //             result: Some(result),
                //             error: None,
                //         };
                //         self.connection.sender.send(lsp::Message::Response(resp))?;
                //         return Ok(());
                //     }
                // }
                // let resp = lsp::Response {
                //     id,
                //     result: Some(serde_json::Value::Null),
                //     error: None,
                // };
                // self.connection.sender.send(lsp::Message::Response(resp))?;
            }
            GotoDefinition::METHOD => {
                eprintln!("Handling GoToDefinition");
                let (id, params): (_, GotoDefinitionParams) =
                    msg.extract(GotoDefinition::METHOD)?;
                // example go to definition handler
                let result = GotoDefinitionResponse::Array(Vec::new());
                let result = serde_json::to_value(&result)?;
                let resp = lsp::Response {
                    id,
                    result: Some(result),
                    error: None,
                };
                self.connection.sender.send(lsp::Message::Response(resp))?;
            }
            _ => eprintln!("Ignored unknown request {}", msg.method),
        }

        Ok(())
    }

    fn handle_notification(&mut self, msg: lsp::Notification) -> Result<(), Box<dyn Error>> {
        use lsp_types::notification::*;
        match &*msg.method {
            DidOpenTextDocument::METHOD => {
                eprintln!("Received DidOpenTextDocument");
                let params: DidOpenTextDocumentParams = msg.extract(DidOpenTextDocument::METHOD)?;
                let path = params
                    .text_document
                    .uri
                    .to_file_path()
                    .map_err(|_| "not a file uri")?;
                let file = self.db.ifiles.intern(&FileLoc::File(path.clone()));
                let (crate_def, crate_root) = self.db.find_crate(file).unwrap_or_else(|| {
                    // TODO better way of finding crate roots
                    let crate_root = find_crate_root(&[path.clone()]).unwrap();
                    let crate_file = self.db.ifiles.intern(&FileLoc::File(crate_root.clone()));
                    (
                        self.db.intern_crate(
                            self.db.name(&self.db.ifiles.get(crate_file).name()),
                            crate_file,
                        ),
                        crate_root,
                    )
                });
                let source = params.text_document.text;
                let m = elab_file(
                    &mut self.db,
                    &crate_root,
                    crate_def,
                    &path,
                    source.rope(),
                    source,
                );
                self.files.insert(m);
                self.signal_change();
            }
            DidChangeTextDocument::METHOD => {
                eprintln!("Received DidChangeTextDocument");
                let params: DidChangeTextDocumentParams =
                    msg.extract(DidChangeTextDocument::METHOD)?;
                let file = self.db.ifiles.intern(&FileLoc::File(
                    params
                        .text_document
                        .uri
                        .to_file_path()
                        .map_err(|_| "not a file uri")?,
                ));
                self.db.modify_file_source(file, |source| {
                    for change in params.content_changes {
                        if let Some(range) = change.range {
                            let (start, srope) = line_to_byte(&source, range.start.line as usize);
                            let start =
                                start + char_to_byte(&srope, range.start.character as usize);
                            let (end, erope) = line_to_byte(&source, range.end.line as usize);
                            let end = end + char_to_byte(&erope, range.end.character as usize);
                            source.extract(start..end);
                            source.insert(start, &change.text);
                        } else {
                            // If range is None then it's the whole document
                            *source = Rope::from(change.text);
                        }
                    }
                });
                self.signal_change();
            }
            _ => eprintln!("Ignored unknown notification {}", msg.method),
        }

        Ok(())
    }

    fn signal_change(&mut self) {
        // Publish diagnostics (example)
        eprintln!("Starting diagnostic publishing...");
        for m in &self.files {
            let mut diagnostics = Vec::new();
            let elab = crate::elab::elab_module(m.file, m.def, &self.db);
            for e in elab.errors {
                let e = e.to_lsp(m.file, &self.db);
                diagnostics.push(e);
            }
            // TODO only send diagnostics if they changed
            let message = lsp::Notification {
                method: PublishDiagnostics::METHOD.to_string(),
                params: serde_json::to_value(&PublishDiagnosticsParams {
                    uri: self.db.ifiles.get(m.file).to_url().unwrap(),
                    version: None,
                    diagnostics,
                })
                .unwrap(),
            };
            self.connection
                .sender
                .send(lsp::Message::Notification(message))
                .unwrap();
        }
        eprintln!("Published diagnostics!");
    }
}
