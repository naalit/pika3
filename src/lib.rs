mod args;
mod common;
mod elab;
mod lexer;
mod parser;
mod pretty;
mod query;

use std::{io::Read, path::PathBuf};

use args::Config;
use pretty::IntoStyle;

use crate::common::*;

#[derive(Clone)]
pub struct ElabResult {
    pub files: Vec<File>,
    pub db: DB,
}
pub struct ElabError {
    err: Error,
    file: File,
}
impl ElabError {
    pub fn write_err(&self, db: &DB) {
        let mut cache = FileCache::new(db.clone());
        self.err.clone().write_cli(self.file, &mut cache);
    }
}
impl ElabResult {
    pub fn all_errors(&mut self) -> Vec<ElabError> {
        self.files
            .iter()
            .copied()
            .flat_map(|file| {
                let name = self.db.ifiles.get(file).name();
                let mdef = self.db.intern_crate(self.db.name(&name), file);
                elab::elab_module(file, mdef, &self.db)
                    .errors
                    .into_iter()
                    .map(move |err| ElabError { err, file })
            })
            .collect()
    }
}

pub fn elab_files(filenames: &[PathBuf]) -> Result<ElabResult, (PathBuf, std::io::Error)> {
    let mut db = DB::default();
    let mut files = Vec::new();
    for file_name in filenames {
        let (input, input_s) = {
            let mut file = std::fs::File::open(&file_name).map_err(|e| (file_name.clone(), e))?;
            let mut input = String::new();
            file.read_to_string(&mut input)
                .map_err(|e| (file_name.clone(), e))?;
            (input.rope(), input)
        };

        let file = db.ifiles.intern(&FileLoc::File(
            std::path::Path::new(&file_name).canonicalize().unwrap(),
        ));
        let name = db.ifiles.get(file).name();
        // Need to establish a crate root for the file
        // TODO crates with multiple files...
        db.intern_crate(db.name(&name), file);
        db.set_file_source(file, input.clone(), Some(input_s.into()));
        files.push(file);
    }

    Ok(ElabResult { files, db })
}

pub fn driver(config: Config) {
    // CLI driver
    if config.files.is_empty() {
        Doc::none()
            .add("Error", ariadne::Color::Red.style())
            .add(": No input files: exiting", ())
            .emit_stderr();
        std::process::exit(1)
    }

    let mut r = elab_files(&config.files).unwrap_or_else(|(file, _)| {
        Doc::none()
            .add("Error", ariadne::Color::Red)
            .add(": File not found: '", ())
            .add(file.display(), ariadne::Color::Cyan)
            .add("'", ())
            .emit_stderr();
        std::process::exit(1)
    });

    for file in r.files.clone() {
        let name = r.db.ifiles.get(file).name();
        let mdef = r.db.intern_crate(r.db.name(&name), file);
        let module = elab::elab_module(file, mdef, &r.db);
        for i in &module.module.defs {
            (Doc::keyword("val ") + i.name.pretty(&r.db) + " : " + i.ty.pretty(&r.db))
                // + " = "
                // + i.body.as_ref().map_or("".into(), |x| x.pretty(&db)))
                .emit_stderr();
        }
    }

    let all_errors = r.all_errors();
    for e in &all_errors {
        e.write_err(&r.db);
    }
    if !all_errors.is_empty() {
        eprintln!("{} errors emitted", all_errors.len());
    }
}

pub fn cli_main() {
    let config = Config::from_cmd_args();

    driver(config)
}
