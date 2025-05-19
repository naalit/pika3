mod args;
mod common;
mod elab;
mod lexer;
mod parser;
mod pretty;
mod query;
mod server;
mod vm;

use std::{io::Read, path::PathBuf};

use args::Config;
use elab::DefElab;
use pretty::IntoStyle;

use crate::common::*;

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub struct ElabModule {
    pub file: File,
    pub def: Def,
}
#[derive(Clone)]
pub struct ElabResult {
    pub files: Vec<ElabModule>,
    pub crate_def: Def,
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
            .flat_map(|m| {
                elab::elab_module(m.file, m.def, &self.db)
                    .errors
                    .into_iter()
                    .map(move |err| ElabError { err, file: m.file })
            })
            .collect()
    }
}

/// Finds the smallest directory that is a parent of all the given paths.
/// Returns `None` if the input is empty or no common parent exists.
fn find_crate_root(paths: &[PathBuf]) -> Option<PathBuf> {
    if paths.is_empty() {
        return None;
    }

    // Start with the first path as the initial "common prefix"
    let mut common_path = paths[0].clone();

    for path in &paths[1..] {
        while !path.starts_with(&common_path) {
            // Remove the last component of `common_path` to backtrack
            if !common_path.pop() {
                // If we can't pop anymore, there's no common directory
                return None;
            }
        }
    }

    Some(common_path)
}

pub fn elab_files(filenames: &[PathBuf]) -> Result<ElabResult, (Option<PathBuf>, std::io::Error)> {
    let mut db = DB::default();
    let crate_root =
        find_crate_root(filenames).ok_or((None, std::io::Error::other("no crate root found")))?;
    eprintln!("crate root: {}", crate_root.display());
    let root_file = db
        .ifiles
        .intern(&FileLoc::File(crate_root.canonicalize().unwrap()));
    let crate_def = db.intern_crate(db.name(&db.ifiles.get(root_file).name()), root_file);
    let mut files = Vec::new();
    for file_name in filenames {
        let (input, input_s) = {
            let mut file =
                std::fs::File::open(&file_name).map_err(|e| (file_name.clone().into(), e))?;
            let mut input = String::new();
            file.read_to_string(&mut input)
                .map_err(|e| (file_name.clone().into(), e))?;
            (input.rope(), input)
        };
        let module = elab_file(&mut db, &crate_root, crate_def, file_name, input, input_s);
        files.push(module);
    }

    Ok(ElabResult {
        files,
        db,
        crate_def,
    })
}

pub fn elab_file(
    db: &mut DB,
    crate_root: &PathBuf,
    crate_def: Interned<DefLoc>,
    file_name: &PathBuf,
    input: Rope,
    input_s: String,
) -> ElabModule {
    let file = db.ifiles.intern(&FileLoc::File(
        std::path::Path::new(&file_name).canonicalize().unwrap(),
    ));
    let def = file_name
        .components()
        .skip(crate_root.components().count())
        .fold(crate_def, |acc, component| {
            db.idefs.intern(&DefLoc::Child(
                acc,
                // TODO better handling of multiple . in file names
                db.name(
                    &component
                        .as_os_str()
                        .to_string_lossy()
                        .trim_end_matches(".pk"),
                ),
            ))
        });
    db.set_file_source(def, file, input.clone(), Some(input_s.into()));
    let module = ElabModule { file, def };
    module
}

fn pretty_def(e: &DefElab, db: &DB) -> Doc {
    let mut doc = (Doc::keyword("val ") + e.name.pretty(&db) + " : " + e.ty.pretty(&db)).indent();
    // + " = "
    // + e.body.as_ref().map_or("".into(), |x| match x {
    //     elab::DefBody::Val(x) => x.pretty(&db),
    //     elab::DefBody::Type(_) => Doc::start("<datatype>"),
    // });

    for (_, i) in &e.children {
        doc = doc.chain((Doc::none().hardline() + pretty_def(i, db)).indent());
    }
    if e.can_eval {
        Doc::start("@transparent")
            .style(Doc::style_annotation())
            .hardline()
            + doc
    } else {
        doc
    }
}

pub fn driver(config: Config) {
    // CLI driver
    if config.command == args::Command::Server {
        let mut server = crate::server::Server::start(default());
        server.main_loop();
        server.shutdown();
        return;
    }

    if config.files.is_empty() {
        Doc::none()
            .add("Error", ariadne::Color::Red.style())
            .add(": No input files: exiting", ())
            .emit_stderr();
        std::process::exit(1)
    }

    let mut r = elab_files(&config.files).unwrap_or_else(|(file, err)| match file {
        Some(file) => {
            Doc::none()
                .add("Error", ariadne::Color::Red)
                .add(": File not found: '", ())
                .add(file.display(), ariadne::Color::Cyan)
                .add("'", ())
                .emit_stderr();
            std::process::exit(1)
        }
        None => {
            Doc::none()
                .add("Error", ariadne::Color::Red)
                .add(": ", ())
                .add(err, ariadne::Color::Cyan)
                .emit_stderr();
            std::process::exit(1)
        }
    });

    for m in r.files.clone() {
        let module = elab::elab_module(m.file, m.def, &r.db);
        let mut m = None;
        for i in &module.module.defs {
            pretty_def(i, &r.db).emit_stderr();
            if i.name.0 == r.db.name("main") {
                if let Some(elab::DefBody::Val(f)) = &i.body {
                    if let elab::Term::Fun(f) = &**f {
                        m = Some(f.lower(&default()));
                    }
                }
            }
        }
        if let Some((m, _)) = m {
            println!("\nmain function bytecode:\n{}", m.pretty(&r.db));
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
