mod common;
mod elab;
mod lexer;
mod parser;
mod pretty;
mod query;

use std::io::Read;

use lsp_types::Url;

use crate::common::*;

fn main() {
    let (input, input_s) = {
        let mut file = std::fs::File::open("demo.pk").unwrap();
        let mut input = String::new();
        file.read_to_string(&mut input).unwrap();
        (input.rope(), input)
    };
    let mut db = DB::default();
    let file = db.ifiles.intern(&FileLoc::Url(
        Url::from_file_path(std::path::Path::new("demo.pk").canonicalize().unwrap()).unwrap(),
    ));
    db.set_file_source(file, input.clone(), Some(input_s.into()));

    let module = elab::all_errors(file, &db);
    let mut cache = FileCache::new(db.clone());
    for i in &module.module.defs {
        (Doc::keyword("val ")
            + i.name.pretty(&db)
            + " : "
            + i.ty.pretty(&db)
            + " = "
            + i.body.as_ref().map_or("".into(), |x| x.pretty(&db)))
        .emit_stderr();
    }
    for i in module.errors {
        i.write_cli(file, &mut cache);
    }
}
