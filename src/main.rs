mod common;
mod elab;
mod lexer;
mod parser;
mod pretty;
mod query;

use std::io::Read;

use crate::common::*;

fn main() {
    let mod_s = "Demo";
    let (input, input_s) = {
        let mut file = std::fs::File::open(&format!("{mod_s}.pk")).unwrap();
        let mut input = String::new();
        file.read_to_string(&mut input).unwrap();
        (input.rope(), input)
    };
    let mut db = DB::default();
    let file = db.ifiles.intern(&FileLoc::File(
        std::path::Path::new(&format!("{mod_s}.pk"))
            .canonicalize()
            .unwrap(),
    ));
    let mdef = db.init_crate(db.name(mod_s), file);
    db.set_file_source(file, input.clone(), Some(input_s.into()));

    let module = elab::elab_module(file, mdef, &db);
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
