extern crate codespan;
extern crate ddl;

use codespan::CodeMap;
use std::env;
use std::fs::File;
use std::io::prelude::*;

use ddl::syntax::core::Module;

fn main() {
    let mut codemap = CodeMap::new();
    let filemap = codemap.add_filemap_from_disk("src/stl.ddl").unwrap();

    let module = ddl::syntax::parse::module(&filemap).unwrap();
    let mut module = Module::from_concrete(&module).unwrap();
    module.substitute(&ddl::syntax::core::base_defs());
    ddl::semantics::check_module(&module).unwrap();
    let ir = ddl::compile::ir::Module::from(&module);

    let out_dir = env::var("OUT_DIR").unwrap();
    let mut file = File::create(out_dir + "/stl_parser.rs").unwrap();
    write!(file, "{}", ddl::compile::codegen::LowerModule(&ir)).unwrap();
}
