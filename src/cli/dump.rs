use codespan_reporting::termcolor::{ColorChoice, StandardStream};
use failure::Error;
use std::path::PathBuf;

use semantics::parser::Value as ParseValue;

/// Options for the `dump` subcommand
#[derive(Debug, StructOpt)]
pub struct Opts {
    /// Path to the DDL file to use for parsing
    #[structopt(name = "DDL-PATH", parse(from_os_str))]
    pub ddl_path: PathBuf,
    /// Path to the binary file to parse
    #[structopt(name = "BINARY-PATH", parse(from_os_str))]
    pub binary_path: PathBuf,
    /// Root label
    pub root: String,
}

/// Run the `check` subcommand with the given options
pub fn run(color: ColorChoice, opts: Opts) -> Result<(), Error> {
    use codespan::CodeMap;
    use codespan_reporting;

    use semantics::{self, TcEnv};
    use syntax::translation::{Desugar, DesugarEnv};
    use syntax::{parse, Label};

    let mut codemap = CodeMap::new();
    let tc_env = TcEnv::default();
    let desugar_env = DesugarEnv::new(tc_env.mappings());
    let writer = StandardStream::stderr(color);

    let file = codemap.add_filemap_from_disk(opts.ddl_path)?;
    let (concrete_module, parse_errors) = parse::module(&file);

    if !parse_errors.is_empty() {
        let mut writer = writer.lock();
        for error in parse_errors {
            codespan_reporting::emit(&mut writer, &codemap, &error.to_diagnostic())?;
        }
        return Err(format_err!("encountered an error!"));
    }

    let raw_module = match concrete_module.desugar(&desugar_env) {
        Ok(raw_module) => raw_module,
        Err(err) => {
            codespan_reporting::emit(&mut writer.lock(), &codemap, &err.to_diagnostic())?;
            return Err(format_err!("encountered an error!"));
        },
    };

    let module = match semantics::check_module(&tc_env, &raw_module) {
        Ok(module) => module,
        Err(err) => {
            codespan_reporting::emit(&mut writer.lock(), &codemap, &err.to_diagnostic())?;
            return Err(format_err!("encountered an error!"));
        },
    };

    let values = {
        use std::fs::File;
        use std::io::{self, Read};

        let mut buf = Vec::new();
        File::open(&opts.binary_path)?.read_to_end(&mut buf)?;
        let mut bytes = io::Cursor::new(&buf);

        // TODO
        semantics::parser::parse_module(&tc_env, &Label(opts.root.clone()), &module, &mut bytes)
            .unwrap()
    };

    for (pos, value) in &values {
        println!("{}:", pos);
        print_parse_value(2, value);
    }

    Ok(())
}

fn print_parse_value(indent: usize, value: &ParseValue) {
    match value {
        ParseValue::Pos(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::U8(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::U16(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::U32(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::U64(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::S8(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::S16(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::S32(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::S64(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::F32(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::F64(ref value) => println!("{:width$}{}", "", value, width = indent),
        ParseValue::Struct(ref fields) => {
            for (label, value) in fields {
                println!("{:width$}{label}: ", "", width = indent, label = label);
                print_parse_value(indent + 2, value);
            }
        },
        ParseValue::Array(ref elems) => {
            for elem in elems {
                print_parse_value(indent, elem);
            }
        },
    }
}
