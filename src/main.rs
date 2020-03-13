pub mod errors;
pub mod parser;
pub mod ast;
pub mod walk;

#[cfg(not(test))]
use std::process::exit;

use crate::ast::VM;
use crate::parser::cst::{self, Cst};
use crate::parser::lexer::reader::Reader;
use crate::parser::parser::Parser;

use std::default::Default;
use docopt::Docopt;
use serde::Deserialize;

extern crate bit_vec;

const USAGE: &'static str = "
Naval Fate.

Usage:
  llama [-p | --print] <file>
  llama (-h | --help)
  llama (-v | --version)

Options:
  -h --help       Show this screen.
  -v, --version   Show version.
  -p, --print     Print concrete syntax tree.
";

#[derive(Debug, Deserialize)]
struct Args {
    pub arg_file: String,
    pub flag_version: bool,
    pub flag_print: bool,
}

impl Default for Args {
    fn default() -> Args {
        Args {
            arg_file: "".into(),
            flag_version: false,
            flag_print: false,
        }
    }
}

pub fn start() -> i32 {
    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());

    if args.flag_version {
        println!("llama v0.01");
        return 0;
    }

    let mut cst = Cst::new();
    let mut vm = VM::new();

    let arg_file = args.arg_file.clone();
    let res = parse_file(&arg_file, &mut vm, &mut cst);

    if let Err(code) = res {
        return code;
    }
    
    if args.flag_print {
        cst::dump::dump(&cst, &vm.interner);
    }

    walk::walk(&mut vm, &cst);

    if args.flag_print {
        println!("\n\n{}\n\n", vm);
    }

    if vm.diagnostic.has_errors() {
        vm.diagnostic.dump();
        let num_errors = vm.diagnostic.errors().len();

        if num_errors == 1 {
            eprintln!("{} error found.", num_errors);
        } else {
            eprintln!("{} errors found.", num_errors);
        }

        return 1;
    }

    0
}


fn parse_file(filename: &str, vm: &mut VM, cst: &mut Cst) -> Result<(), i32> {
    let reader = if filename == "-" {
        match Reader::from_input() {
            Ok(reader) => reader,

            Err(_) => {
                println!("unable to read from stdin.");
                return Err(1);
            }
        }
    } else {
        match Reader::from_file(filename) {
            Ok(reader) => reader,

            Err(_) => {
                println!("unable to read file `{}`", filename);
                return Err(1);
            }
        }
    };

    parse_reader(reader, vm, cst)
}

fn parse_reader(reader: Reader, vm: &mut VM, cst: &mut Cst) -> Result<(), i32> {
    let filename: String = reader.path().into();
    let parser = Parser::new(reader, &vm.id_generator, cst, &mut vm.interner);

    match parser.parse() {
        Ok(()) => Ok(()),
        Err(error) => {
            println!(
                "error in {} at {}: {}",
                filename,
                error.pos,
                error.error.message()
            );
            println!("error during parsing.");

            Err(1)
        }
    }
}

#[cfg(not(test))]
fn main() {
    exit(start());
}