use std::fs;
use std::env;

#[macro_use]
extern crate pest_derive;
extern crate pest;

#[macro_use] 
extern crate log;
extern crate env_logger;

mod context;
mod eval;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("No input file given!");

    let unparsed_file = fs::read_to_string(f).expect("cannot read file");
    let mut q = context::Context::new();
    q.parse_file(&unparsed_file).expect("cannot parse file");
    println!("{}", q);
    q.eval();
    println!("{}", q);
}