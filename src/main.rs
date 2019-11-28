use std::fs;
use std::env;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod smtlib;

fn main() {
    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("No input file given!");
    let g = args.get(2).expect("No output file given!");

    let unparsed_file = fs::read_to_string(f).expect("cannot read file");
    let q = smtlib::parse_smtlib_file(&unparsed_file).unwrap();
    q.write_dot(g.to_string());
}