use std::fs;
use std::env;

extern crate pest;
#[macro_use]
extern crate pest_derive;

#[macro_use] 
extern crate log;
extern crate env_logger;

mod smtlib;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("No input file given!");
    let g = args.get(2).expect("No output file given!");


    let unparsed_file = fs::read_to_string(f).expect("cannot read file");
    let q = smtlib::parse_smtlib_file(&unparsed_file).expect("cannot parse file");
    q.write_dot(g.to_string());
    println!("{}", q.to_smtlib());
}