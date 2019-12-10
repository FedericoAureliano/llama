use std::fs;
use std::env;

#[macro_use]
extern crate pest_derive;
extern crate pest;

#[macro_use] 
extern crate log;
extern crate env_logger;

extern crate multimap;

mod ast;
mod ctx;
mod evl;
mod qry;
mod rwr;
mod smt;
mod syn;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("no query file given!");

    let unparsed_query = fs::read_to_string(f).expect("cannot read file");
    let mut query = qry::Query::new();
    query.parse_query(&unparsed_query).expect("cannot parse file");
    
    println!("{}\n", query);
    println!("solution: {}", query.solve().expect("failed to synthesize"));
}