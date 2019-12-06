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

use crate::smt::cvc4::CVC4;
use crate::smt::Solver;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("no query file given!");

    let unparsed_query = fs::read_to_string(f).expect("cannot read file");
    let mut query = qry::Query::new();
    query.parse_query(&unparsed_query).expect("cannot parse file");
    
    println!("{}\n", query);
    let cvc4 = CVC4::new();
    let cvc4_answer = cvc4.solve(&query);

    let sol_cvc4 = query.parse_answer(&cvc4_answer).expect("cannot parse file");
    debug!("cvc4 answer: {:?}", sol_cvc4);
    println!("cvc4 model check: {}", query.eval(&sol_cvc4));
}