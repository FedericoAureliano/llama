use std::fs;
use std::env;

#[macro_use]
extern crate pest_derive;
extern crate pest;

#[macro_use] 
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate enum_display_derive;

extern crate multimap;

mod ast;
mod ctx;
mod evl;
mod qry;
mod rwr;
mod smt;

use crate::smt::Solver;
use crate::smt::cvc4::CVC4;
use crate::smt::z3::Z3;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();

    let f = args.get(1).expect("no query file given!");

    let unparsed_query = fs::read_to_string(f).expect("cannot read file");
    let mut query = qry::Query::new();
    query.parse_query(&unparsed_query).expect("cannot parse file");
    
    let cvc4 = CVC4::new();
    let z3 = Z3::new();

    let cvc4_answer = cvc4.solve(&query);
    let z3_answer = z3.solve(&query);

    debug!("cvc4_answer: {}", cvc4_answer);
    debug!("z3_answer: {}", z3_answer);

    let sol_cvc4 = query.parse_answer(&cvc4_answer).expect("cannot parse file");
    let sol_z3 = query.parse_answer(&z3_answer).expect("cannot parse file");
    println!("{}", query);
    println!("cvc4 evaluates to {}", query.eval(&sol_cvc4));
    println!("z3 evaluates to {}", query.eval(&sol_z3));
}