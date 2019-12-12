use std::fs;
use std::io;

#[macro_use]
extern crate pest_derive;
extern crate pest;

#[macro_use] 
extern crate log;
extern crate env_logger;

extern crate multimap;

extern crate clap;

use clap::App;

mod ast;
mod ctx;
mod evl;
mod qry;
mod rwr;
mod smt;
mod syn;

fn main() {
    env_logger::init();

    let matches = App::new("llama")
                          .version("0.0")
                          .author("Federico Mora Rocha <fmorarocha@gmail.com>")
                          .about("smt-lib function synthesis engine")
                          .args_from_usage(
                              "[input] 'Sets the input file to use, stdin otherwise'")
                          .get_matches();

    let mut raw_query = String::new();

    if matches.is_present("input") {
        let f = matches.value_of("input").expect("must give an input file");
        raw_query = fs::read_to_string(f).expect("cannot read file");
    } else {
        while !raw_query.contains("(check-sat)") {
            match io::stdin().read_line(&mut raw_query) {
                Ok(n) => debug!("read: {}", n),
                Err(error) => println!("error: {}", error),
            }
        }
    }
    let mut query = qry::Query::new();
    query.parse_query(&raw_query).expect("cannot parse file");
    
    println!("Query\n---------\n{}\n\n", query);
    println!("Solution\n---------\n{}", query.solve().expect("failed to synthesize"));
}