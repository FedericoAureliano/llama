#[macro_use]
extern crate pest_derive;
extern crate pest;
#[macro_use] 
extern crate log;
extern crate env_logger;
extern crate multimap;
extern crate clap;
extern crate bit_vec;

use std::fs;
use std::io;
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

    let matches = App::new("Llama")
                          .version("0.0")
                          .author("Federico Mora Rocha <fmorarocha@gmail.com>")
                          .about("SMT-LIB Function Synthesis Engine")
                          .args_from_usage(
                              "[input] 'Sets the input file to use, stdin otherwise'
                              -v, --verbose 'Verbose'")
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

    let result = query.solve();
    if result.is_some() {
        if matches.is_present("verbose") {
            query.add_body(query.get_synth().expect("must have function to synthesize").as_str(), result.unwrap());
            println!("{}", query);
        } else {
            let name = query.get_synth().expect("must have function to synthesize");
            let (params, rsort) = query.peek_ctx().get_decl(&name).expect("declaration not found!").first().expect("ureachable");
            let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
            println!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), result.unwrap());
        }
    } else {
        println!("(no-solution)");
    };
    
}