use std::process::Command;

use crate::qry::Query;
use crate::smt::{Solver, write_to_tmp};

pub struct CVC4 {}

impl CVC4 {
    pub fn new() -> CVC4 {
        CVC4 {}
    }
}

impl Solver for CVC4 {
    fn solve(&self, q: &Query) -> String {
        let path_name = write_to_tmp(q);
        let output = Command::new("cvc4")
            .arg("--lang")
            .arg("smt")
            .arg("--produce-models")
            .arg(path_name)
            .output()
            .expect("failed to execute process");

        String::from_utf8(output.stdout).expect("failed to read stdout")
    }
}