use std::process::Command;

use crate::qry::Query;
use crate::smt::{Solver, write_to_tmp};

pub struct Z3 {}

impl Z3 {
    pub fn new() -> Z3 {
        Z3 {}
    }
}

impl Solver for Z3 {
    fn solve(&self, q: &Query) -> String {
        let path_name = write_to_tmp(q);
        let output = Command::new("z3")
            .arg(path_name)
            .output()
            .expect("failed to execute process");

        String::from_utf8(output.stdout).expect("failed to read stdout")
    }
}