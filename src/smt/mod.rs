pub mod cvc4;
pub mod z3;

use std::fs::File;
use std::io::Write;
use std::env;

use crate::qry::Query;

pub trait Solver {
    fn solve(&self, q: &Query) -> String;
}

pub(crate) fn write_to_tmp(q: &Query) -> String {
    let mut dir = env::temp_dir();
    dir.push("tmp.smt2");

    let path_name = format!("{}", dir.to_string_lossy());

    let mut file = File::create(dir).expect("failed to create tmp file");
    file.write_all(format!("{}", q).as_bytes()).expect("failed to write to tmp file");

    path_name
}