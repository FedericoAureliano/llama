use std::process::Command;
use std::io::Write;
use std::fs::File;
use std::env;

use crate::qry::{Query};

fn write_to_tmp(q: &Query) -> String {
    let mut dir = env::temp_dir();
    dir.push("tmp.smt2");

    let path_name = format!("{}", dir.to_string_lossy());

    let mut file = File::create(dir).expect("failed to create tmp file");
    file.write_all(format!("{}", q).as_bytes()).expect("failed to write to tmp file");

    path_name
}

#[allow(dead_code)]
pub struct CVC4 {}

impl CVC4 {
    #[allow(dead_code)]
    pub fn new() -> CVC4 {
        CVC4 {}
    }

    pub fn solve(&self, q: &Query) -> String {
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

#[allow(dead_code)]
pub struct Z3 {}

impl Z3 {
    #[allow(dead_code)]
    pub fn new() -> Z3 {
        Z3 {}
    }

    #[allow(dead_code)]
    pub fn solve(&self, q: &Query) -> String {
        let path_name = write_to_tmp(q);
        let output = Command::new("z3")
            .arg(path_name)
            .output()
            .expect("failed to execute process");

        String::from_utf8(output.stdout).expect("failed to read stdout")
    }
}

#[cfg(test)]
mod test {
    use super::{CVC4, Z3};
    use crate::qry::Query;

    #[test]
    fn test_cvc4_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
  
        let cvc4 = CVC4::new();
        let cvc4_answer = cvc4.solve(&q);

        let sol_cvc4 = q.parse_answer(&cvc4_answer).expect("cannot parse file");
        assert!(q.eval(&sol_cvc4).unwrap());
    }

    #[test]
    fn test_z3_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
  
        let z3 = Z3::new();
        let z3_answer = z3.solve(&q);

        let sol_z3 = q.parse_answer(&z3_answer).expect("cannot parse file");
        assert!(q.eval(&sol_z3).unwrap());
    }

}