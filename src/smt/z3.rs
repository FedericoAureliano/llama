use std::process::Command;

use crate::qry::Query;
use crate::smt::{Solver, write_to_tmp};


#[allow(dead_code)]
pub struct Z3 {}

impl Z3 {
    #[allow(dead_code)]
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

#[cfg(test)]
mod test {
    use super::{Z3, Solver};
    use crate::qry::Query;

    #[test]
    fn test_z3_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
  
        let z3 = Z3::new();
        let z3_answer = z3.solve(&q);

        let sol_z3 = q.parse_answer(&z3_answer).expect("cannot parse file");
        assert!(q.eval(&sol_z3));
    }

}