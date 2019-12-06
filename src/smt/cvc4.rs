use std::process::Command;

use crate::qry::Query;
use crate::smt::{Solver, write_to_tmp};


#[allow(dead_code)]
pub struct CVC4 {}

impl CVC4 {
    #[allow(dead_code)]
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

#[cfg(test)]
mod test {
    use super::{CVC4, Solver};
    use crate::qry::Query;
    use crate::ast::Symbol;

    #[test]
    fn test_cvc4_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
  
        let cvc4 = CVC4::new();
        let cvc4_answer = cvc4.solve(&q);

        let sol_cvc4 = q.parse_answer(&cvc4_answer).expect("cannot parse file");
        assert_eq!(q.eval(&sol_cvc4), Symbol::BoolLit(true));
    }

}