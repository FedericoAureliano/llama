use std::process::Command;
use std::io::Write;
use std::fs::File;
use std::env;

use crate::qry::{Query};
use crate::ctx::Solution;

impl Query {
    fn write_to_tmp(&self) -> String {
        let mut dir = env::temp_dir();
        dir.push("tmp.smt2");

        let path_name = format!("{}", dir.to_string_lossy());

        let mut file = File::create(dir).expect("failed to create tmp file");
        file.write_all(format!("{}", self).as_bytes()).expect("failed to write to tmp file");

        path_name
    }

    pub fn check_cvc4(&self) -> Solution {
        let path_name = self.write_to_tmp();
        let output = Command::new("cvc4")
            .arg("--lang")
            .arg("smt")
            .arg("--produce-models")
            .arg(path_name)
            .output()
            .expect("failed to execute process");

        self.parse_answer(std::str::from_utf8(&output.stdout).expect("failed to read stdout"))
            .expect("failed to parse answer")
    }

    #[allow(dead_code)]
    pub fn check_z3(&self) -> Solution {
        let path_name = self.write_to_tmp();
        let output = Command::new("z3")
            .arg(path_name)
            .output()
            .expect("failed to execute process");
        
        self.parse_answer(std::str::from_utf8(&output.stdout).expect("failed to read stdout"))
            .expect("failed to parse answer")
    }
}

#[cfg(test)]
mod test {
    use crate::qry::Query;

    #[test]
    fn test_cvc4_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();

        let sol_cvc4 = q.check_cvc4();
        assert!(q.eval(&sol_cvc4).unwrap());
    }

    #[test]
    fn test_z3_qfuflia() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();

        let sol_z3 = q.check_z3();
        assert!(q.eval(&sol_z3).unwrap());
    }

}