use crate::context::{Context};
use crate::term::{Term};

impl Context {
    // TODO: need to deal with overflow at some point
    pub fn eval_int(&self, t: &Term) -> i64 {
        match t.peek_name().as_str() {
            "+" => t.peek_args().iter().fold(0, |r, a| r + self.eval_int(&*a)),
            "-" => t.peek_args().iter().fold(0, |r, a| r - self.eval_int(&*a)),
            "*" => t.peek_args().iter().fold(1, |r, a| r * self.eval_int(&*a)),
            "ite" => {
                if self.eval_bool(&*t.peek_args()[0]) {self.eval_int(&*t.peek_args()[1])} else {self.eval_int(&*t.peek_args()[2])}
            }
            name => {
                panic!("{} not implemented yet", name)
            }
        }
    }
}


#[cfg(test)]
mod test {
    use crate::query::Query;

    #[test]
    fn test_eval_int(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuflia.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuflia_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }

    #[test]
    fn test_eval_int_ite(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuflia_ite.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuflia_ite_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}