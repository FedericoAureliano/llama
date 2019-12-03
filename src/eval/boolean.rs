use crate::context::{Context};
use crate::term::{Term};

impl Context {
    pub fn eval_bool(&self, t: &Term) -> bool {
        match t.peek_name().as_str() {
            "true" => true,
            "false" => false,
            "not" => !self.eval_bool(&*t.peek_args()[0]),
            "or" => t.peek_args().iter().fold(false, |r, a| r || self.eval_bool(&*a)),
            "and" => t.peek_args().iter().fold(true, |r, a| r && self.eval_bool(&*a)),
            "=>" => !self.eval_bool(&*t.peek_args()[0]) || self.eval_bool(&*t.peek_args()[1]),
            ">" => self.eval_int(&*t.peek_args()[0]) > self.eval_int(&*t.peek_args()[1]),
            "<" => self.eval_int(&*t.peek_args()[0]) < self.eval_int(&*t.peek_args()[1]),
            ">=" => self.eval_int(&*t.peek_args()[0]) >= self.eval_int(&*t.peek_args()[1]),
            "<=" => self.eval_int(&*t.peek_args()[0]) <= self.eval_int(&*t.peek_args()[1]),
            // polymorphic
            "ite" => {
                if self.eval_bool(&*t.peek_args()[0]) {self.eval_bool(&*t.peek_args()[1])} else {self.eval_bool(&*t.peek_args()[2])}
            }
            "=" => {
                panic!("= not implemented yet")
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
    fn test_eval_bool(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuf.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}