use crate::context::{Context, Solution};
use crate::term::{Term};

impl Context {
    // TODO: need to deal with overflow at some point
    pub fn eval_int(&self, t: &Term, s: &Solution) -> i64 {
        match t.peek_name().as_str() {
            "+" => t.peek_args().iter().fold(0, |r, a| r + self.eval_int(&*a, s)),
            "-" => t.peek_args().iter().fold(0, |r, a| r - self.eval_int(&*a, s)),
            "*" => t.peek_args().iter().fold(1, |r, a| r * self.eval_int(&*a, s)),
            // polymorphic
            "ite" => {
                if self.eval_bool(&*t.peek_args()[0], s) {self.eval_int(&*t.peek_args()[1], s)} else {self.eval_int(&*t.peek_args()[2], s)}
            }
            name => {
                match self.get_defn(t.peek_name()) {
                    Some((params, _, body)) => {
                        let args = t.peek_args();
                        let sol = self.build_solution(params, args, s);
                        self.eval_int(body, &sol)
                    },
                    None => {
                        match s.get(&name.to_owned()) {
                            Some((params, _, body)) => {
                                let args = t.peek_args();
                                let sol = self.build_solution(params, args, s);
                                self.eval_int(body, &sol)
                            },
                            None => name.parse::<i64>().expect(format!("unknown symbol {}", name).as_str())
                        }
                    }
                }
            }
        }
    }
}


#[cfg(test)]
mod test {
    use super::Context;

    #[test]
    fn test_eval_int(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuflia.smt2").expect("cannot read file");
        let mut query = Context::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuflia_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }

    #[test]
    fn test_eval_int_ite(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuflia_ite.smt2").expect("cannot read file");
        let mut query = Context::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuflia_ite_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}