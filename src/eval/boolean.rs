use crate::context::{Context, Solution};
use crate::context::form::well_formed_term;
use crate::term::{Term};

impl Context {
    pub fn eval_bool(&self, t: &Term, s: &Solution) -> bool {
        match t.peek_name().as_str() {
            "true" => true,
            "false" => false,
            "not" => !self.eval_bool(&*t.peek_args()[0], s),
            "or" => t.peek_args().iter().fold(false, |r, a| r || self.eval_bool(&*a, s)),
            "and" => t.peek_args().iter().fold(true, |r, a| r && self.eval_bool(&*a, s)),
            "=>" => !self.eval_bool(&*t.peek_args()[0], s) || self.eval_bool(&*t.peek_args()[1], s),
            ">" => self.eval_int(&*t.peek_args()[0], s) > self.eval_int(&*t.peek_args()[1], s),
            "<" => self.eval_int(&*t.peek_args()[0], s) < self.eval_int(&*t.peek_args()[1], s),
            ">=" => self.eval_int(&*t.peek_args()[0], s) >= self.eval_int(&*t.peek_args()[1], s),
            "<=" => self.eval_int(&*t.peek_args()[0], s) <= self.eval_int(&*t.peek_args()[1], s),
            // polymorphic
            "ite" => {
                if self.eval_bool(&*t.peek_args()[0], s) {self.eval_bool(&*t.peek_args()[1], s)} else {self.eval_bool(&*t.peek_args()[2], s)}
            }
            "=" => {
                let mut st = self.get_symbol_table();
                for (f, (params, rsort, _)) in s {
                    st.insert(f.clone(), (params.into_iter().map(|(_, s)| s.clone()).collect(), rsort.clone()));
                }
                let args = t.peek_args();
                match well_formed_term(&st, &*args[0]).expect("should have already type checked").as_str() {
                    "Bool" => {
                        let mut prev = self.eval_bool(&*args[0], s); 
                        let mut result = true;
                        for i in 1..args.len() {
                            let curr = self.eval_bool(&*args[i], s);
                            if prev != curr {
                                result = false;
                            }
                            prev = curr;
                        }
                        result
                    }
                    "Int" => {
                        let mut prev = self.eval_int(&*args[0], s); 
                        let mut result = true;
                        for i in 1..args.len() {
                            let curr = self.eval_int(&*args[i], s);
                            if prev != curr {
                                result = false;
                            }
                            prev = curr;
                        }
                        result
                    }
                    _ => unreachable!("unsuported type---should have type checked already")
                }

            }
            name => {
                match self.get_defn(t.peek_name()) {
                    Some((params, _, body)) => {
                        let args = t.peek_args();
                        let sol = self.build_solution(params, args, s);
                        self.eval_bool(body, &sol)
                    },
                    None => {
                        match s.get(&name.to_owned()) {
                            Some((params, _, body)) => {
                                let args = t.peek_args();
                                let sol = self.build_solution(params, args, s);
                                self.eval_bool(body, &sol)
                            },
                            None => {
                                debug!("{} is not supported yet", name);
                                panic!("not supported yet")
                            }
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
    fn test_eval_bool(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/qfuf.smt2").expect("cannot read file");
        let mut query = Context::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/qfuf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}