use crate::ctx::{Context, Solution};
use crate::ctx::sort::Sort;
use crate::ast::{Term};
use crate::api::mk_const;

impl Context {
    pub fn eval_bool(&self, s: &Solution, t: &Term) -> bool {
        let mut args = t.get_args();
        match t.get_symbol().as_str() {
            "true" => true,
            "false" => false,
            "not" => !self.eval_bool(s, args.next().expect("must have first argument")),
            "or" => args.fold(false, |r, a| r || self.eval_bool(s, a)),
            "and" => args.fold(true, |r, a| r && self.eval_bool(s, a)),
            "=>" => !self.eval_bool(s, args.next().expect("must have first argument")) 
                    || self.eval_bool(s, args.next().expect("must have second argument")),
            ">" => self.eval_int(s, args.next().expect("must have first argument")) 
                    > self.eval_int(s, args.next().expect("must have second argument")),
            "<" => self.eval_int(s, args.next().expect("must have first argument")) 
                    < self.eval_int(s, args.next().expect("must have second argument")),
            ">=" => self.eval_int(s, args.next().expect("must have first argument")) 
                    >= self.eval_int(s, args.next().expect("must have second argument")),
            "<=" => self.eval_int(s, args.next().expect("must have first argument")) 
                    <= self.eval_int(s, args.next().expect("must have second argument")),
            // polymorphic
            "ite" => {
                if self.eval_bool(s,  args.next().expect("must have first argument")) {
                    self.eval_bool(s, args.next().expect("must have second argument"))
                } else {
                    args.next().expect("must have second argument");
                    self.eval_bool(s, args.next().expect("must have third argument"))
                }
            }
            "=" => {
                let first = args.next().expect("must have first argument");
                let args: Vec<String> = match self.get_sort(&first) {
                    Some(Sort::Bool) => t.get_args().map(|a| self.eval_bool(s, a).to_string()).collect(),
                    Some(Sort::Int) => t.get_args().map(|a| self.eval_int(s, a).to_string()).collect(),
                    None => panic!("{} failed type check", first)
                }; 
                let mut result = true;
                for i in 1..args.len() {
                    let prev = &args[i-1];
                    let curr = &args[i];
                    if prev != curr {
                        result = false;
                    }
                }
                result
            }
            name => {
                // create a temporary context for evaluating the body
                let mut tmp_sol = Context::new();
                tmp_sol.update_logic(self.get_logic());

                if self.get_decl(name).is_some() {
                    let entries = self.get_decl(name).expect("unreachable");
                    assert!(entries.len() == 1);
                    let (params, rsort) = entries.first().expect("unreachable");
                    assert!(rsort == &Sort::Bool);
                    let mut args = t.get_args();
                    for i in 0..params.len() {
                        let a = match params[i].1 {
                            Sort::Bool => self.eval_bool(s, args.next().expect("more params than arguments")).to_string(),
                            Sort::Int => self.eval_int(s, args.next().expect("more params than arguments")).to_string()
                        };
                        tmp_sol.add_decl(name, params.clone(), rsort.clone());
                        tmp_sol.add_body(name, mk_const(a.as_str()));
                    }
                }

                // find the body: it is either in the definitions or the solution
                let body = self.get_body(name).unwrap_or_else(|| s.get(name).expect("declaration without body"));

                // evaluate the body
                tmp_sol.eval_bool(&Solution::new(), body)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::qry::Query;

    #[test]
    fn test_eval_bool(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuf.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}