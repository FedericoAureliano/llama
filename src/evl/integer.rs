use crate::ctx::{Context, Solution};
use crate::ctx::sort::Sort;
use crate::ast::{Term};
use crate::api::{mk_const};

impl Context {
    // TODO: need to deal with overflow at some point
    pub fn eval_int(&self, s: &Solution, t: &Term) -> i64 {
        let mut args = t.get_args();
        match t.get_symbol().as_str() {
            "+" => args.fold(0, |r, a| r + self.eval_int(s, a)),
            "-" => args.fold(0, |r, a| r - self.eval_int(s, a)),
            "*" => args.fold(1, |r, a| r * self.eval_int(s, a)),
            "ite" => {
                if self.eval_bool(s, args.next().expect("must have first argument")) {
                    self.eval_int(s, args.next().expect("must have second argument"))
                } else {
                    args.next().expect("must have second argument");
                    self.eval_int(s, args.next().expect("must have third argument"))
                }
            }
            name => {
                if name.parse::<i64>().is_ok() {
                    name.parse::<i64>().unwrap()
                } else {
                    // create a temporary context for evaluating the body
                    let mut tmp_sol = Context::new();
                    tmp_sol.update_logic(self.get_logic());

                    if self.get_decl(name).is_some() {
                        let entries = self.get_decl(name).expect("unreachable");
                        assert!(entries.len() == 1);
                        let (params, rsort) = entries.first().expect("unreachable");
                        assert!(rsort == &Sort::Int);
                        let mut args = t.get_args();
                        for i in 0..params.len() {
                            let a = match params[i].1 {
                                Sort::Bool => self.eval_bool(s, args.next().expect("more params than arguments")).to_string(),
                                Sort::Int => self.eval_int(s, args.next().expect("more params than arguments")).to_string()
                            };
                            tmp_sol.add_decl(params[i].0.as_str(), vec![], params[i].1);
                            tmp_sol.add_body(params[i].0.as_str(), mk_const(a.as_str()));
                        }
                    }

                    // find the body: it is either in the definitions or the solution
                    let body = self.get_body(name).unwrap_or_else(|| s.get(name).expect("declaration without body"));

                    // evaluate the body
                    tmp_sol.eval_int(&Solution::new(), body)
                }
            }
        }
    }
}


#[cfg(test)]
mod test {
    use crate::qry::Query;

    #[test]
    fn test_eval_int(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }

    #[test]
    fn test_eval_int_ite(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia_ite.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_ite_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}