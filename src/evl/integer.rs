use crate::ctx::{Context, Solution};
use crate::ctx::sort::Sort;
use crate::ast::{Term, Symbol, mk_const_from_symbol};

impl Context {
    pub fn eval_int(&self, s: &Solution, t: &Term) -> Symbol {
        let mut args = t.get_args();
        match t.get_symbol() {
            Symbol::IntLit(i) => Symbol::IntLit(*i),
            Symbol::IntNT(n) => Symbol::IntNT(n.clone()),
            Symbol::Name(name) => {
                match name.as_str() {
                    "+" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval_int(s, a) {
                                Symbol::IntLit(b) => result = result + b,
                                Symbol::IntNT(n) => return Symbol::IntNT(n),
                                _ => panic!("expecting Int!")
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    "-" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval_int(s, a) {
                                Symbol::IntLit(b) => result = result - b,
                                Symbol::IntNT(n) => return Symbol::IntNT(n),
                                _ => panic!("expecting Int!")
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    "*" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval_int(s, a) {
                                Symbol::IntLit(b) => result = result * b,
                                Symbol::IntNT(n) => return Symbol::IntNT(n),
                                _ => panic!("expecting Int!")
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    // polymorphic
                    "ite" => {
                        match self.eval_bool(s, args.next().expect("must have first argument")) {
                            Symbol::BoolLit(b1) => {
                                if b1 {
                                    match self.eval_int(s, args.next().expect("must have second argument")) {
                                        Symbol::IntLit(b2) => Symbol::IntLit(b2),
                                        Symbol::IntNT(n) => Symbol::IntNT(n),
                                        _ => panic!("expecting Int!")
                                    }
                                }
                                else {
                                    args.next();
                                    match self.eval_int(s, args.next().expect("must have third argument")) {
                                        Symbol::IntLit(b2) => Symbol::IntLit(b2),
                                        Symbol::IntNT(n) => Symbol::IntNT(n),
                                        _ => panic!("expecting Int!")
                                    }
                                }
                            }
                            Symbol::IntNT(n) => Symbol::IntNT(n),
                            _ => panic!("expecting bool!")
                        }
                    },
                    _ => {
                        // we have a declared thing
                        assert!(self.get_decl(name).is_some(), "can't find {}", name);
        
                        let entries = self.get_decl(name).expect("unreachable");
                        assert!(entries.len() == 1, "too many candidates for {}", name);
                        let (params, rsort) = entries.first().expect("unreachable");
                        assert!(rsort == &Sort::Int, "{} of wrong type", name);

                        // create a temporary context for evaluating the body
                        let mut tmp_sol = Context::new();
                        tmp_sol.update_logic(self.get_logic());

                        for (label, lsort) in params {
                            let a = match lsort {
                                Sort::Bool => self.eval_bool(s, args.next().expect("more params than arguments")),
                                Sort::Int => self.eval_int(s, args.next().expect("more params than arguments"))
                            };
                            tmp_sol.add_decl(label.as_str(), vec![], lsort.clone());
                            tmp_sol.add_body(label.as_str(), mk_const_from_symbol(a));
                        }
                        
                        // find the body: it is either in the definitions or the solution
                        let body = self.get_body(name).unwrap_or_else(|| s.get(name).expect(format!("can't find body of {}", name).as_str()));
        
                        // evaluate the body
                        tmp_sol.eval_int(&Solution::new(), body)
        
                    }
                }
            }
            _ => panic!("expecting int!")
        }
    }
}


#[cfg(test)]
mod test {
    use crate::qry::Query;
    use crate::ast::Symbol;
    use crate::ctx::{Solution};

    #[test]
    fn test_eval_int(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert_eq!(query.eval(&s), Symbol::BoolLit(true));
    }

    #[test]
    fn test_eval_int_ite(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia_ite.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_ite_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert_eq!(query.eval(&s), Symbol::BoolLit(true));
    }

    #[test]
    fn test_partial_false() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let a1 = q.mk_app("f", vec! [q.mk_neg(q.mk_const("1")),  q.mk_const("1")]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        
        let mut sol = Solution::new();

        let ite = q.mk_ite(q.mk_const("true"), q.mk_ge(q.mk_const("!a!"), q.mk_const("7")), q.mk_nonterminal("N", "Bool"));

        sol.insert("f".to_owned(), ite);

        // -1 is less than 7
        assert_eq!(q.eval(&sol), Symbol::BoolLit(false));
    }

    #[test]
    fn test_partial_nt() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let a1 = q.mk_app("f", vec! [q.mk_neg( q.mk_const("1")),  q.mk_const("1")]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        
        let mut sol = Solution::new();

        let ite = q.mk_ite(q.mk_const("false"), q.mk_ge(q.mk_const("!a!"), q.mk_const("7")), q.mk_nonterminal("N", "Bool"));

        sol.insert("f".to_owned(), ite);

        assert_eq!(q.eval(&sol), Symbol::BoolNT("N".to_owned()));
    }
}