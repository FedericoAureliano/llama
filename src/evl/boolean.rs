use crate::ctx::{Context, Solution};
use crate::ctx::sort::Sort;
use crate::ast::{Term, Symbol, mk_const_from_symbol};

impl Context {
    pub fn eval_bool(&self, s: &Solution, t: &Term) -> Symbol {
        let mut args = t.get_args();
        match t.get_symbol() {
            Symbol::BoolLit(b) => Symbol::BoolLit(*b),
            Symbol::BoolNT(n) => Symbol::BoolNT(n.clone()),
            Symbol::Name(name) => {
                match name.as_str() {
                    "not" => match self.eval_bool(s, args.next().expect("must have first argument")) {
                        Symbol::BoolLit(b) => Symbol::BoolLit(!b),
                        Symbol::BoolNT(n) => Symbol::BoolNT(n),
                        _ => panic!("expecting bool!")
                    },
                    "or" => {
                        let mut result = false;
                        for a in args {
                            match self.eval_bool(s, a) {
                                Symbol::BoolLit(b) => result = result || b,
                                Symbol::BoolNT(n) => return Symbol::BoolNT(n),
                                _ => panic!("expecting bool!")
                            }
                        }
                        Symbol::BoolLit(result)
                    },
                    "and" => {
                        let mut result = true;
                        for a in args {
                            match self.eval_bool(s, a) {
                                Symbol::BoolLit(b) => result = result && b,
                                Symbol::BoolNT(n) => return Symbol::BoolNT(n),
                                _ => panic!("expecting bool!")
                            }
                        }
                        Symbol::BoolLit(result)
                    },
                    "=>" => {
                        match self.eval_bool(s, args.next().expect("must have first argument")) {
                            Symbol::BoolLit(b1) => {
                                match self.eval_bool(s, args.next().expect("must have second argument")) {
                                    Symbol::BoolLit(b2) => Symbol::BoolLit(!b1 || b2,),
                                    Symbol::BoolNT(n) => Symbol::BoolNT(n),
                                    _ => panic!("expecting bool!")
                                }
                            }
                            Symbol::BoolNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting bool!")
                        }
                    },
                    ">" => {
                        match self.eval_int(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval_int(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 > i2,),
                                    Symbol::IntNT(n) => Symbol::BoolNT(n),
                                    _ => panic!("expecting int!")
                                }
                            }
                            Symbol::IntNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting int!")
                        }
                    },
                    "<" => {
                        match self.eval_int(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval_int(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 < i2,),
                                    Symbol::IntNT(n) => Symbol::BoolNT(n),
                                    _ => panic!("expecting int!")
                                }
                            }
                            Symbol::IntNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting int!")
                        }
                    },
                    ">=" => {
                        match self.eval_int(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval_int(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 >= i2,),
                                    Symbol::IntNT(n) => Symbol::BoolNT(n),
                                    _ => panic!("expecting int!")
                                }
                            }
                            Symbol::IntNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting int!")
                        }
                    },
                    "<=" => {
                        match self.eval_int(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval_int(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 <= i2,),
                                    Symbol::IntNT(n) => Symbol::BoolNT(n),
                                    _ => panic!("expecting int!")
                                }
                            }
                            Symbol::IntNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting int!")
                        }
                    },
                    // polymorphic
                    "ite" => {
                        match self.eval_bool(s, args.next().expect("must have first argument")) {
                            Symbol::BoolLit(b1) => {
                                if b1 {
                                    match self.eval_bool(s, args.next().expect("must have second argument")) {
                                        Symbol::BoolLit(b2) => Symbol::BoolLit(b2),
                                        Symbol::BoolNT(n) => Symbol::BoolNT(n),
                                        _ => panic!("expecting int!")
                                    }
                                }
                                else {
                                    args.next();
                                    match self.eval_bool(s, args.next().expect("must have third argument")) {
                                        Symbol::BoolLit(b2) => Symbol::BoolLit(b2),
                                        Symbol::BoolNT(n) => Symbol::BoolNT(n),
                                        _ => panic!("expecting int!")
                                    }
                                }
                            }
                            Symbol::BoolNT(n) => Symbol::BoolNT(n),
                            _ => panic!("expecting bool!")
                        }
                    },
                    "=" => {
                        let eval_args: Vec<Symbol> = args.into_iter().map(|a| match self.get_sort(a) {
                            Some(Sort::Bool) => self.eval_bool(s, a),
                            Some(Sort::Int) => self.eval_int(s, a),
                            None => panic!("{} failed type check", a)
                        }).collect();

                        for i in 1..eval_args.len() {
                            if eval_args[0] != eval_args[i] {
                                return Symbol::BoolLit(false)
                            }
                        };

                        Symbol::BoolLit(true)
                    }
                    _ => {
                        // we have a declared thing
                        assert!(self.get_decl(name).is_some(), "can't find {}", name);
        
                        let entries = self.get_decl(name).expect("unreachable");
                        assert!(entries.len() == 1, "too many candidates for {}", name);
                        let (params, rsort) = entries.first().expect("unreachable");
                        assert!(rsort == &Sort::Bool, "{} of wrong type", name);

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
                        tmp_sol.eval_bool(&Solution::new(), body)
        
                    }
                }
            }
            _ => panic!("expecting bool!")
        }
    }
}

#[cfg(test)]
mod test {
    use crate::qry::Query;
    use crate::ast::Symbol;

    #[test]
    fn test_eval_bool(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuf.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s) == Symbol::BoolLit(true));
    }
}