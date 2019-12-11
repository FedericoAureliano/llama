use crate::ast::{Term, Symbol};
use crate::ctx::{Context, Solution, Sort};
use crate::qry::{Query, Command};

impl Query {
    pub fn eval(&self, s: &Solution) -> Option<bool> {
        for command in self {
            match command {
                Command::Assert(a) => {
                    match self.peek_ctx().eval(s, a) {
                        Symbol::BoolLit(true) => (),
                        Symbol::BoolLit(false) => return Some(false),
                        Symbol::NonTerm(Sort::Bool, _) => return None,
                        other => panic!("expected bool, got {}", other)
                    }
                },
                _ => (),
            }
        };
        Some(true)
    }
}

impl Context {
    pub fn eval(&self, s: &Solution, t: &Term) -> Symbol {
        let mut args = t.get_args();
        match t.get_symbol() {
            Symbol::IntLit(i) => Symbol::IntLit(*i),
            Symbol::BoolLit(b) => Symbol::BoolLit(*b),
            Symbol::NonTerm(s, n) => Symbol::NonTerm(*s, n.clone()),
            Symbol::Func(name) => {
                match name.as_str() {
                    "+" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval(s, a) {
                                Symbol::IntLit(b) => result = result + b,
                                Symbol::NonTerm(Sort::Int, n) => return Symbol::NonTerm(Sort::Int, n),
                                other => panic!("expecting Int, got {}", other)
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    "-" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval(s, a) {
                                Symbol::IntLit(b) => result = result - b,
                                Symbol::NonTerm(Sort::Int, n) => return Symbol::NonTerm(Sort::Int, n),
                                other => panic!("expecting Int, got {}", other)
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    "*" => {
                        let mut result = 0;
                        for a in args {
                            match self.eval(s, a) {
                                Symbol::IntLit(b) => result = result * b,
                                Symbol::NonTerm(Sort::Int, n) => return Symbol::NonTerm(Sort::Int, n),
                                other => panic!("expecting Int, got {}", other)
                            }
                        }
                        Symbol::IntLit(result)
                    },
                    "not" => match self.eval(s, args.next().expect("must have first argument")) {
                        Symbol::BoolLit(b) => Symbol::BoolLit(!b),
                        Symbol::NonTerm(Sort::Bool, n) => Symbol::NonTerm(Sort::Bool, n),
                        other => panic!("expecting bool, got {}", other)
                    },
                    "or" => {
                        let mut result = false;
                        for a in args {
                            match self.eval(s, a) {
                                Symbol::BoolLit(b) => result = result || b,
                                Symbol::NonTerm(Sort::Bool, n) => return Symbol::NonTerm(Sort::Bool, n),
                                other => panic!("expecting bool, got {}", other)
                            }
                        }
                        Symbol::BoolLit(result)
                    },
                    "and" => {
                        let mut result = true;
                        for a in args {
                            match self.eval(s, a) {
                                Symbol::BoolLit(b) => result = result && b,
                                Symbol::NonTerm(Sort::Bool, n) => return Symbol::NonTerm(Sort::Bool, n),
                                other => panic!("expecting bool, got {}", other)
                            }
                        }
                        Symbol::BoolLit(result)
                    },
                    "=>" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::BoolLit(b1) => {
                                match self.eval(s, args.next().expect("must have second argument")) {
                                    Symbol::BoolLit(b2) => Symbol::BoolLit(!b1 || b2,),
                                    Symbol::NonTerm(Sort::Bool, n) => Symbol::NonTerm(Sort::Bool, n),
                                    other => panic!("expecting bool, got {}", other)
                                }
                            }
                            Symbol::NonTerm(Sort::Bool, n) => Symbol::NonTerm(Sort::Bool, n),
                            other => panic!("expecting bool, got {}", other)
                        }
                    },
                    ">" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                let l = args.next().expect("must have second argument");
                                debug!("here: {}", l);
                                match self.eval(s, l){
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 > i2,),
                                    Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                                    other => panic!("expecting int, got {}", other)
                                }
                            }
                            Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                            other => panic!("expecting int, got {}", other)
                        }
                    },
                    "<" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 < i2,),
                                    Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                                    other => panic!("expecting int, got {}", other)
                                }
                            }
                            Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                            other => panic!("expecting int, got {}", other)
                        }
                    },
                    ">=" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 >= i2,),
                                    Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                                    other => panic!("expecting int, got {}", other)
                                }
                            }
                            Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                            other => panic!("expecting int, got {}", other)
                        }
                    },
                    "<=" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::IntLit(i1) => {
                                match self.eval(s, args.next().expect("must have second argument")) {
                                    Symbol::IntLit(i2) => Symbol::BoolLit(i1 <= i2,),
                                    Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                                    other => panic!("expecting int, got {}", other)
                                }
                            }
                            Symbol::NonTerm(Sort::Int, n) => Symbol::NonTerm(Sort::Bool, n),
                            other => panic!("expecting int, got {}", other)
                        }
                    },
                    // polymorphic
                    "ite" => {
                        match self.eval(s, args.next().expect("must have first argument")) {
                            Symbol::BoolLit(b1) => {
                                if b1 {
                                    match self.eval(s, args.next().expect("must have second argument")) {
                                        Symbol::Func(n) => panic!("{} not evaluated!", n),
                                        sym => sym 
                                    }
                                }
                                else {
                                    args.next();
                                    match self.eval(s, args.next().expect("must have third argument")) {
                                        Symbol::Func(n) => panic!("{} not evaluated!", n),
                                        sym => sym 
                                    }
                                }
                            }
                            Symbol::NonTerm(Sort::Bool, n) => {
                                let s = self.get_sort(args.next().expect("must have second argument")).expect("must have sort");
                                Symbol::NonTerm(s, n)
                            } 
                            other => panic!("expecting bool, got {}", other)
                        }
                    },
                    "=" => {
                        let eval_args: Vec<Symbol> = args.into_iter().map(|a| self.eval(s, a)).collect();

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
                        let (params, _) = entries.first().expect("unreachable");

                        // create a temporary context for evaluating the body
                        let mut tmp_sol = Context::new();
                        tmp_sol.update_logic(self.get_logic());

                        for (label, lsort) in params {
                            let a = self.eval(s, args.next().expect("more params than arguments"));
                            tmp_sol.add_decl(label.as_str(), vec![], lsort.clone());
                            tmp_sol.add_body(label.as_str(), Term::mk_const(a));
                        }
                        
                        // find the body: it is either in the definitions or the solution
                        let body = self.get_body(name).unwrap_or_else(|| s.get(name).expect(format!("can't find body of {}", name).as_str()));
        
                        // evaluate the body
                        tmp_sol.eval(&Solution::new(), body)
        
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::rc::Rc;

    use crate::qry::Query;
    use crate::ctx::{Solution};

    #[test]
    fn test_eval_int(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s).unwrap());
    }

    #[test]
    fn test_eval_ite(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuflia_ite.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuflia_ite_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s).unwrap());
    }

    #[test]
    fn test_partial_false() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let one = q.mk_const("1");
        let mone = q.mk_neg(Rc::clone(&one));
        let a1 = q.mk_app("f", vec! [Rc::clone(&mone),  Rc::clone(&one)]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        
        let mut sol = Solution::new();

        let t = q.mk_const("true");
        let seven = q.mk_const("7");
        let arg = q.mk_const("!a!");
        let ge = q.mk_ge(Rc::clone(&arg), Rc::clone(&seven));
        let nt = q.mk_nonterminal("N", "Bool");
        let ite = q.mk_ite(Rc::clone(&t), Rc::clone(&ge), Rc::clone(&nt));

        sol.insert("f".to_owned(), ite);

        // -1 is less than 7
        assert!(!q.eval(&sol).unwrap());
    }

    #[test]
    fn test_partial_nt() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let one = q.mk_const("1");
        let mone = q.mk_neg(Rc::clone(&one));
        let a1 = q.mk_app("f", vec! [Rc::clone(&mone), Rc::clone(&one)]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        
        let mut sol = Solution::new();

        let cond = q.mk_const("false");
        let seven = q.mk_const("7");
        let arg = q.mk_const("!a!");
        let ge = q.mk_ge(Rc::clone(&arg), Rc::clone(&seven));
        let nt = q.mk_nonterminal("N", "Bool");
        let ite = q.mk_ite(Rc::clone(&cond), Rc::clone(&ge), Rc::clone(&nt));

        sol.insert("f".to_owned(), ite);

        assert!(q.eval(&sol).is_none());
    }

    #[test]
    fn test_eval_bool(){
        use std::fs;
        let unparsed_query = fs::read_to_string("tests/data/qfuf.smt2").expect("cannot read file");
        let mut query = Query::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("tests/data/qfuf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s).unwrap());
    }
}