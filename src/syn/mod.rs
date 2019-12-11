use std::collections::VecDeque;
use std::rc::Rc;

use crate::qry::Query;
use crate::ctx::{Solution};
use crate::ast::{Term, Symbol};

impl Query {
    pub fn solve(&mut self) -> Option<Rc<Term>> {
        // These are expansions of the grammar
        let mut expns: VecDeque<Rc<Term>> = VecDeque::new();
        // These are the counter-examples we have accumulated
        let mut ctxs: Vec<Solution> = Vec::new();

        let name = self.get_synth().expect("there must be a function to synthesize");
        let ((_, rsort), _) = self.peek_ctx().get_decl(name.as_str())
            .expect("synth has to have decl")
            .first()
            .expect("synth has to have only one decl");

        // start with the start non terminal in expns
        let start = Term::new(Symbol::NonTerm(*rsort, "start".to_owned()), vec![]);
        expns.push_back(start);

        // if there are no expansions, return unsat
        // else, pop an expansion
        // - test it
        // - - if it fails any test then get rid of it
        // - if it survives then 
        // - if it has no nonterminals, check if it is correct
        // - - if it is correct, then return it
        // - - if it is not, then get rid of it, and add the ctx to counters 
        // - else it has nonterminals
        // - - pick one and expand it in all possible ways, adding all to expns
        loop {
            match expns.pop_front() {
                Some(body) => {
                    self.add_body(name.as_str(), Rc::clone(&body));

                    let mut failed = false;
                    for ctx in &ctxs {
                        if failed {
                            debug!("{} failed test {:?}", body, ctx);
                            self.remove_body(name.as_str());
                            break;
                        }
                        failed = self.eval(&ctx) == Some(true);
                    }

                    if failed {
                            debug!("{} failed test", body);
                        self.remove_body(name.as_str());
                        continue;
                    }

                    if body.is_terminated() {
                        // ask the oracle if it is correct
                        let new_ctx = self.check_cvc4().expect("could not parse");
                        self.remove_body(name.as_str());
                        if new_ctx.is_empty() {
                            return Some(body)
                        }
                        ctxs.push(new_ctx);
                        continue;
                    }

                    for expansion in self.expand_synth(body) {
                        expns.push_back(expansion);
                    }

                    self.remove_body(name.as_str());
                }
                // If there is nothing to pop then we are done: no solution exists
                None => return None
            }
        }
    }

    fn expand_synth(&mut self, t: Rc<Term>) -> Vec<Rc<Term>> {

        match t.get_symbol() {
            Symbol::BoolLit(_)
            | Symbol::IntLit(_) => vec! [Rc::clone(&t)],
            Symbol::Func(name) => {
                let mut expansions : Vec<Rc<Term>> = vec![];
                let mut variations : Vec<Rc<Term>> = vec![];

                let mut idx = 0;
                for a in t.get_args() {
                    variations = self.expand_synth(Rc::clone(a));
                    if variations.len() > 1 {
                        break;
                    }
                    idx += 1;
                }

                for v in variations {
                    let mut tmp = vec! [];
                    let mut j = 0;
                    for a in t.get_args() {
                        if j == idx {
                            tmp.push(Rc::clone(&v));
                        } else {
                            tmp.push(Rc::clone(a));
                        }
                        j += 1;
                    }
                    expansions.push(Term::new(Symbol::Func(name.clone()), tmp));
                }

                expansions
            }
            Symbol::NonTerm(rsort, _) => {
                let ((params, _), _) = self.peek_ctx().get_decl(self.get_synth().as_ref().expect("there must be a function to synthesize").as_str())
                    .expect("synth has to have decl")
                    .first()
                    .expect("synth has to have only one decl");


                let mut expansions : Vec<Rc<Term>> = vec![];

                for (func, ((fparams, fsort), interp)) in self.peek_ctx().get_decls() {
                    if fsort == rsort && *interp {
                        let nonterms : Vec<Rc<Term>> = fparams.iter().map(|(_, s)| Term::new(Symbol::NonTerm(s.clone(), "start".to_owned()), vec![])).collect();
                        expansions.push(self.mk_app(func.as_str(), nonterms));
                    }
                }

                for (vname, vsort) in params {
                    if vsort == rsort {
                        expansions.push(self.mk_const(vname))
                    }
                }

                expansions
            }
        }
    }
}