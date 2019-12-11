use std::collections::VecDeque;
use std::rc::Rc;

use crate::qry::Query;
use crate::ctx::{Solution, Sort};
use crate::ast::{Term, Symbol};

impl Query {
    pub fn solve(&mut self) -> Option<Rc<Term>> {
        // These are expansions of the grammar
        let mut expns: VecDeque<Rc<Term>> = VecDeque::new();
        // These are the counter-examples we have accumulated
        let mut ctxs: Vec<Solution> = Vec::new();

        let name = self.get_synth().expect("there must be a function to synthesize");
        let (_, rsort) = self.peek_ctx().get_decl(name.as_str())
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
                        failed = self.eval(&ctx) == Some(true);
                        if failed {
                            debug!("{} failed test {:?}", body, ctx);
                            self.remove_body(name.as_str());
                            break;
                        }
                    }

                    if failed {
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

                    for expansion in self.expand_term(body) {
                        expns.push_back(expansion);
                    }

                    self.remove_body(name.as_str());
                }
                // If there is nothing to pop then we are done: no solution exists
                None => return None
            }
        }
    }

    fn expand_term(&self, t: Rc<Term>) -> Vec<Rc<Term>> {

        match t.get_symbol() {
            Symbol::BoolLit(_)
            | Symbol::IntLit(_) => vec! [Rc::clone(&t)],
            Symbol::Func(name) => {
                let mut expansions : Vec<Rc<Term>> = vec![];
                let mut variations : Vec<Rc<Term>> = vec![];

                let mut idx = 0;
                for a in t.get_args() {
                    variations = self.expand_term(Rc::clone(a));
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
            Symbol::NonTerm(rsort, nt) => {
                let (params, _) = self.peek_ctx().get_decl(self.get_synth().as_ref().expect("there must be a function to synthesize").as_str())
                    .expect("synth has to have decl")
                    .first()
                    .expect("synth has to have only one decl");
                self.expand_nt(nt, rsort, params)
            } 
        }
    }

    fn expand_nt(&self, nt: &String, rsort: &Sort, leafs: &Vec<(String, Sort)>) -> Vec<Rc<Term>> {
        let mut expansions = vec![];
        match nt.as_str() {
            "start" => {
                expansions.push(Term::mk_const(Symbol::NonTerm(*rsort, "leafs".to_owned())));
                expansions.push(Term::mk_const(Symbol::NonTerm(*rsort, "op".to_owned())));
            }
            "leafs" => {
                match rsort {
                    Sort::Bool => {
                        // add all the bool leafs
                        for (iname, isort) in leafs {
                            if isort == &Sort::Bool {
                                expansions.push(Term::mk_const(Symbol::new(iname.as_str())));
                            }
                        }
                        // add true and false
                        expansions.push(Term::mk_const(Symbol::BoolLit(false)));
                        expansions.push(Term::mk_const(Symbol::BoolLit(true)));
                    },
                    Sort::Int => {
                        // add all the integer leafs
                        for (iname, isort) in leafs {
                            if isort == &Sort::Int {
                                expansions.push(Term::mk_const(Symbol::new(iname.as_str())));
                            }
                        }
                        // add zero and one
                        expansions.push(Term::mk_const(Symbol::IntLit(0)));
                        expansions.push(Term::mk_const(Symbol::IntLit(1)));
                    }
                }
            }
            "op" => {
                match rsort {
                    Sort::Bool => {
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "iteb".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "and".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "or".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "=>".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "not".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "=b".to_owned())));

                        if self.peek_ctx().get_logic().lia {
                            expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "=i".to_owned())));
                            expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, ">".to_owned())));
                            expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, ">=".to_owned())));
                        }
                    },
                    Sort::Int => {
                        // add general operators
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "itei".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "+".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "-".to_owned())));
                        expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "*".to_owned())));
                    }
                }                
            }
            "+"
            |"-" => {
                assert!(rsort == &Sort::Int);
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::IntLit(0)));
                order.push(Term::mk_const(Symbol::IntLit(1)));
                for (iname, isort) in leafs {
                    if isort == &Sort::Int {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "op".to_owned())));

                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new(nt.as_str()), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "*" => {
                assert!(rsort == &Sort::Int);
                let mut constants = vec![];
                constants.push(Term::mk_const(Symbol::IntLit(0)));
                constants.push(Term::mk_const(Symbol::IntLit(1)));
                constants.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c-op".to_owned())));
                
                let mut vars = vec![];
                for (iname, isort) in leafs {
                    if isort == &Sort::Int {
                        vars.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                vars.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "op".to_owned())));

                // enforce simple commutativity based on order
                for c in constants {
                    for v in &vars {
                        expansions.push(Term::mk_app(Symbol::new("*"), vec![Rc::clone(&c), Rc::clone(&v)]));
                    }
                }
            }
            "iteb" => { 
                assert!(rsort == &Sort::Bool);
                let mut order = vec![];
                for (iname, isort) in leafs {
                    if isort == &Sort::Bool {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned())));

                let bool_op = Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned()));
                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("ite"), vec![Rc::clone(&bool_op), Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "itei" => {
                assert!(rsort == &Sort::Int);
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::IntLit(0)));
                order.push(Term::mk_const(Symbol::IntLit(1)));
                for (iname, isort) in leafs {
                    if isort == &Sort::Int {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "op".to_owned())));

                let bool_op = Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned()));
                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("ite"), vec![Rc::clone(&bool_op), Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "and"
            |"or" 
            | "=>" => {
                assert!(rsort == &Sort::Bool);
                let mut order = vec![];
                for (iname, isort) in leafs {
                    if isort == &Sort::Bool {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned())));

                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new(nt.as_str()), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "not" => {
                assert!(rsort == &Sort::Bool);
                for (iname, isort) in leafs {
                    if isort == &Sort::Bool {
                        expansions.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned())));
            }
            ">"
            |">=" => {
                let mut choices = vec![];
                for (iname, isort) in leafs {
                    if isort == &Sort::Int {
                        choices.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                choices.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "op".to_owned())));

                for i in 0..choices.len() {
                    for j in 0+1..choices.len() {
                        if i != j {
                            expansions.push(Term::mk_app(Symbol::new(nt.as_str()), vec![Rc::clone(&choices[i]), Rc::clone(&choices[j])]));
                        }
                    }
                }
            }
            "=b" => {
                let mut order = vec![];
                for (iname, isort) in leafs {
                    if isort == &Sort::Bool {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Bool, "op".to_owned())));
                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("="), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "=i" => {
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::IntLit(0)));
                order.push(Term::mk_const(Symbol::IntLit(1)));
                for (iname, isort) in leafs {
                    if isort == &Sort::Int {
                        order.push(Term::mk_const(Symbol::new(iname.as_str())));
                    }
                }
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "op".to_owned())));
                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i+1..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("="), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "c-op" => {
                assert!(rsort == &Sort::Int);
                // add general operators
                expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c+".to_owned())));
                expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c-".to_owned())));
                expansions.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c*".to_owned())));            
            }
            "c+" => {
                assert!(rsort == &Sort::Int);
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::IntLit(1)));
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c-op".to_owned())));

                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("+"), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "c-" => {
                assert!(rsort == &Sort::Int);
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::IntLit(0)));
                order.push(Term::mk_const(Symbol::IntLit(1)));
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c-op".to_owned())));

                for i in 0..order.len()-1 {
                    for j in i..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("-"), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            "c*" => {
                assert!(rsort == &Sort::Int);
                let mut order = vec![];
                order.push(Term::mk_const(Symbol::NonTerm(Sort::Int, "c-op".to_owned())));

                // enforce simple commutativity based on order
                for i in 0..order.len()-1 {
                    for j in i..order.len() {
                        expansions.push(Term::mk_app(Symbol::new("*"), vec![Rc::clone(&order[i]), Rc::clone(&order[j])]));
                    }
                }
            }
            _ => panic!("unknown non-terminal: {}", nt)
        }
        expansions
    }
}