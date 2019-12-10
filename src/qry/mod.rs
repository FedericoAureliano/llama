use core::slice::{self};
use std::collections::{HashMap};
use std::fmt;
use std::rc::Rc;

use pest::Parser;
use pest::error::Error;
use pest::iterators::Pair;

use crate::ast::{Term, Symbol};
use crate::ctx::{Context, Logic, Sort, Solution};
use crate::rwr::rename;


pub enum Command {
    SetLogic,
    Declare(String),
    Define(String),
    Synth(String),
    Assert(Rc<Term>),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

pub struct Query {
    script: Vec<Command>,
    ctx: Context,
    synth: Option<String>,
}

impl Query {
    pub fn new() -> Query {
        let query = Query {
            script: vec![],
            ctx: Context::new(),
            synth: None,
        };
        query
    }

    pub fn peek_ctx(&self) -> &Context {
        &self.ctx
    }

    pub fn set_logic(&mut self, logic: &str) {
        let l = Logic::to_logic(logic);
        self.ctx.update_logic(&l);
        self.script.push(Command::SetLogic);
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<&str>, rsort: &str) {
        debug!("declaring {}", name);
        let mut labels = "abcd".chars();
        let params: Vec<(String, Sort)> = asorts
            .into_iter()
            .map(|s| (format!{"!{}!", labels.next().expect("max 4 arguments")}, Sort::new(s)))
            .collect();
        self.ctx.add_decl(name, params, Sort::new(rsort));
        self.script.push(Command::Declare(name.to_owned()));
    }

    pub fn declare_const(&mut self, name: &str, rsort: &str) {
        self.declare_fun(name, vec![], rsort)
    }

    pub fn define_synth(&mut self, name: &str, params: Vec<(&str, &str)>, rsort: &str) {
        assert!(self.synth.is_none());
        let params: Vec<(String, Sort)> = params
            .into_iter()
            .map(|(n, s)| (n.to_owned(), Sort::new(s)))
            .collect();
        self.ctx.add_synth(name, params, Sort::new(rsort));
        self.script.push(Command::Synth(name.to_owned()));
        self.synth = Some(name.to_owned());
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(&str, &str)>, rsort: &str, body: Rc<Term>) {
        let params: Vec<(String, Sort)> = params
            .into_iter()
            .map(|(n, s)| (n.to_owned(), Sort::new(s)))
            .collect();
        self.ctx.add_decl(name, params, Sort::new(rsort));
        self.ctx.add_body(name, body);
        self.script.push(Command::Define(name.to_owned()));
    }

    pub fn assert(&mut self, node: Rc<Term>) {
        self.script.push(Command::Assert(node));
    }

    pub fn check_sat(&mut self) {
        self.script.push(Command::CheckSat);
    }

    pub fn get_model(&mut self) {
        self.script.push(Command::GetModel);
    }

    pub fn get_synth(&self) -> &Option<String> {
        &self.synth
    }

}

impl<'a> IntoIterator for &'a Query {
    type Item = &'a Command;
    type IntoIter = slice::Iter<'a, Command>;

    fn into_iter(self) -> slice::Iter<'a, Command> {
        self.script.iter()
    }
}


#[derive(Parser)]
#[grammar = "pst/synth.pest"]
struct SynthParser;

impl Query {
    fn parse_fapp(&self, pair: Pair<Rule>) -> Result<Rc<Term>, Error<Rule>> {
        match pair.as_rule() {
            Rule::fapp => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_span().as_str();
                let mut args : Vec<Rc<Term>> = vec! [];
                for i in inner {
                    args.push(self.parse_fapp(i)?)
                }
                Ok(self.mk_app(func, args))
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting function application!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_command(&mut self, pair: Pair<Rule>) -> Result<(), Error<Rule>> {
        match pair.as_rule() {
            Rule::setlogic => {
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();
                self.set_logic(&name);
                Ok(())
            }
            Rule::declare => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();

                let mut sorts = vec! []; 
                for s in inner {
                    sorts.push(s.as_span().as_str());
                }

                let rsort = sorts.pop().unwrap();
                self.declare_fun(&name, sorts, rsort);
                Ok(())
            }
            Rule::synth => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }
                
                let rsort = defn.pop().unwrap().as_span().as_str();
                let params = defn.into_iter().map(|r| match r.as_rule() {
                    Rule::param => {
                        let mut inner = r.into_inner();
                        let name = inner.next().unwrap().as_span().as_str();
                        let sort = inner.next().unwrap().as_span().as_str();
                        (name, sort)
                    },
                    _ => panic!("must be a param rule!")
                }).collect();
                self.define_synth(&name, params, rsort);
                Ok(())
            }
            Rule::define => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }

                let body = self.parse_fapp(defn.pop().unwrap())?;
                let rsort = defn.pop().unwrap().as_span().as_str();
                let params = defn.into_iter().map(|r| match r.as_rule() {
                    Rule::param => {
                        let mut inner = r.into_inner();
                        let name = inner.next().unwrap().as_span().as_str();
                        let sort = inner.next().unwrap().as_span().as_str();
                        (name, sort)
                    },
                    _ => panic!("must be a param rule!")
                }).collect();
                self.define_fun(&name, params, rsort, body);
                Ok(())
            }
            Rule::checksat => {self.check_sat(); Ok(())},
            Rule::getmodel => {self.get_model(); Ok(())},
            Rule::assert => {
                let node = self.parse_fapp(pair.into_inner().next().unwrap())?;
                self.assert(node);
                Ok(())
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_model(&self, pair: Pair<Rule>) -> Result<(String, (Vec<(String, Sort)>, Sort, Rc<Term>)), Error<Rule>> {
        match pair.as_rule() {
            // this is slightly different from command parsing above
            // - we do not define
            // - we produce String rather than &str
            Rule::define => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }

                let body = self.parse_fapp(defn.pop().unwrap())?;
                let rsort = defn.pop().unwrap().as_span().as_str();
                let params = defn.into_iter().map(|r| match r.as_rule() {
                    Rule::param => {
                        let mut inner = r.into_inner();
                        let name = inner.next().unwrap().as_span().as_str().to_owned();
                        let sort = Sort::new(inner.next().unwrap().as_span().as_str());
                        (name, sort)
                    },
                    _ => panic!("must be a param rule!")
                }).collect();
                Ok((name, (params, Sort::new(rsort), body)))
            }
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    pub fn parse_query(&mut self, file: &str) -> Result<(), Error<Rule>> {
        let syntax = SynthParser::parse(Rule::query, file).expect("failed to read!");    
        let mut empty = false;
        for r in syntax {
            self.parse_command(r)?;
            empty = true
        };
        // self.well_formed();
        assert!(empty, "problem with grammar: query is empty!");
        Ok(())
    }

    pub fn parse_answer(&self, file: &str) -> Result<Solution, Error<Rule>> {
        let syntax = SynthParser::parse(Rule::query, file).expect("failed to read!");
        let mut sol = Solution::new();
        for r in syntax {
            let (name, (params, rsort, body)) = self.parse_model(r)?;
            
            let (exp_params, exp_rsort) = self.peek_ctx()
                .get_decl(name.as_str())
                .expect("definition must have been declared!")
                .first().expect("unreachable");

            assert!(exp_rsort == &rsort, "expected return sorts must be the same");
            assert!(exp_params.len() == params.len(), "paramaters must match in length");
            let mut rewrite: HashMap<String, String> = HashMap::new();
            for i in 0..params.len() {
                assert!(params[i].1 == exp_params[i].1, "paramater sorts must match");
                rewrite.insert(params[i].0.clone(), exp_params[i].0.clone());
            }
            let nbody = rename(&rewrite, &body);
            sol.insert(name, nbody);
        };
        Ok(sol)
    }
}

impl Query {
    fn command_to_string(&self, c : &Command) -> String {
        match c {
            Command::SetLogic => format!("(set-logic {})", self.ctx.get_logic()),
            Command::Declare(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                let args : Vec<String> = params.into_iter().map(|(_, s)| s.to_string()).collect();
                if args.len() > 0 {
                    format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string())
                } else {
                    format!("(declare-const {} {})", name, rsort.to_string())
                }
            },
            Command::Define(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                let body = self.ctx.get_body(&name).expect("definition body not found");
                let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                format!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), body)
            },
            Command::Synth(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                match self.ctx.get_body(&name) {
                    Some(b) => {
                        let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                        format!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), b)
                    },
                    None => {
                        let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                        format!("(synth-blocking-fun {} ({}) {})", name, args.join(" "), rsort.to_string())    
                    }
                }
            },
            Command::Assert(a) => format!("(assert {})", a),
            Command::CheckSat => "(check-sat)".to_string(),
            Command::GetModel => "(get-model)".to_string(),
            Command::Push => "(push)".to_string(),
            Command::Pop => "(pop)".to_string(),
        }
    }
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q_iter = self.into_iter();
        let q_str : Vec<String> = q_iter.map(|c| self.command_to_string(c)).collect();
        write!(f, "{}", q_str.join("\n"))
    }
}

impl Query {
    pub fn well_formed(&self) -> bool {
        self.into_iter().fold(true, |r, c| r && 
        match c {
            Command::SetLogic => true,
            Command::Declare(n) => self.ctx.get_decl(n.as_str()).is_some(),
            Command::Define(n) => {
                let sigs = self.ctx.get_decl(n.as_str()).expect("definition must have unique declaration");
                assert!(sigs.len() == 1);
                let (params, rsort) = sigs.first().expect("must have one definition");
                let mut ctx = Context::new();
                ctx.update_logic(self.ctx.get_logic());
                for (n, s) in params {
                    ctx.add_decl(n.as_str(), vec![], *s);
                }
                let body = self.ctx.get_body(n).expect("definition must have body");
                rsort == &ctx.check_sort(body).expect("body must be well formed")
            },
            Command::Synth(n) => {
                let sigs = self.ctx.get_decl(n.as_str()).expect("definition must have unique declaration");
                assert!(sigs.len() == 1);
                let (params, rsort) = sigs.first().expect("must have one definition");
                let mut ctx = Context::new();
                match self.ctx.get_body(n) {
                    Some(body) => {
                        ctx.update_logic(self.ctx.get_logic());
                        for (n, s) in params {
                            ctx.add_decl(n.as_str(), vec![], *s);
                        }
                        rsort == &ctx.check_sort(body).expect("body must be well formed")
                    }
                    None => true
                }
            },
            Command::Assert(t) => self.ctx.check_sort(t).expect("assertion not well formed") == Sort::Bool,
            Command::CheckSat => true,
            Command::GetModel => true,
            Command::Push => true,
            Command::Pop => true,
        })
    }
}

impl Query {

    pub fn mk_nonterminal(&self, name: &str, sort: &str) -> Rc<Term> {
        Term::new(Symbol::NonTerm(Sort::new(sort), name.to_owned()), vec![])
    }

    pub fn mk_const(&self, name: &str) -> Rc<Term> {
        Term::new(Symbol::new(name), vec! [])
    }

    pub fn mk_app(&self, name: &str, args: Vec<Rc<Term>>) -> Rc<Term> {
        let rcargs = args.into_iter().map(|a| Rc::clone(&a)).collect();
        Term::new(Symbol::new(name), rcargs)
    }

    #[allow(dead_code)]
    pub fn mk_add(&self, x: Rc<Term>, y: Rc<Term>) -> Rc<Term> {
        self.mk_app("+", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_sub(&self, x: Rc<Term>, y: Rc<Term>) -> Rc<Term> {
        self.mk_app("-", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_neg(&self, x: Rc<Term>) -> Rc<Term> {
        self.mk_app("-", vec![x])
    }

    #[allow(dead_code)]
    pub fn mk_ge(&self, x: Rc<Term>, y: Rc<Term>) -> Rc<Term> {
        self.mk_app(">=", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_le(&self, x: Rc<Term>, y: Rc<Term>) -> Rc<Term> {
        self.mk_app("<=", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_ite(&self, x: Rc<Term>, y: Rc<Term>, z: Rc<Term>) -> Rc<Term> {
        self.mk_app("ite", vec![x, y, z])
    }    
}


#[cfg(test)]
mod test {
    use std::rc::Rc;
    use crate::qry::Query;

    #[test]
    fn test_multiple_asserts(){
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("x", vec! [], "Int");
        q.declare_fun("f", vec! ["Int", "Int"], "Int");
        let node_x = q.mk_const("x");
        let node_7 = q.mk_const("7");
        let node_ge = q.mk_ge(Rc::clone(&node_x), Rc::clone(&node_7));
        let node_f = q.mk_app("f", vec! [Rc::clone(&node_x), Rc::clone(&node_x)]);
        let node_neg = q.mk_neg(node_f);
        let node_add = q.mk_add(node_neg, node_7);
        let node_le = q.mk_le(q.mk_sub(node_x, q.mk_const("33")), node_add);
        q.assert(node_ge);
        q.assert(node_le);
        assert_eq!("(set-logic QF_UFLIA)
(declare-const x Int)
(declare-fun f (Int Int) Int)
(assert (>= x 7))
(assert (<= (- x 33) (+ (- (f x x)) 7)))", format!("{}", q));
    }

   #[test]
    fn test_parse_query() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
        assert_eq!(unparsed_file, format!("{}", q));
    }

    #[test]
    fn test_parse_query_synth() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/simple.synth").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
        assert_eq!(unparsed_file, format!("{}", q));
    }

    #[test]
    fn test_parse_answer() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
        let unparsed_file = fs::read_to_string("tests/data/qfuflia_result.smt2").expect("cannot read file");
        let sol = q.parse_answer(&unparsed_file).unwrap();
        let x_term = sol.get("x").expect("couldn't find x");
        assert_eq!("8", format!("{}", x_term));
        let f_term = sol.get("f").expect("couldn't find f");
        assert_eq!("(- 1)", format!("{}", f_term));
    }

    #[test]
    fn test_multiple_asserts_lia(){
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_fun("x", vec! [], "Int");
        let node_x = q.mk_const("x");
        let node_7 = q.mk_const("7");
        let a1 = q.mk_ge(Rc::clone(&node_x), Rc::clone(&node_7));
        let a2 = q.mk_le(Rc::clone(&node_x), Rc::clone(&node_7));
        q.assert(a1);
        q.assert(a2);
        q.check_sat();
        q.get_model();
        assert_eq!("(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 7))
(assert (<= x 7))
(check-sat)
(get-model)", format!("{}", q));
    }

    #[test]
    fn test_uf_and_set_logic() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let node_n1 = q.mk_const("1");
        let node_sub = q.mk_neg(Rc::clone(&node_n1));
        let a1 = q.mk_app("f", vec! [node_sub, Rc::clone(&node_n1)]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        assert_eq!("(set-logic QF_UFLIA)
(declare-fun f (Int Int) Bool)
(assert (f (- 1) 1))
(check-sat)
(get-model)", format!("{}", q));
    }

    #[test]
    #[should_panic]
    fn test_bad_uf() {
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
    }

    #[test]
    #[should_panic]
    fn test_bad_ints() {
        let mut q = Query::new();
        q.set_logic("QF_UF");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
    }

    #[test]
    fn test_well_formed() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let node_n1 = q.mk_const("1");
        let node_sub = q.mk_sub(Rc::clone(&node_n1), Rc::clone(&node_n1));
        let a1 = q.mk_app("f", vec! [node_sub, node_n1]);
        q.assert(a1);
        println!("{}", q.well_formed());
        assert!(q.well_formed())
    }
}