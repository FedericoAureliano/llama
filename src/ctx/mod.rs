use std::collections::{HashMap};
use multimap::MultiMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::{Term, Symbol};

pub type Signature = (Vec<(String, Sort)>, Sort);
pub type Solution = HashMap<String, Rc<Term>>;

pub struct Context {
    symbol_tbl: MultiMap<String, Signature>,
    body_tbl: Solution,
    logic: Logic,
}

impl Context {
    pub fn new() -> Context {
        let mut ctx = Context {
            symbol_tbl: MultiMap::new(),
            body_tbl: HashMap::new(),
            logic: Logic::new(),
        };
        ctx.add_booleans();
        ctx
    }

    pub fn get_decl(&self, name: &str) -> Option<&Vec<Signature>> {
        // some interpreted functions are polymorphic (e.g. =)
        self.symbol_tbl.get_vec(name)
    }

    pub fn get_decls(&self) -> multimap::Iter<String, Signature> {
        self.symbol_tbl.iter()
    }

    pub fn add_decl(&mut self, name: &str, params: Vec<(String, Sort)>, rsort: Sort) {
        // can declare each function exactly once
        // debug!("ctx declaring {}", name);
        assert!(!self.symbol_tbl.contains_key(name), "{} already in symbol table", name);
        assert!(self.logic.uf || params.len() == 0);
        assert!(! (rsort == Sort::Int) || self.logic.lia);
        for (_, s) in params.iter() {
            assert!(! (s == &Sort::Int) || self.logic.lia);
        }
        self.symbol_tbl.insert(name.to_owned(), (params, rsort));
    }

    pub fn add_synth(&mut self, name: &str, params: Vec<(String, Sort)>, rsort: Sort) {
        // can declare each function exactly once
        assert!(!self.symbol_tbl.contains_key(name), "{} already in symbol table", name);
        self.symbol_tbl.insert(name.to_owned(), (params, rsort));
    }

    pub fn get_body(&self, name: &str) -> Option<&Rc<Term>> {
        self.body_tbl.get(name)
    }
    
    pub fn add_body(&mut self, name: &str, body: Rc<Term>) {
        // the new body has to be associated to exactly one function
        assert_eq!(self.symbol_tbl.get_vec(name).unwrap().len(), 1);
        self.body_tbl.insert(name.to_owned(), body);
    }

    pub fn remove_body(&mut self, name: &str) {
        // the new body has to be associated to exactly one function
        assert_eq!(self.symbol_tbl.get_vec(name).unwrap().len(), 1);
        self.body_tbl.remove(&name.to_owned());
    }

    pub fn update_logic(&mut self, l: &Logic) {
        if l.q {
            self.logic.q = true;
        }
        if l.lia {
            self.logic.lia = true;
            self.add_integers();
        }
        if l.uf {
            self.logic.uf = true;
        }
    }

    pub fn get_logic(&self) -> &Logic {
        &self.logic
    }

    // shallow version of check_sort
    pub fn get_sort(&self, t: &Rc<Term>) -> Option<Sort> {
        match t.get_symbol() {
            Symbol::Func(s) => {
                match self.get_decl(s) {
                    Some(v) => {
                        if v.len() == 1 {
                            let (_, rsort) = v[0];
                            Some(rsort)
                        } else {
                            // we have to figure out which version of the polymorphic operator we're dealing with
                            let args: Vec<&Rc<Term>> = t.get_args().collect();
                            for (params, rsort) in v {
                                if args.len() == params.len() {
                                    let mut matches = true;
                                    for i in 0..params.len() {
                                        matches = matches && match self.get_sort(args[i]) {
                                            Some(r) => r == params[i].1,
                                            None => false
                                        }
                                    }
                                    if matches {
                                        return Some(*rsort)
                                    }
                                }
                            }
                            None
                        }
                    }
                    None => None                    
                }
            },
            Symbol::BoolLit(_) => Some(Sort::Bool),
            Symbol::IntLit(_) => Some(Sort::Int),
            Symbol::NonTerm(s, _) => Some(*s),
        }
    }

    pub fn check_sort(&self, t: &Rc<Term>) -> Option<Sort> {
        let arg_sorts: Vec<Sort> = t.get_args()
            .inspect(|x| debug!("checking {}", x))
            .map(|a| self.check_sort(a)
            .expect("term not well-formed!"))
            .collect();

        match t.get_symbol() {
            Symbol::Func(s) => {
                match self.get_decl(s) {
                    Some(v) => {
                        for (params, rsort) in v {
                            let exp_sorts: Vec<&Sort> = params.into_iter().map(|(_, s)| s).collect();
                            if exp_sorts.len() != arg_sorts.len() {
                                continue
                            };
                            let mut result = true;
                            for i in 0..arg_sorts.len() {
                                result = result && exp_sorts[i] == &arg_sorts[i];
                            }
                            if result {
                                debug!("name: {} rsort: {}", t.get_symbol(), rsort);
                                return Some(*rsort)
                            }  
                        }
                        None
                    }
                    None => None                    
                }
            },
            Symbol::BoolLit(_) => Some(Sort::Bool),
            Symbol::IntLit(_) => Some(Sort::Int),
            Symbol::NonTerm(s, _) => Some(*s),
        }
    }

    fn add_booleans(&mut self) {
        // only support upto 4-ary
        for op in vec! ["and", "or", "="] {
            for names in vec! [vec! ["a", "b"], vec! ["a", "b"], vec! ["a", "b", "c"], vec! ["a", "b", "c", "d"]] {
                let params = names.into_iter().map(|n| (n.to_owned(), Sort::Bool)).collect();
                self.symbol_tbl.insert(op.to_owned(), (params, Sort::Bool));
            }
        }
        self.symbol_tbl.insert("not".to_owned(), (vec![("a".to_owned(), Sort::Bool)], Sort::Bool));
        self.symbol_tbl.insert("=>".to_owned(), (vec![("a".to_owned(), Sort::Bool), ("b".to_owned(), Sort::Bool)], Sort::Bool));
        self.symbol_tbl.insert("ite".to_owned(), (vec![("a".to_owned(), Sort::Bool), ("b".to_owned(), Sort::Bool), ("c".to_owned(), Sort::Bool)], Sort::Bool));
    }

    fn add_integers(&mut self) {
        // only support upto 4-ary
        for op in vec! ["="] {
            for names in vec! [vec! ["a", "b"], vec! ["a", "b"], vec! ["a", "b", "c"], vec! ["a", "b", "c", "d"]] {
                let params = names.into_iter().map(|n| (n.to_owned(), Sort::Int)).collect();
                self.symbol_tbl.insert(op.to_owned(), (params, Sort::Bool));
            }
        }
        // binary
        for op in vec! ["<", "<=", ">", ">="] {
            for names in vec! [vec! ["a", "b"]] {
                let params = names.into_iter().map(|n| (n.to_owned(), Sort::Int)).collect();
                self.symbol_tbl.insert(op.to_owned(), (params, Sort::Bool));
            }
        }
        // only support upto 4-ary
        for op in vec! ["+", "*", "-"] {
            for names in vec! [vec! ["a", "b"], vec! ["a", "b"], vec! ["a", "b", "c"], vec! ["a", "b", "c", "d"]] {
                let params = names.into_iter().map(|n| (n.to_owned(), Sort::Int)).collect();
                self.symbol_tbl.insert(op.to_owned(), (params, Sort::Int));
            }
        }
        self.symbol_tbl.insert("-".to_owned(), (vec![("a".to_owned(), Sort::Int)], Sort::Int));
        self.symbol_tbl.insert("ite".to_owned(), (vec![("a".to_owned(), Sort::Bool), ("b".to_owned(), Sort::Int), ("c".to_owned(), Sort::Int)], Sort::Int));
    }
}

#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Sort {
    Bool,
    Int,
}

impl Sort {
    pub fn new(s: &str) -> Sort {
        match s {
            "Bool" => Sort::Bool,
            "Int" => Sort::Int,
            _ => panic!(format!("sort {} not supported", s))
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printable = match *self {
            Sort::Bool => "Bool",
            Sort::Int => "Int",
        };
        write!(f, "{}", printable)
    }
}


pub struct Logic {
    pub q: bool,
    pub lia: bool,
    pub uf: bool,
}

impl Logic {
    pub fn new() -> Logic {
        let l = Logic {
            q: false,
            lia: false,
            uf: false,
        };
        l
    }
    pub fn to_logic(s: &str) -> Logic {
        match s {
            "QF_UF" => Logic {
                q: false,
                lia: false,
                uf: true,
            },
            "QF_LIA" => Logic {
                q: false,
                lia: true,
                uf: false,
            },
            "QF_UFLIA" => Logic {
                q: false,
                lia: true,
                uf: true,
            },
            "ALL" => Logic {
                q: true,
                lia: true,
                uf: true,
            },
            _ => panic!(format!("logic {} not supported", s))
        }
    }
}

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q = if self.q {""} else {"QF_"};
        let uf = if self.uf {"UF"} else {""};
        let lia = if self.lia {"LIA"} else {""};
        write!(f, "{}{}{}", q, uf, lia)
    }
}