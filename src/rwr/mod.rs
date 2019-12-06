use std::collections::{HashMap};
use std::rc::Rc;

use crate::ast::{Term, Symbol};

pub fn rename(rules: &HashMap<String, String>, t: &Rc<Term>) -> Rc<Term> {
    let args = t.get_args().map(|a| rename(&rules, a)).collect();
    let symbol = match t.get_symbol() {
        Symbol::Func(n) => if rules.contains_key(n) {
            Symbol::Func(rules.get(n).unwrap().clone())
        } else {
            Symbol::Func(n.clone())
        }
        Symbol::BoolLit(b) => Symbol::BoolLit(*b),
        Symbol::IntLit(b) => Symbol::IntLit(*b),
        Symbol::NonTerm(s, n) => Symbol::NonTerm(*s, n.clone()),

    };
    Term::mk_app(symbol, args)
}