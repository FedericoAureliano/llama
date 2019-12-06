use std::collections::{HashMap};

use crate::ast::{Term, Symbol, mk_app_from_symbol};

pub fn rename(rules: &HashMap<String, String>, t: &Term) -> Term {
    let args = t.get_args().map(|a| rename(&rules, a)).collect();
    let symbol = match t.get_symbol() {
        Symbol::Name(n) => if rules.contains_key(n) {
            Symbol::Name(rules.get(n).unwrap().clone())
        } else {
            Symbol::Name(n.clone())
        }
        Symbol::BoolLit(b) => Symbol::BoolLit(*b),
        Symbol::BoolNT(b) => Symbol::BoolNT(b.clone()),
        Symbol::IntLit(b) => Symbol::IntLit(*b),
        Symbol::IntNT(b) => Symbol::IntNT(b.clone()), 

    };
    mk_app_from_symbol(symbol, args)
}