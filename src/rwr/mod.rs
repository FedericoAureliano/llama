use std::collections::{HashMap};

use crate::ast::Term;

pub fn rename(rules: &HashMap<String, String>, t: Term) -> Term {
    let name = t.peek_name().clone();
    let args: Vec<Box<Term>> = t.get_args().into_iter().map(|a| Box::new(rename(rules, *a))).collect();
    Term::new(rules.get(&name).unwrap_or(&name).to_string(), args)
}
