use std::collections::{HashMap};

use crate::ast::{Term};
use crate::api::{mk_app};

pub fn rename(rules: &HashMap<String, String>, t: &Term) -> Term {
    let args = t.get_args().map(|a| rename(&rules, a)).collect();
    let symbol = rules.get(t.get_symbol()).unwrap_or(t.get_symbol());
    mk_app(symbol, args)
}