use crate::qry::{Query, Command};
use crate::ctx::{Solution};
use crate::ast::Symbol;

mod boolean;
mod integer;

impl Query {
    pub fn eval(&self, s: &Solution) -> Symbol {
        for command in self {
            match command {
                Command::Assert(a) => {
                    match self.peek_ctx().eval_bool(s, a) {
                        Symbol::BoolLit(true) => (),
                        Symbol::BoolLit(false) => return Symbol::BoolLit(false),
                        Symbol::BoolNT(n) => return Symbol::BoolNT(n),
                        _ => panic!("expected bool!")
                    }
                },
                _ => (),
            }
        };
        Symbol::BoolLit(true)
    }
}
