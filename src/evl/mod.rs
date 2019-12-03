use crate::qry::{Query, Command};
use crate::ctx::{Solution};

mod boolean;
mod integer;

impl Query {
    pub fn eval(&self, s: &Solution) -> bool {
        let mut result = true;
        for command in self {
            match command {
                Command::Assert(a) => {result = result && self.peek_ctx().eval_bool(s, a)},
                _ => (),
            }
        };
        result
    }
}
