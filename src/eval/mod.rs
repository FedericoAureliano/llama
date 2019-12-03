use crate::query::{Query, Command};
use crate::context::Context;

mod boolean;
mod integer;

impl Query {
    pub fn eval(&self, s: &Context) -> bool {
        let mut result = true;
        for command in self {
            match command {
                Command::Assert(a) => {result = result && s.eval_bool(a)},
                _ => (),
            }
        };
        result
    }
}
