use crate::context::Context;

pub mod arith;

impl Context {
    pub fn eval(&mut self) {
        // substitute in definitions

        // use the theory evaluators
        self.eval_arith();
    }
}