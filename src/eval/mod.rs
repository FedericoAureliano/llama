use crate::context::{Context, Command, Solution};
use crate::term::{Term, mk_app};

mod boolean;
mod integer;

impl Context {
    pub fn eval(&self, s: &Solution) -> bool {
        let mut result = true;
        for command in self {
            match command {
                Command::Assert(a) => {result = result && self.eval_bool(a, s)},
                _ => (),
            }
        };
        result
    }

    pub(crate) fn build_solution(&self, params: &Vec<(String, String)>, args: &Vec<Box<Term>>, s: &Solution) -> Solution {
        let mut tmp_sol = Solution::new();
        for i in 0..params.len() {
            let a = match params[i].1.as_str() {
                "Bool" => self.eval_bool(&*args[i], s).to_string(),
                "Int" => self.eval_int(&*args[i], s).to_string(),
                _ => unimplemented!(),
            };
            tmp_sol.insert(params[i].0.clone(), (vec![], params[i].1.clone(), mk_app(a.as_str(), vec![])));
        }
        tmp_sol
    }
}
