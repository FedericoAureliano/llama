use crate::context::{Context, Command, Solution};
use crate::term::{Term, apply};

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

    pub fn eval_bool(&self, t: &Term, s: &Solution) -> bool {
        let args: Vec<bool> = t.peek_args().into_iter().map(|a| {
            if interpreted(a.peek_name()) {
                self.eval_bool(&a, s)
            } else {
                match self.get_sort(&a).as_str() {
                    "Bool" => self.eval_bool(&a, s),
                    _ => panic!("not supported yet")
                }
            }
        }).collect();
        match t.peek_name().as_str() {
            "true" => true,
            "false" => true,
            "not" => !args[0],
            "or" => args.iter().fold(false, |r, a| r || *a),
            "and" => args.iter().fold(true, |r, a| r && *a),
            "=" => args.iter().fold(false, |r, a| r == *a),
            "=>" => !args[0] || args[1],
            name => {
                if self.has_defn(t.peek_name()) {
                    let mut tmp_sol = Solution::new();

                    let (params, _, body) = self.get_defn(t.peek_name());
                    for i in 0..params.len() {
                        tmp_sol.insert(params[i].0.clone(), (vec![], params[i].1.clone(), apply(&format!("{}", args[i]).to_owned(), vec![])));
                    }
                    self.eval_bool(body, &tmp_sol)
                    
                } else if s.contains_key(name) {
                    let mut tmp_sol = Solution::new();

                    let (params, _, body) = s.get(&name.to_owned()).expect("can't find definition in solution");
                    for i in 0..params.len() {
                        tmp_sol.insert(params[i].0.clone(), (vec![], params[i].1.clone(), apply(&format!("{}", args[i]).to_owned(), vec![])));
                    }
                    self.eval_bool(body, &tmp_sol)

                } else {
                    debug!("{} is not supported yet", name);
                    panic!("not supported yet")
                }
            }
        }
    }
}

fn interpreted(a: &str) -> bool {
    match a {
        "true"
        | "false" 
        | "not"
        | "or" 
        | "and" 
        | "=" 
        | "=>" => true,
        _ => false,
    }
}


#[cfg(test)]
mod test {
    use super::Context;

    #[test]
    fn test_eval(){
        use std::fs;
        let unparsed_query = fs::read_to_string("examples/uf.smt2").expect("cannot read file");
        let mut query = Context::new();
        query.parse_query(&unparsed_query).expect("cannot parse file");
        
        let unparsed_answer = fs::read_to_string("examples/uf_result.smt2").expect("cannot read file");
        let s = query.parse_answer(&unparsed_answer).expect("cannot parse file");
        assert!(query.eval(&s));
    }
}