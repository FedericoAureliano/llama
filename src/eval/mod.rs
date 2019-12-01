use crate::context::{Context, Command, Solution};
use crate::term::Term;

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
        debug!("evaluating {} with {:?}", self.tm.get_name(t), s);
        let args: Vec<bool> = self.tm.get_args(t).into_iter().map(|a| {
            if interpreted(self.tm.get_name(&a)) {
                self.eval_bool(&a, s)
            } else {
                match self.get_sort(&a).as_str() {
                    "Bool" => self.eval_bool(&a, s),
                    _ => panic!("not supported yet")
                }
            }
        }).collect();
        match self.tm.get_name(t).as_str() {
            "true" => true,
            "false" => true,
            "not" => !args[0],
            "or" => args.iter().fold(false, |r, a| r || *a),
            "and" => args.iter().fold(true, |r, a| r && *a),
            "=" => args.iter().fold(false, |r, a| r == *a),
            "=>" => !args[0] || args[1],
            name => {
                if self.defns.contains_key(name) {
                    let mut tmp_context = self.clone();
                    let mut tmp_sol = Solution::new();

                    let (params, _, body) = tmp_context.defns.get(name).expect("can't find definition in tmp_context");
                    let mut arg_terms: Vec<Term> = vec! [];
                    for a in args {
                        arg_terms.push(tmp_context.tm.apply(&format!("{}", a).to_owned(), vec![]));
                    }

                    assert_eq!(params.len(), arg_terms.len());
                    for i in 0..arg_terms.len() {
                        tmp_sol.insert(params[i].0.clone(), (vec![], params[i].1.clone(), arg_terms[i]));
                    }
                    self.eval_bool(body, &tmp_sol)
                    
                } else if s.contains_key(name) {
                    let mut tmp_context = self.clone();
                    let mut tmp_sol = Solution::new();

                    let (params, _, body) = s.get(&name.to_owned()).expect("can't find definition in solution");
                    
                    let mut arg_terms: Vec<Term> = vec! [];
                    for a in args {
                        arg_terms.push(tmp_context.tm.apply(&format!("{}", a).to_owned(), vec![]));
                    }

                    for i in 0..arg_terms.len() {
                        tmp_sol.insert(params[i].0.clone(), (vec![], params[i].1.clone(), arg_terms[i]));
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