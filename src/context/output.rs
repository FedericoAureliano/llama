use std::fmt;

use crate::context::Context;
use crate::context::Command;

impl Context {
    fn command_to_string(&self, c : &Command) -> String {
        match c {
            Command::SetLogic(l) => format!("(set-logic {})", l),
            Command::Declare(name) => {
                let (asorts, rsort) = self.get_decl(&name);
                let args : Vec<String> = asorts.into_iter().map(|s| s.to_string()).collect();
                if args.len() > 0 {
                    format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string())
                } else {
                    format!("(declare-const {} {})", name, rsort.to_string())
                }
            },
            Command::Define(name) => {
                let (params, rsort, body) = self.get_defn(&name);
                let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                format!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), body)
            },
            Command::Assert(a) => format!("(assert {})", a),
            Command::CheckSat => "(check-sat)".to_string(),
            Command::GetModel => "(get-model)".to_string(),
            Command::Push => "(push)".to_string(),
            Command::Pop => "(pop)".to_string(),
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q_iter = self.into_iter();
        let q_str : Vec<String> = q_iter.map(|c| self.command_to_string(c)).collect();
        write!(f, "{}", q_str.join("\n"))
    }
}


#[cfg(test)]
mod test {
    use super::Context;
    use crate::term::apply;

    #[test]
    fn test_to_smtlib(){
        let mut q = Context::new();
        q.declare_fun("x", vec! [], "Int".to_owned());
        let a1 = apply(">=", vec! [apply("x", vec! []),  apply("7", vec! [])]);
        let a2 = apply("<=", vec! [apply("x", vec! []),  apply("7", vec! [])]);
        q.assert(a1);
        q.assert(a2);
        q.check_sat();
        q.get_model();
        println!("{}", q);
    }

    #[test]
    fn test_uf() {
        let mut q = Context::new();
        q.set_logic("QF_LIA".to_owned());
        q.declare_fun("f", vec! ["Int".to_owned(), "Int".to_owned()], "Bool".to_owned());
        let node_n1 = apply("-1", vec! []);
        let node_1 = apply("1", vec! []);
        let a1 = apply("f", vec! [node_n1, node_1]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        println!("{}", q);
    }
}