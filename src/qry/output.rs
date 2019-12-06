use std::fmt;

use crate::qry::{Query, Command};

impl Query {
    fn command_to_string(&self, c : &Command) -> String {
        match c {
            Command::SetLogic => format!("(set-logic {})", self.ctx.get_logic()),
            Command::Declare(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                let args : Vec<String> = params.into_iter().map(|(_, s)| s.to_string()).collect();
                if args.len() > 0 {
                    format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string())
                } else {
                    format!("(declare-const {} {})", name, rsort.to_string())
                }
            },
            Command::Define(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                let body = self.ctx.get_body(&name).expect("definition body not found");
                let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                format!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), body)
            },
            Command::Synth(name) => {
                let (params, rsort) = self.ctx.get_decl(&name).expect("declaration not found!").first().expect("ureachable");
                match self.ctx.get_body(&name) {
                    Some(b) => {
                        let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                        format!("(define-fun {} ({}) {} {})", name, args.join(" "), rsort.to_string(), b)
                    },
                    None => {
                        let args : Vec<String> = params.into_iter().map(|(n, s)| format!("({} {})", n, s)).collect();
                        format!("(synth-blocking-fun {} ({}) {})", name, args.join(" "), rsort.to_string())    
                    }
                }
            },
            Command::Assert(a) => format!("(assert {})", a),
            Command::CheckSat => "(check-sat)".to_string(),
            Command::GetModel => "(get-model)".to_string(),
            Command::Push => "(push)".to_string(),
            Command::Pop => "(pop)".to_string(),
        }
    }
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q_iter = self.into_iter();
        let q_str : Vec<String> = q_iter.map(|c| self.command_to_string(c)).collect();
        write!(f, "{}", q_str.join("\n"))
    }
}

#[cfg(test)]
mod test {
    use std::rc::Rc;
    use super::Query;

    #[test]
    fn test_multiple_asserts(){
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_fun("x", vec! [], "Int");
        let node_x = q.mk_const("x");
        let node_7 = q.mk_const("7");
        let a1 = q.mk_ge(Rc::clone(&node_x), Rc::clone(&node_7));
        let a2 = q.mk_le(Rc::clone(&node_x), Rc::clone(&node_7));
        q.assert(a1);
        q.assert(a2);
        q.check_sat();
        q.get_model();
        assert_eq!("(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 7))
(assert (<= x 7))
(check-sat)
(get-model)", format!("{}", q));
    }

    #[test]
    fn test_uf_and_set_logic() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let node_n1 = q.mk_const("1");
        let node_sub = q.mk_neg(Rc::clone(&node_n1));
        let a1 = q.mk_app("f", vec! [node_sub, Rc::clone(&node_n1)]);
        q.assert(a1);
        q.check_sat();
        q.get_model();
        assert_eq!("(set-logic QF_UFLIA)
(declare-fun f (Int Int) Bool)
(assert (f (- 1) 1))
(check-sat)
(get-model)", format!("{}", q));
    }

    #[test]
    #[should_panic]
    fn test_bad_uf() {
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
    }

    #[test]
    #[should_panic]
    fn test_bad_ints() {
        let mut q = Query::new();
        q.set_logic("QF_UF");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
    }
}