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
    use super::Query;
    use crate::ast::integer::{mk_ge, mk_le, mk_sub};
    use crate::ast::{mk_const, mk_app};

    #[test]
    fn test_multiple_asserts(){
        let mut q = Query::new();
        q.declare_fun("x", vec! [], "Int");
        let a1 = mk_ge(vec! [mk_const("x"),  mk_const("7")]);
        let a2 = mk_le(vec! [mk_const("x"),  mk_const("7")]);
        q.assert(a1);
        q.assert(a2);
        q.check_sat();
        q.get_model();
        assert_eq!("(declare-const x Int)
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
        let node_n1 = mk_const("1");
        let node_1 = mk_const("1");
        let a1 = mk_app("f", vec! [mk_sub(vec![node_n1]), node_1]);
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
}