use std::fmt;

use crate::ast::Query;
use crate::ast::Command;
use crate::ast::ASTNode;

fn command_to_string(c : &Command, q: &Query) -> String {
    match c {
        Command::SetLogic(l) => format!("(set-logic {})", l),
        Command::Declare(name) => {
            let (asorts, rsort) = q.get_signature(&name);
            let args : Vec<String> = asorts.into_iter().map(|s| s.to_string()).collect();
            if args.len() > 0 {
                format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string())
            } else {
                format!("(declare-const {} {})", name, rsort.to_string())
            }
        },
        Command::Assert(a) => format!("(assert {})", subtree_to_string(q, a)),
        Command::CheckSat => "(check-sat)".to_string(),
        Command::GetModel => "(get-model)".to_string(),
        Command::Push => "(push)".to_string(),
        Command::Pop => "(pop)".to_string(),
    }
}

fn subtree_to_string(q: &Query, parent: &ASTNode) -> String {
    let children = q.get_args(parent);
    let args : Vec<String> = children.into_iter().map(|s| subtree_to_string(q, &s)).collect();
    if args.len() > 0 {
        format!("({} {})", q.get_name(parent), args.join(" "))
    } else {
        format!("{}", q.get_name(parent))
    }
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q_iter = self.into_iter();
        let q_str : Vec<String> = q_iter.map(|c| command_to_string(c, self)).collect();
        write!(f, "{}", q_str.join("\n"))
    }
}

#[test]
fn test_subtree_to_string(){
    let mut q = Query::new();
    q.declare_fun("x", vec! [], "Int".to_owned());
    let node_x = q.apply("x", vec! []);
    let node_7 = q.apply("7", vec! []);
    let node_gt = q.apply(">", vec! [node_x, node_7]);
    println!("{}", subtree_to_string(&q, &node_gt));
}

#[test]
fn test_to_smtlib(){
    let mut q = Query::new();
    q.declare_fun("x", vec! [], "Int".to_owned());
    let node_x = q.apply("x", vec! []);
    let node_7 = q.apply("7", vec! []);
    let a1 = q.apply(">=", vec! [node_x, node_7]);
    let a2 = q.apply("<=", vec! [node_x, node_7]);
    q.assert(a1);
    q.assert(a2);
    q.check_sat();
    q.get_model();
    println!("{}", q);
}

#[test]
fn test_uf() {
    let mut q = Query::new();
    q.set_logic("QF_LIA".to_owned());
    q.declare_fun("f", vec! ["Int".to_owned(), "Int".to_owned()], "Bool".to_owned());
    let node_n1 = q.apply("-1", vec! []);
    let node_1 = q.apply("1", vec! []);
    let a1 = q.apply("f", vec! [node_n1, node_1]);
    q.assert(a1);
    q.check_sat();
    q.get_model();
    println!("{}", q);
}