use crate::ast::{Node, Term};

pub fn mk_app(name: &str, args: Vec<Term>) -> Term {
   Term::new(Node:: new(
        name.to_owned(), 
        args
    ))
}

pub fn mk_const(name: &str) -> Term {
   Term::new(Node:: new(
        name.to_owned(), 
        vec! []
    ))
}

#[allow(dead_code)]
pub fn mk_add(x: Term, y: Term) -> Term {
    Term::new(Node::new( 
        "+".to_owned(), 
        vec![x, y]
    ))
}

#[allow(dead_code)]
pub fn mk_sub(x: Term, y: Term) -> Term {
    Term::new(Node::new( 
        "-".to_owned(), 
        vec![x, y]
    ))
}

#[allow(dead_code)]
pub fn mk_neg(x: Term) -> Term {
    Term::new(Node::new( 
        "-".to_owned(), 
        vec![x]
    ))
}

#[allow(dead_code)]
pub fn mk_ge(x: Term, y: Term) -> Term {
    Term::new(Node::new( 
        ">=".to_owned(), 
        vec![x, y]
    ))
}

#[allow(dead_code)]
pub fn mk_le(x: Term, y: Term) -> Term {
    Term::new(Node::new( 
        "<=".to_owned(), 
        vec![x, y]
    ))
}


#[cfg(test)]
mod test {
    use std::rc::Rc;
    use crate::qry::Query;
    use super::{mk_ge, mk_le, mk_neg, mk_const, mk_app, mk_sub, mk_add};

    #[test]
    fn test_multiple_asserts(){
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("x", vec! [], "Int");
        q.declare_fun("f", vec! ["Int", "Int"], "Int");
        let node_x = mk_const("x");
        let node_7 = mk_const("7");
        let node_ge = mk_ge(Rc::clone(&node_x), Rc::clone(&node_7));
        let node_f = mk_app("f", vec! [Rc::clone(&node_x), Rc::clone(&node_x)]);
        let node_neg = mk_neg(node_f);
        let node_add = mk_add(node_neg, node_7);
        let node_le = mk_le(mk_sub(node_x, mk_const("33")), node_add);
        q.assert(node_ge);
        q.assert(node_le);
        assert_eq!("(set-logic QF_UFLIA)
(declare-const x Int)
(declare-fun f (Int Int) Int)
(assert (>= x 7))
(assert (<= (- x 33) (+ (- (f x x)) 7)))", format!("{}", q));
    }
}