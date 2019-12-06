use crate::qry::Query;
use crate::ast::{Term, Node, Symbol, symbol_from_str};
use crate::ctx::sort::{Sort, to_sort};

impl Query {

    pub fn mk_nonterminal(&self, name: &str, sort: &str) -> Term {
        let symbol = match to_sort(sort) {
            Sort::Bool => Symbol::BoolNT(name.to_owned()),
            Sort::Int => Symbol::IntNT(name.to_owned())
        };
        Term::new(Node:: new(
            symbol,
            vec! []
        ))
    }

    pub fn mk_const(&self, name: &str) -> Term {
        Term::new(Node:: new(
            symbol_from_str(name), 
            vec! []
        ))
    }

    pub fn mk_app(&self, name: &str, args: Vec<Term>) -> Term {
        Term::new(Node:: new(
            symbol_from_str(name), 
            args
        ))
    }

    #[allow(dead_code)]
    pub fn mk_add(&self, x: Term, y: Term) -> Term {
        self.mk_app("+", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_sub(&self, x: Term, y: Term) -> Term {
        self.mk_app("-", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_neg(&self, x: Term) -> Term {
        self.mk_app("-", vec![x])
    }

    #[allow(dead_code)]
    pub fn mk_ge(&self, x: Term, y: Term) -> Term {
        self.mk_app(">=", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_le(&self, x: Term, y: Term) -> Term {
        self.mk_app("<=", vec![x, y])
    }

    #[allow(dead_code)]
    pub fn mk_ite(&self, x: Term, y: Term, z: Term) -> Term {
        self.mk_app("ite", vec![x, y, z])
    }    
}

#[cfg(test)]
mod test {
    use std::rc::Rc;
    use crate::qry::Query;

    #[test]
    fn test_multiple_asserts(){
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("x", vec! [], "Int");
        q.declare_fun("f", vec! ["Int", "Int"], "Int");
        let node_x = q.mk_const("x");
        let node_7 = q.mk_const("7");
        let node_ge = q.mk_ge(Rc::clone(&node_x), Rc::clone(&node_7));
        let node_f = q.mk_app("f", vec! [Rc::clone(&node_x), Rc::clone(&node_x)]);
        let node_neg = q.mk_neg(node_f);
        let node_add = q.mk_add(node_neg, node_7);
        let node_le = q.mk_le(q.mk_sub(node_x, q.mk_const("33")), node_add);
        q.assert(node_ge);
        q.assert(node_le);
        assert_eq!("(set-logic QF_UFLIA)
(declare-const x Int)
(declare-fun f (Int Int) Int)
(assert (>= x 7))
(assert (<= (- x 33) (+ (- (f x x)) 7)))", format!("{}", q));
    }
}