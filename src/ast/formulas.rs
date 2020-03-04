use crate::ast::terms::Term;

#[derive(Debug, Clone)]
pub enum Formula {
    True,
    False,
    Constant(u32),
    Application(u32, Vec<Term>),

    Equal(Box<Term>, Box<Term>),

    Not(Box<Term>),
    And(Box<Term>, Box<Term>),
    Or(Box<Term>, Box<Term>),
    Implies(Box<Term>, Box<Term>),

    Bvsle(Box<Term>, Box<Term>),
    Bvslt(Box<Term>, Box<Term>),
    Bvsge(Box<Term>, Box<Term>),
    Bvsgt(Box<Term>, Box<Term>),
}