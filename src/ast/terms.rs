use bit_vec::BitVec;

#[derive(Debug, Clone)]
pub enum Term {
    SpecialConstant(Literal),
    Constant(usize),
    Application(usize, Vec<Term>),

    BvAdd(Box<Term>, Box<Term>),
    BvMinus(Box<Term>, Box<Term>),
    BvMul(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
pub enum Literal {
    BitVec(BitVec),
}