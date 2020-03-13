use bit_vec::BitVec;

use crate::ast::symbols::SymbolId;

#[derive(Debug, Clone)]
pub enum Term {
    SpecialConstant(Literal),
    Constant(SymbolId),
    Application(SymbolId, Vec<Box<Term>>),

    BvAdd(Box<Term>, Box<Term>),
    BvMinus(Box<Term>, Box<Term>),
    BvMul(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
pub enum Literal {
    BitVec(BitVec),
}