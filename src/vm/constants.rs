use parking_lot::Mutex;
use std::sync::Arc;

use crate::parser::cst;
use crate::parser::interner::Name;
use crate::parser::lexer::position::Position;

use crate::types::BuiltinType;
use crate::utils::GrowableVec;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstId(usize);

impl From<usize> for ConstId {
    fn from(data: usize) -> ConstId {
        ConstId(data)
    }
}

impl GrowableVec<Mutex<ConstData>> {
    pub fn idx(&self, index: ConstId) -> Arc<Mutex<ConstData>> {
        self.idx_usize(index.0 as usize)
    }
}

#[derive(Clone, Debug)]
pub struct ConstData {
    pub id: ConstId,
    pub pos: Position,
    pub name: Name,
    pub ty: BuiltinType,
    pub expr: Box<cst::Expr>,
    pub value: ConstValue,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {
    None,
    Bool(bool),
    Char(char),
    Int(i64),
    Float(f64),
}

impl ConstValue {
    pub fn to_bool(&self) -> bool {
        match self {
            &ConstValue::Bool(b) => b,
            _ => unreachable!(),
        }
    }

    pub fn to_char(&self) -> char {
        match self {
            &ConstValue::Char(c) => c,
            _ => unreachable!(),
        }
    }

    pub fn to_int(&self) -> i64 {
        match self {
            &ConstValue::Int(i) => i,
            _ => unreachable!(),
        }
    }

    pub fn to_float(&self) -> f64 {
        match self {
            &ConstValue::Float(f) => f,
            _ => unreachable!(),
        }
    }
}
