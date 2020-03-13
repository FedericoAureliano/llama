use std::fmt;

use crate::ast::symbols::Symbol;

pub type TypeId = usize;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    BitVec(u32),
    Array(Box<Type>, Box<Type>),
    Lambda(Vec<Box<Type>>, Box<Type>),
    Tuple(Vec<Box<Type>>),
    Alias(Box<Type>),
    Enum(Vec<Symbol>),
}

#[derive(Debug)]
pub struct TypeLevel {
    map : Vec<Type>,
}

impl TypeLevel {
    pub fn new() -> TypeLevel {
        TypeLevel {
            map : Vec::new(),
        }
    }

    pub fn contains(&self, ty: &Type) -> bool {
        self.map.contains(&ty)
    }

    pub fn type_to_typeid(&self, ty: &Type) -> Option<TypeId> {
        for i in 0..self.map.len() {
            if &self.map[i] == ty {
                return Some(i)
            }
        }
        None
    }

    pub fn typeid_to_type(&self, id: &TypeId) -> Option<&Type> {
        self.map.get(*id)
    }

    pub fn insert(&mut self, ty: Type) -> TypeId {
        self.map.push(ty);
        self.map.len() - 1 
    }
}

impl fmt::Display for TypeLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.map)
    }
}