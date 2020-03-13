use std::fmt;

use crate::ast::types::TypeId;

pub type SymbolId = usize;
pub type Symbol = String;

#[derive(Debug)]
pub struct SymbolLevel {
    map : Vec<(Symbol, TypeId)>
}

impl SymbolLevel {
    pub fn new() -> SymbolLevel {
        SymbolLevel {
            map : Vec::new()
        }
    }

    pub fn symbol_to_symbolid(&self, sy: &Symbol) -> Option<SymbolId> {
        for i in 0..self.map.len() {
            let (s, _) = &self.map[i];
            if  s == sy {
                return Some(i)
            }
        }
        None
    }

    pub fn symbol_to_typeid(&self, sy: &Symbol) -> Option<TypeId> {
        for i in 0..self.map.len() {
            let (s, tid) = &self.map[i];
            if  s == sy {
                return Some(*tid)
            }
        }
        None
    }

    pub fn symbolid_to_symbol(&self, id: SymbolId) -> Option<&Symbol> {
        let (sy, _) = self.map.get(id)?;
        Some(sy)
    }

    pub fn insert(&mut self, sy: Symbol, ty: TypeId) -> SymbolId {
        self.map.push((sy, ty));
        self.map.len() - 1
    }
}

impl fmt::Display for SymbolLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.map)
    }
}