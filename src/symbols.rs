use std::collections::HashMap;

use self::Symbol::*;
use crate::vm::{EnumId};
use crate::parser::interner::Name;

#[derive(Debug)]
pub struct SymTable {
    levels: Vec<SymLevel>,
}

impl SymTable {
    pub fn new() -> SymTable {
        SymTable {
            levels: vec![SymLevel::new()],
        }
    }

    pub fn push_level(&mut self) {
        self.levels.push(SymLevel::new());
    }

    pub fn pop_level(&mut self) {
        assert!(self.levels.len() > 1);

        self.levels.pop();
    }

    pub fn levels(&self) -> usize {
        self.levels.len()
    }

    pub fn get(&self, name: Name) -> Option<Symbol> {
        for level in self.levels.iter().rev() {
            if let Some(val) = level.get(name) {
                return Some(val.clone());
            }
        }

        None
    }

    pub fn get_enum(&self, name: Name) -> Option<EnumId> {
        self.get(name).and_then(|n| n.to_enum())
    }

    pub fn insert(&mut self, name: Name, sym: Symbol) -> Option<Symbol> {
        self.levels.last_mut().unwrap().insert(name, sym)
    }
}

#[derive(Debug)]
pub struct SymLevel {
    map: HashMap<Name, Symbol>,
}

impl SymLevel {
    // creates a new table
    pub fn new() -> SymLevel {
        SymLevel {
            map: HashMap::new(),
        }
    }

    pub fn contains(&self, name: Name) -> bool {
        self.map.contains_key(&name)
    }

    // finds symbol in table
    pub fn get(&self, name: Name) -> Option<&Symbol> {
        self.map.get(&name)
    }

    pub fn insert(&mut self, name: Name, sym: Symbol) -> Option<Symbol> {
        self.map.insert(name, sym)
    }
}

#[derive(Debug, Clone)]
pub enum Symbol {
    EnumSymbol(EnumId),
}

impl Symbol {
    pub fn is_enum(&self) -> bool {
        match *self {
            EnumSymbol(_) => true,
            // _ => false,
        }
    }

    pub fn to_enum(&self) -> Option<EnumId> {
        match *self {
            EnumSymbol(id) => Some(id),
            // _ => None,
        }
    }
}
