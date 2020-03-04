use std::collections::HashMap;

use crate::parser::interner::Name;

#[derive(Debug)]
pub struct SymbolMap {
    levels: Vec<SymbolLevel>,
}

impl SymbolMap {
    pub fn new() -> SymbolMap {
        SymbolMap {
            levels: vec![SymbolLevel::new()],
        }
    }

    pub fn push_level(&mut self) {
        self.levels.push(SymbolLevel::new());
    }

    pub fn pop_level(&mut self) {
        assert!(self.levels.len() > 1);

        self.levels.pop();
    }

    pub fn levels(&self) -> usize {
        self.levels.len()
    }

    pub fn get(&self, name: Name) -> Option<usize> {
        for level in self.levels.iter().rev() {
            if let Some(val) = level.get(name) {
                return Some(val.clone());
            }
        }

        None
    }

    pub fn insert(&mut self, name: Name, sym: usize) -> Option<usize> {
        self.levels.last_mut().unwrap().insert(name, sym)
    }
}

#[derive(Debug)]
pub struct SymbolLevel {
    map: HashMap<Name, usize>,
}

impl SymbolLevel {
    // creates a new table
    pub fn new() -> SymbolLevel {
        SymbolLevel {
            map: HashMap::new(),
        }
    }

    pub fn contains(&self, name: Name) -> bool {
        self.map.contains_key(&name)
    }

    // finds symbol in table
    pub fn get(&self, name: Name) -> Option<&usize> {
        self.map.get(&name)
    }

    pub fn insert(&mut self, name: Name, sym: usize) -> Option<usize> {
        self.map.insert(name, sym)
    }
}
