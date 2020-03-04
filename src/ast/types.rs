use std::collections::HashMap;
use crate::parser::interner::Name;

#[derive(Debug, Clone)]
pub enum Type {
    BitVec(u32),
    Array(Box<Type>, Box<Type>),
    Lambda(Vec<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Alias(Box<Type>),
    Enum(Vec<usize>),
}

#[derive(Debug)]
pub struct TypeMap {
    levels: Vec<TypeLevel>,
}

impl TypeMap {
    pub fn new() -> TypeMap {
        TypeMap {
            levels: vec![TypeLevel::new()],
        }
    }

    pub fn push_level(&mut self) {
        self.levels.push(TypeLevel::new());
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
pub struct TypeLevel {
    map: HashMap<Name, usize>,
}

impl TypeLevel {
    // creates a new table
    pub fn new() -> TypeLevel {
        TypeLevel {
            map: HashMap::new(),
        }
    }

    pub fn contains(&self, name: Name) -> bool {
        self.map.contains_key(&name)
    }

    // finds Type in table
    pub fn get(&self, name: Name) -> Option<&usize> {
        self.map.get(&name)
    }

    pub fn insert(&mut self, name: Name, sym: usize) -> Option<usize> {
        self.map.insert(name, sym)
    }
}
