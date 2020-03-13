use crate::parser::interner::Interner;
use crate::errors::diagnostic::Diagnostic;
use crate::parser::parser::NodeIdGenerator;
use crate::ast::symbols::{Symbol, SymbolId, SymbolLevel};
use crate::ast::types::{Type, TypeId, TypeLevel};

use crate::errors::message::SemError;
use crate::parser::lexer::position::Position;

use std::collections::HashMap;
use std::fmt;

pub mod symbols;
pub mod terms;
pub mod formulas;
pub mod types;

pub struct VM {
    pub interner: Interner,
    pub id_generator: NodeIdGenerator,
    pub diagnostic: Diagnostic,

    symbol_table: SymbolTable,
}

impl VM {
    pub fn new() -> Box<VM> {
        let vm = Box::new(VM {
            interner: Interner::new(),
            id_generator: NodeIdGenerator::new(),
            diagnostic: Diagnostic::new(),
            
            symbol_table: SymbolTable::new(),
        });

        vm
    }

    pub fn declare_enum(&mut self, ename: Symbol, evariants: Vec<Symbol>, pos: &Position) {
        if evariants.is_empty() {
            self.diagnostic.report(*pos, SemError::NoEnumValue(ename));
            return
        }

        let t = Type::Enum(evariants.clone());

        if self.symbol_table.type_data.contains(&t) {
            self.diagnostic.report(*pos, SemError::DuplicateEnum(ename));
            return
        }

        let tid = self.symbol_table.insert_type(t);
        self.symbol_table.name_type(ename.clone(), tid);

        for vname in evariants {
            if let Some(other_id) = self.symbol_table.get_type_id(&vname) {
                let other_name = self.symbol_table.get_type_name(&other_id).unwrap();
                self.diagnostic.report(*pos, SemError::DuplicateEnumVariant(vname, ename, other_name.clone()));
                return
            }
            self.symbol_table.insert_symbol(vname, tid);
        }
    }
}

impl fmt::Display for VM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol_table)
    }
}

pub struct SymbolTable {
    levels     : Vec<SymbolLevel>,
    type_data  : TypeLevel, // theres only one type level (global)
    type_names : HashMap<TypeId, String>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            levels     : vec![SymbolLevel::new()],
            type_data  : TypeLevel::new(),
            type_names : HashMap::new(),
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

    pub fn get_type_id(&self, sy: &Symbol) -> Option<TypeId> {
        for level in self.levels.iter().rev() {
            if let Some(tid) = level.get_type_id(sy) {
                return Some(tid);
            }
        }

        None
    }

    pub fn insert_symbol(&mut self, sy: Symbol, tid: TypeId) -> SymbolId {
        self.levels.last_mut().unwrap().insert(sy, tid)
    }

    pub fn insert_type(&mut self, ty: Type) -> TypeId {
        self.type_data.insert(ty)
    }

    pub fn name_type(&mut self, name: String, tid: TypeId) -> Option<String> {
        self.type_names.insert(tid, name)
    }

    pub fn get_type_name(&self, tid: &TypeId) ->  Option<&String> {
        self.type_names.get(&tid)
    }
}


impl fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let types = format!("{}", self.type_data);
        let aliases = format!("{:?}", self.type_names);
        let symbols = format!("{:?}", self.levels);
        write!(f, "Type Data:\n\t{}\nType Names:\n\t{}\nSymbols:\n\t{}", types, aliases, symbols)
    }
}