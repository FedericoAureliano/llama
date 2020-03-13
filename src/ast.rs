use crate::parser::interner::Interner;
use crate::errors::diagnostic::Diagnostic;
use crate::parser::parser::NodeIdGenerator;
use crate::ast::symbols::{Symbol, SymbolId, SymbolLevel};
use crate::ast::types::{Type, TypeId, TypeLevel};
use crate::parser::cst::TypeIdentifierSyntaxObject;
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

    pub fn parse_type(&self, so: &TypeIdentifierSyntaxObject) -> Type {
        match so {
            TypeIdentifierSyntaxObject::Basic(b) => {
                let mut type_str = self.interner.str(b.name).to_string();

                if let Some(tid) = self.symbol_table.name_to_typeid(&type_str) {
                    return self.symbol_table.typeid_to_type(&tid).unwrap().clone()
                }

                let width = type_str.split_off(2).parse::<u32>().unwrap();
                assert_eq!(type_str, "bv");
                let base = Type::BitVec(width);

                if let Some(p) = &b.params {
                    Type::Array(Box::new(base), Box::new(self.parse_type(&p)))
                } else {
                    base
                }
            }
            TypeIdentifierSyntaxObject::Tuple(t) => {
                let mut contents = Vec::new();
                for e in &t.subtypes {
                    contents.push(Box::new(self.parse_type(&e)))
                };
                Type::Tuple(contents)
            }
        }
    }

    pub fn declare_enum(&mut self, ename: Symbol, evariants: Vec<Symbol>, pos: &Position) {
        if evariants.is_empty() {
            self.diagnostic.report(*pos, SemError::NoEnumValue(ename));
            return
        }

        let t = Type::Enum(evariants.clone());

        let tid = match self.symbol_table.insert_type(t) {
            Some(id) => {
                self.symbol_table.name_type(ename.clone(), id); 
                id
            }
            None => {
                self.diagnostic.report(*pos, SemError::DuplicateEnum(ename));
                return
            }
        };

        for vname in evariants {
            if let Some(other_id) = self.symbol_table.symbol_to_typeid(&vname) {
                let other_name = self.symbol_table.typeid_to_name(&other_id).unwrap();
                self.diagnostic.report(*pos, SemError::DuplicateEnumVariant(vname, ename, other_name.clone()));
                return
            }
            self.symbol_table.insert_symbol(vname, tid);
        }
    }

    pub fn declare_alias(&mut self, name: Symbol, tid : TypeId, pos: &Position) {
        if let Some(_) = self.symbol_table.name_to_typeid(&name) {
            self.diagnostic.report(*pos, SemError::DuplicateAlias(name));
            return
        }
        self.symbol_table.name_type(name, tid);
    }

    pub fn declare_type(&mut self, ty: Type) -> TypeId {
        if let Some(tid) = self.symbol_table.type_to_typeid(&ty) {
            tid
        } else {
            self.symbol_table.insert_type(ty).unwrap()
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

    pub fn symbol_to_typeid(&self, sy: &Symbol) -> Option<TypeId> {
        for level in self.levels.iter().rev() {
            if let Some(tid) = level.symbol_to_typeid(sy) {
                return Some(tid);
            }
        }

        None
    }

    pub fn insert_symbol(&mut self, sy: Symbol, tid: TypeId) -> SymbolId {
        self.levels.last_mut().unwrap().insert(sy, tid)
    }

    pub fn insert_type(&mut self, ty: Type) -> Option<TypeId> {
        if self.type_data.contains(&ty) {
            None
        } else {
            Some(self.type_data.insert(ty))
        }
    }

    pub fn name_type(&mut self, name: String, tid: TypeId) -> Option<String> {
        self.type_names.insert(tid, name)
    }

    pub fn typeid_to_name(&self, tid: &TypeId) ->  Option<&String> {
        self.type_names.get(&tid)
    }


    pub fn typeid_to_type(&self, tid: &TypeId) ->  Option<&Type> {
        self.type_data.typeid_to_type(tid)
    }

    pub fn name_to_typeid(&self, name: &String) -> Option<TypeId> {
        for (tid, n) in &self.type_names {
            if n == name {
                return Some(*tid)
            }
        }

        None   
    }

    pub fn type_to_typeid(&self, ty: &Type) -> Option<TypeId> {
        self.type_data.type_to_typeid(ty)
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