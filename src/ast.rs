use crate::parser::interner::Interner;
use crate::errors::diagnostic::Diagnostic;
use crate::parser::parser::NodeIdGenerator;
use crate::ast::symbols::SymbolMap;
use crate::ast::types::{Type, TypeMap};
use crate::parser::interner::Name;

pub mod symbols;
pub mod terms;
pub mod formulas;
pub mod types;

pub struct VM {
    pub interner: Interner,
    pub id_generator: NodeIdGenerator,
    pub diagnostic: Diagnostic,
 
    // indexed by type id
    pub type_def: Vec<Type>,
    // indexed by type id, gives name
    pub type_name: Vec<Name>,
    // Map from Name to type id (usize)
    pub type_map: TypeMap,

    // indexed by symbol id, gives us type id (usize)
    pub symbol_type: Vec<usize>,
    // indexed by symbol id, gives name
    pub symbol_name: Vec<Name>,
    // Map from Name to symbol (usize)
    pub symbol_map: SymbolMap,
}

impl VM {
    pub fn new() -> Box<VM> {
        let vm = Box::new(VM {
            interner: Interner::new(),
            id_generator: NodeIdGenerator::new(),
            diagnostic: Diagnostic::new(),
            
            type_def: Vec::new(),
            type_name: Vec::new(),
            type_map: TypeMap::new(),
            
            symbol_type: Vec::new(),
            symbol_name: Vec::new(),
            symbol_map: SymbolMap::new(),
        });

        vm
    }
}
