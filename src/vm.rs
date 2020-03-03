use parking_lot::{Mutex, RwLock};

use crate::parser::interner::*;
use crate::parser::parser::NodeIdGenerator;
use crate::errors::diagnostic::Diagnostic;
use crate::symbols::SymTable;
use crate::types::TypeLists;

pub use self::source::{NodeMap};
pub use self::enums::{EnumData, EnumId};

mod source;
mod enums;

pub struct VM {
    pub interner: Interner,
    pub id_generator: NodeIdGenerator,
    pub diagnostic: Mutex<Diagnostic>,

    pub enum_defs: Vec<RwLock<EnumData>>,

    pub symbol_table: Mutex<SymTable>,
    pub type_lists: Mutex<TypeLists>,
}

impl VM {
    pub fn new() -> Box<VM> {
        let vm = Box::new(VM {
            interner: Interner::new(),
            id_generator: NodeIdGenerator::new(),
            diagnostic: Mutex::new(Diagnostic::new()),

            enum_defs: Vec::new(),

            symbol_table: Mutex::new(SymTable::new()),
            type_lists: Mutex::new(TypeLists::new()),
        });

        vm
    }
}
