use parking_lot::{Mutex, RwLock};

use crate::parser::cst;
use crate::parser::interner::*;
use crate::parser::parser::NodeIdGenerator;
use crate::errors::diagnostic::Diagnostic;
use crate::symbols::SymTable;
use crate::types::TypeLists;
use crate::utils::GrowableVec;

pub use self::source::{CallType, ConvInfo, FctSrc, ForTypeInfo, IdentType, NodeMap, Var, VarId};
pub use self::constants::{ConstData, ConstId, ConstValue};
pub use self::enums::{EnumData, EnumId};
pub use self::functions::{Fct, FctId, FctKind, FctParent, Intrinsic};
pub use self::fields::{Field, FieldDef, FieldId};

mod source;
mod constants;
mod enums;
mod fields;
mod functions;

pub struct VM<'cst> {
    pub interner: Interner,
    pub cst: &'cst cst::Cst,
    pub id_generator: NodeIdGenerator,

    pub enum_defs: Vec<RwLock<EnumData>>,
    pub function_defs: GrowableVec<RwLock<Fct<'cst>>>,

    pub diagnostic: Mutex<Diagnostic>,
    pub symbol_table: Mutex<SymTable>,
    pub type_lists: Mutex<TypeLists>,
}

impl<'cst> VM<'cst> {
    pub fn new(cst: &'cst cst::Cst) -> Box<VM<'cst>> {
        let vm = Box::new(VM {
            interner: Interner::new(),
            cst,

            enum_defs: Vec::new(),
            function_defs: GrowableVec::new(),

            id_generator: NodeIdGenerator::new(),
            diagnostic: Mutex::new(Diagnostic::new()),
            symbol_table: Mutex::new(SymTable::new()),
            type_lists: Mutex::new(TypeLists::new()),
        });

        vm
    }
}
