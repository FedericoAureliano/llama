use parking_lot::{Mutex, RwLock};
use std::ptr;

use crate::parser::ast;
use crate::parser::interner::*;
use crate::parser::lexer::File;
use crate::parser::parser::NodeIdGenerator;
use crate::errors::diag::Diagnostic;
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

static mut VM_GLOBAL: *const u8 = ptr::null();

pub fn get_vm() -> &'static VM<'static> {
    unsafe { &*(VM_GLOBAL as *const VM) }
}

pub fn set_vm(vm: &VM) {
    let ptr = vm as *const _ as *const u8;

    unsafe {
        VM_GLOBAL = ptr;
    }
}

pub struct VM<'ast> {
    pub interner: Interner,
    pub ast: &'ast ast::Ast,
    pub id_generator: NodeIdGenerator,
    pub files: Vec<File>,

    pub enum_defs: Vec<RwLock<EnumData>>,
    pub function_defs: GrowableVec<RwLock<Fct<'ast>>>,

    pub diagnostic: Mutex<Diagnostic>,
    pub symbol_table: Mutex<SymTable>,
    pub type_lists: Mutex<TypeLists>,
}

impl<'ast> VM<'ast> {
    pub fn new(ast: &'ast ast::Ast) -> Box<VM<'ast>> {
        let vm = Box::new(VM {
            files: Vec::new(),
            interner: Interner::new(),
            ast,

            enum_defs: Vec::new(),
            function_defs: GrowableVec::new(),

            id_generator: NodeIdGenerator::new(),
            diagnostic: Mutex::new(Diagnostic::new()),
            symbol_table: Mutex::new(SymTable::new()),
            type_lists: Mutex::new(TypeLists::new()),
        });

        set_vm(&vm);

        vm
    }

    pub fn file(&self, idx: FileId) -> &File {
        &self.files[idx.0 as usize]
    }
}

unsafe impl<'ast> Sync for VM<'ast> {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl From<u32> for FileId {
    fn from(data: u32) -> FileId {
        FileId(data)
    }
}
