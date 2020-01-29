use parking_lot::{Mutex, RwLock};
use std::ptr;
use std::sync::Arc;

use crate::error::diag::Diagnostic;
use crate::sym::Sym::*;
use crate::sym::*;
use crate::ty::{BuiltinType, LambdaTypes, TypeList, TypeLists, TypeParamId};
use crate::utils::GrowableVec;

use crate::parser::ast;
use crate::parser::interner::*;
use crate::parser::lexer::File;
use crate::parser::parser::NodeIdGenerator;

pub use self::class::{
    find_field_in_class, find_method_in_class, find_methods_in_class, Class, ClassDef, ClassDefId,
    ClassId, TypeParam,
};
pub use self::cnst::{ConstData, ConstId, ConstValue};
pub use self::enums::{EnumData, EnumId};
pub use self::fct::{Fct, FctId, FctKind, FctParent, Intrinsic};
pub use self::field::{Field, FieldDef, FieldId};
pub use self::global::{GlobalData, GlobalId};
pub use self::impls::{ImplData, ImplId};
pub use self::src::{CallType, ConvInfo, FctSrc, ForTypeInfo, IdentType, NodeMap, Var, VarId};
pub use self::strct::{
    StructData, StructDef, StructDefId, StructFieldData, StructFieldDef, StructId,
};
pub use self::traits::{TraitData, TraitId};
pub use self::vip::{KnownClasses, KnownElements, KnownFunctions};

pub mod class;
mod cnst;
mod enums;
mod fct;
mod field;
mod global;
mod impls;
mod src;
mod strct;
mod traits;
mod vip;

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
    pub diag: Mutex<Diagnostic>,
    pub sym: Mutex<SymTable>,
    pub vips: KnownElements,
    pub consts: GrowableVec<Mutex<ConstData>>, // stores all const definitions
    pub structs: GrowableVec<Mutex<StructData>>, // stores all struct source definitions
    pub struct_defs: GrowableVec<Mutex<StructDef>>, // stores all struct definitions
    pub classes: GrowableVec<RwLock<Class>>,   // stores all class source definitions
    pub class_defs: GrowableVec<RwLock<ClassDef>>, // stores all class definitions
    pub fcts: GrowableVec<RwLock<Fct<'ast>>>,  // stores all function definitions
    pub enums: Vec<RwLock<EnumData>>,          // store all enum definitions
    pub traits: Vec<RwLock<TraitData>>,        // stores all trait definitions
    pub impls: Vec<RwLock<ImplData>>,          // stores all impl definitions
    pub globals: GrowableVec<Mutex<GlobalData>>, // stores all global variables
    pub lists: Mutex<TypeLists>,
    pub lambda_types: Mutex<LambdaTypes>,
}

impl<'ast> VM<'ast> {
    pub fn new(ast: &'ast ast::Ast) -> Box<VM<'ast>> {
        let empty_class_id: ClassId = 0.into();
        let empty_class_def_id: ClassDefId = 0.into();
        let empty_trait_id: TraitId = 0.into();
        let empty_fct_id: FctId = 0.into();
        // let gc = Gc::new(&args);

        let vm = Box::new(VM {
            consts: GrowableVec::new(),
            structs: GrowableVec::new(),
            struct_defs: GrowableVec::new(),
            classes: GrowableVec::new(),
            files: Vec::new(),
            class_defs: GrowableVec::new(),
            enums: Vec::new(),
            traits: Vec::new(),
            impls: Vec::new(),
            globals: GrowableVec::new(),
            interner: Interner::new(),
            vips: KnownElements {
                bool_class: empty_class_id,
                byte_class: empty_class_id,
                char_class: empty_class_id,
                int_class: empty_class_id,
                long_class: empty_class_id,
                float_class: empty_class_id,
                double_class: empty_class_id,
                object_class: empty_class_id,
                string_class: empty_class_id,

                array_class: empty_class_id,

                cls: KnownClasses {
                    string_buffer: empty_class_id,
                },

                fct: KnownFunctions {
                    string_buffer_empty: empty_fct_id,
                    string_buffer_append: empty_fct_id,
                    string_buffer_to_string: empty_fct_id,
                },

                testing_class: empty_class_id,
                throwable_class: empty_class_id,
                error_class: empty_class_id,
                exception_class: empty_class_id,
                stack_trace_element_class: empty_class_id,

                equals_trait: empty_trait_id,
                comparable_trait: empty_trait_id,
                stringable_trait: empty_trait_id,
                iterator_trait: Mutex::new(None),

                byte_array_def: Mutex::new(None),
                int_array_def: Mutex::new(None),
                str_class_def: Mutex::new(None),
                obj_class_def: Mutex::new(None),
                ste_class_def: Mutex::new(None),
                ex_class_def: Mutex::new(None),

                free_object_class_def: empty_class_def_id,
                free_array_class_def: empty_class_def_id,
            },
            ast,
            id_generator: NodeIdGenerator::new(),
            diag: Mutex::new(Diagnostic::new()),
            sym: Mutex::new(SymTable::new()),
            fcts: GrowableVec::new(),
            lists: Mutex::new(TypeLists::new()),
            lambda_types: Mutex::new(LambdaTypes::new()),
        });

        set_vm(&vm);

        vm
    }

    pub fn add_fct(&mut self, mut fct: Fct<'ast>) -> FctId {
        let mut fcts = self.fcts.lock();
        let fctid = FctId(fcts.len());

        fct.id = fctid;

        fcts.push(Arc::new(RwLock::new(fct)));

        fctid
    }

    pub fn add_fct_to_sym(&mut self, fct: Fct<'ast>) -> Result<FctId, Sym> {
        let name = fct.name;
        let fctid = self.add_fct(fct);

        let mut sym = self.sym.lock();

        match sym.get(name) {
            Some(sym) => Err(sym),
            None => {
                assert!(sym.insert(name, SymFct(fctid)).is_none());

                Ok(fctid)
            }
        }
    }

    #[cfg(test)]
    pub fn cls_by_name(&self, name: &'static str) -> ClassId {
        let name = self.interner.intern(name);
        self.sym.lock().get_class(name).expect("class not found")
    }

    #[cfg(test)]
    pub fn const_by_name(&self, name: &'static str) -> ConstId {
        let name = self.interner.intern(name);
        self.sym.lock().get_const(name).expect("class not found")
    }

    #[cfg(test)]
    pub fn cls_method_by_name(
        &self,
        class_name: &'static str,
        function_name: &'static str,
        is_static: bool,
    ) -> Option<FctId> {
        let class_name = self.interner.intern(class_name);
        let function_name = self.interner.intern(function_name);

        let cls_id = self
            .sym
            .lock()
            .get_class(class_name)
            .expect("class not found");
        let cls = self.cls(cls_id);

        let candidates = find_methods_in_class(self, cls, function_name, is_static);
        if candidates.len() == 1 {
            Some(candidates[0].1)
        } else {
            None
        }
    }

    pub fn fct_by_name(&self, name: &str) -> Option<FctId> {
        let name = self.interner.intern(name);
        self.sym.lock().get_fct(name)
    }

    #[cfg(test)]
    pub fn ctor_by_name(&self, name: &str) -> FctId {
        let name = self.interner.intern(name);
        let cls_id = self.sym.lock().get_class(name).expect("class not found");
        let cls = self.classes.idx(cls_id);
        let cls = cls.read();

        cls.constructor.expect("no ctor found")
    }

    #[cfg(test)]
    pub fn global_by_name(&self, name: &str) -> GlobalId {
        let name = self.interner.intern(name);
        self.sym.lock().get_global(name).expect("global not found")
    }

    pub fn cls(&self, cls_id: ClassId) -> BuiltinType {
        let list_id = self.lists.lock().insert(TypeList::empty());
        BuiltinType::Class(cls_id, list_id)
    }

    pub fn cls_with_type_params(
        &self,
        cls_id: ClassId,
        type_params: Vec<BuiltinType>,
    ) -> BuiltinType {
        let list = TypeList::with(type_params);
        let list_id = self.lists.lock().insert(list);
        BuiltinType::Class(cls_id, list_id)
    }

    pub fn cls_with_type_list(&self, cls_id: ClassId, type_list: TypeList) -> BuiltinType {
        let list_id = self.lists.lock().insert(type_list);
        BuiltinType::Class(cls_id, list_id)
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Trap {
    DIV0,
    ASSERT,
    NIL,
    THROW,
    CAST,
    UNEXPECTED,
    OOM,
}

impl Trap {
    pub fn int(self) -> u32 {
        match self {
            Trap::DIV0 => 1,
            Trap::ASSERT => 2,
            Trap::NIL => 3,
            Trap::THROW => 4,
            Trap::CAST => 5,
            Trap::UNEXPECTED => 6,
            Trap::OOM => 7,
        }
    }

    pub fn from(value: u32) -> Option<Trap> {
        match value {
            1 => Some(Trap::DIV0),
            2 => Some(Trap::ASSERT),
            3 => Some(Trap::NIL),
            4 => Some(Trap::THROW),
            5 => Some(Trap::CAST),
            6 => Some(Trap::UNEXPECTED),
            7 => Some(Trap::OOM),
            _ => None,
        }
    }
}
