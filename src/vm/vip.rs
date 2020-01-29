use parking_lot::Mutex;

use crate::ty::{BuiltinType};
use crate::vm::{ClassDefId, ClassId, FctId, TraitId};

#[derive(Debug)]
pub struct KnownElements {
    pub bool_class: ClassId,
    pub byte_class: ClassId,
    pub char_class: ClassId,
    pub int_class: ClassId,
    pub long_class: ClassId,
    pub float_class: ClassId,
    pub double_class: ClassId,
    pub object_class: ClassId,
    pub string_class: ClassId,
    pub array_class: ClassId,

    pub cls: KnownClasses,
    pub fct: KnownFunctions,

    pub testing_class: ClassId,
    pub throwable_class: ClassId,
    pub error_class: ClassId,
    pub exception_class: ClassId,
    pub stack_trace_element_class: ClassId,

    pub equals_trait: TraitId,
    pub comparable_trait: TraitId,
    pub stringable_trait: TraitId,
    pub iterator_trait: Mutex<Option<TraitId>>,

    pub byte_array_def: Mutex<Option<ClassDefId>>,
    pub int_array_def: Mutex<Option<ClassDefId>>,
    pub str_class_def: Mutex<Option<ClassDefId>>,
    pub obj_class_def: Mutex<Option<ClassDefId>>,
    pub ste_class_def: Mutex<Option<ClassDefId>>,
    pub ex_class_def: Mutex<Option<ClassDefId>>,

    pub free_object_class_def: ClassDefId,
    pub free_array_class_def: ClassDefId,
}

#[derive(Debug)]
pub struct KnownClasses {
    pub string_buffer: ClassId,
}

#[derive(Debug)]
pub struct KnownFunctions {
    pub string_buffer_empty: FctId,
    pub string_buffer_append: FctId,
    pub string_buffer_to_string: FctId,
}

impl KnownElements {
    pub fn iterator(&self) -> TraitId {
        self.iterator_trait.lock().expect("iterator trait not set")
    }

    pub fn find_class(&self, ty: BuiltinType) -> Option<ClassId> {
        match ty {
            BuiltinType::Bool => Some(self.bool_class),
            BuiltinType::Byte => Some(self.byte_class),
            BuiltinType::Char => Some(self.char_class),
            BuiltinType::Int => Some(self.int_class),
            BuiltinType::Long => Some(self.long_class),
            BuiltinType::Float => Some(self.float_class),
            BuiltinType::Double => Some(self.double_class),
            _ => None,
        }
    }
}
