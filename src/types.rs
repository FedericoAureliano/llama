use std::collections::HashMap;
use std::ops::Index;
use std::sync::Arc;

use crate::vm::VM;
use crate::vm::{EnumId};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BuiltinType {
    // couldn't determine type because of error
    Error,

    // type with only one value: ()
    Unit,

    // value types
    Bool,

    Char,
    Byte,
    Int,
    Long,

    Float,
    Double,

    // some tuple
    Tuple(TypeListId),

    // some enum
    Enum(EnumId),
}

impl BuiltinType {
    pub fn is_error(&self) -> bool {
        match *self {
            BuiltinType::Error => true,
            _ => false,
        }
    }

    pub fn is_enum(&self) -> bool {
        match *self {
            BuiltinType::Enum(_) => true,
            _ => false,
        }
    }

    pub fn is_unit(&self) -> bool {
        match *self {
            BuiltinType::Unit => true,
            _ => false,
        }
    }

    pub fn is_float(&self) -> bool {
        match self {
            &BuiltinType::Float | &BuiltinType::Double => true,
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            &BuiltinType::Bool => true,
            _ => false,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match self {
            &BuiltinType::Tuple(_) => true,
            _ => false,
        }
    }

    pub fn value_type(&self) -> bool {
        match *self {
            BuiltinType::Unit
            | BuiltinType::Bool
            | BuiltinType::Byte
            | BuiltinType::Int
            | BuiltinType::Long
            | BuiltinType::Float
            | BuiltinType::Double => true,
            _ => false,
        }
    }

    pub fn name(&self, vm: &VM) -> String {
        match *self {
            BuiltinType::Error => "<error>".into(),
            BuiltinType::Unit => "()".into(),
            BuiltinType::Byte => "Byte".into(),
            BuiltinType::Char => "Char".into(),
            BuiltinType::Int => "Int".into(),
            BuiltinType::Long => "Long".into(),
            BuiltinType::Float => "Float".into(),
            BuiltinType::Double => "Double".into(),
            BuiltinType::Bool => "Bool".into(),

            BuiltinType::Enum(id) => {
                let xenum = vm.enum_defs[id].read();
                vm.interner.str(xenum.name).to_string()
            }

            BuiltinType::Tuple(list_id) => {
                let types = vm.type_lists.lock().get(list_id);

                let types = types
                    .iter()
                    .map(|ty| ty.name(vm))
                    .collect::<Vec<_>>()
                    .join(", ");

                format!("({})", types)
            }
        }
    }

    pub fn allows(&self, vm: &VM, other: BuiltinType) -> bool {
        match *self {
            // allow all types for Error, there is already an error,
            // don't report too many messages for the same error
            BuiltinType::Error => true,

            BuiltinType::Unit
            | BuiltinType::Bool
            | BuiltinType::Byte
            | BuiltinType::Char => *self == other,
            BuiltinType::Int => *self == other,
            BuiltinType::Long => *self == other,
            BuiltinType::Float | BuiltinType::Double => *self == other,
            BuiltinType::Tuple(list_id) => match other {
                BuiltinType::Tuple(other_list_id) => {
                    if list_id == other_list_id {
                        return true;
                    }

                    let subtypes = vm.type_lists.lock().get(list_id);
                    let other_subtypes = vm.type_lists.lock().get(other_list_id);

                    if subtypes.len() != other_subtypes.len() {
                        return false;
                    }

                    let len = subtypes.len();

                    for idx in 0..len {
                        let ty = subtypes[idx];
                        let other_ty = other_subtypes[idx];

                        if !ty.allows(vm, other_ty) {
                            return false;
                        }
                    }

                    true
                }

                _ => false,
            },

            BuiltinType::Enum(_) => *self == other,
        }
    }

    pub fn is_concrete_type(&self) -> bool {
        match *self {
            BuiltinType::Error => false,
            BuiltinType::Unit
            | BuiltinType::Bool
            | BuiltinType::Byte
            | BuiltinType::Char
            | BuiltinType::Int
            | BuiltinType::Long
            | BuiltinType::Float
            | BuiltinType::Double
            | BuiltinType::Enum(_) => true,
            BuiltinType::Tuple(_) => {
                unimplemented!()
            }
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct TypeListId(u32);

impl TypeListId {
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for TypeListId {
    fn from(data: usize) -> TypeListId {
        assert!(data < u32::max_value() as usize);
        TypeListId(data as u32)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TypeList {
    Empty,
    List(Arc<Vec<BuiltinType>>),
}

impl TypeList {
    pub fn empty() -> TypeList {
        TypeList::Empty
    }

    pub fn single(ty: BuiltinType) -> TypeList {
        TypeList::List(Arc::new(vec![ty]))
    }

    pub fn with(type_params: Vec<BuiltinType>) -> TypeList {
        if type_params.len() == 0 {
            TypeList::Empty
        } else {
            TypeList::List(Arc::new(type_params))
        }
    }

    pub fn len(&self) -> usize {
        match self {
            &TypeList::Empty => 0,
            &TypeList::List(ref params) => params.len(),
        }
    }

    pub fn iter(&self) -> TypeListIter {
        TypeListIter {
            params: self,
            idx: 0,
        }
    }
}

impl Index<usize> for TypeList {
    type Output = BuiltinType;

    fn index(&self, idx: usize) -> &BuiltinType {
        match self {
            &TypeList::Empty => panic!("out-of-bounds"),
            &TypeList::List(ref params) => &params[idx],
        }
    }
}

pub struct TypeListIter<'a> {
    params: &'a TypeList,
    idx: usize,
}

impl<'a> Iterator for TypeListIter<'a> {
    type Item = BuiltinType;

    fn next(&mut self) -> Option<BuiltinType> {
        match self.params {
            &TypeList::Empty => None,

            &TypeList::List(ref params) => {
                if self.idx < params.len() {
                    let ret = params[self.idx];
                    self.idx += 1;

                    Some(ret)
                } else {
                    None
                }
            }
        }
    }
}

pub struct TypeLists {
    lists: HashMap<TypeList, TypeListId>,
    values: Vec<TypeList>,
    next_id: usize,
}

impl TypeLists {
    pub fn new() -> TypeLists {
        TypeLists {
            lists: HashMap::new(),
            values: Vec::new(),
            next_id: 0,
        }
    }

    pub fn insert(&mut self, list: TypeList) -> TypeListId {
        if let Some(&val) = self.lists.get(&list) {
            return val;
        }

        let id: TypeListId = self.next_id.into();
        self.lists.insert(list.clone(), id);

        self.values.push(list);

        self.next_id += 1;

        id
    }

    pub fn get(&self, id: TypeListId) -> TypeList {
        self.values[id.idx()].clone()
    }
}