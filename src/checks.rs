use crate::errors::msg::SemError;
use crate::vm::{FileId, NodeMap, VM};
use crate::parser::ast::Type::{BasicType, TupleType, TypeAlias, EnumType};
use crate::parser::ast::{Type};
use crate::types::{BuiltinType, TypeList};
use crate::symbols::Sym::{SymEnum};

mod enums;

macro_rules! return_on_error {
    ($vm: ident) => {{
        if $vm.diagnostic.lock().has_errors() {
            return;
        }
    }};
}

pub fn check<'ast>(vm: &mut VM<'ast>) {
    // TODO set to mutable and actually collect them
    let map_enum_defs = NodeMap::new(); // get EnumId from ast node

    // check enums
    enums::check(vm, &vm.ast, &map_enum_defs);
    return_on_error!(vm);
}

pub fn read_type<'ast>(vm: &VM<'ast>, file: FileId, t: &'ast Type) -> Option<BuiltinType> {
    match *t {
        BasicType(ref basic) => {
            let sym = vm.symbol_table.lock().get(basic.name);
            if let Some(sym) = sym {
                match sym {
                    SymEnum(enum_id) => {
                        if basic.params.len() > 0 {
                            let msg = SemError::NoTypeParamsExpected;
                            vm.diagnostic.lock().report(file, basic.pos, msg);
                        }

                        return Some(BuiltinType::Enum(enum_id));
                    }
                    _ => {
                        let name = vm.interner.str(basic.name).to_string();
                        let msg = SemError::ExpectedType(name);
                        vm.diagnostic.lock().report(file, basic.pos, msg);
                    }
                }
            } else {
                let name = vm.interner.str(basic.name).to_string();
                let msg = SemError::UnknownType(name);
                vm.diagnostic.lock().report(file, basic.pos, msg);
            }

            None
        }

        TypeAlias(ref a) => {
            read_type(vm, file, &*a.alias)
        }

        EnumType(_) => {
            // what to do?
            None
        }

        TupleType(ref tuple) => {
            if tuple.subtypes.len() == 0 {
                Some(BuiltinType::Unit)
            } else {
                let mut subtypes = Vec::new();

                for subtype in &tuple.subtypes {
                    if let Some(ty) = read_type(vm, file, subtype) {
                        subtypes.push(ty);
                    } else {
                        return None;
                    }
                }

                let list = TypeList::with(subtypes);
                let list_id = vm.type_lists.lock().insert(list);

                Some(BuiltinType::Tuple(list_id))
            }
        }
    }
}