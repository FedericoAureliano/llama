use crate::errors::message::SemError;
use crate::vm::{NodeMap, VM};
use crate::parser::cst::Type::{BasicType, TupleType, TypeAlias, EnumType};
use crate::parser::cst::{Type};
use crate::types::{BuiltinType, TypeList};
use crate::symbols::Sym::{SymEnum};

mod enumcheck;
mod defcheck;

macro_rules! return_on_error {
    ($vm: ident) => {{
        if $vm.diagnostic.lock().has_errors() {
            return;
        }
    }};
}

pub fn check<'cst>(vm: &mut VM<'cst>) {

    let mut map_enum_defs = NodeMap::new();

    // add user defined fcts and classes to vm
    // this check does not look into fct or class bodies
    defcheck::check(vm, &mut map_enum_defs);
    return_on_error!(vm);

    // check enums
    enumcheck::check(vm, &vm.cst, &map_enum_defs);
    return_on_error!(vm);
}

pub fn read_type<'cst>(vm: &VM<'cst>, t: &'cst Type) -> Option<BuiltinType> {
    match *t {
        BasicType(ref basic) => {
            let sym = vm.symbol_table.lock().get(basic.name);
            if let Some(sym) = sym {
                match sym {
                    SymEnum(enum_id) => {
                        if basic.params.len() > 0 {
                            let msg = SemError::NoTypeParamsExpected;
                            vm.diagnostic.lock().report(basic.pos, msg);
                        }

                        return Some(BuiltinType::Enum(enum_id));
                    }
                    _ => {
                        let name = vm.interner.str(basic.name).to_string();
                        let msg = SemError::ExpectedType(name);
                        vm.diagnostic.lock().report(basic.pos, msg);
                    }
                }
            } else {
                let name = vm.interner.str(basic.name).to_string();
                let msg = SemError::UnknownType(name);
                vm.diagnostic.lock().report(basic.pos, msg);
            }

            None
        }

        TypeAlias(ref a) => {
            read_type(vm, &*a.alias)
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
                    if let Some(ty) = read_type(vm, subtype) {
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