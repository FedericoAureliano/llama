use crate::errors::message::SemError;
use crate::vm::{NodeMap, VM};
use crate::parser::cst::Cst;
use crate::parser::cst::{TypeIdentCst};
use crate::types::{BuiltinType, TypeList};
use crate::symbols::Symbol::{EnumSymbol};

mod enumcheck;
mod declpass;

macro_rules! return_on_error {
    ($vm: ident) => {{
        if $vm.diagnostic.lock().has_errors() {
            return;
        }
    }};
}

pub fn pass(vm: &mut VM, cst: &Cst) {

    let mut map_enum_defs = NodeMap::new();

    // populate tables
    declpass::pass(vm, cst, &mut map_enum_defs);
    return_on_error!(vm);

    // check enums
    enumcheck::pass(vm, cst, &map_enum_defs);
    return_on_error!(vm);
}

pub fn read_type(vm: &VM, t: &TypeIdentCst) -> Option<BuiltinType> {
    match *t {
        TypeIdentCst::Basic(ref basic) => {
            let sym = vm.symbol_table.lock().get(basic.name);
            if let Some(sym) = sym {
                match sym {
                    EnumSymbol(enum_id) => {
                        if basic.params.len() > 0 {
                            let msg = SemError::NoTypeParamsExpected;
                            vm.diagnostic.lock().report(basic.pos, msg);
                        }

                        return Some(BuiltinType::Enum(enum_id));
                    }
                    // _ => {
                    //     let name = vm.interner.str(basic.name).to_string();
                    //     let msg = SemError::ExpectedType(name);
                    //     vm.diagnostic.lock().report(basic.pos, msg);
                    // }
                }
            } else {
                let name = vm.interner.str(basic.name).to_string();
                let msg = SemError::UnknownType(name);
                vm.diagnostic.lock().report(basic.pos, msg);
            }

            None
        }

        TypeIdentCst::Tuple(ref tuple) => {
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