use parking_lot::{RwLock};
use std::collections::HashMap;

use crate::errors::message::SemError;
use crate::symbols::Symbol::{self, EnumSymbol};
use crate::vm::{EnumData, EnumId, NodeMap, VM};
use crate::parser::cst::visit::*;
use crate::parser::cst::{Cst, TypeDeclCst};
use crate::parser::interner::Name;
use crate::parser::lexer::position::Position;

pub fn pass<'cst>(
    vm: &mut VM,
    cst: &Cst,
    map_enum_defs: &mut NodeMap<EnumId>,
) {
    let mut gdef = Decl {
        vm,
        map_enum_defs,
    };

    gdef.visit_cst(cst);
}

struct Decl<'x> {
    vm: &'x mut VM,
    map_enum_defs: &'x mut NodeMap<EnumId>,
}

impl<'x, 'cst> Visitor<'cst> for Decl<'x> {
    fn visit_type_decl(&mut self, t: &'cst TypeDeclCst) {
        match t {
            TypeDeclCst::Enum(e) => {
                let id: EnumId = self.vm.enum_defs.len().into();
                let xenum = EnumData {
                    id,
                    pos: e.pos,
                    name: e.name,
                    values: Vec::new(),
                    name_to_value: HashMap::new(),
                };
        
                self.vm.enum_defs.push(RwLock::new(xenum));
                self.map_enum_defs.insert(e.id, id);
        
                let sym = EnumSymbol(id);
        
                if let Some(sym) = self.vm.symbol_table.lock().insert(e.name, sym) {
                    report(self.vm, e.name, e.pos, sym);
                }
            }
            TypeDeclCst::Alias(_) => {
                // TODO
            }
        }

    }
}

fn report(vm: &VM, name: Name, pos: Position, sym: Symbol) {
    let name = vm.interner.str(name).to_string();

    let msg = match sym {
        EnumSymbol(_) => SemError::DuplicateEnum(name),
        // _ => unimplemented!(),
    };

    vm.diagnostic.lock().report(pos, msg);
}