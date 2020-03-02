use parking_lot::{RwLock};
use std::collections::HashMap;

use crate::errors::message::SemError;
use crate::symbols::Sym::{self, SymConst, SymEnum, SymFct};
use crate::vm::{EnumData, EnumId, NodeMap, VM};
use crate::parser::cst::visit::*;
use crate::parser::cst::*;
use crate::parser::interner::Name;
use crate::parser::lexer::position::Position;

pub fn check<'cst>(
    vm: &mut VM<'cst>,
    map_enum_defs: &mut NodeMap<EnumId>,
) {
    let cst = vm.cst;
    let mut gdef = Defn {
        vm,
        map_enum_defs,
    };

    gdef.visit_cst(cst);
}

struct Defn<'x, 'cst: 'x> {
    vm: &'x mut VM<'cst>,
    map_enum_defs: &'x mut NodeMap<EnumId>,
}

impl<'x, 'cst> Visitor<'cst> for Defn<'x, 'cst> {
    fn visit_enum(&mut self, e: &'cst EnumType) {
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

        let sym = SymEnum(id);

        if let Some(sym) = self.vm.symbol_table.lock().insert(e.name, sym) {
            report(self.vm, e.name, e.pos, sym);
        }
    }
}

fn report(vm: &VM, name: Name, pos: Position, sym: Sym) {
    let name = vm.interner.str(name).to_string();

    let msg = match sym {
        SymFct(_) => SemError::DuplicateFunction(name),
        SymConst(_) => SemError::DuplicateConst(name),
        SymEnum(_) => SemError::DuplicateEnum(name),
        _ => unimplemented!(),
    };

    vm.diagnostic.lock().report(pos, msg);
}