use crate::parser::cst::visit::Visitor;
use crate::parser::cst::{Cst, EnumType};

use crate::errors::message::SemError;
use crate::vm::{EnumId, NodeMap, VM};

pub fn check<'cst>(vm: &mut VM<'cst>, cst: &'cst Cst, map_enum_defs: &NodeMap<EnumId>) {
    let mut enumck = EnumCheck {
        vm,
        cst,
        map_enum_defs,
    };

    enumck.check();
}

struct EnumCheck<'x, 'cst: 'x> {
    vm: &'x mut VM<'cst>,
    cst: &'cst Cst,
    map_enum_defs: &'x NodeMap<EnumId>,
}

impl<'x, 'cst> EnumCheck<'x, 'cst> {
    fn check(&mut self) {
        self.visit_cst(self.cst);
    }
}

impl<'x, 'cst> Visitor<'cst> for EnumCheck<'x, 'cst> {
    fn visit_enum(&mut self, e: &'cst EnumType) {

        let enum_id = *self.map_enum_defs.get(e.id).unwrap();

        let mut xenum = self.vm.enum_defs[enum_id].write();
        let mut enum_value_int: u32 = 0;

        let name = self.vm.interner.str(e.name).to_string();

        for variant in &e.variants {
            
            xenum.values.push(*variant);
            let result = xenum.name_to_value.insert(*variant, enum_value_int);

            if result.is_some() {
                let v = self.vm.interner.str(*variant).to_string();
                self.vm
                    .diagnostic
                    .lock()
                    .report(e.pos, SemError::DuplicateEnumVariant(name.clone(), v));
            }

            enum_value_int += 1;
        }

        if e.variants.is_empty() {
            self.vm
                .diagnostic
                .lock()
                .report(e.pos, SemError::NoEnumValue(name));
        }
    }
}
