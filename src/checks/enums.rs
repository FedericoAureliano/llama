use crate::parser::ast::visit::Visitor;
use crate::parser::ast::{Ast, Enum};

use crate::errors::msg::SemError;
use crate::vm::{EnumId, NodeMap, VM};

pub fn check<'ast>(vm: &mut VM<'ast>, ast: &'ast Ast, map_enum_defs: &NodeMap<EnumId>) {
    let mut enumck = EnumCheck {
        vm,
        ast,
        map_enum_defs,
    };

    enumck.check();
}

struct EnumCheck<'x, 'ast: 'x> {
    vm: &'x mut VM<'ast>,
    ast: &'ast Ast,
    map_enum_defs: &'x NodeMap<EnumId>,
}

impl<'x, 'ast> EnumCheck<'x, 'ast> {
    fn check(&mut self) {
        self.visit_ast(self.ast);
    }
}

impl<'x, 'ast> Visitor<'ast> for EnumCheck<'x, 'ast> {
    fn visit_enum(&mut self, e: &'ast Enum) {

        // TODO: failing here because haven't actually populated enum table
        let enum_id = *self.map_enum_defs.get(e.id).unwrap();

        let mut xenum = self.vm.enum_defs[enum_id].write();
        let mut enum_value_int: u32 = 0;

        for variant in &e.variants {
            
            xenum.values.push(*variant);
            let result = xenum.name_to_value.insert(*variant, enum_value_int);

            if result.is_some() {
                let name = self.vm.interner.str(*variant).to_string();
                self.vm
                    .diagnostic
                    .lock()
                    .report(xenum.file, e.pos, SemError::ShadowEnumValue(name));
            }

            enum_value_int += 1;
        }

        if e.variants.is_empty() {
            self.vm
                .diagnostic
                .lock()
                .report(xenum.file, e.pos, SemError::NoEnumValue);
        }
    }
}
