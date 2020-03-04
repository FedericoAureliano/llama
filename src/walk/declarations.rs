use crate::errors::message::SemError;
use crate::ast::VM;
use crate::parser::cst::visit::*;
use crate::parser::cst::{Cst, TypeDeclarationSyntaxObject};
use crate::ast::types::Type;

pub fn walk<'cst>(
    vm: &mut VM,
    cst: &Cst,
) {
    let mut gdef = Declaration {
        vm,
    };

    gdef.visit_cst(cst);
}

struct Declaration<'x> {
    vm: &'x mut VM,
}

impl<'x, 'cst> Visitor<'cst> for Declaration<'x> {
    fn visit_type_decl(&mut self, t: &'cst TypeDeclarationSyntaxObject) {
        match t {
            TypeDeclarationSyntaxObject::Enum(e) => {
                assert_eq!(self.vm.type_def.len(), self.vm.type_name.len());
                assert_eq!(self.vm.symbol_type.len(), self.vm.symbol_name.len());

                // we need the type if for the enum itself
                let enum_type_id: usize = self.vm.type_def.len();
                // add the name right away
                self.vm.type_name.push(e.name);

                if e.variants.is_empty() {
                    let enum_name_str = self.vm.interner.str(e.name).to_string();
                    self.vm.diagnostic.report(e.pos, SemError::NoEnumValue(enum_name_str));
                }

                // get the next id we should be using
                let mut variant_symbol_id = self.vm.symbol_type.len();
                // keep track of the variant symbols we are creating
                let mut variants = Vec::new();
                for v in &e.variants {
                    // if we try to use a name we've already used
                    if let Some(sym) = self.vm.symbol_map.insert(v.name, variant_symbol_id) {
                        // then give an error message
                        let v1 = self.vm.interner.str(v.name).to_string();
                        let e1 = self.vm.interner.str(e.name).to_string();
                        // get the enum this variant already existed in
                        let t = self.vm.type_name[self.vm.symbol_type[sym]];
                        let e2 = self.vm.interner.str(t).to_string();
                        self.vm.diagnostic.report(v.pos, SemError::DuplicateEnumVariant(v1, e1, e2));
                    }
                    // if we succeded, then add the variant
                    self.vm.symbol_name.push(v.name);
                    self.vm.symbol_type.push(enum_type_id);
                    // and keep track of the variants
                    variants.push(variant_symbol_id);
                    // and go to the next
                    variant_symbol_id += 1;
                }

                if let Some(_) = self.vm.type_map.insert(e.name, enum_type_id) {
                    // if we've already declared this enum then give an error
                    let enum_name_str = self.vm.interner.str(e.name).to_string();
                    self.vm.diagnostic.report(e.pos, SemError::DuplicateEnum(enum_name_str));
                }
                // otherwise add it and its variants that we kept track of earlier
                self.vm.type_def.push(Type::Enum(variants));

            }
            TypeDeclarationSyntaxObject::Alias(_) => {
                // TODO
            }
        }
    }
}