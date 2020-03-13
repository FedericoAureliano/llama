use crate::ast::VM;
use crate::parser::cst::visit::*;
use crate::parser::cst::{Cst, TypeDeclarationSyntaxObject};

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
                let name = self.vm.interner.str(e.name).to_string();
                let variants : Vec<String> = e.variants.iter().map(|v| self.vm.interner.str(*v).to_string()).collect();
                self.vm.declare_enum(name, variants, &e.pos);
            }
            TypeDeclarationSyntaxObject::Alias(a) => {
                let name = self.vm.interner.str(a.name).to_string();
                let ty = self.vm.parse_type(&a.alias);
                let tid = self.vm.declare_type(ty);
                self.vm.declare_alias(name, tid, &a.pos);
            }
        }
    }
}