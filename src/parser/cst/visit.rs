use crate::parser::cst::{Cst, ModuleSyntaxObject, TypeDeclarationSyntaxObject};

pub trait Visitor<'v>: Sized {
    fn visit_cst(&mut self, a: &'v Cst) {
        walk_cst(self, a);
    }

    fn visit_module(&mut self, m: &'v ModuleSyntaxObject) {
        walk_module(self, m);
    }

    fn visit_type_decl(&mut self, t: &'v TypeDeclarationSyntaxObject) {
        walk_type_decl(self, t);
    }
}

pub fn walk_cst<'v, V: Visitor<'v>>(v: &mut V, a: &'v Cst) {
    for m in &a.modules {
        v.visit_module(m)
    }
}

pub fn walk_module<'v, V: Visitor<'v>>(v: &mut V, m: &'v ModuleSyntaxObject) {
    for t in &m.types {
        v.visit_type_decl(t);
    }
}

pub fn walk_type_decl<'v, V: Visitor<'v>>(_: &mut V, _: &'v TypeDeclarationSyntaxObject) {

}
