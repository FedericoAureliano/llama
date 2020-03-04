use crate::ast::VM;
use crate::parser::cst::Cst;

mod declarations;

macro_rules! return_on_error {
    ($vm: ident) => {{
        if $vm.diagnostic.has_errors() {
            return;
        }
    }};
}

pub fn walk(vm: &mut VM, cst: &Cst) {
    // populate tables
    declarations::walk(vm, cst);
    return_on_error!(vm);
}