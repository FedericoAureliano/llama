use crate::vm::VM;

pub mod specialize;
pub mod typeparamck;

pub fn check<'ast>(vm: &mut VM<'ast>) {
    println!("checking {:?}", vm.ast);
}