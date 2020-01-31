use std::ptr;
use crate::parser::ast;
use crate::parser::interner::*;
use crate::parser::lexer::File;
use crate::parser::parser::NodeIdGenerator;

static mut VM_GLOBAL: *const u8 = ptr::null();

pub fn get_vm() -> &'static VM<'static> {
    unsafe { &*(VM_GLOBAL as *const VM) }
}

pub fn set_vm(vm: &VM) {
    let ptr = vm as *const _ as *const u8;

    unsafe {
        VM_GLOBAL = ptr;
    }
}

pub struct VM<'ast> {
    pub interner: Interner,
    pub ast: &'ast ast::Ast,
    pub id_generator: NodeIdGenerator,
    pub files: Vec<File>,
}

impl<'ast> VM<'ast> {
    pub fn new(ast: &'ast ast::Ast) -> Box<VM<'ast>> {
        let vm = Box::new(VM {
            files: Vec::new(),
            interner: Interner::new(),
            ast,
            id_generator: NodeIdGenerator::new(),
        });

        set_vm(&vm);

        vm
    }

    pub fn file(&self, idx: FileId) -> &File {
        &self.files[idx.0 as usize]
    }
}

unsafe impl<'ast> Sync for VM<'ast> {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl From<u32> for FileId {
    fn from(data: u32) -> FileId {
        FileId(data)
    }
}
