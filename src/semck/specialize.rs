use crate::ty::{BuiltinType, TypeList};
use crate::vm::VM;

pub fn replace_type_param(
    vm: &VM,
    ty: BuiltinType,
    cls_tp: &TypeList,
    fct_tp: &TypeList,
    self_ty: Option<BuiltinType>,
) -> BuiltinType {
    match ty {
        BuiltinType::ClassTypeParam(_, tpid) => cls_tp[tpid.idx()],
        BuiltinType::PrcdTypeParam(_, tpid) => fct_tp[tpid.idx()],

        BuiltinType::Class(cls_id, list_id) => {
            let params = vm.lists.lock().get(list_id);

            let params = TypeList::with(
                params
                    .iter()
                    .map(|p| replace_type_param(vm, p, cls_tp, fct_tp, self_ty))
                    .collect::<Vec<_>>(),
            );

            let list_id = vm.lists.lock().insert(params);
            BuiltinType::Class(cls_id, list_id)
        }

        BuiltinType::This => self_ty.expect("no type for Self given"),

        BuiltinType::Lambda(_) => unimplemented!(),

        _ => ty,
    }
}