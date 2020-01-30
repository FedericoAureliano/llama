use parking_lot::RwLock;

use std::sync::Arc;

use crate::parser::ast;
use crate::parser::interner::Name;
use crate::parser::lexer::position::Position;

use crate::ty::BuiltinType;
use crate::utils::GrowableVec;
use crate::vm::{ClassId, PrcdSrc, FileId, ImplId, TraitId, TypeParam, VM};

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct PrcdId(pub usize);

impl PrcdId {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for PrcdId {
    fn from(id: usize) -> PrcdId {
        PrcdId(id)
    }
}

impl<'ast> GrowableVec<RwLock<Prcd<'ast>>> {
    pub fn idx(&self, index: PrcdId) -> Arc<RwLock<Prcd<'ast>>> {
        self.idx_usize(index.0)
    }
}

#[derive(Debug)]
pub struct Prcd<'ast> {
    pub id: PrcdId,
    pub ast: &'ast ast::Procedure,
    pub pos: Position,
    pub name: Name,
    pub parent: PrcdParent,
    pub has_open: bool,
    pub has_override: bool,
    pub has_final: bool,
    pub has_optimize_immediately: bool,
    pub is_static: bool,
    pub is_pub: bool,
    pub is_abstract: bool,
    pub is_test: bool,
    pub use_cannon: bool,
    pub internal: bool,
    pub internal_resolved: bool,
    pub overrides: Option<PrcdId>,
    pub param_types: Vec<BuiltinType>,
    pub return_type: BuiltinType,
    pub is_constructor: bool,
    pub file: FileId,

    pub vtable_index: Option<u32>,
    pub impl_for: Option<PrcdId>,
    pub initialized: bool,
    pub throws: bool,

    pub type_params: Vec<TypeParam>,
    pub kind: PrcdKind,
}

impl<'ast> Prcd<'ast> {
    pub fn is_virtual(&self) -> bool {
        (self.has_open || self.has_override) && !self.has_final
    }

    pub fn in_class(&self) -> bool {
        match self.parent {
            PrcdParent::Class(_) => true,
            _ => false,
        }
    }

    pub fn in_trait(&self) -> bool {
        match self.parent {
            PrcdParent::Trait(_) => true,
            _ => false,
        }
    }

    pub fn cls_id(&self) -> ClassId {
        match self.parent {
            PrcdParent::Class(clsid) => clsid,
            _ => unreachable!(),
        }
    }

    pub fn trait_id(&self) -> TraitId {
        match self.parent {
            PrcdParent::Trait(traitid) => traitid,
            _ => unreachable!(),
        }
    }

    pub fn full_name(&self, vm: &VM) -> String {
        let mut repr = String::new();

        if let PrcdParent::Class(class_id) = self.parent {
            let cls = vm.classes.idx(class_id);
            let cls = cls.read();
            let name = cls.name;
            repr.push_str(&vm.interner.str(name));

            if self.is_static {
                repr.push_str("::");
            } else {
                repr.push_str(".");
            }
        }

        repr.push_str(&vm.interner.str(self.name));

        if self.type_params.len() > 0 {
            repr.push('[');

            repr.push_str(
                &self
                    .type_params
                    .iter()
                    .map(|n| vm.interner.str(n.name).to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            repr.push(']');
        }

        repr.push_str("(");

        for (ind, ty) in self.params_without_self().iter().enumerate() {
            if ind > 0 {
                repr.push_str(", ");
            }

            let name = ty.name(vm);
            repr.push_str(&name);
        }

        repr.push_str(")");

        if self.return_type != BuiltinType::Unit {
            repr.push_str(" -> ");

            let name = self.return_type.name(vm);
            repr.push_str(&name);
        }

        repr
    }

    pub fn is_src(&self) -> bool {
        match self.kind {
            PrcdKind::Source(_) => true,
            _ => false,
        }
    }

    pub fn pos(&self) -> Position {
        self.ast.pos
    }

    pub fn src(&self) -> &RwLock<PrcdSrc> {
        match self.kind {
            PrcdKind::Source(ref src) => src,
            _ => panic!("source expected"),
        }
    }

    pub fn has_self(&self) -> bool {
        match self.parent {
            PrcdParent::Class(_) | PrcdParent::Trait(_) | PrcdParent::Impl(_) => !self.is_static,

            _ => false,
        }
    }

    pub fn params_with_self(&self) -> &[BuiltinType] {
        &self.param_types
    }

    pub fn params_without_self(&self) -> &[BuiltinType] {
        if self.has_self() {
            &self.param_types[1..]
        } else {
            &self.param_types
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrcdParent {
    Class(ClassId),
    Trait(TraitId),
    Impl(ImplId),
    None,
}

impl PrcdParent {
    pub fn is_none(&self) -> bool {
        match self {
            &PrcdParent::None => true,
            _ => false,
        }
    }

    pub fn is_trait(&self) -> bool {
        match self {
            &PrcdParent::Trait(_) => true,
            _ => false,
        }
    }

    pub fn cls_id(&self) -> ClassId {
        match self {
            &PrcdParent::Class(id) => id,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
pub enum PrcdKind {
    Source(RwLock<PrcdSrc>),
    Definition,
    // Native(Address),
    Builtin(Intrinsic),
}

impl PrcdKind {
    pub fn is_src(&self) -> bool {
        match *self {
            PrcdKind::Source(_) => true,
            _ => false,
        }
    }

    pub fn is_intrinsic(&self) -> bool {
        match *self {
            PrcdKind::Builtin(_) => true,
            _ => false,
        }
    }

    pub fn is_definition(&self) -> bool {
        match *self {
            PrcdKind::Definition => true,
            _ => false,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    GenericArrayCtorEmpty,
    GenericArrayCtorElem,
    GenericArrayLen,
    GenericArrayGet,
    GenericArraySet,

    DefaultValue,

    Assert,
    Debug,
    Shl,

    StrLen,
    StrGet,
    StrSet,

    BoolEq,
    BoolNot,
    BoolToInt,
    BoolToLong,

    ByteEq,
    ByteCmp,
    ByteNot,
    ByteToInt,
    ByteToLong,

    CharEq,
    CharCmp,
    CharToInt,
    CharToLong,

    IntToByte,
    IntToChar,
    IntToLong,
    IntToFloat,
    IntToDouble,
    IntAsFloat,

    EnumEq,
    EnumNe,

    IntEq,
    IntCmp,

    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,

    IntOr,
    IntAnd,
    IntXor,

    IntShl,
    IntSar,
    IntShr,

    IntNot,
    IntNeg,
    IntPlus,

    LongToInt,
    LongToChar,
    LongToByte,
    LongToFloat,
    LongToDouble,
    LongAsDouble,

    LongEq,
    LongCmp,

    LongAdd,
    LongSub,
    LongMul,
    LongDiv,
    LongMod,

    LongOr,
    LongAnd,
    LongXor,

    LongShl,
    LongSar,
    LongShr,

    LongNot,
    LongNeg,
    LongPlus,

    FloatToInt,
    FloatToLong,
    FloatToDouble,
    FloatAsInt,

    FloatEq,
    FloatCmp,

    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,

    FloatPlus,
    FloatNeg,
    FloatIsNan,
    FloatSqrt,

    FloatArrayLen,
    FloatArrayGet,
    FloatArraySet,

    DoubleToInt,
    DoubleToLong,
    DoubleToFloat,
    DoubleAsLong,

    DoubleEq,
    DoubleCmp,

    DoubleAdd,
    DoubleSub,
    DoubleMul,
    DoubleDiv,

    DoublePlus,
    DoubleNeg,
    DoubleIsNan,
    DoubleSqrt,

    DoubleArrayLen,
    DoubleArrayGet,
    DoubleArraySet,
}
