use parking_lot::RwLock;

use std::sync::Arc;

use crate::parser::cst;
use crate::parser::interner::Name;
use crate::parser::lexer::position::Position;

use crate::types::BuiltinType;
use crate::utils::GrowableVec;
use crate::vm::{FctSrc, VM};

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct FctId(pub usize);

impl FctId {
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl From<usize> for FctId {
    fn from(id: usize) -> FctId {
        FctId(id)
    }
}

impl<'cst> GrowableVec<RwLock<Fct<'cst>>> {
    pub fn idx(&self, index: FctId) -> Arc<RwLock<Fct<'cst>>> {
        self.idx_usize(index.0)
    }
}

#[derive(Debug)]
pub struct Fct<'cst> {
    pub id: FctId,
    pub cst: &'cst cst::Function,
    pub pos: Position,
    pub name: Name,

    pub param_types: Vec<BuiltinType>,
    pub return_type: BuiltinType,

    pub vtable_index: Option<u32>,
    pub impl_for: Option<FctId>,
    pub initialized: bool,

    pub kind: FctKind,
}

impl<'cst> Fct<'cst> {

    pub fn full_name(&self, vm: &VM) -> String {
        let mut repr = String::new();

        repr.push_str(&vm.interner.str(self.name));

        repr.push_str("(");

        for (ind, ty) in self.params().iter().enumerate() {
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
            FctKind::Source(_) => true,
            _ => false,
        }
    }

    pub fn pos(&self) -> Position {
        self.cst.pos
    }

    pub fn src(&self) -> &RwLock<FctSrc> {
        match self.kind {
            FctKind::Source(ref src) => src,
            _ => panic!("source expected"),
        }
    }

    pub fn params(&self) -> &[BuiltinType] {
        &self.param_types
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FctParent {
    None,
}

impl FctParent {
    pub fn is_none(&self) -> bool {
        match self {
            &FctParent::None => true,
        }
    }
}

#[derive(Debug)]
pub enum FctKind {
    Source(RwLock<FctSrc>),
    Definition,
    Builtin(Intrinsic),
}

impl FctKind {
    pub fn is_src(&self) -> bool {
        match *self {
            FctKind::Source(_) => true,
            _ => false,
        }
    }

    pub fn is_intrinsic(&self) -> bool {
        match *self {
            FctKind::Builtin(_) => true,
            _ => false,
        }
    }

    pub fn is_definition(&self) -> bool {
        match *self {
            FctKind::Definition => true,
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
