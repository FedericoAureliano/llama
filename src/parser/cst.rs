use std::fmt;
use std::slice::Iter;
use bit_vec::BitVec;

use crate::parser::interner::{Interner, Name};
use crate::parser::lexer::position::{Position, Span};
use crate::parser::lexer::token::{FloatSuffix, IntBase, IntSuffix};

pub mod dump;
pub mod visit;

#[derive(Clone, Debug)]
pub struct Cst {
    pub modules: Vec<Module>,
}

impl Cst {
    pub fn new() -> Cst {
        Cst { modules: Vec::new() }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct NodeId(pub usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub enum Type {
    BasicType(BasicType),
    TypeAlias(TypeAlias),
    EnumType(EnumType),
    TupleType(TupleType),
}

#[derive(Clone, Debug)]
pub struct BasicType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    // Params are for arrays
    pub params: Vec<Box<Type>>,
}

#[derive(Clone, Debug)]
pub struct TypeAlias {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub alias: Box<Type>,
}

#[derive(Clone, Debug)]
pub struct EnumType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub variants: Vec<Name>,
}

#[derive(Clone, Debug)]
pub struct TupleType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub subtypes: Vec<Box<Type>>,
}

impl Type {

    pub fn create_basic(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        params: Vec<Box<Type>>,
    ) -> Type {
        Type::BasicType(BasicType {
            id,
            pos,
            span,
            name,
            params,
        })
    }

    pub fn create_alias(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        alias: Box<Type>,
    ) -> Type {
        Type::TypeAlias(TypeAlias {
            id,
            pos,
            span,
            name,
            alias,
        })
    }

    pub fn create_enum(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        variants: Vec<Name>,
    ) -> Type {
        Type::EnumType(EnumType {
            id,
            pos,
            span,
            name,
            variants,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, subtypes: Vec<Box<Type>>) -> Type {
        Type::TupleType(TupleType {
            id,
            pos,
            span,
            subtypes,
        })
    }

    pub fn to_basic(&self) -> Option<&BasicType> {
        match *self {
            Type::BasicType(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_alias(&self) -> Option<&TypeAlias> {
        match *self {
            Type::TypeAlias(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_enum(&self) -> Option<&EnumType> {
        match *self {
            Type::EnumType(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_basic_without_type_params(&self) -> Option<Name> {
        match *self {
            Type::BasicType(ref basic) => {
                if basic.params.len() == 0 {
                    Some(basic.name)
                } else {
                    None
                }
            }

            _ => None,
        }
    }

    pub fn to_tuple(&self) -> Option<&TupleType> {
        match *self {
            Type::TupleType(ref val) => Some(val),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn is_unit(&self) -> bool {
        match self {
            &Type::TupleType(ref val) if val.subtypes.len() == 0 => true,
            _ => false,
        }
    }

    pub fn to_string(&self, interner: &Interner) -> String {
        match *self {
            Type::BasicType(ref val) => {
                if val.params.len() > 0 {
                    let types: Vec<String> = val.params.iter().map(|t| format!("{}", t.to_string(interner))).collect();
                    format!("[{}]{}", types.join(", "),  *interner.str(val.name))
                } else {
                    format!("{}", *interner.str(val.name))
                }
            }

            Type::TypeAlias(ref val) => format!("`{}` := `{}`", *interner.str(val.name), val.alias.to_string(interner)),

            Type::EnumType(ref val) => {
                let types: Vec<String> = val.variants.iter().map(|t| format!("{}", *interner.str(*t))).collect();
                format!("enum {} of {{{}}}", *interner.str(val.name), types.join(", "))
            }

            Type::TupleType(ref val) => {
                let types: Vec<String> =
                    val.subtypes.iter().map(|t| t.to_string(interner)).collect();

                format!("({})", types.join(", "))
            }
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            Type::BasicType(ref val) => val.pos,
            Type::TypeAlias(ref val) => val.pos,
            Type::EnumType(ref val) => val.pos,
            Type::TupleType(ref val) => val.pos,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            Type::BasicType(ref val) => val.id,
            Type::TypeAlias(ref val) => val.id,
            Type::EnumType(ref val) => val.id,
            Type::TupleType(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    // TODO: instances of other modules
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    
    pub types: Vec<Type>,

    pub inputs: Vec<Field>,
    pub outputs: Vec<Field>,
    pub variables: Vec<Field>,
    pub constants: Vec<Field>,

    pub definitions: Vec<Define>,

    pub functions: Vec<Function>,
    pub procedures: Vec<Procedure>,

    pub theorems: Vec<Property>,
    pub lemmas: Vec<Property>,

    pub init: Option<Box<TransitionSystemBlock>>,
    pub next: Option<Box<TransitionSystemBlock>>,
    pub control: Option<Box<TransitionSystemBlock>>,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub data_type: Type,
    pub expr: Option<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct Property {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub expr: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub to_synthesize: bool,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
}

#[derive(Clone, Debug)]
pub struct Define {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub expr: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct Procedure {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub params: Vec<Param>,

    pub returns: Vec<Param>,
    pub modifies: Vec<Name>,
    pub requires: Vec<StmtPredicateType>,
    pub ensures: Vec<StmtPredicateType>,

    pub block: Option<Box<ExprBlockType>>,
}

impl Procedure {
    pub fn block(&self) -> &ExprBlockType {
        self.block.as_ref().unwrap()
    }
}

#[derive(Clone, Debug)]
pub struct Modifiers(Vec<ModifierElement>);

impl Modifiers {
    pub fn new() -> Modifiers {
        Modifiers(Vec::new())
    }

    pub fn contains(&self, modifier: Modifier) -> bool {
        self.0.iter().find(|el| el.value == modifier).is_some()
    }

    pub fn add(&mut self, modifier: Modifier, pos: Position, span: Span) {
        self.0.push(ModifierElement {
            value: modifier,
            pos,
            span,
        });
    }

    pub fn iter(&self) -> Iter<ModifierElement> {
        self.0.iter()
    }
}

#[derive(Clone, Debug)]
pub struct ModifierElement {
    pub value: Modifier,
    pub pos: Position,
    pub span: Span,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Modifier {
    Inline,
    Synthesis,
}

impl Modifier {
    pub fn name(&self) -> &'static str {
        match *self {
            Modifier::Inline => "inline",
            Modifier::Synthesis => "synthesis",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub id: NodeId,
    pub idx: u32,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub data_type: Type,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    StmtInduction(StmtInductionType),
    StmtSimulate(StmtSimulateType),
    StmtAssert(StmtPredicateType),
    StmtAssume(StmtPredicateType),
    StmtCall(StmtCallType),
    StmtHavoc(StmtHavocType),
    StmtVar(StmtVarType),
    StmtWhile(StmtWhileType),
    StmtFor(StmtForType),
    StmtExpr(StmtExprType),
}

impl Stmt {
    pub fn create_var(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        reassignable: bool,
        data_type: Option<Type>,
        expr: Option<Box<Expr>>,
    ) -> Stmt {
        Stmt::StmtVar(StmtVarType {
            id,
            pos,
            span,

            name,
            reassignable,
            data_type,
            expr,
        })
    }

    pub fn create_assume(
        id: NodeId,
        pos: Position,
        span: Span,
        expr: Box<Expr>,
    ) -> Stmt {
        Stmt::StmtAssume(StmtPredicateType {
            id,
            pos,
            span,
            expr,
        })
    }

    pub fn create_assert(
        id: NodeId,
        pos: Position,
        span: Span,
        expr: Box<Expr>,
    ) -> Stmt {
        Stmt::StmtAssert(StmtPredicateType {
            id,
            pos,
            span,
            expr,
        })
    }

    pub fn create_havoc(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
    ) -> Stmt {
        Stmt::StmtHavoc(StmtHavocType {
            id,
            pos,
            span,

            name,
        })
    }

    pub fn create_simulate(
        id: NodeId,
        pos: Position,
        span: Span,
        steps: u64,
    ) -> Stmt {
        Stmt::StmtSimulate(StmtSimulateType {
            id,
            pos,
            span,
            steps,
        })
    }

    pub fn create_induction(
        id: NodeId,
        pos: Position,
        span: Span,
        steps: u64,
    ) -> Stmt {
        Stmt::StmtInduction(StmtInductionType {
            id,
            pos,
            span,
            steps,
        })
    }

    pub fn create_call(
        id: NodeId,
        pos: Position,
        span: Span,
        func: Name,
        rets: Vec<Name>,
        args: Vec<Box<Expr>>,
    ) -> Stmt {
        Stmt::StmtCall(StmtCallType {
            id,
            pos,
            span,
            func,
            rets,
            args,
        })
    }

    pub fn create_for(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        expr: Box<Expr>,
        block: Box<Stmt>,
    ) -> Stmt {
        Stmt::StmtFor(StmtForType {
            id,
            pos,
            span,

            name,
            expr,
            block,
        })
    }

    pub fn create_while(
        id: NodeId,
        pos: Position,
        span: Span,
        cond: Box<Expr>,
        block: Box<Stmt>,
    ) -> Stmt {
        Stmt::StmtWhile(StmtWhileType {
            id,
            pos,
            span,

            cond,
            block,
        })
    }

    pub fn create_expr(id: NodeId, pos: Position, span: Span, expr: Box<Expr>) -> Stmt {
        Stmt::StmtExpr(StmtExprType {
            id,
            pos,
            span,

            expr,
        })
    }

    pub fn id(&self) -> NodeId {
        match *self {
            Stmt::StmtInduction(ref stmt) => stmt.id,
            Stmt::StmtSimulate(ref stmt) => stmt.id,
            Stmt::StmtAssert(ref stmt) => stmt.id,
            Stmt::StmtAssume(ref stmt) => stmt.id,
            Stmt::StmtCall(ref stmt) => stmt.id,
            Stmt::StmtHavoc(ref stmt) => stmt.id,
            Stmt::StmtVar(ref stmt) => stmt.id,
            Stmt::StmtWhile(ref stmt) => stmt.id,
            Stmt::StmtFor(ref stmt) => stmt.id,
            Stmt::StmtExpr(ref stmt) => stmt.id,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            Stmt::StmtInduction(ref stmt) => stmt.pos,
            Stmt::StmtSimulate(ref stmt) => stmt.pos,
            Stmt::StmtAssert(ref stmt) => stmt.pos,
            Stmt::StmtAssume(ref stmt) => stmt.pos,
            Stmt::StmtCall(ref stmt) => stmt.pos,
            Stmt::StmtHavoc(ref stmt) => stmt.pos,
            Stmt::StmtVar(ref stmt) => stmt.pos,
            Stmt::StmtWhile(ref stmt) => stmt.pos,
            Stmt::StmtFor(ref stmt) => stmt.pos,
            Stmt::StmtExpr(ref stmt) => stmt.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            Stmt::StmtInduction(ref stmt) => stmt.span,
            Stmt::StmtSimulate(ref stmt) => stmt.span,
            Stmt::StmtAssert(ref stmt) => stmt.span,
            Stmt::StmtAssume(ref stmt) => stmt.span,
            Stmt::StmtCall(ref stmt) => stmt.span,
            Stmt::StmtHavoc(ref stmt) => stmt.span,
            Stmt::StmtVar(ref stmt) => stmt.span,
            Stmt::StmtWhile(ref stmt) => stmt.span,
            Stmt::StmtFor(ref stmt) => stmt.span,
            Stmt::StmtExpr(ref stmt) => stmt.span,
        }
    }

    pub fn to_var(&self) -> Option<&StmtVarType> {
        match *self {
            Stmt::StmtVar(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_var(&self) -> bool {
        match *self {
            Stmt::StmtVar(_) => true,
            _ => false,
        }
    }

    pub fn to_while(&self) -> Option<&StmtWhileType> {
        match *self {
            Stmt::StmtWhile(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_while(&self) -> bool {
        match *self {
            Stmt::StmtWhile(_) => true,
            _ => false,
        }
    }

    pub fn to_for(&self) -> Option<&StmtForType> {
        match *self {
            Stmt::StmtFor(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_for(&self) -> bool {
        match *self {
            Stmt::StmtFor(_) => true,
            _ => false,
        }
    }

    pub fn to_expr(&self) -> Option<&StmtExprType> {
        match *self {
            Stmt::StmtExpr(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_expr(&self) -> bool {
        match *self {
            Stmt::StmtExpr(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StmtCallType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub func: Name,
    pub rets: Vec<Name>,
    pub args: Vec<Box<Expr>>,
}


#[derive(Clone, Debug)]
pub struct StmtHavocType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct StmtPredicateType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub expr: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct StmtInductionType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct StmtSimulateType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct StmtVarType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub reassignable: bool,

    pub data_type: Option<Type>,
    pub expr: Option<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct StmtForType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub expr: Box<Expr>,
    pub block: Box<Stmt>,
}

#[derive(Clone, Debug)]
pub struct StmtWhileType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<Expr>,
    pub block: Box<Stmt>,
}

#[derive(Clone, Debug)]
pub struct StmtExprType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub expr: Box<Expr>,
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum UnOp {
    Plus,
    Neg,
    Not,
}

impl UnOp {
    pub fn as_str(&self) -> &'static str {
        match *self {
            UnOp::Plus => "+",
            UnOp::Neg => "-",
            UnOp::Not => "!",
        }
    }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Ult,
    Ule,
    Ugt,
    Uge,
}

impl CmpOp {
    pub fn as_str(&self) -> &'static str {
        match *self {
            CmpOp::Eq => "==",
            CmpOp::Ne => "!=",
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
            CmpOp::Ult => "<_u",
            CmpOp::Ule => "<=_u",
            CmpOp::Ugt => ">_u",
            CmpOp::Uge => ">=_u",
        }
    }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum BinOp {
    Assign,
    Add,
    Concat,
    Sub,
    Mul,
    Div,
    Mod,
    Cmp(CmpOp),
    Or,
    And,
    BitOr,
    BitAnd,
    BitXor,
    ShiftL,
    ArithShiftR,
    LogicalShiftR,
    Range
}

impl BinOp {
    pub fn as_str(&self) -> &'static str {
        match *self {
            BinOp::Assign => "=",
            BinOp::Add => "+",
            BinOp::Concat => "++",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Cmp(op) => op.as_str(),
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::BitOr => "|",
            BinOp::BitAnd => "&",
            BinOp::BitXor => "^",
            BinOp::ShiftL => "<<",
            BinOp::ArithShiftR => ">>",
            BinOp::LogicalShiftR => ">>>",
            BinOp::Range => ":",
        }
    }

    pub fn is_any_assign(&self) -> bool {
        match *self {
            BinOp::Assign => true,
            _ => false,
        }
    }

    pub fn is_compare(&self) -> bool {
        match *self {
            BinOp::Cmp(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    ExprUn(ExprUnType),
    ExprBin(ExprBinType),
    ExprLitInt(ExprLitIntType),
    ExprLitFloat(ExprLitFloatType),
    ExprLitBitVec(ExprLitBitVecType),
    ExprLitBool(ExprLitBoolType),
    ExprIdent(ExprIdentType),
    ExprCall(ExprCallType),
    ExprExtract(ExprExtractType),
    ExprDot(ExprDotType),
    ExprBlock(ExprBlockType),
    ExprIf(ExprIfType),
    ExprTuple(ExprTupleType),
}

impl Expr {
    pub fn create_block(
        id: NodeId,
        pos: Position,
        span: Span,
        stmts: Vec<Box<Stmt>>,
    ) -> Expr {
        Expr::ExprBlock(ExprBlockType {
            id,
            pos,
            span,

            stmts,
        })
    }

    pub fn create_if(
        id: NodeId,
        pos: Position,
        span: Span,
        cond: Box<Expr>,
        then_block: Box<Expr>,
        else_block: Option<Box<Expr>>,
    ) -> Expr {
        Expr::ExprIf(ExprIfType {
            id,
            pos,
            span,

            cond,
            then_block,
            else_block,
        })
    }

    pub fn create_un(id: NodeId, pos: Position, span: Span, op: UnOp, opnd: Box<Expr>) -> Expr {
        Expr::ExprUn(ExprUnType {
            id,
            pos,
            span,

            op,
            opnd,
        })
    }

    pub fn create_bin(
        id: NodeId,
        pos: Position,
        span: Span,
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    ) -> Expr {
        Expr::ExprBin(ExprBinType {
            id,
            pos,
            span,

            op,
            lhs,
            rhs,
        })
    }

    pub fn create_lit_int(
        id: NodeId,
        pos: Position,
        span: Span,
        value: u64,
        base: IntBase,
        suffix: IntSuffix,
    ) -> Expr {
        Expr::ExprLitInt(ExprLitIntType {
            id,
            pos,
            span,

            value,
            base,
            suffix,
        })
    }

    pub fn create_lit_float(
        id: NodeId,
        pos: Position,
        span: Span,
        value: f64,
        suffix: FloatSuffix,
    ) -> Expr {
        Expr::ExprLitFloat(ExprLitFloatType {
            id,
            pos,
            span,
            value,
            suffix,
        })
    }

    pub fn create_lit_bitvec(
        id: NodeId,
        pos: Position,
        span: Span,
        value: BitVec,
    ) -> Expr {
        Expr::ExprLitBitVec(ExprLitBitVecType {
            id,
            pos,
            span,
            value,
        })
    }

    pub fn create_lit_bool(id: NodeId, pos: Position, span: Span, value: bool) -> Expr {
        Expr::ExprLitBool(ExprLitBoolType {
            id,
            pos,
            span,

            value,
        })
    }

    pub fn create_ident(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        type_params: Option<Vec<Type>>,
    ) -> Expr {
        Expr::ExprIdent(ExprIdentType {
            id,
            pos,
            span,

            name,
            type_params,
        })
    }

    pub fn create_call(
        id: NodeId,
        pos: Position,
        span: Span,
        callee: Box<Expr>,
        args: Vec<Box<Expr>>,
    ) -> Expr {
        Expr::ExprCall(ExprCallType {
            id,
            pos,
            span,

            callee,
            args,
        })
    }

    pub fn create_deref(
        id: NodeId,
        pos: Position,
        span: Span,
        array: Box<Expr>,
        args: Vec<Box<Expr>>,
    ) -> Expr {
        Expr::ExprExtract(ExprExtractType {
            id,
            pos,
            span,

            array,
            args,
        })
    }

    pub fn create_dot(
        id: NodeId,
        pos: Position,
        span: Span,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    ) -> Expr {
        Expr::ExprDot(ExprDotType {
            id,
            pos,
            span,

            lhs,
            rhs,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, values: Vec<Box<Expr>>) -> Expr {
        Expr::ExprTuple(ExprTupleType {
            id,
            pos,
            span,
            values,
        })
    }

    pub fn to_un(&self) -> Option<&ExprUnType> {
        match *self {
            Expr::ExprUn(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_un(&self) -> bool {
        match *self {
            Expr::ExprUn(_) => true,
            _ => false,
        }
    }

    pub fn to_bin(&self) -> Option<&ExprBinType> {
        match *self {
            Expr::ExprBin(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_bin(&self) -> bool {
        match *self {
            Expr::ExprBin(_) => true,
            _ => false,
        }
    }

    pub fn to_ident(&self) -> Option<&ExprIdentType> {
        match *self {
            Expr::ExprIdent(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_ident(&self) -> bool {
        match *self {
            Expr::ExprIdent(_) => true,
            _ => false,
        }
    }

    pub fn to_call(&self) -> Option<&ExprCallType> {
        match *self {
            Expr::ExprCall(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_call(&self) -> bool {
        match *self {
            Expr::ExprCall(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_int(&self) -> Option<&ExprLitIntType> {
        match *self {
            Expr::ExprLitInt(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_int(&self) -> bool {
        match *self {
            Expr::ExprLitInt(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_float(&self) -> Option<&ExprLitFloatType> {
        match *self {
            Expr::ExprLitFloat(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_float(&self) -> bool {
        match *self {
            Expr::ExprLitFloat(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bitvec(&self) -> Option<&ExprLitBitVecType> {
        match *self {
            Expr::ExprLitBitVec(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bitvec(&self) -> bool {
        match *self {
            Expr::ExprLitBitVec(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bool(&self) -> Option<&ExprLitBoolType> {
        match *self {
            Expr::ExprLitBool(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bool(&self) -> bool {
        match *self {
            Expr::ExprLitBool(_) => true,
            _ => false,
        }
    }

    pub fn is_lit_true(&self) -> bool {
        match *self {
            Expr::ExprLitBool(ref lit) if lit.value => true,
            _ => false,
        }
    }

    pub fn to_dot(&self) -> Option<&ExprDotType> {
        match *self {
            Expr::ExprDot(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_dot(&self) -> bool {
        match *self {
            Expr::ExprDot(_) => true,
            _ => false,
        }
    }

    pub fn to_tuple(&self) -> Option<&ExprTupleType> {
        match *self {
            Expr::ExprTuple(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match *self {
            Expr::ExprTuple(_) => true,
            _ => false,
        }
    }

    pub fn to_block(&self) -> Option<&ExprBlockType> {
        match *self {
            Expr::ExprBlock(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_block(&self) -> bool {
        match self {
            &Expr::ExprBlock(_) => true,
            _ => false,
        }
    }

    pub fn to_if(&self) -> Option<&ExprIfType> {
        match *self {
            Expr::ExprIf(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_if(&self) -> bool {
        match *self {
            Expr::ExprIf(_) => true,
            _ => false,
        }
    }

    pub fn needs_semicolon(&self) -> bool {
        match self {
            &Expr::ExprBlock(_) => false,
            &Expr::ExprIf(_) => false,
            _ => true,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            Expr::ExprUn(ref val) => val.pos,
            Expr::ExprBin(ref val) => val.pos,
            Expr::ExprLitInt(ref val) => val.pos,
            Expr::ExprLitFloat(ref val) => val.pos,
            Expr::ExprLitBitVec(ref val) => val.pos,
            Expr::ExprLitBool(ref val) => val.pos,
            Expr::ExprIdent(ref val) => val.pos,
            Expr::ExprCall(ref val) => val.pos,
            Expr::ExprExtract(ref val) => val.pos,
            Expr::ExprDot(ref val) => val.pos,
            Expr::ExprBlock(ref val) => val.pos,
            Expr::ExprIf(ref val) => val.pos,
            Expr::ExprTuple(ref val) => val.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            Expr::ExprUn(ref val) => val.span,
            Expr::ExprBin(ref val) => val.span,
            Expr::ExprLitInt(ref val) => val.span,
            Expr::ExprLitFloat(ref val) => val.span,
            Expr::ExprLitBitVec(ref val) => val.span,
            Expr::ExprLitBool(ref val) => val.span,
            Expr::ExprIdent(ref val) => val.span,
            Expr::ExprCall(ref val) => val.span,
            Expr::ExprExtract(ref val) => val.span,
            Expr::ExprDot(ref val) => val.span,
            Expr::ExprBlock(ref val) => val.span,
            Expr::ExprIf(ref val) => val.span,
            Expr::ExprTuple(ref val) => val.span,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            Expr::ExprUn(ref val) => val.id,
            Expr::ExprBin(ref val) => val.id,
            Expr::ExprLitInt(ref val) => val.id,
            Expr::ExprLitFloat(ref val) => val.id,
            Expr::ExprLitBitVec(ref val) => val.id,
            Expr::ExprLitBool(ref val) => val.id,
            Expr::ExprIdent(ref val) => val.id,
            Expr::ExprCall(ref val) => val.id,
            Expr::ExprExtract(ref val) => val.id,
            Expr::ExprDot(ref val) => val.id,
            Expr::ExprBlock(ref val) => val.id,
            Expr::ExprIf(ref val) => val.id,
            Expr::ExprTuple(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExprIfType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<Expr>,
    pub then_block: Box<Expr>,
    pub else_block: Option<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct ExprTupleType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub values: Vec<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct ExprUnType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: UnOp,
    pub opnd: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct ExprBinType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: BinOp,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct ExprLitIntType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: u64,
    pub base: IntBase,
    pub suffix: IntSuffix,
}

#[derive(Clone, Debug)]
pub struct ExprLitFloatType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: f64,
    pub suffix: FloatSuffix,
}

#[derive(Clone, Debug)]
pub struct ExprLitBitVecType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: BitVec,
}

#[derive(Clone, Debug)]
pub struct ExprLitBoolType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: bool,
}

#[derive(Clone, Debug)]
pub struct ExprBlockType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub stmts: Vec<Box<Stmt>>,
}

#[derive(Clone, Debug)]
pub struct TransitionSystemBlock {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub block: Box<ExprBlockType>,
}

#[derive(Clone, Debug)]
pub struct ExprIdentType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub type_params: Option<Vec<Type>>,
}

#[derive(Clone, Debug)]
pub struct ExprExtractType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub array: Box<Expr>,
    pub args: Vec<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct ExprCallType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub callee: Box<Expr>,
    pub args: Vec<Box<Expr>>,
}

impl ExprCallType {
    pub fn object(&self) -> Option<&Expr> {
        if let Some(dot) = self.callee.to_dot() {
            Some(&dot.lhs)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExprDotType {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}
