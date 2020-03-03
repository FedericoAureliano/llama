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
    pub modules: Vec<ModuleCst>,
}

impl Cst {
    pub fn new() -> Cst {
        Cst { modules: Vec::new() }
    }
}

#[derive(Clone, Debug)]
pub struct ModuleCst {
    // TODO: instances of other modules
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    
    pub types: Vec<TypeDeclCst>,

    pub inputs: Vec<FieldDeclCst>,
    pub outputs: Vec<FieldDeclCst>,
    pub variables: Vec<FieldDeclCst>,
    pub constants: Vec<FieldDeclCst>,

    pub macros: Vec<MacroDeclCst>,

    pub functions: Vec<FunctionDeclCst>,
    pub procedures: Vec<ProcedureDeclCst>,

    pub theorems: Vec<PropertyDeclCst>,
    pub lemmas: Vec<PropertyDeclCst>,

    pub init: Option<Box<TransitionSystemBlockCst>>,
    pub next: Option<Box<TransitionSystemBlockCst>>,
    pub control: Option<Box<TransitionSystemBlockCst>>,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct NodeId(pub usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub enum TypeIdentCst {
    Basic(BasicTypeIdentCst),
    Tuple(TupleTypeIdentCst),
}

#[derive(Clone, Debug)]
pub struct BasicTypeIdentCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    // Params are for arrays
    pub params: Vec<Box<TypeIdentCst>>,
}

#[derive(Clone, Debug)]
pub struct TupleTypeIdentCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub subtypes: Vec<Box<TypeIdentCst>>,
}

impl TypeIdentCst {

    pub fn create_basic(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        params: Vec<Box<TypeIdentCst>>,
    ) -> TypeIdentCst {
        TypeIdentCst::Basic(BasicTypeIdentCst {
            id,
            pos,
            span,
            name,
            params,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, subtypes: Vec<Box<TypeIdentCst>>) -> TypeIdentCst {
        TypeIdentCst::Tuple(TupleTypeIdentCst {
            id,
            pos,
            span,
            subtypes,
        })
    }

    pub fn to_basic(&self) -> Option<&BasicTypeIdentCst> {
        match *self {
            TypeIdentCst::Basic(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_tuple(&self) -> Option<&TupleTypeIdentCst> {
        match *self {
            TypeIdentCst::Tuple(ref val) => Some(val),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn is_unit(&self) -> bool {
        match self {
            &TypeIdentCst::Tuple(ref val) if val.subtypes.len() == 0 => true,
            _ => false,
        }
    }

    pub fn to_string(&self, interner: &Interner) -> String {
        match *self {
            TypeIdentCst::Basic(ref val) => {
                if val.params.len() > 0 {
                    let types: Vec<String> = val.params.iter().map(|t| format!("{}", t.to_string(interner))).collect();
                    format!("[{}]{}", types.join(", "),  *interner.str(val.name))
                } else {
                    format!("{}", *interner.str(val.name))
                }
            }

            TypeIdentCst::Tuple(ref val) => {
                let types: Vec<String> =
                    val.subtypes.iter().map(|t| t.to_string(interner)).collect();

                format!("({})", types.join(", "))
            }
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            TypeIdentCst::Basic(ref val) => val.pos,
            TypeIdentCst::Tuple(ref val) => val.pos,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            TypeIdentCst::Basic(ref val) => val.id,
            TypeIdentCst::Tuple(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeDeclCst {
    Alias(TypeAliasCst),
    Enum(EnumDeclCst),
}

#[derive(Clone, Debug)]
pub struct TypeAliasCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub alias: Box<TypeIdentCst>,
}

#[derive(Clone, Debug)]
pub struct EnumDeclCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub variants: Vec<NameCst>,
}


impl TypeDeclCst {

    pub fn create_alias(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        alias: Box<TypeIdentCst>,
    ) -> TypeDeclCst {
        TypeDeclCst::Alias(TypeAliasCst {
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
        variants: Vec<NameCst>,
    ) -> TypeDeclCst {
        TypeDeclCst::Enum(EnumDeclCst {
            id,
            pos,
            span,
            name,
            variants,
        })
    }

    pub fn to_alias(&self) -> Option<&TypeAliasCst> {
        match *self {
            TypeDeclCst::Alias(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_enum(&self) -> Option<&EnumDeclCst> {
        match *self {
            TypeDeclCst::Enum(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_string(&self, interner: &Interner) -> String {
        match *self {
            TypeDeclCst::Alias(ref val) => format!("`{}` := `{}`", *interner.str(val.name), val.alias.to_string(interner)),
            TypeDeclCst::Enum(ref val) => {
                let types: Vec<String> = val.variants.iter().map(|t| format!("{}", *interner.str(t.name))).collect();
                format!("enum {} of {{{}}}", *interner.str(val.name), types.join(", "))
            }
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            TypeDeclCst::Alias(ref val) => val.pos,
            TypeDeclCst::Enum(ref val) => val.pos,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            TypeDeclCst::Alias(ref val) => val.id,
            TypeDeclCst::Enum(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDeclCst {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub data_type: TypeIdentCst,
    pub expr: Option<Box<ExprCst>>,
}

#[derive(Clone, Debug)]
pub struct PropertyDeclCst {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub expr: Box<ExprCst>,
}

#[derive(Clone, Debug)]
pub struct FunctionDeclCst {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub to_synthesize: bool,
    
    pub params: Vec<ParamCst>,
    pub return_type: Option<TypeIdentCst>,
}

#[derive(Clone, Debug)]
pub struct MacroDeclCst {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub params: Vec<ParamCst>,
    pub return_type: Option<TypeIdentCst>,
    pub expr: Box<ExprCst>,
}

#[derive(Clone, Debug)]
pub struct ProcedureDeclCst {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub params: Vec<ParamCst>,

    pub returns: Vec<ParamCst>,
    pub modifies: Vec<NameCst>,
    pub requires: Vec<PredicateStmtCst>,
    pub ensures: Vec<PredicateStmtCst>,

    pub block: Option<Box<BlockCst>>,
}

impl ProcedureDeclCst {
    pub fn block(&self) -> &BlockCst {
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
pub struct ParamCst {
    pub id: NodeId,
    pub idx: u32,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub data_type: TypeIdentCst,
}

#[derive(Clone, Debug)]
pub enum StmtCst {
    Induction(InductionStmtCst),
    Simulate(SimulateStmtCst),
    Assert(PredicateStmtCst),
    Assume(PredicateStmtCst),
    Call(CallStmtCst),
    Havoc(HavocStmtCst),
    Var(VarStmtCst),
    While(WhileStmtCst),
    Expr(ExprStmtCst),
}

impl StmtCst {
    pub fn create_var(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        reassignable: bool,
        data_type: Option<TypeIdentCst>,
        expr: Option<Box<ExprCst>>,
    ) -> StmtCst {
        StmtCst::Var(VarStmtCst {
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
        expr: Box<ExprCst>,
    ) -> StmtCst {
        StmtCst::Assume(PredicateStmtCst {
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
        expr: Box<ExprCst>,
    ) -> StmtCst {
        StmtCst::Assert(PredicateStmtCst {
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
    ) -> StmtCst {
        StmtCst::Havoc(HavocStmtCst {
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
    ) -> StmtCst {
        StmtCst::Simulate(SimulateStmtCst {
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
    ) -> StmtCst {
        StmtCst::Induction(InductionStmtCst {
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
        rets: Vec<NameCst>,
        args: Vec<Box<ExprCst>>,
    ) -> StmtCst {
        StmtCst::Call(CallStmtCst {
            id,
            pos,
            span,
            func,
            rets,
            args,
        })
    }

    pub fn create_while(
        id: NodeId,
        pos: Position,
        span: Span,
        cond: Box<ExprCst>,
        block: Box<StmtCst>,
    ) -> StmtCst {
        StmtCst::While(WhileStmtCst {
            id,
            pos,
            span,

            cond,
            block,
        })
    }

    pub fn create_expr_stmt(id: NodeId, pos: Position, span: Span, expr: Box<ExprCst>) -> StmtCst {
        StmtCst::Expr(ExprStmtCst {
            id,
            pos,
            span,

            expr,
        })
    }

    pub fn id(&self) -> NodeId {
        match *self {
            StmtCst::Induction(ref stmt) => stmt.id,
            StmtCst::Simulate(ref stmt) => stmt.id,
            StmtCst::Assert(ref stmt) => stmt.id,
            StmtCst::Assume(ref stmt) => stmt.id,
            StmtCst::Call(ref stmt) => stmt.id,
            StmtCst::Havoc(ref stmt) => stmt.id,
            StmtCst::Var(ref stmt) => stmt.id,
            StmtCst::While(ref stmt) => stmt.id,
            StmtCst::Expr(ref stmt) => stmt.id,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            StmtCst::Induction(ref stmt) => stmt.pos,
            StmtCst::Simulate(ref stmt) => stmt.pos,
            StmtCst::Assert(ref stmt) => stmt.pos,
            StmtCst::Assume(ref stmt) => stmt.pos,
            StmtCst::Call(ref stmt) => stmt.pos,
            StmtCst::Havoc(ref stmt) => stmt.pos,
            StmtCst::Var(ref stmt) => stmt.pos,
            StmtCst::While(ref stmt) => stmt.pos,
            StmtCst::Expr(ref stmt) => stmt.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            StmtCst::Induction(ref stmt) => stmt.span,
            StmtCst::Simulate(ref stmt) => stmt.span,
            StmtCst::Assert(ref stmt) => stmt.span,
            StmtCst::Assume(ref stmt) => stmt.span,
            StmtCst::Call(ref stmt) => stmt.span,
            StmtCst::Havoc(ref stmt) => stmt.span,
            StmtCst::Var(ref stmt) => stmt.span,
            StmtCst::While(ref stmt) => stmt.span,
            StmtCst::Expr(ref stmt) => stmt.span,
        }
    }

    pub fn to_var(&self) -> Option<&VarStmtCst> {
        match *self {
            StmtCst::Var(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_var(&self) -> bool {
        match *self {
            StmtCst::Var(_) => true,
            _ => false,
        }
    }

    pub fn to_while(&self) -> Option<&WhileStmtCst> {
        match *self {
            StmtCst::While(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_while(&self) -> bool {
        match *self {
            StmtCst::While(_) => true,
            _ => false,
        }
    }

    pub fn to_expr(&self) -> Option<&ExprStmtCst> {
        match *self {
            StmtCst::Expr(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_expr(&self) -> bool {
        match *self {
            StmtCst::Expr(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CallStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub func: Name,
    pub rets: Vec<NameCst>,
    pub args: Vec<Box<ExprCst>>,
}


#[derive(Clone, Debug)]
pub struct HavocStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct PredicateStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub expr: Box<ExprCst>,
}

#[derive(Clone, Debug)]
pub struct InductionStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct SimulateStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct VarStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub reassignable: bool,

    pub data_type: Option<TypeIdentCst>,
    pub expr: Option<Box<ExprCst>>,
}

#[derive(Clone, Debug)]
pub struct ForStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub expr: Box<ExprCst>,
    pub block: Box<StmtCst>,
}

#[derive(Clone, Debug)]
pub struct WhileStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<ExprCst>,
    pub block: Box<StmtCst>,
}

#[derive(Clone, Debug)]
pub struct ExprStmtCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub expr: Box<ExprCst>,
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
pub enum ExprCst {
    Un(UnExprCst),
    Bin(BinExprCst),
    LitInt(LitIntExprCst),
    LitFloat(LitFloatExprCst),
    LitBitVec(LitBitVecExprCst),
    LitBool(LitBoolExprCst),
    Ident(NameCst),
    Call(CallExprCst),
    Extract(ExtractExprCst),
    Dot(DotExprCst),
    Block(BlockCst),
    If(IfExprCst),
    Tuple(TupleExprCst),
}

impl ExprCst {
    pub fn create_block(
        id: NodeId,
        pos: Position,
        span: Span,
        stmts: Vec<Box<StmtCst>>,
    ) -> ExprCst {
        ExprCst::Block(BlockCst {
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
        cond: Box<ExprCst>,
        then_block: Box<ExprCst>,
        else_block: Option<Box<ExprCst>>,
    ) -> ExprCst {
        ExprCst::If(IfExprCst {
            id,
            pos,
            span,

            cond,
            then_block,
            else_block,
        })
    }

    pub fn create_un(id: NodeId, pos: Position, span: Span, op: UnOp, opnd: Box<ExprCst>) -> ExprCst {
        ExprCst::Un(UnExprCst {
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
        lhs: Box<ExprCst>,
        rhs: Box<ExprCst>,
    ) -> ExprCst {
        ExprCst::Bin(BinExprCst {
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
    ) -> ExprCst {
        ExprCst::LitInt(LitIntExprCst {
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
    ) -> ExprCst {
        ExprCst::LitFloat(LitFloatExprCst {
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
    ) -> ExprCst {
        ExprCst::LitBitVec(LitBitVecExprCst {
            id,
            pos,
            span,
            value,
        })
    }

    pub fn create_lit_bool(id: NodeId, pos: Position, span: Span, value: bool) -> ExprCst {
        ExprCst::LitBool(LitBoolExprCst {
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
    ) -> ExprCst {
        ExprCst::Ident(NameCst {
            id,
            pos,
            span,

            name,
        })
    }

    pub fn create_call(
        id: NodeId,
        pos: Position,
        span: Span,
        callee: Box<ExprCst>,
        args: Vec<Box<ExprCst>>,
    ) -> ExprCst {
        ExprCst::Call(CallExprCst {
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
        array: Box<ExprCst>,
        args: Vec<Box<ExprCst>>,
    ) -> ExprCst {
        ExprCst::Extract(ExtractExprCst {
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
        lhs: Box<ExprCst>,
        rhs: Box<ExprCst>,
    ) -> ExprCst {
        ExprCst::Dot(DotExprCst {
            id,
            pos,
            span,

            lhs,
            rhs,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, values: Vec<Box<ExprCst>>) -> ExprCst {
        ExprCst::Tuple(TupleExprCst {
            id,
            pos,
            span,
            values,
        })
    }

    pub fn to_un(&self) -> Option<&UnExprCst> {
        match *self {
            ExprCst::Un(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_un(&self) -> bool {
        match *self {
            ExprCst::Un(_) => true,
            _ => false,
        }
    }

    pub fn to_bin(&self) -> Option<&BinExprCst> {
        match *self {
            ExprCst::Bin(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_bin(&self) -> bool {
        match *self {
            ExprCst::Bin(_) => true,
            _ => false,
        }
    }

    pub fn to_ident(&self) -> Option<&NameCst> {
        match *self {
            ExprCst::Ident(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_ident(&self) -> bool {
        match *self {
            ExprCst::Ident(_) => true,
            _ => false,
        }
    }

    pub fn to_call(&self) -> Option<&CallExprCst> {
        match *self {
            ExprCst::Call(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_call(&self) -> bool {
        match *self {
            ExprCst::Call(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_int(&self) -> Option<&LitIntExprCst> {
        match *self {
            ExprCst::LitInt(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_int(&self) -> bool {
        match *self {
            ExprCst::LitInt(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_float(&self) -> Option<&LitFloatExprCst> {
        match *self {
            ExprCst::LitFloat(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_float(&self) -> bool {
        match *self {
            ExprCst::LitFloat(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bitvec(&self) -> Option<&LitBitVecExprCst> {
        match *self {
            ExprCst::LitBitVec(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bitvec(&self) -> bool {
        match *self {
            ExprCst::LitBitVec(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bool(&self) -> Option<&LitBoolExprCst> {
        match *self {
            ExprCst::LitBool(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bool(&self) -> bool {
        match *self {
            ExprCst::LitBool(_) => true,
            _ => false,
        }
    }

    pub fn is_lit_true(&self) -> bool {
        match *self {
            ExprCst::LitBool(ref lit) if lit.value => true,
            _ => false,
        }
    }

    pub fn to_dot(&self) -> Option<&DotExprCst> {
        match *self {
            ExprCst::Dot(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_dot(&self) -> bool {
        match *self {
            ExprCst::Dot(_) => true,
            _ => false,
        }
    }

    pub fn to_tuple(&self) -> Option<&TupleExprCst> {
        match *self {
            ExprCst::Tuple(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match *self {
            ExprCst::Tuple(_) => true,
            _ => false,
        }
    }

    pub fn to_block(&self) -> Option<&BlockCst> {
        match *self {
            ExprCst::Block(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_block(&self) -> bool {
        match self {
            &ExprCst::Block(_) => true,
            _ => false,
        }
    }

    pub fn to_if(&self) -> Option<&IfExprCst> {
        match *self {
            ExprCst::If(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_if(&self) -> bool {
        match *self {
            ExprCst::If(_) => true,
            _ => false,
        }
    }

    pub fn needs_semicolon(&self) -> bool {
        match self {
            &ExprCst::Block(_) => false,
            &ExprCst::If(_) => false,
            _ => true,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            ExprCst::Un(ref val) => val.pos,
            ExprCst::Bin(ref val) => val.pos,
            ExprCst::LitInt(ref val) => val.pos,
            ExprCst::LitFloat(ref val) => val.pos,
            ExprCst::LitBitVec(ref val) => val.pos,
            ExprCst::LitBool(ref val) => val.pos,
            ExprCst::Ident(ref val) => val.pos,
            ExprCst::Call(ref val) => val.pos,
            ExprCst::Extract(ref val) => val.pos,
            ExprCst::Dot(ref val) => val.pos,
            ExprCst::Block(ref val) => val.pos,
            ExprCst::If(ref val) => val.pos,
            ExprCst::Tuple(ref val) => val.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            ExprCst::Un(ref val) => val.span,
            ExprCst::Bin(ref val) => val.span,
            ExprCst::LitInt(ref val) => val.span,
            ExprCst::LitFloat(ref val) => val.span,
            ExprCst::LitBitVec(ref val) => val.span,
            ExprCst::LitBool(ref val) => val.span,
            ExprCst::Ident(ref val) => val.span,
            ExprCst::Call(ref val) => val.span,
            ExprCst::Extract(ref val) => val.span,
            ExprCst::Dot(ref val) => val.span,
            ExprCst::Block(ref val) => val.span,
            ExprCst::If(ref val) => val.span,
            ExprCst::Tuple(ref val) => val.span,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            ExprCst::Un(ref val) => val.id,
            ExprCst::Bin(ref val) => val.id,
            ExprCst::LitInt(ref val) => val.id,
            ExprCst::LitFloat(ref val) => val.id,
            ExprCst::LitBitVec(ref val) => val.id,
            ExprCst::LitBool(ref val) => val.id,
            ExprCst::Ident(ref val) => val.id,
            ExprCst::Call(ref val) => val.id,
            ExprCst::Extract(ref val) => val.id,
            ExprCst::Dot(ref val) => val.id,
            ExprCst::Block(ref val) => val.id,
            ExprCst::If(ref val) => val.id,
            ExprCst::Tuple(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct IfExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<ExprCst>,
    pub then_block: Box<ExprCst>,
    pub else_block: Option<Box<ExprCst>>,
}

#[derive(Clone, Debug)]
pub struct TupleExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub values: Vec<Box<ExprCst>>,
}

#[derive(Clone, Debug)]
pub struct UnExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: UnOp,
    pub opnd: Box<ExprCst>,
}

#[derive(Clone, Debug)]
pub struct BinExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: BinOp,
    pub lhs: Box<ExprCst>,
    pub rhs: Box<ExprCst>,
}

#[derive(Clone, Debug)]
pub struct LitIntExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: u64,
    pub base: IntBase,
    pub suffix: IntSuffix,
}

#[derive(Clone, Debug)]
pub struct LitFloatExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: f64,
    pub suffix: FloatSuffix,
}

#[derive(Clone, Debug)]
pub struct LitBitVecExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: BitVec,
}

#[derive(Clone, Debug)]
pub struct LitBoolExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: bool,
}

#[derive(Clone, Debug)]
pub struct BlockCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub stmts: Vec<Box<StmtCst>>,
}

#[derive(Clone, Debug)]
pub struct TransitionSystemBlockCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub block: Box<BlockCst>,
}

#[derive(Clone, Debug)]
pub struct NameCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct ExtractExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub array: Box<ExprCst>,
    pub args: Vec<Box<ExprCst>>,
}

#[derive(Clone, Debug)]
pub struct CallExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub callee: Box<ExprCst>,
    pub args: Vec<Box<ExprCst>>,
}

impl CallExprCst {
    pub fn object(&self) -> Option<&ExprCst> {
        if let Some(dot) = self.callee.to_dot() {
            Some(&dot.lhs)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct DotExprCst {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub lhs: Box<ExprCst>,
    pub rhs: Box<ExprCst>,
}
