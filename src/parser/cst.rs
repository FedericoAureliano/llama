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
    pub modules: Vec<ModuleSyntaxObject>,
}

impl Cst {
    pub fn new() -> Cst {
        Cst { modules: Vec::new() }
    }
}

#[derive(Clone, Debug)]
pub struct ModuleSyntaxObject {
    // TODO: instances of other modules
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    
    pub types: Vec<TypeDeclarationSyntaxObject>,

    pub inputs: Vec<FieldDeclarationSyntaxObject>,
    pub outputs: Vec<FieldDeclarationSyntaxObject>,
    pub variables: Vec<FieldDeclarationSyntaxObject>,
    pub constants: Vec<FieldDeclarationSyntaxObject>,

    pub macros: Vec<MacroDeclarationSyntaxObject>,

    pub functions: Vec<FunctionDeclarationSyntaxObject>,
    pub procedures: Vec<ProcedureDeclarationSyntaxObject>,

    pub theorems: Vec<PropertyDeclarationSyntaxObject>,
    pub lemmas: Vec<PropertyDeclarationSyntaxObject>,

    pub init: Option<Box<TransitionSystemBlockSyntaxObject>>,
    pub next: Option<Box<TransitionSystemBlockSyntaxObject>>,
    pub control: Option<Box<TransitionSystemBlockSyntaxObject>>,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct NodeId(pub usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub enum TypeIdentifierSyntaxObject {
    Basic(BasicTypeIdentifierSyntaxObject),
    Tuple(TupleTypeIdentifierSyntaxObject),
}

#[derive(Clone, Debug)]
pub struct BasicTypeIdentifierSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    // Params are for arrays
    pub params: Option<Box<TypeIdentifierSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct TupleTypeIdentifierSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub subtypes: Vec<Box<TypeIdentifierSyntaxObject>>,
}

impl TypeIdentifierSyntaxObject {

    pub fn create_basic(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        params: Option<Box<TypeIdentifierSyntaxObject>>,
    ) -> TypeIdentifierSyntaxObject {
        TypeIdentifierSyntaxObject::Basic(BasicTypeIdentifierSyntaxObject {
            id,
            pos,
            span,
            name,
            params,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, subtypes: Vec<Box<TypeIdentifierSyntaxObject>>) -> TypeIdentifierSyntaxObject {
        TypeIdentifierSyntaxObject::Tuple(TupleTypeIdentifierSyntaxObject {
            id,
            pos,
            span,
            subtypes,
        })
    }

    pub fn to_basic(&self) -> Option<&BasicTypeIdentifierSyntaxObject> {
        match *self {
            TypeIdentifierSyntaxObject::Basic(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_tuple(&self) -> Option<&TupleTypeIdentifierSyntaxObject> {
        match *self {
            TypeIdentifierSyntaxObject::Tuple(ref val) => Some(val),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn is_unit(&self) -> bool {
        match self {
            &TypeIdentifierSyntaxObject::Tuple(ref val) if val.subtypes.len() == 0 => true,
            _ => false,
        }
    }

    pub fn to_string(&self, interner: &Interner) -> String {
        match *self {
            TypeIdentifierSyntaxObject::Basic(ref val) => {
                if let Some(p) = &val.params {
                    let types = format!("{}", p.to_string(interner));
                    format!("[{}]{}", types,  *interner.str(val.name))
                } else {
                    format!("{}", *interner.str(val.name))
                }
            }

            TypeIdentifierSyntaxObject::Tuple(ref val) => {
                let types: Vec<String> =
                    val.subtypes.iter().map(|t| t.to_string(interner)).collect();

                format!("({})", types.join(", "))
            }
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            TypeIdentifierSyntaxObject::Basic(ref val) => val.pos,
            TypeIdentifierSyntaxObject::Tuple(ref val) => val.pos,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            TypeIdentifierSyntaxObject::Basic(ref val) => val.id,
            TypeIdentifierSyntaxObject::Tuple(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeDeclarationSyntaxObject {
    Alias(TypeAliasSyntaxObject),
    Enum(EnumDeclarationSyntaxObject),
}

#[derive(Clone, Debug)]
pub struct TypeAliasSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub alias: Box<TypeIdentifierSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct EnumDeclarationSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub variants: Vec<Name>,
}


impl TypeDeclarationSyntaxObject {

    pub fn create_alias(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        alias: Box<TypeIdentifierSyntaxObject>,
    ) -> TypeDeclarationSyntaxObject {
        TypeDeclarationSyntaxObject::Alias(TypeAliasSyntaxObject {
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
    ) -> TypeDeclarationSyntaxObject {
        TypeDeclarationSyntaxObject::Enum(EnumDeclarationSyntaxObject {
            id,
            pos,
            span,
            name,
            variants,
        })
    }

    pub fn to_alias(&self) -> Option<&TypeAliasSyntaxObject> {
        match *self {
            TypeDeclarationSyntaxObject::Alias(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_enum(&self) -> Option<&EnumDeclarationSyntaxObject> {
        match *self {
            TypeDeclarationSyntaxObject::Enum(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn to_string(&self, interner: &Interner) -> String {
        match *self {
            TypeDeclarationSyntaxObject::Alias(ref val) => format!("`{}` := `{}`", *interner.str(val.name), val.alias.to_string(interner)),
            TypeDeclarationSyntaxObject::Enum(ref val) => {
                let types: Vec<String> = val.variants.iter().map(|t| format!("{}", *interner.str(*t))).collect();
                format!("enum {} of {{{}}}", *interner.str(val.name), types.join(", "))
            }
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            TypeDeclarationSyntaxObject::Alias(ref val) => val.pos,
            TypeDeclarationSyntaxObject::Enum(ref val) => val.pos,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            TypeDeclarationSyntaxObject::Alias(ref val) => val.id,
            TypeDeclarationSyntaxObject::Enum(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDeclarationSyntaxObject {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub data_type: TypeIdentifierSyntaxObject,
    pub expr: Option<Box<ExprSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct PropertyDeclarationSyntaxObject {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub expr: Box<ExprSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct FunctionDeclarationSyntaxObject {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub to_synthesize: bool,
    
    pub params: Vec<ParamSyntaxObject>,
    pub return_type: Option<TypeIdentifierSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct MacroDeclarationSyntaxObject {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub params: Vec<ParamSyntaxObject>,
    pub return_type: Option<TypeIdentifierSyntaxObject>,
    pub expr: Box<ExprSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct ProcedureDeclarationSyntaxObject {
    pub id: NodeId,
    pub name: Name,
    pub pos: Position,
    pub span: Span,
    pub params: Vec<ParamSyntaxObject>,

    pub returns: Vec<ParamSyntaxObject>,
    pub modifies: Vec<NameSyntaxObject>,
    pub requires: Vec<PredicateStmtSyntaxObject>,
    pub ensures: Vec<PredicateStmtSyntaxObject>,

    pub block: Option<Box<BlockSyntaxObject>>,
}

impl ProcedureDeclarationSyntaxObject {
    pub fn block(&self) -> &BlockSyntaxObject {
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
pub struct ParamSyntaxObject {
    pub id: NodeId,
    pub idx: u32,
    pub name: Name,
    pub pos: Position,
    pub span: Span,

    pub data_type: TypeIdentifierSyntaxObject,
}

#[derive(Clone, Debug)]
pub enum StmtSyntaxObject {
    Induction(InductionStmtSyntaxObject),
    Simulate(SimulateStmtSyntaxObject),
    Assert(PredicateStmtSyntaxObject),
    Assume(PredicateStmtSyntaxObject),
    Call(CallStmtSyntaxObject),
    Havoc(HavocStmtSyntaxObject),
    Var(VarStmtSyntaxObject),
    While(WhileStmtSyntaxObject),
    Expr(ExprStmtSyntaxObject),
}

impl StmtSyntaxObject {
    pub fn create_var(
        id: NodeId,
        pos: Position,
        span: Span,
        name: Name,
        reassignable: bool,
        data_type: Option<TypeIdentifierSyntaxObject>,
        expr: Option<Box<ExprSyntaxObject>>,
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Var(VarStmtSyntaxObject {
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
        expr: Box<ExprSyntaxObject>,
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Assume(PredicateStmtSyntaxObject {
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
        expr: Box<ExprSyntaxObject>,
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Assert(PredicateStmtSyntaxObject {
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
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Havoc(HavocStmtSyntaxObject {
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
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Simulate(SimulateStmtSyntaxObject {
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
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Induction(InductionStmtSyntaxObject {
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
        rets: Vec<NameSyntaxObject>,
        args: Vec<Box<ExprSyntaxObject>>,
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::Call(CallStmtSyntaxObject {
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
        cond: Box<ExprSyntaxObject>,
        block: Box<StmtSyntaxObject>,
    ) -> StmtSyntaxObject {
        StmtSyntaxObject::While(WhileStmtSyntaxObject {
            id,
            pos,
            span,

            cond,
            block,
        })
    }

    pub fn create_expr_stmt(id: NodeId, pos: Position, span: Span, expr: Box<ExprSyntaxObject>) -> StmtSyntaxObject {
        StmtSyntaxObject::Expr(ExprStmtSyntaxObject {
            id,
            pos,
            span,

            expr,
        })
    }

    pub fn id(&self) -> NodeId {
        match *self {
            StmtSyntaxObject::Induction(ref stmt) => stmt.id,
            StmtSyntaxObject::Simulate(ref stmt) => stmt.id,
            StmtSyntaxObject::Assert(ref stmt) => stmt.id,
            StmtSyntaxObject::Assume(ref stmt) => stmt.id,
            StmtSyntaxObject::Call(ref stmt) => stmt.id,
            StmtSyntaxObject::Havoc(ref stmt) => stmt.id,
            StmtSyntaxObject::Var(ref stmt) => stmt.id,
            StmtSyntaxObject::While(ref stmt) => stmt.id,
            StmtSyntaxObject::Expr(ref stmt) => stmt.id,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            StmtSyntaxObject::Induction(ref stmt) => stmt.pos,
            StmtSyntaxObject::Simulate(ref stmt) => stmt.pos,
            StmtSyntaxObject::Assert(ref stmt) => stmt.pos,
            StmtSyntaxObject::Assume(ref stmt) => stmt.pos,
            StmtSyntaxObject::Call(ref stmt) => stmt.pos,
            StmtSyntaxObject::Havoc(ref stmt) => stmt.pos,
            StmtSyntaxObject::Var(ref stmt) => stmt.pos,
            StmtSyntaxObject::While(ref stmt) => stmt.pos,
            StmtSyntaxObject::Expr(ref stmt) => stmt.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            StmtSyntaxObject::Induction(ref stmt) => stmt.span,
            StmtSyntaxObject::Simulate(ref stmt) => stmt.span,
            StmtSyntaxObject::Assert(ref stmt) => stmt.span,
            StmtSyntaxObject::Assume(ref stmt) => stmt.span,
            StmtSyntaxObject::Call(ref stmt) => stmt.span,
            StmtSyntaxObject::Havoc(ref stmt) => stmt.span,
            StmtSyntaxObject::Var(ref stmt) => stmt.span,
            StmtSyntaxObject::While(ref stmt) => stmt.span,
            StmtSyntaxObject::Expr(ref stmt) => stmt.span,
        }
    }

    pub fn to_var(&self) -> Option<&VarStmtSyntaxObject> {
        match *self {
            StmtSyntaxObject::Var(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_var(&self) -> bool {
        match *self {
            StmtSyntaxObject::Var(_) => true,
            _ => false,
        }
    }

    pub fn to_while(&self) -> Option<&WhileStmtSyntaxObject> {
        match *self {
            StmtSyntaxObject::While(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_while(&self) -> bool {
        match *self {
            StmtSyntaxObject::While(_) => true,
            _ => false,
        }
    }

    pub fn to_expr(&self) -> Option<&ExprStmtSyntaxObject> {
        match *self {
            StmtSyntaxObject::Expr(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_expr(&self) -> bool {
        match *self {
            StmtSyntaxObject::Expr(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CallStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub func: Name,
    pub rets: Vec<NameSyntaxObject>,
    pub args: Vec<Box<ExprSyntaxObject>>,
}


#[derive(Clone, Debug)]
pub struct HavocStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct PredicateStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub expr: Box<ExprSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct InductionStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct SimulateStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,
    pub steps: u64,
}

#[derive(Clone, Debug)]
pub struct VarStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub reassignable: bool,

    pub data_type: Option<TypeIdentifierSyntaxObject>,
    pub expr: Option<Box<ExprSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct ForStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
    pub expr: Box<ExprSyntaxObject>,
    pub block: Box<StmtSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct WhileStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<ExprSyntaxObject>,
    pub block: Box<StmtSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct ExprStmtSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub expr: Box<ExprSyntaxObject>,
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
pub enum ExprSyntaxObject {
    Un(UnExprSyntaxObject),
    Bin(BinExprSyntaxObject),
    LitInt(LitIntExprSyntaxObject),
    LitFloat(LitFloatExprSyntaxObject),
    LitBitVec(LitBitVecExprSyntaxObject),
    LitBool(LitBoolExprSyntaxObject),
    Identifier(NameSyntaxObject),
    Call(CallExprSyntaxObject),
    Extract(ExtractExprSyntaxObject),
    Dot(DotExprSyntaxObject),
    Block(BlockSyntaxObject),
    If(IfExprSyntaxObject),
    Tuple(TupleExprSyntaxObject),
}

impl ExprSyntaxObject {
    pub fn create_block(
        id: NodeId,
        pos: Position,
        span: Span,
        stmts: Vec<Box<StmtSyntaxObject>>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Block(BlockSyntaxObject {
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
        cond: Box<ExprSyntaxObject>,
        then_block: Box<ExprSyntaxObject>,
        else_block: Option<Box<ExprSyntaxObject>>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::If(IfExprSyntaxObject {
            id,
            pos,
            span,

            cond,
            then_block,
            else_block,
        })
    }

    pub fn create_un(id: NodeId, pos: Position, span: Span, op: UnOp, opnd: Box<ExprSyntaxObject>) -> ExprSyntaxObject {
        ExprSyntaxObject::Un(UnExprSyntaxObject {
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
        lhs: Box<ExprSyntaxObject>,
        rhs: Box<ExprSyntaxObject>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Bin(BinExprSyntaxObject {
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
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::LitInt(LitIntExprSyntaxObject {
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
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::LitFloat(LitFloatExprSyntaxObject {
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
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::LitBitVec(LitBitVecExprSyntaxObject {
            id,
            pos,
            span,
            value,
        })
    }

    pub fn create_lit_bool(id: NodeId, pos: Position, span: Span, value: bool) -> ExprSyntaxObject {
        ExprSyntaxObject::LitBool(LitBoolExprSyntaxObject {
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
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Identifier(NameSyntaxObject {
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
        callee: Box<ExprSyntaxObject>,
        args: Vec<Box<ExprSyntaxObject>>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Call(CallExprSyntaxObject {
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
        array: Box<ExprSyntaxObject>,
        args: Vec<Box<ExprSyntaxObject>>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Extract(ExtractExprSyntaxObject {
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
        lhs: Box<ExprSyntaxObject>,
        rhs: Box<ExprSyntaxObject>,
    ) -> ExprSyntaxObject {
        ExprSyntaxObject::Dot(DotExprSyntaxObject {
            id,
            pos,
            span,

            lhs,
            rhs,
        })
    }

    pub fn create_tuple(id: NodeId, pos: Position, span: Span, values: Vec<Box<ExprSyntaxObject>>) -> ExprSyntaxObject {
        ExprSyntaxObject::Tuple(TupleExprSyntaxObject {
            id,
            pos,
            span,
            values,
        })
    }

    pub fn to_un(&self) -> Option<&UnExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::Un(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_un(&self) -> bool {
        match *self {
            ExprSyntaxObject::Un(_) => true,
            _ => false,
        }
    }

    pub fn to_bin(&self) -> Option<&BinExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::Bin(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_bin(&self) -> bool {
        match *self {
            ExprSyntaxObject::Bin(_) => true,
            _ => false,
        }
    }

    pub fn to_ident(&self) -> Option<&NameSyntaxObject> {
        match *self {
            ExprSyntaxObject::Identifier(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_ident(&self) -> bool {
        match *self {
            ExprSyntaxObject::Identifier(_) => true,
            _ => false,
        }
    }

    pub fn to_call(&self) -> Option<&CallExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::Call(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_call(&self) -> bool {
        match *self {
            ExprSyntaxObject::Call(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_int(&self) -> Option<&LitIntExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::LitInt(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_int(&self) -> bool {
        match *self {
            ExprSyntaxObject::LitInt(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_float(&self) -> Option<&LitFloatExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::LitFloat(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_float(&self) -> bool {
        match *self {
            ExprSyntaxObject::LitFloat(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bitvec(&self) -> Option<&LitBitVecExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::LitBitVec(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bitvec(&self) -> bool {
        match *self {
            ExprSyntaxObject::LitBitVec(_) => true,
            _ => false,
        }
    }

    pub fn to_lit_bool(&self) -> Option<&LitBoolExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::LitBool(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_lit_bool(&self) -> bool {
        match *self {
            ExprSyntaxObject::LitBool(_) => true,
            _ => false,
        }
    }

    pub fn is_lit_true(&self) -> bool {
        match *self {
            ExprSyntaxObject::LitBool(ref lit) if lit.value => true,
            _ => false,
        }
    }

    pub fn to_dot(&self) -> Option<&DotExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::Dot(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_dot(&self) -> bool {
        match *self {
            ExprSyntaxObject::Dot(_) => true,
            _ => false,
        }
    }

    pub fn to_tuple(&self) -> Option<&TupleExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::Tuple(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match *self {
            ExprSyntaxObject::Tuple(_) => true,
            _ => false,
        }
    }

    pub fn to_block(&self) -> Option<&BlockSyntaxObject> {
        match *self {
            ExprSyntaxObject::Block(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_block(&self) -> bool {
        match self {
            &ExprSyntaxObject::Block(_) => true,
            _ => false,
        }
    }

    pub fn to_if(&self) -> Option<&IfExprSyntaxObject> {
        match *self {
            ExprSyntaxObject::If(ref val) => Some(val),
            _ => None,
        }
    }

    pub fn is_if(&self) -> bool {
        match *self {
            ExprSyntaxObject::If(_) => true,
            _ => false,
        }
    }

    pub fn needs_semicolon(&self) -> bool {
        match self {
            &ExprSyntaxObject::Block(_) => false,
            &ExprSyntaxObject::If(_) => false,
            _ => true,
        }
    }

    pub fn pos(&self) -> Position {
        match *self {
            ExprSyntaxObject::Un(ref val) => val.pos,
            ExprSyntaxObject::Bin(ref val) => val.pos,
            ExprSyntaxObject::LitInt(ref val) => val.pos,
            ExprSyntaxObject::LitFloat(ref val) => val.pos,
            ExprSyntaxObject::LitBitVec(ref val) => val.pos,
            ExprSyntaxObject::LitBool(ref val) => val.pos,
            ExprSyntaxObject::Identifier(ref val) => val.pos,
            ExprSyntaxObject::Call(ref val) => val.pos,
            ExprSyntaxObject::Extract(ref val) => val.pos,
            ExprSyntaxObject::Dot(ref val) => val.pos,
            ExprSyntaxObject::Block(ref val) => val.pos,
            ExprSyntaxObject::If(ref val) => val.pos,
            ExprSyntaxObject::Tuple(ref val) => val.pos,
        }
    }

    pub fn span(&self) -> Span {
        match *self {
            ExprSyntaxObject::Un(ref val) => val.span,
            ExprSyntaxObject::Bin(ref val) => val.span,
            ExprSyntaxObject::LitInt(ref val) => val.span,
            ExprSyntaxObject::LitFloat(ref val) => val.span,
            ExprSyntaxObject::LitBitVec(ref val) => val.span,
            ExprSyntaxObject::LitBool(ref val) => val.span,
            ExprSyntaxObject::Identifier(ref val) => val.span,
            ExprSyntaxObject::Call(ref val) => val.span,
            ExprSyntaxObject::Extract(ref val) => val.span,
            ExprSyntaxObject::Dot(ref val) => val.span,
            ExprSyntaxObject::Block(ref val) => val.span,
            ExprSyntaxObject::If(ref val) => val.span,
            ExprSyntaxObject::Tuple(ref val) => val.span,
        }
    }

    pub fn id(&self) -> NodeId {
        match *self {
            ExprSyntaxObject::Un(ref val) => val.id,
            ExprSyntaxObject::Bin(ref val) => val.id,
            ExprSyntaxObject::LitInt(ref val) => val.id,
            ExprSyntaxObject::LitFloat(ref val) => val.id,
            ExprSyntaxObject::LitBitVec(ref val) => val.id,
            ExprSyntaxObject::LitBool(ref val) => val.id,
            ExprSyntaxObject::Identifier(ref val) => val.id,
            ExprSyntaxObject::Call(ref val) => val.id,
            ExprSyntaxObject::Extract(ref val) => val.id,
            ExprSyntaxObject::Dot(ref val) => val.id,
            ExprSyntaxObject::Block(ref val) => val.id,
            ExprSyntaxObject::If(ref val) => val.id,
            ExprSyntaxObject::Tuple(ref val) => val.id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct IfExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub cond: Box<ExprSyntaxObject>,
    pub then_block: Box<ExprSyntaxObject>,
    pub else_block: Option<Box<ExprSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct TupleExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub values: Vec<Box<ExprSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct UnExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: UnOp,
    pub opnd: Box<ExprSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct BinExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub op: BinOp,
    pub lhs: Box<ExprSyntaxObject>,
    pub rhs: Box<ExprSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct LitIntExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: u64,
    pub base: IntBase,
    pub suffix: IntSuffix,
}

#[derive(Clone, Debug)]
pub struct LitFloatExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: f64,
    pub suffix: FloatSuffix,
}

#[derive(Clone, Debug)]
pub struct LitBitVecExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: BitVec,
}

#[derive(Clone, Debug)]
pub struct LitBoolExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub value: bool,
}

#[derive(Clone, Debug)]
pub struct BlockSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub stmts: Vec<Box<StmtSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct TransitionSystemBlockSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub block: Box<BlockSyntaxObject>,
}

#[derive(Clone, Debug)]
pub struct NameSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct ExtractExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub array: Box<ExprSyntaxObject>,
    pub args: Vec<Box<ExprSyntaxObject>>,
}

#[derive(Clone, Debug)]
pub struct CallExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub callee: Box<ExprSyntaxObject>,
    pub args: Vec<Box<ExprSyntaxObject>>,
}

impl CallExprSyntaxObject {
    pub fn object(&self) -> Option<&ExprSyntaxObject> {
        if let Some(dot) = self.callee.to_dot() {
            Some(&dot.lhs)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct DotExprSyntaxObject {
    pub id: NodeId,
    pub pos: Position,
    pub span: Span,

    pub lhs: Box<ExprSyntaxObject>,
    pub rhs: Box<ExprSyntaxObject>,
}
