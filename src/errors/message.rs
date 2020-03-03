use crate::parser::lexer::position::Position;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SemError {
    Unimplemented,

    UnknownType(String),
    UnknownIdent(String),
    UnknownFunction(String),
    UnknownField(String, String),
    UnknownEnumValue(String),
    IdentExists(String),

    DuplicateFunction(String),
    DuplicateParam(String),
    DuplicateField(String),
    DuplicateConst(String),

    DuplicateEnumVariant(String, String),
    DuplicateEnum(String),
    NoEnumValue(String),
    
    InvalidLhsAssignment,
    VarNeedsTypeInfo(String),
    ParamTypesIncompatible(String, Vec<String>, Vec<String>),
    
    WhileCondType(String),
    IfCondType(String),
    ReturnType(String, String),

    LvalueExpected,
    AssignType(String, String, String),
    AssignField(String, String, String, String),
    
    UnOpType(String, String),
    BinOpType(String, String, String),
    ConstValueExpected,
    OutsideLoop,
    NoReturnValue,
    MainNotFound,
    WrongMainDefinition,
    LetMissingInitialization,
    LetReassigned,
    PrcdReassigned,
    PrcdUsedAsIdent,
    EnumUsedAsIdent,
    UnderivableType(String),
    CycleInHierarchy,
    TypesIncompatible(String, String),
    ReturnTypeMismatch(String, String),
    UnresolvedInternal,
    UnclosedComment,
    NumberOverflow(String),
    ExpectedFactor(String),
    ExpectedToken(String, String),
    ExpectedTopLevelElement(String),
    ExpectedType(String),
    ExpectedIdent(String),
    ExpectedStringable(String),
    ExpectedSomeIdent,
    MisplacedElse,
    IoError,
    MisplacedAnnotation(String),
    RedundantAnnotation(String),
    UnknownAnnotation(String),
    InvalidEscapeSequence(char),
    MissingPrcdBody,
    PrcdCallExpected,
    RecursiveStructure,
    TraitMethodWithBody,
    AssignmentToConst,
    BoundExpected,
    MakeIteratorReturnType(String),
    InvalidLeftSideOfSeparator,
    IfBranchTypesIncompatible(String, String),
    NameExpected,
    IndexExpected,
    IllegalTupleIndex(u64, String),
    NoTypeParamsExpected,
}

impl SemError {
    pub fn message(&self) -> String {
        match *self {
            SemError::Unimplemented => format!("feature not implemented yet."),
            SemError::UnknownType(ref name) => format!("type `{}` does not exist.", name),
            SemError::UnknownIdent(ref name) => format!("unknown ident `{}`.", name),
            SemError::UnknownFunction(ref name) => format!("unknown function `{}`", name),
            SemError::UnknownEnumValue(ref name) => {
                format!("no value with name `{}` in enumeration.", name)
            }
            SemError::UnknownField(ref field, ref ty) => {
                format!("unknown field `{}` for type `{}`", field, ty)
            }
            SemError::IdentExists(ref name) => {
                format!("can not redefine ident `{}`.", name)
            }
            SemError::DuplicateFunction(ref name) => format!("duplicate function `{}`.", name),
            SemError::DuplicateParam(ref name) => format!("duplicate param `{}`.", name),
            SemError::DuplicateField(ref name) => {
                format!("field with name `{}` already exists.", name)
            }
            SemError::DuplicateConst(ref name) => format!("duplicate const `{}`.", name),
            SemError::DuplicateEnumVariant(ref e, ref v) => format!("enum `{}` duplicates variant `{}`.", e, v),
            SemError::DuplicateEnum(ref name) => format!("duplicate enum `{}`.", name),
            SemError::NoEnumValue(ref name) => format!("enum `{}` needs at least one variant.", name),
            SemError::VarNeedsTypeInfo(ref name) => format!(
                "variable `{}` needs either type declaration or expression.",
                name
            ),
            SemError::ParamTypesIncompatible(ref name, ref def, ref expr) => {
                let def = def.join(", ");
                let expr = expr.join(", ");

                format!(
                    "function `{}({})` cannot be called as `{}({})`",
                    name, def, name, expr
                )
            }
            SemError::WhileCondType(ref ty) => {
                format!("`while` expects condition of type `bool` but got `{}`.", ty)
            }
            SemError::IfCondType(ref ty) => {
                format!("`if` expects condition of type `bool` but got `{}`.", ty)
            }
            SemError::ReturnType(ref def, ref expr) => format!(
                "`return` expects value of type `{}` but got `{}`.",
                def, expr
            ),
            SemError::LvalueExpected => format!("lvalue expected for assignment"),
            SemError::AssignType(ref name, ref def, ref expr) => format!(
                "cannot assign `{}` to variable `{}` of type `{}`.",
                expr, name, def
            ),
            SemError::AssignField(ref name, ref cls, ref def, ref expr) => format!(
                "cannot assign `{}` to field `{}`.`{}` of type `{}`.",
                expr, cls, name, def
            ),
            SemError::UnOpType(ref op, ref expr) => format!(
                "unary operator `{}` can not handle value of type `{} {}`.",
                op, op, expr
            ),
            SemError::BinOpType(ref op, ref lhs, ref rhs) => format!(
                "binary operator `{}` can not handle expression of type `{} {} {}`",
                op, lhs, op, rhs
            ),
            SemError::ConstValueExpected => "constant value expected".into(),
            SemError::OutsideLoop => "statement only allowed inside loops".into(),
            SemError::NoReturnValue => "function does not return a value in all code paths".into(),
            SemError::MainNotFound => "no `main` function found in the program".into(),
            SemError::WrongMainDefinition => "`main` function has wrong definition".into(),
            SemError::LetMissingInitialization => "`let` binding is missing initialization.".into(),
            SemError::LetReassigned => "`let` binding cannot be reassigned.".into(),
            SemError::PrcdReassigned => "function cannot be reassigned.".into(),
            SemError::PrcdUsedAsIdent => "function cannot be used as ident.".into(),
            SemError::EnumUsedAsIdent => "enum cannot be used as ident.".into(),
            SemError::InvalidLhsAssignment => "invalid left-hand-side of assignment.".into(),
            SemError::UnderivableType(ref name) => {
                format!("type `{}` cannot be used as super class.", name)
            }
            SemError::CycleInHierarchy => "cycle in type hierarchy detected.".into(),
            SemError::TypesIncompatible(ref na, ref nb) => {
                format!("types `{}` and `{}` incompatible.", na, nb)
            }
            SemError::ReturnTypeMismatch(ref fct, ref sup) => {
                format!("return types `{}` and `{}` do not match.", fct, sup)
            }
            SemError::UnresolvedInternal => "unresolved internal.".into(),
            SemError::MisplacedElse => "misplace else.".into(),
            SemError::ExpectedToken(ref exp, ref got) => {
                format!("expected {} but got {}.", exp, got)
            }
            SemError::NumberOverflow(ref ty) => format!("number does not fit into type {}.", ty),
            SemError::ExpectedFactor(ref got) => format!("factor expected but got {}.", got),
            SemError::ExpectedType(ref got) => format!("type expected but got {}.", got),
            SemError::ExpectedIdent(ref tok) => {
                format!("ident expected but got {}.", tok)
            }
            SemError::ExpectedSomeIdent => "ident expected".into(),
            SemError::ExpectedTopLevelElement(ref token) => {
                format!("expected function or class but got {}.", token)
            }
            SemError::ExpectedStringable(ref ty) => {
                format!("type {} does not implement Stringable.", ty)
            }
            SemError::MisplacedAnnotation(ref modifier) => {
                format!("misplaced annotation `{}`.", modifier)
            }
            SemError::RedundantAnnotation(ref token) => format!("redundant annotation {}.", token),
            SemError::UnknownAnnotation(ref token) => format!("unknown annotation {}.", token),
            SemError::UnclosedComment => "unclosed comment.".into(),
            SemError::InvalidEscapeSequence(ch) => format!("unknown escape sequence `\\{}`.", ch),
            SemError::IoError => "error reading from file.".into(),
            SemError::MissingPrcdBody => "missing function body.".into(),
            SemError::PrcdCallExpected => format!("function call expected"),
            SemError::RecursiveStructure => "recursive structure is not allowed.".into(),
            SemError::TraitMethodWithBody => {
                "trait method is not allowed to have definition".into()
            }
            SemError::AssignmentToConst => "cannot assign to const variable.".into(),
            SemError::BoundExpected => "class or trait bound expected".into(),
            SemError::MakeIteratorReturnType(ref ty) => format!(
                "makeIterator() returns `{}` which does not implement Iterator.",
                ty
            ),
            SemError::InvalidLeftSideOfSeparator => {
                "left hand side of separator is not a class.".into()
            }
            SemError::IfBranchTypesIncompatible(ref then_block, ref else_block) => format!(
                "if-branches have incompatible types `{}` and `{}`.",
                then_block, else_block
            ),
            SemError::NameExpected => "name expected for dot-operator.".into(),
            SemError::IndexExpected => "index expected as right-hand-side for tuple.".into(),
            SemError::IllegalTupleIndex(idx, ref ty) => {
                format!("illegal index `{}` for type `{}`", idx, ty)
            }
            SemError::NoTypeParamsExpected => "no type params allowed".into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SemErrorAndPos {
    pub pos: Position,
    pub msg: SemError,
}

impl SemErrorAndPos {
    pub fn new(pos: Position, msg: SemError) -> SemErrorAndPos {
        SemErrorAndPos {pos, msg }
    }

    pub fn message(&self) -> String {
        format!(
            "error at {}: {}",
            self.pos,
            self.msg.message()
        )
    }
}
