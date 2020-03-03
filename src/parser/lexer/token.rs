use std::fmt;
use std::result::Result;

use crate::parser::lexer::position::{Position, Span};

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TokenKind {
    LitInt(String, IntBase, IntSuffix),
    LitFloat(String, FloatSuffix),
    LitBitVec(String, String),
    Ident(String),
    End,

    // Keywords
    While,
    If,
    Else,
    True,
    False,
    At,
    
    // Operators
    Add,
    Concat,
    AddEq,
    Sub,
    Mul,
    Div,
    Mod,
    Not,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Dot,
    Colon,
    Arrow,
    Tilde,
    BitOr,
    BitAnd,
    Caret,
    And,
    Or,
    
    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    Ult,
    Ule,
    Ugt,
    Uge,

    GtGt,
    GtGtGt,
    LtLt,
    
    // UCLID5
    Module,

    Enum,
    Type,

    Input,
    Output,
    Var,
    Const,

    Define,
    
    Function,
    Procedure,
    
    Theorem,
    Lemma,
    
    Init,
    Next,
    Control,

    Havoc,
    Call,

    Returns,
    Modifies,
    Requires,
    Ensures,

    Assume,
    Assert,

    Induction,
    Simulate,
}

impl TokenKind {
    pub fn name(&self) -> &str {
        match *self {
            TokenKind::LitInt(_, _, suffix) => match suffix {
                IntSuffix::Byte => "byte number",
                IntSuffix::Int => "int number",
                IntSuffix::Long => "long number",
            },

            TokenKind::LitFloat(_, suffix) => match suffix {
                FloatSuffix::Float => "float number",
                FloatSuffix::Double => "double number",
            },

            TokenKind::LitBitVec(_, _) => "bitvec number",

            TokenKind::Ident(_) => "ident",
            TokenKind::End => "<<EOF>>",

            // Keywords
            TokenKind::Define => "define",
            TokenKind::Function => "function",
            TokenKind::Procedure => "procedure",
            TokenKind::Input => "input",
            TokenKind::Output => "output",
            TokenKind::Var => "var",
            TokenKind::While => "while",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::At => "@",

            TokenKind::Enum => "enum",
            TokenKind::Type => "type",
            TokenKind::Module => "module",
            TokenKind::Const => "const",

            // Operators
            TokenKind::Add => "+",
            TokenKind::Concat => "++",
            TokenKind::AddEq => "+=",
            TokenKind::Sub => "-",
            TokenKind::Mul => "*",
            TokenKind::Div => "/",
            TokenKind::Mod => "%",
            TokenKind::Not => "!",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::Comma => ",",
            TokenKind::Semicolon => ";",
            TokenKind::Dot => ".",
            TokenKind::Colon => ":",
            TokenKind::Arrow => "->",
            TokenKind::Tilde => "~",
            TokenKind::BitOr => "|",
            TokenKind::BitAnd => "&",
            TokenKind::Caret => "^",
            TokenKind::And => "&&",
            TokenKind::Or => "||",

            TokenKind::Eq => "=",
            TokenKind::EqEq => "==",
            TokenKind::Ne => "!=",
            TokenKind::Lt => "<",
            TokenKind::Le => "<=",
            TokenKind::Gt => ">",
            TokenKind::Ge => ">=",

            TokenKind::Ult => "<_u",
            TokenKind::Ule => "<=_u",
            TokenKind::Ugt => ">_u",
            TokenKind::Uge => ">=_u",

            TokenKind::GtGt => ">>",
            TokenKind::GtGtGt => ">>>",
            TokenKind::LtLt => "<<",

            TokenKind::Theorem => "theorem",
            TokenKind::Lemma => "lemma",
            TokenKind::Init => "init",
            TokenKind::Next => "next",
            TokenKind::Control => "control",

            TokenKind::Havoc => "havoc",
            TokenKind::Call => "call",

            TokenKind::Assume => "assume",
            TokenKind::Assert => "assert",
            
            TokenKind::Returns => "returns",
            TokenKind::Modifies => "modifies",
            TokenKind::Requires => "requires",
            TokenKind::Ensures => "ensures",

            TokenKind::Simulate => "simulate",
            TokenKind::Induction => "induction",
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum IntSuffix {
    Int,
    Long,
    Byte,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum FloatSuffix {
    Float,
    Double,
}

#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub position: Position,
    pub span: Span,
}

impl Token {
    pub fn new(tok: TokenKind, pos: Position, span: Span) -> Token {
        Token {
            kind: tok,
            position: pos,
            span,
        }
    }

    pub fn is_eof(&self) -> bool {
        self.kind == TokenKind::End
    }

    pub fn is(&self, kind: TokenKind) -> bool {
        self.kind == kind
    }

    pub fn name(&self) -> String {
        match self.kind {
            TokenKind::LitInt(ref val, _, suffix) => {
                let suffix = match suffix {
                    IntSuffix::Byte => "B",
                    IntSuffix::Int => "",
                    IntSuffix::Long => "L",
                };

                format!("{}{}", val, suffix)
            }

            TokenKind::Ident(ref val) => val.clone(),

            _ => self.kind.name().into(),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IntBase {
    Bin,
    Dec,
    Hex,
}

impl IntBase {
    pub fn num(self) -> u32 {
        match self {
            IntBase::Bin => 2,
            IntBase::Dec => 10,
            IntBase::Hex => 16,
        }
    }
}
