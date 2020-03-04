use crate::parser::lexer::position::Position;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    // Lexer errors
    UnknownChar(char),
    ExpectedBitVec,
    UnclosedComment,
    InvalidEscapeSequence(char),

    // Parser errors
    ExpectedTopLevelElement(String),
    ExpectedModuleElement(String),
    UnknownAnnotation(String),
    RedundantAnnotation(String),
    MisplacedAnnotation(String),
    ExpectedToken(String, String),
    ExpectedType(String),
    MisplacedElse,
    ExpectedFactor(String),
    NumberOverflow(String),
    ExpectedIdentifier(String),
    ExpectedStatement,
    ExpectedBlock,
}

impl ParseError {
    pub fn message(&self) -> String {
        match self {
            ParseError::ExpectedBitVec => {
                format!("expected bitvector.")
            }
            ParseError::UnknownChar(ch) => {
                format!("unknown character {} (codepoint {}).", ch, *ch as usize)
            }
            ParseError::UnclosedComment => "unclosed comment.".into(),
            ParseError::InvalidEscapeSequence(ch) => format!("unknown escape sequence `\\{}`.", ch),

            // Parser errors
            ParseError::ExpectedTopLevelElement(ref token) => {
                format!("expected module but got {}.", token)
            }
            ParseError::ExpectedModuleElement(ref token) => {
                format!("expected top level module element, but got {}.", token)
            }
            ParseError::MisplacedAnnotation(ref modifier) => {
                format!("misplaced annotation `{}`.", modifier)
            }
            ParseError::RedundantAnnotation(ref token) => {
                format!("redundant annotation {}.", token)
            }
            ParseError::UnknownAnnotation(ref token) => format!("unknown annotation {}.", token),
            ParseError::ExpectedToken(ref exp, ref got) => {
                format!("expected {} but got {}.", exp, got)
            }
            ParseError::NumberOverflow(ref ty) => format!("number does not fit into type {}.", ty),
            ParseError::ExpectedType(ref got) => format!("type expected but got {}.", got),
            ParseError::MisplacedElse => "misplace else.".into(),
            ParseError::ExpectedFactor(ref got) => format!("factor expected but got {}.", got),
            ParseError::ExpectedIdentifier(ref tok) => {
                format!("ident expected but got {}.", tok)
            },
            ParseError::ExpectedStatement => "expected a statement.".into(),
            ParseError::ExpectedBlock => "expected a block.".into(),
        }
    }
}

#[derive(Debug)]
pub struct ParseErrorAndPos {
    pub pos: Position,
    pub error: ParseError,
}

impl ParseErrorAndPos {
    pub fn new(pos: Position, error: ParseError) -> ParseErrorAndPos {
        ParseErrorAndPos { pos, error }
    }
}
