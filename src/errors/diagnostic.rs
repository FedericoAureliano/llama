use crate::errors::message::{SemError, SemErrorAndPos};
use crate::parser::lexer::position::Position;

pub struct Diagnostic {
    errors: Vec<SemErrorAndPos>,
}

impl Diagnostic {
    pub fn new() -> Diagnostic {
        Diagnostic { errors: Vec::new() }
    }

    pub fn errors(&self) -> &[SemErrorAndPos] {
        &self.errors
    }

    pub fn report(&mut self, pos: Position, msg: SemError) {
        self.errors.push(SemErrorAndPos::new(pos, msg));
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn dump(&self) {
        for err in &self.errors {
            eprintln!("{}", &err.message());
        }
    }
}
