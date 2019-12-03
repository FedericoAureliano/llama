use core::slice::{self};

use crate::term::Term;
use crate::context::Context;
use crate::context::logic::Logic;
use crate::context::sort::{Sort, to_sort};

pub mod input;
pub mod output;
pub mod form;

pub enum Command {
    SetLogic,
    Declare(String),
    Define(String),
    Assert(Term),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

pub struct Query {
    script: Vec<Command>,
    ctx: Context,
}

impl Query {
    pub fn new() -> Query {
        let query = Query {
            script: vec![],
            ctx: Context::new(),
        };
        query
    }

    pub fn peek_ctx(&self) -> &Context {
        &self.ctx
    }

    pub fn set_logic(&mut self, logic: &str) {
        let l = Logic::to_logic(logic);
        self.ctx.set_logic(&l);
        self.script.push(Command::SetLogic);
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<&str>, rsort: &str) {
        let params: Vec<(String, Sort)> = asorts
            .into_iter()
            .map(|s| ("_".to_owned(), to_sort(s)))
            .collect();
        self.ctx.add_decl(name, params, to_sort(rsort));
        self.script.push(Command::Declare(name.to_owned()));
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(&str, &str)>, rsort: &str, body: Term) {
        let params: Vec<(String, Sort)> = params
            .into_iter()
            .map(|(n, s)| (n.to_owned(), to_sort(s)))
            .collect();
        self.ctx.add_decl(name, params, to_sort(rsort));
        self.ctx.add_body(name, body);
        self.script.push(Command::Define(name.to_owned()));
    }

    pub fn assert(&mut self, node: Term) {
        self.script.push(Command::Assert(node));
    }

    pub fn check_sat(&mut self) {
        self.script.push(Command::CheckSat);
    }

    pub fn get_model(&mut self) {
        self.script.push(Command::GetModel);
    }

}

impl<'a> IntoIterator for &'a Query {
    type Item = &'a Command;
    type IntoIter = slice::Iter<'a, Command>;

    fn into_iter(self) -> slice::Iter<'a, Command> {
        self.script.iter()
    }
}