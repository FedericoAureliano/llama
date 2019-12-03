use std::collections::{HashMap};
use core::slice::{self};

pub mod input;
pub mod output;
pub mod form;

use crate::term::Term;

pub type Solution = HashMap<String, (Vec<(String, String)>, String, Term)>;
pub type TypeTable = HashMap<String, (Vec<String>, String)>;

pub enum Command {
    SetLogic(String),
    Declare(String),
    Define(String),
    Assert(Term),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

pub struct Context {
    decls: TypeTable,
    defns: Solution,
    script: Vec<Command>,
    logic: Option<String>,
}

impl Context {
    pub fn new() -> Context {
        let context = Context {
            decls:  HashMap::new(),
            defns:  Solution::new(),
            script: vec![],
            logic: None,
        };
        context
    }

    pub fn get_decl(&self, name: &String) -> Option<&(Vec<String>, String)> {
        self.decls.get(name)
    }

    pub fn get_defn(&self, name: &String) -> Option<&(Vec<(String, String)>, String, Term)> {
        self.defns.get(name)
    }

    // TODO: don't create a new table
    pub fn get_symbol_table(&self) -> TypeTable {
        let mut tbl = TypeTable::new();
        for (f, (params, rsort, _)) in &self.defns {
            tbl.insert(f.clone(), (params.into_iter().map(|(_, s)| s.clone()).collect(), rsort.clone()));
        }
        for (f, (asorts, rsort)) in &self.decls {
            tbl.insert(f.clone(), (asorts.clone(), rsort.clone()));
        }
        tbl
    }

    pub fn get_sort(&self, t: &Term) -> Option<&String> {
        match self.get_decl(t.peek_name()) {
            Some((_, s)) => Some(s),
            None => None,
        }
    }

    pub fn set_logic(&mut self, logic: &str) {
        self.logic = Some(logic.to_owned());
        self.script.push(Command::SetLogic(logic.to_owned()));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<&str>, rsort: &str) {
        assert!(!self.decls.contains_key(name), "can't declare a function twice!");
        let decl = Command::Declare(name.to_owned());
        self.script.push(decl);
        self.decls.insert(name.to_owned(), (asorts.into_iter().map(|s| s.to_owned()).collect(), rsort.to_owned()));
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(&str, &str)>, rsort: &str, body: Term) {
        assert!(!self.defns.contains_key(name), "can't define a function twice!");
        let defn = Command::Define(name.to_owned());
        self.script.push(defn);
        self.defns.insert(name.to_owned(), (params.into_iter().map(|(n, s)| (n.to_owned(), s.to_owned())).collect(), rsort.to_owned(), body));
    }

    pub fn assert(&mut self, node: Term) {
        self.script.push(Command::Assert(node));
    }

    pub fn push(&mut self) {
        self.script.push(Command::Push);
    }

    pub fn pop(&mut self) {
        self.script.push(Command::Pop);
    }

    pub fn check_sat(&mut self) {
        self.script.push(Command::CheckSat);
    }

    pub fn get_model(&mut self) {
        self.script.push(Command::GetModel);
    }

}

impl<'a> IntoIterator for &'a Context {
    type Item = &'a Command;
    type IntoIter = slice::Iter<'a, Command>;

    fn into_iter(self) -> slice::Iter<'a, Command> {
        self.script.iter()
    }
}