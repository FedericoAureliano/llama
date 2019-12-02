use std::collections::{HashMap};
use core::slice::{self};

pub mod input;
pub mod output;

use crate::term::Term;

pub type Solution = HashMap<String, (Vec<(String, String)>, String, Term)>;

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
    decls: HashMap<String, (Vec<String>, String)>,
    defns: Solution,
    script: Vec<Command>,
}

impl Context {
    pub fn new() -> Context {
        let context = Context {
            decls:  HashMap::new(),
            defns:  Solution::new(),
            script: vec![],
        };
        context
    }

    pub fn has_decl(&self, name: &String) -> bool {
        self.decls.contains_key(name)
    }

    pub fn get_decl(&self, name: &String) -> &(Vec<String>, String) {
        self.decls.get(name).expect("can't find declaration!")
    }

    pub fn has_defn(&self, name: &String) -> bool {
        self.defns.contains_key(name)
    }

    pub fn get_defn(&self, name: &String) -> &(Vec<(String, String)>, String, Term) {
        self.defns.get(name).expect("can't find definition!")
    }

    pub fn get_sort(&self, t: &Term) -> &String {
        let (_, s) = self.get_decl(t.peek_name());
        s
    }

    pub fn set_logic(&mut self, logic: String) {
        self.script.push(Command::SetLogic(logic));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<String>, rsort: String) {
        assert!(!self.decls.contains_key(name), "can't declare a function twice!");
        let decl = Command::Declare(name.to_string());
        self.script.push(decl);
        self.decls.insert(name.to_string(), (asorts, rsort));
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(String, String)>, rsort: String, body: Term) {
        assert!(!self.defns.contains_key(name), "can't define a function twice!");
        let defn = Command::Define(name.to_string());
        self.script.push(defn);
        self.defns.insert(name.to_string(), (params, rsort, body));
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