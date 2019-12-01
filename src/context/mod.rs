use std::collections::{HashMap};
use core::slice::{self};

pub mod input;
pub mod output;

use crate::term::{Term, TermManager};

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
    pub tm:    TermManager,
    decls:     HashMap<String, (Vec<String>, String)>,
    pub defns: Solution,
    script:    Vec<Command>,
}

impl Context {
    pub fn new() -> Context {
        let context = Context {
            tm:     TermManager::new(),
            decls:  HashMap::new(),
            defns:  Solution::new(),
            script: vec![],
        };
        context
    }

    pub fn get_declaration(&self, name: &String) -> &(Vec<String>, String) {
        self.decls.get(name).expect("can't find declaration!")
    }

    pub fn get_definition(&self, name: &String) -> &(Vec<(String, String)>, String, Term) {
        self.defns.get(name).expect("can't find definition!")
    }

    pub fn get_sort(&self, t: &Term) -> &String {
        let (_, s) = self.get_declaration(self.tm.get_name(t));
        s
    }

    pub fn set_logic(&mut self, logic: String) {
        self.script.push(Command::SetLogic(logic));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<String>, rsort: String) {
        assert!(!self.decls.contains_key(name), "can't declare a function twice!");
        debug!("declaring {}", name);
        let decl = Command::Declare(name.to_string());
        self.script.push(decl);
        self.decls.insert(name.to_string(), (asorts, rsort));
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(String, String)>, rsort: String, body: Term) {
        assert!(!self.defns.contains_key(name), "can't define a function twice!");
        debug!("defining {}", name);
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

impl Clone for Context {
    //TODO: there must be a better way to do this
    fn clone(&self) -> Context {
        let mut output = Context::new();
        output.tm = self.tm.clone();
        for command in self {
            match command {
                Command::SetLogic(l) => output.set_logic(l.clone()),
                Command::Declare(name) => {
                    let (asorts, rsort) = self.get_declaration(&name);
                    output.declare_fun(name, asorts.clone(), rsort.clone())
                },
                Command::Define(name) => {
                    let (params, rsort, body) = self.get_definition(&name);
                    output.define_fun(name, params.clone(), rsort.clone(), body.clone())
                },
                Command::Assert(a) => {
                    output.assert(a.clone())
                },
                Command::CheckSat => output.check_sat(),
                Command::GetModel => output.get_model(),
                Command::Push => output.push(),
                Command::Pop => output.pop(),
            }
        }
        output
    }
}