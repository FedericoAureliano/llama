use petgraph::graph::{Graph, NodeIndex, EdgeReference};
use petgraph::EdgeDirection;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap};
use core::slice::{self};

pub mod input;
pub mod output;

pub type ASTNode = NodeIndex;
pub type Solution = HashMap<String, (Vec<(String, String)>, String, ASTNode)>;

pub enum Command {
    SetLogic(String),
    Declare(String),
    Define(String),
    Assert(ASTNode),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

pub struct Context {
    ast:    Graph<String, usize>,
    utable: HashMap<String, (Vec<String>, String)>,
    itable: Solution,
    script: Vec<Command>,
}

impl Context {
    pub fn new() -> Context {
        let solver = Context {
            ast:    Graph::new(),
            utable: HashMap::new(),
            itable: HashMap::new(),
            script: vec![],
        };
        solver
    }

    pub fn get_decl(&self, name: &String) -> &(Vec<String>, String) {
        self.utable.get(name).expect("can't find declaration!")
    }

    pub fn get_defn(&self, name: &String) -> &(Vec<(String, String)>, String, ASTNode) {
        self.itable.get(name).expect("can't find definition!")
    }

    pub fn get_args(&self, node: &ASTNode) -> Vec<ASTNode> {
        let mut children : Vec<EdgeReference<usize>> = self.ast.edges_directed(*node, EdgeDirection::Outgoing).collect();
        children.sort_by(|x, y| x.weight().cmp(y.weight()));
        children.into_iter().map(|c : EdgeReference<usize> | c.target()).collect()
    }

    pub fn get_name(&self, node: &ASTNode) -> &String {
        &self.ast[*node]
    }

    pub fn set_logic(&mut self, logic: String) {
        self.script.push(Command::SetLogic(logic));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<String>, rsort: String) {
        assert!(!self.utable.contains_key(name), "can't declare a function twice!");
        debug!("declaring {}", name);
        let decl = Command::Declare(name.to_string());
        self.script.push(decl);
        self.utable.insert(name.to_string(), (asorts, rsort));
    }

    pub fn define_fun(&mut self, name: &str, params: Vec<(String, String)>, rsort: String, body: ASTNode) {
        assert!(!self.itable.contains_key(name), "can't define a function twice!");
        debug!("defining {}", name);
        let defn = Command::Define(name.to_string());
        self.script.push(defn);
        self.itable.insert(name.to_string(), (params, rsort, body));
    }

    pub fn apply(&mut self, name: &str, args: Vec<ASTNode>) -> ASTNode {
        let parent = self.ast.add_node(name.to_string());
        let mut count = 0;
        for child in args {
            self.ast.add_edge(parent, child, count);
            count += 1;
        }
        parent
    }

    pub fn assert(&mut self, node: ASTNode) {
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

    pub fn get_interpretation(&self) -> &Solution {
        &self.itable
    }
}

impl<'a> IntoIterator for &'a Context {
    type Item = &'a Command;
    type IntoIter = slice::Iter<'a, Command>;

    fn into_iter(self) -> slice::Iter<'a, Command> {
        self.script.iter()
    }
}