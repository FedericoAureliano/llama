use petgraph::graph::{Graph, NodeIndex, EdgeReference};
use petgraph::EdgeDirection;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap};
use core::slice::{self};

pub mod input;
pub mod output;

pub type ASTNode = NodeIndex;

pub enum Command {
    SetLogic(String),
    Declare(String),
    Assert(ASTNode),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

pub struct Query {
    ast:    Graph<String, usize>,
    utable: HashMap<String, (Vec<String>, String)>,
    script: Vec<Command>,
}

impl Query {
    pub fn new() -> Query {
        let solver = Query {
            ast   : Graph::new(),
            utable: HashMap::new(),
            script: vec![],
        };
        solver
    }

    pub fn get_signature(&self, name: &String) -> &(Vec<String>, String) {
        self.utable.get(name).expect("unknown symbol!")
    }

    pub fn get_args(&self, node: &ASTNode) -> Vec<ASTNode> {
        let mut children : Vec<EdgeReference<usize>> = self.ast.edges_directed(*node, EdgeDirection::Outgoing).collect();
        children.sort_by(|x, y| x.weight().cmp(y.weight()));
        children.into_iter().map(|c : EdgeReference<usize> | c.target()).collect()
    }

    pub fn get_name(&self, node: &ASTNode) -> &String {
        &self.ast[*node]
    }

    pub fn get_script_len(&self) -> usize {
        self.script.len()
    }

    pub fn get_command(&self, n: usize) -> &Command {
        &self.script[n]
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
}

impl<'a> IntoIterator for &'a Query {
    type Item = &'a Command;
    type IntoIter = slice::Iter<'a, Command>;

    fn into_iter(self) -> slice::Iter<'a, Command> {
        self.script.iter()
    }
}