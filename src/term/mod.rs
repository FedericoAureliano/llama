use petgraph::graph::{Graph, NodeIndex, EdgeReference};
use petgraph::EdgeDirection;
use petgraph::visit::EdgeRef;

pub type Term = NodeIndex;

pub struct TermManager {
    ast: Graph<String, usize>,
}

impl TermManager {
    pub fn new() -> TermManager {
        let tm = TermManager {
            ast: Graph::new(),
        };
        tm
    }

    pub fn get_args(&self, node: &Term) -> Vec<Term> {
        let mut children : Vec<EdgeReference<usize>> = self.ast.edges_directed(*node, EdgeDirection::Outgoing).collect();
        children.sort_by(|x, y| x.weight().cmp(y.weight()));
        children.into_iter().map(|c : EdgeReference<usize> | c.target()).collect()
    }

    pub fn get_name(&self, node: &Term) -> &String {
        debug!("looking for {}", node.index());
        &self.ast[*node]
    }

    pub fn apply(&mut self, name: &str, args: Vec<Term>) -> Term {
        let parent = self.ast.add_node(name.to_string());
        debug!("creating node with label {} at {}", name, parent.index());
        let mut count = 0;
        for child in args {
            self.ast.add_edge(parent, child, count);
            count += 1;
        }
        parent
    }

    pub(crate) fn set_ast(&mut self, ast: Graph<String, usize>) {
        self.ast = ast;
    }
}

impl Clone for TermManager {
    fn clone(&self) -> TermManager {
        let mut output = TermManager::new();
        output.set_ast(self.ast.clone());
        output
    }
}