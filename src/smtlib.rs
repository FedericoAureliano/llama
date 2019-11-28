#![allow(dead_code)]
use petgraph::graph::{Graph, NodeIndex, EdgeReference};
use petgraph::dot::{Dot};
use petgraph::EdgeDirection;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap};

use std::fs::File;
use std::io::{Write};

use pest::Parser;
use pest::error::Error;

#[derive(Parser)]
#[grammar = "smtlib.pest"]
pub struct SMTLIBParser;

pub enum Logic {
    QFLIA
}

impl Logic {
    fn to_string (&self) -> String {
        match &self {
            Logic::QFLIA => "QF_LIA".to_string()
        }
    }
}

pub enum Sort {
    Bool,
    Int,
}

impl Sort {
    fn to_string (&self) -> String {
        match &self {
            Sort::Int => "Int".to_string(),
            Sort::Bool => "Bool".to_string()
        }
    }
}

type AST = Graph<String, u8>;
type SymbolTable = HashMap<String, (Vec<Sort>, Sort, bool)>;

pub struct Query {
    ast: AST,
    st: SymbolTable,
    logic: Option<Logic>,
    checksat : bool,
    getmodel : bool,
}

impl Query {
    pub fn new() -> Query {
        let solver = Query {
            ast: Graph::new(),
            st: HashMap::new(),
            logic: None,
            checksat: false,
            getmodel: false,
        };
        solver
    }

    pub fn set_logic(&mut self, logic : Logic) {
        match logic {
            Logic::QFLIA => self.add_lia_symbols(),
        }
        self.logic = Some(logic);
    }

    fn add_lia_symbols(&mut self) {
        self.add_bool_symbols();

        self.st.insert("+".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Int, true));
        self.st.insert("-".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Int, true));
        self.st.insert("*".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Int, true));

        self.st.insert("=".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool, true));
        self.st.insert("<".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool, true));
        self.st.insert("<=".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool, true));
        self.st.insert(">".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool, true));
        self.st.insert(">=".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool, true));
    }
    
    fn add_bool_symbols(&mut self) {
        self.st.insert("and".to_string(), (vec! [Sort::Bool, Sort::Bool], Sort::Bool, true));
        self.st.insert("or".to_string(), (vec! [Sort::Bool, Sort::Bool], Sort::Bool, true));
        self.st.insert("=".to_string(), (vec! [Sort::Bool, Sort::Bool], Sort::Bool, true));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Option<Vec<Sort>>, rsort: Sort) -> bool {
        if !self.st.contains_key(&name.to_string()) {
            self.st.insert(name.to_string(), (asorts.unwrap_or_default(), rsort, false));
            true
        } else {
            false
        }
    }

    pub fn apply(&mut self, name: &str, args: Option<Vec<NodeIndex>>) -> NodeIndex {
        let parent = self.ast.add_node(name.to_string());
        match args {
            Some(ls) => {
                let mut count = 0;
                for child in ls {
                    self.ast.add_edge(parent, child, count);
                    count += 1;
                }
                parent
            }
            None => parent,
        }
    }

    pub fn write_dot(&self, file_name: String) {
        let mut f = File::create(file_name).unwrap();
        let output = format!("{}", Dot::with_config(&self.ast, &[]));
        f.write_all(&output.as_bytes()).expect("could not write file");
    }

    fn subtree_to_string(&self, parent: NodeIndex) -> String {
        let mut children : Vec<EdgeReference<u8>> = self.ast.edges_directed(parent, EdgeDirection::Outgoing).collect();
        children.sort_by(|x, y| x.weight().cmp(y.weight()));

        if !self.st.contains_key(&self.ast[parent]) {
            // Assume that if the symbol is not in the symbol table, 
            // then it is an interpreted constant
            format!("{}", self.ast[parent])
        } else if self.st[&self.ast[parent]].0.len() == 0 {
            // Otherwise, if it has no arguments, make it a leaf
            format!("{}", self.ast[parent])
        } else {
            // If it does have arguments, recurse down into them
            let args : Vec<String> = children.into_iter().map(|s| self.subtree_to_string(s.target())).collect();
            format!("({} {})", self.ast[parent], args.join(" "))
        }
    }

    pub fn to_smtlib(&self) -> String {
        let mut decls = Vec::new();
        for (name, (asorts, rsort, interp)) in &self.st {
            if !interp {
                let args : Vec<String> = asorts.into_iter().map(|s| s.to_string()).collect();
                decls.push(format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string()));
            }
        }
        let mut assertions = Vec::new();
        for idx in self.ast.node_indices() {
            if self.ast.edges_directed(idx, EdgeDirection::Incoming).collect::<Vec<_>>().is_empty() {
                match self.st[&self.ast[idx]].1 {
                    Sort::Bool => assertions.push(format!("(assert {})", self.subtree_to_string(idx))),
                    _ => ()
                }
            }
        }

        let log = match &self.logic {Some(l) => format!("(set-logic {})\n", l.to_string()), None => "".to_string()};
        let cs = if self.checksat {"(check-sat)\n"} else {""};
        let gm = if self.getmodel {"(get-model)\n"} else {""};
        let post = format!("{}{}", cs, gm);
        format!("{}{}\n{}\n{}", log, decls.join("\n"), assertions.join("\n"), post)
    }
}

pub fn parse_smtlib_file(file: &str) -> Result<Query, Error<Rule>> {
    let mut q = Query::new();

    let smtlib = SMTLIBParser::parse(Rule::query, file).unwrap();
    use pest::iterators::Pair;

    fn parse_logic(pair: Pair<Rule>) -> Logic {
        match pair.as_rule() {
            Rule::logic => { 
                let l = pair.as_span().as_str();
                match l {
                    "QF_LIA" => Logic::QFLIA,
                    _ => unreachable!(format!("{:?}", pair))
            }}
            _ => unreachable!(format!("{:?}", pair)),
    }}

    fn parse_sort(pair: Pair<Rule>) -> Sort {
        match pair.as_rule() {
            Rule::sort => { 
                let s = pair.as_span().as_str();
                match s {
                    "Int" => Sort::Int,
                    "Bool" => Sort::Bool,
                    _ => unreachable!(format!("{:?}", pair)),
            }}
            _ => unreachable!(format!("{:?}", pair)),
    }}

    fn parse_fapp(pair: Pair<Rule>, q : &mut Query) -> NodeIndex {
        match pair.as_rule() {
            Rule::fapp => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_span().as_str();
                let mut args : Vec<NodeIndex> = vec!();
                for i in inner {
                    args.push(parse_fapp(i, q))
                }
                if args.len() > 0 {
                    q.apply(func, Some(args))
                } else {
                    q.apply(func, None)
                }
            },
            _ => unreachable!(format!("{:?}", pair)),
        }
    }

    fn parse_query(pair: Pair<Rule>, q : &mut Query) {
        match pair.as_rule() {
            Rule::setlogic => {
                let l = parse_logic(pair.into_inner().next().unwrap());
                q.set_logic(l);
            }
            Rule::declare => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_string();

                let mut sorts = vec!(); 
                for i in inner {
                    sorts.push(parse_sort(i));
                }

                let rsort = sorts.pop().unwrap();
                let asorts = if sorts.len() > 0 {
                    Some(sorts)
                } else {
                    None
                };
                q.declare_fun(&name, asorts, rsort);
            }
            Rule::checksat => q.checksat = true,
            Rule::getmodel => q.getmodel = true,
            Rule::assert => {
                parse_fapp(pair.into_inner().next().unwrap(), q);
            },
            _ => unreachable!(format!("{:?}", pair)),
    }}
    for r in smtlib {
        parse_query(r, &mut q);
    }
    Ok(q)
}


#[test]
fn test_dot(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", None, Sort::Int);
    let node_x = q.apply("x", None);
    let node_7 = q.apply("7", None);
    let node_gt = q.apply(">", Some(vec! [node_x, node_7]));
    let node_lt = q.apply("<", Some(vec! [node_x, node_7]));
    q.apply("or", Some(vec! [node_gt, node_lt]));
    q.write_dot("example.dot".to_string());
}

#[test]
fn test_subtree_to_string(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", None, Sort::Int);
    let node_x = q.apply("x", None);
    let node_7 = q.apply("7", None);
    let node_gt = q.apply(">", Some(vec! [node_x, node_7]));
    println!("{}", q.subtree_to_string(node_gt));
}

#[test]
fn test_to_smtlib(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", None, Sort::Int);
    let node_x = q.apply("x", None);
    let node_7 = q.apply("7", None);
    q.apply(">=", Some(vec! [node_x, node_7]));
    q.apply("<=", Some(vec! [node_x, node_7]));
    q.checksat = true;
    q.getmodel = true;
    println!("{}", q.to_smtlib());
}

#[test]
fn test_read() {
    use std::fs;
    let unparsed_file = fs::read_to_string("examples/qflia.smt2").expect("cannot read file");
    let q = SMTLIBParser::parse(Rule::query, &unparsed_file);
    println!("{:?}", q.unwrap());
}

#[test]
fn test_parse() {
    use std::fs;
    let unparsed_file = fs::read_to_string("examples/qflia.smt2").expect("cannot read file");
    let q = parse_smtlib_file(&unparsed_file).unwrap();
    q.write_dot("example.dot".to_string());
}
