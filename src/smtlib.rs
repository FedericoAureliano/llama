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
    QFLIA,
    QFUFLIA,
}

impl Logic {
    fn to_string (&self) -> String {
        match &self {
            Logic::QFLIA => "QF_LIA".to_string(),
            Logic::QFUFLIA => "QF_UFLIA".to_string(),
        }
    }
}

pub enum Sort {
    Nary,
    Any,
    Tbd,
    Bool,
    Int,
}

impl Sort {
    fn to_string (&self) -> String {
        match &self {
            Sort::Int => "Int".to_string(),
            Sort::Bool => "Bool".to_string(),
            Sort::Nary 
            | Sort::Any 
            | Sort::Tbd => unreachable!("Nary, Any, and Tbd should never be printed"),
        }
    }
}

pub enum Command {
    SetLogic(Logic),
    Declare(String),
    Assert(NodeIndex),
    CheckSat,
    GetModel,
    Push,
    Pop,
}

impl Command {
    fn to_string (&self, q: &Query) -> String {
        match &self {
            Command::SetLogic(l) => format!("(set-logic {})", l.to_string()),
            Command::Declare(name) => {
                let (asorts, rsort) = q.st.get(name).expect("unknown symbol");
                let args : Vec<String> = asorts.into_iter().map(|s| s.to_string()).collect();
                if args.len() > 0 {
                    format!("(declare-fun {} ({}) {})", name, args.join(" "), rsort.to_string())
                } else {
                    format!("(declare-const {} {})", name, rsort.to_string())
                }
            },
            Command::Assert(a) => format!("(assert {})", q.subtree_to_string(*a)),
            Command::CheckSat => "(check-sat)".to_string(),
            Command::GetModel => "(get-model)".to_string(),
            Command::Push => "(push)".to_string(),
            Command::Pop => "(pop)".to_string(),
        }
    }
}

type AST = Graph<String, u8>;
type SymbolTable = HashMap<String, (Vec<Sort>, Sort)>;

pub struct Query {
    ast: AST,
    st: SymbolTable,
    script: Vec<Command>,
}

impl Query {
    pub fn new() -> Query {
        let solver = Query {
            ast: Graph::new(),
            st: HashMap::new(),
            script: vec! [],
        };
        solver
    }

    pub fn set_logic(&mut self, logic : Logic) {
        for c in &self.script {
            match c {
                Command::SetLogic(_) => panic!("can't set logic twice!"),
                _ => (),
            }
        }
        match logic {
            Logic::QFLIA => self.add_lia_symbols(),
            Logic::QFUFLIA => self.add_lia_symbols(),
        }
        self.script.push(Command::SetLogic(logic));
    }

    fn add_lia_symbols(&mut self) {
        self.add_bool_symbols();

        self.st.insert("+".to_string(), (vec! [Sort::Nary, Sort::Int], Sort::Int));
        self.st.insert("*".to_string(), (vec! [Sort::Nary, Sort::Int], Sort::Int));
        self.st.insert("-".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Int));
        self.st.insert("<".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool));
        self.st.insert("<=".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool));
        self.st.insert(">".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool));
        self.st.insert(">=".to_string(), (vec! [Sort::Int, Sort::Int], Sort::Bool));
    }
    
    fn add_bool_symbols(&mut self) {
        self.st.insert("and".to_string(), (vec! [Sort::Nary, Sort::Bool], Sort::Bool));
        self.st.insert("or".to_string(), (vec! [Sort::Nary, Sort::Bool], Sort::Bool));
        self.st.insert("=".to_string(), (vec! [Sort::Nary, Sort::Any], Sort::Bool));
    }

    pub fn declare_fun(&mut self, name: &str, asorts: Vec<Sort>, rsort: Sort) {
        debug!("declaring function: {}", name);
        assert!(!self.st.contains_key(name), "can't declare a function twice!");

        // TODO: Check logic for UF
        let decl = Command::Declare(name.to_string());
        self.script.push(decl);
        self.st.insert(name.to_string(), (asorts, rsort));
    }

    pub fn apply(&mut self, name: &str, args: Vec<NodeIndex>) -> NodeIndex {
        // TODO: Typechecking and inference
        let parent = self.ast.add_node(name.to_string());
        if args.len() > 0 {
            let mut count = 0;
            for child in args {
                self.ast.add_edge(parent, child, count);
                count += 1;
            }
            parent
        } else {
            if !self.st.contains_key(name) {
                self.st.insert(name.to_string(), (vec! [], Sort::Tbd));
            }
            parent
        }
    }

    pub fn assert(&mut self, node: NodeIndex) {
        // TODO: how to check if boolean?
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

    pub fn write_dot(&self, file_name: String) {
        let mut f = File::create(file_name).unwrap();
        let output = format!("{}", Dot::with_config(&self.ast, &[]));
        f.write_all(&output.as_bytes()).expect("could not write file");
    }

    fn subtree_to_string(&self, parent: NodeIndex) -> String {
        let mut children : Vec<EdgeReference<u8>> = self.ast.edges_directed(parent, EdgeDirection::Outgoing).collect();
        children.sort_by(|x, y| x.weight().cmp(y.weight()));

        assert!(self.st.contains_key(&self.ast[parent]), "unknown symbol!");

        let args : Vec<String> = children.into_iter().map(|s| self.subtree_to_string(s.target())).collect();
        format!("({} {})", self.ast[parent], args.join(" "))
    }

    pub fn to_smtlib(&self) -> String {
        let q_iter = self.script.iter();
        let q_str : Vec<String> = q_iter.map(|c| c.to_string(self)).collect();
        q_str.join("\n")
    }
}

pub fn parse_smtlib_file(file: &str) -> Result<Query, Error<Rule>> {
    use pest::iterators::Pair;
    let mut q = Query::new();
    let smtlib = SMTLIBParser::parse(Rule::query, file)?;

    fn parse_logic(pair: Pair<Rule>) -> Result<Logic, Error<Rule>> {
        match pair.as_rule() {
            Rule::logic => { 
                let l = pair.as_span().as_str();
                match l {
                    "QF_LIA" => Ok(Logic::QFLIA),
                    "QF_UFLIA" => Ok(Logic::QFUFLIA),
                    _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "unsupported logic!".to_owned(),
                    }, pair.as_span()))
            }}
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting logic!".to_owned(),
                    }, pair.as_span())),
    }}

    fn parse_sort(pair: Pair<Rule>) -> Result<Sort, Error<Rule>> {
        match pair.as_rule() {
            Rule::sort => { 
                let s = pair.as_span().as_str();
                match s {
                    "Int" => Ok(Sort::Int),
                    "Bool" => Ok(Sort::Bool),
                    _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "unsupported sort!".to_owned(),
                    }, pair.as_span()))
            }}
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting sort!".to_owned(),
                    }, pair.as_span())),
    }}

    fn parse_fapp(pair: Pair<Rule>, q : &mut Query) -> Result<NodeIndex, Error<Rule>> {
        match pair.as_rule() {
            Rule::fapp => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_span().as_str();
                let mut args : Vec<NodeIndex> = vec! [];
                for i in inner {
                    args.push(parse_fapp(i, q)?)
                }
                Ok(q.apply(func, args))
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting function application!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_query(pair: Pair<Rule>, q : &mut Query) -> Result<(), Error<Rule>>{
        match pair.as_rule() {
            Rule::setlogic => {
                let l = parse_logic(pair.into_inner().next().unwrap())?;
                q.set_logic(l);
                Ok(())
            }
            Rule::declare => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_string();

                let mut sorts = vec! []; 
                for i in inner {
                    sorts.push(parse_sort(i)?);
                }

                let rsort = sorts.pop().unwrap();
                q.declare_fun(&name, sorts, rsort);
                Ok(())
            }
            Rule::checksat => {q.check_sat(); Ok(())},
            Rule::getmodel => {q.get_model(); Ok(())},
            Rule::assert => {
                let node = parse_fapp(pair.into_inner().next().unwrap(), q)?;
                q.assert(node);
                Ok(())
            },
            Rule::push => {q.push(); Ok(())},
            Rule::pop => {q.pop(); Ok(())},
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    let mut empty = false;
    for r in smtlib {
        parse_query(r, &mut q)?;
        empty = true
    };
    
    assert!(empty, "problem with grammar: query is empty!");
    Ok(q)
}


#[test]
fn test_dot(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", vec! [], Sort::Int);
    let node_x = q.apply("x", vec! []);
    let node_7 = q.apply("7", vec! []);
    let node_gt = q.apply(">", vec! [node_x, node_7]);
    let node_lt = q.apply("<", vec! [node_x, node_7]);
    q.apply("or", vec! [node_gt, node_lt]);
    q.write_dot("tmp.dot".to_string());
}

#[test]
fn test_subtree_to_string(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", vec! [], Sort::Int);
    let node_x = q.apply("x", vec! []);
    let node_7 = q.apply("7", vec! []);
    let node_gt = q.apply(">", vec! [node_x, node_7]);
    println!("{}", q.subtree_to_string(node_gt));
}

#[test]
fn test_to_smtlib(){
    let mut q = Query::new();
    q.set_logic(Logic::QFLIA);
    q.declare_fun("x", vec! [], Sort::Int);
    let node_x = q.apply("x", vec! []);
    let node_7 = q.apply("7", vec! []);
    let a1 = q.apply(">=", vec! [node_x, node_7]);
    let a2 = q.apply("<=", vec! [node_x, node_7]);
    q.assert(a1);
    q.assert(a2);
    q.check_sat();
    q.get_model();
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
    q.write_dot("tmp.dot".to_string());
}

#[test]
fn test_uf() {
    let mut q = Query::new();
    q.set_logic(Logic::QFUFLIA);
    q.declare_fun("f", vec! [Sort::Int, Sort::Int], Sort::Bool);
    let node_n1 = q.apply("-1", vec! []);
    let node_1 = q.apply("1", vec! []);
    let a1 = q.apply("f", vec! [node_n1, node_1]);
    q.assert(a1);
    q.check_sat();
    q.get_model();
    println!("{}", q.to_smtlib());
}