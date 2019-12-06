use std::fmt;
use std::rc::Rc;

#[derive(PartialEq)]
pub enum Symbol {
    Name(String),
    BoolLit(bool),
    BoolNT(String),
    IntLit(i64),
    IntNT(String),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printable = match self {
            Symbol::Name(s) => s.clone(),
            Symbol::BoolLit(b) => b.to_string(),
            Symbol::BoolNT(s) => format!("?b?{}", s),
            Symbol::IntLit(i) => i.to_string(),
            Symbol::IntNT(s) => format!("?i?{}", s),
        };
        write!(f, "{}", printable)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub struct Node {
    symbol: Symbol,
    args: Vec<Term>,
}

pub type Term = Rc<Node>;

impl Node {
    pub fn new(symbol: Symbol, args: Vec<Term>) -> Node {
        Node {
            symbol: symbol,
            args: args
        }
    }

    pub fn get_args(&self) -> std::slice::Iter<Term> {
        self.args.iter()
    }

    pub fn get_symbol(&self) -> &Symbol {
        &self.symbol
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args : Vec<String> = self.get_args().map(|s| format!("{}", s)).collect();
        if args.len() > 0 {
            write!(f, "({} {})", self.get_symbol(), args.join(" "))
        } else {
            write!(f, "{}", self.get_symbol())
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn mk_const_from_symbol(symbol: Symbol) -> Term {
Term::new(Node:: new(
        symbol, 
        vec! []
    ))
}

pub fn mk_app_from_symbol(symbol: Symbol, args: Vec<Term>) -> Term {
Term::new(Node:: new(
        symbol, 
        args
    ))
}

#[cfg(test)]
mod test {
    use crate::qry::Query;

    #[test]
    fn simple_expr() {
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_const("x", "Int");
        q.declare_const("y", "Int");
        let x = q.mk_const("x");
        let y = q.mk_const("y");
        let plus = q.mk_add(x, y);
        assert_eq!("(+ x y)", format!("{}", plus));
    }
}


pub fn symbol_from_str(name: &str) -> Symbol {
    match name {
        "true" => Symbol::BoolLit(true),
        "false" => Symbol::BoolLit(false),
        _ => match name.parse::<i64>() {
            Ok(v) => Symbol::IntLit(v),
            Err(_) => Symbol::Name(name.to_owned())
        }
    }
}