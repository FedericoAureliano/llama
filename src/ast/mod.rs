use crate::ctx::Sort;

use std::fmt;
use std::rc::Rc;

#[derive(PartialEq)]
pub enum Symbol {
    BoolLit(bool),
    IntLit(i64),
    Func(String),
    NonTerm(Sort, String),
}

impl Symbol {
    pub fn new(name: &str) -> Symbol {
        match name {
            "true" => Symbol::BoolLit(true),
            "false" => Symbol::BoolLit(false),
            _ => match name.parse::<i64>() {
                Ok(v) => Symbol::IntLit(v),
                Err(_) => Symbol::Func(name.to_owned())
            }
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printable = match self {
            Symbol::BoolLit(b) => b.to_string(),
            Symbol::IntLit(i) => i.to_string(),
            Symbol::Func(s) => s.clone(),
            Symbol::NonTerm(_, n) => format!("?{}?", n),
        };
        write!(f, "{}", printable)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub struct Term {
    symbol: Symbol,
    args: Vec<Rc<Term>>,
}

impl Term {
    pub fn new(symbol: Symbol, args: Vec<Rc<Term>>) -> Rc<Term> {
        Rc::new(Term {
            symbol: symbol,
            args: args
        })
    }

    pub fn mk_const(symbol: Symbol) -> Rc<Term> {
        Term::new(symbol, vec! [])
    }

    pub fn mk_app(symbol: Symbol, args: Vec<Rc<Term>>) -> Rc<Term> {
        Term::new(symbol, args)
    }

    pub fn get_args(&self) -> std::slice::Iter<Rc<Term>> {
        self.args.iter()
    }

    pub fn get_symbol(&self) -> &Symbol {
        &self.symbol
    }

    pub fn is_terminated(&self) -> bool {
        match self.symbol {
            Symbol::NonTerm(_, _) => false,
            _ => self.args.iter().fold(true, |acc, a| acc && a.is_terminated())
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args : Vec<String> = self.get_args().map(|s| format!("{}", s)).collect();
        if args.len() > 0 {
            write!(f, "({} {})", self.get_symbol(), args.join(" "))
        } else {
            write!(f, "{}", self.get_symbol())
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[cfg(test)]
mod test {
    use std::rc::Rc;

    use crate::qry::Query;

    #[test]
    fn simple_expr() {
        let mut q = Query::new();
        q.set_logic("QF_LIA");
        q.declare_const("x", "Int");
        q.declare_const("y", "Int");
        let x = q.mk_const("x");
        let y = q.mk_const("y");
        let plus = q.mk_add(Rc::clone(&x), Rc::clone(&y));
        assert_eq!("(+ x y)", format!("{}", plus));
    }
}