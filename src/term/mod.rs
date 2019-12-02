use std::fmt;

pub mod boolean;
pub mod integer;

pub struct Term {
    name: String,
    args: Vec<Box<Term>>,
}

impl Term {
    pub fn peek_args(&self) -> &Vec<Box<Term>> {
        self.args.as_ref()
    }

    pub fn peek_name(&self) -> &String {
        &self.name
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let children = self.peek_args();
        let args : Vec<String> = children.into_iter().map(|s| format!("{}", s)).collect();
        if args.len() > 0 {
            write!(f, "({} {})", self.peek_name(), args.join(" "))
        } else {
            write!(f, "{}", self.peek_name())
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn mk_app(name: &str, args: Vec<Term>) -> Term {
    Term { 
        name: name.to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_const(name: &str) -> Term {
    Term { 
        name: name.to_owned(), 
        args: vec![],
    }
}

#[cfg(test)]
mod test {
    use super::{mk_const};
    use crate::term::integer::mk_add;

    #[test]
    fn simple_expr() {
        let x = mk_const("x");
        let y = mk_const("y");
        let plus = mk_add(vec![x, y]);
        assert_eq!("(+ x y)", format!("{}", plus));
    }
}