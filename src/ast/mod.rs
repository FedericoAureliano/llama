use std::fmt;
use std::rc::Rc;

pub struct Node {
    symbol: String,
    args: Vec<Term>,
}

pub type Term = Rc<Node>;

impl Node {
    pub fn new(symbol: String, args: Vec<Term>) -> Node {
        Node {
            symbol: symbol,
            args: args
        }
    }

    pub fn get_args(&self) -> std::slice::Iter<Term> {
        self.args.iter()
    }

    pub fn get_symbol(&self) -> &String {
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

#[cfg(test)]
mod test {
    use crate::api::{mk_const, mk_add};

    #[test]
    fn simple_expr() {
        let x = mk_const("x");
        let y = mk_const("y");
        let plus = mk_add(x, y);
        assert_eq!("(+ x y)", format!("{}", plus));
    }
}