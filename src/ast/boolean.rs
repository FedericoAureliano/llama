use crate::ast::Term;

#[allow(dead_code)]
pub fn mk_false() -> Term {
    Term { 
        name: "false".to_owned(), 
        args: vec![],
    }
}

#[allow(dead_code)]
pub fn mk_true() -> Term {
    Term { 
        name: "true".to_owned(), 
        args: vec![],
    }
}

#[allow(dead_code)]
pub fn mk_iff(args: Vec<Term>) -> Term {
    Term { 
        name: "=b".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_or(args: Vec<Term>) -> Term {
    Term { 
        name: "or".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_and(args: Vec<Term>) -> Term {
    Term { 
        name: "and".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_if(args: Vec<Term>) -> Term {
    assert_eq!(args.len(), 2);
    Term { 
        name: "=>".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_ite(args: Vec<Term>) -> Term {
    assert_eq!(args.len(), 3);
    Term { 
        name: "iteb".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}