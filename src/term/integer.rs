use crate::term::Term;

#[allow(dead_code)]
pub fn mk_eq(args: Vec<Term>) -> Term {
    Term { 
        name: "=i".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_lt(args: Vec<Term>) -> Term {
    Term { 
        name: "<".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_le(args: Vec<Term>) -> Term {
    Term { 
        name: "<=".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_gt(args: Vec<Term>) -> Term {
    Term { 
        name: ">".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}


#[allow(dead_code)]
pub fn mk_ge(args: Vec<Term>) -> Term {
    Term { 
        name: ">=".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}


#[allow(dead_code)]
pub fn mk_add(args: Vec<Term>) -> Term {
    Term { 
        name: "+".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}


#[allow(dead_code)]
pub fn mk_mult(args: Vec<Term>) -> Term {
    Term { 
        name: "*".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_sub(args: Vec<Term>) -> Term {
    Term { 
        name: "-".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}

#[allow(dead_code)]
pub fn mk_ite(args: Vec<Term>) -> Term {
    assert_eq!(args.len(), 3);
    Term { 
        name: "itei".to_owned(), 
        args: args.into_iter().map(|t| Box::new(t)).collect(),
    }
}