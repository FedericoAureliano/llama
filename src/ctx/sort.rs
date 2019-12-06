use std::fmt;

#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Sort {
    Bool,
    Int,
}

pub fn to_sort(s: &str) -> Sort {
    match s {
        "Bool" => Sort::Bool,
        "Int" => Sort::Int,
        _ => panic!(format!("sort {} not supported", s))
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printable = match *self {
            Sort::Bool => "Bool",
            Sort::Int => "Int",
        };
        write!(f, "{}", printable)
    }
}