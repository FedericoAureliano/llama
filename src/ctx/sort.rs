use std::fmt::Display;

#[derive(Display, PartialEq, Eq, Copy, Clone)]
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