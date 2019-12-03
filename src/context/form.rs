use crate::context::{Command, Context, TypeTable};
use crate::term::Term;

impl Context {
    pub fn well_formed(&self) -> bool {
        self.into_iter().fold(true, |r, c| r && 
        match c {
            Command::SetLogic(l) => {
                match l.as_str() {
                    "QF_UF" => true,
                    "QF_LIA" => true,
                    "QF_UFLIA" => true,
                    _ => panic!("failed at set logic"),
                }
            },
            Command::Declare(n) => {
                match self.get_decl(n) {
                    Some((asorts, rsort)) => {
                        asorts.into_iter().fold(well_formed_sort(rsort), |r, s| r && well_formed_sort(s))
                    }
                    None => panic!("failed at declare")
                }
            },
            Command::Define(n) => {
                match self.get_defn(n) {
                    Some((asorts, rsort, body)) => {
                        let mut tbl: TypeTable = TypeTable::new();
                        let mut sorts_check = well_formed_sort(rsort);
                        for (n, s) in asorts {
                            sorts_check = sorts_check && well_formed_sort(s);
                            tbl.insert(n.clone(), (vec![], s.clone()));
                        }
                        sorts_check && match well_formed_term(&tbl, body){
                            Some(s) => s == *rsort,
                            None => panic!("failed at define sorts check"),
                        }
                    }
                    None => panic!("failed at define")
                }      
            },
            Command::Assert(t) => {
                debug!("asserting {}", t);
                match well_formed_term(&self.get_symbol_table(), t) {
                    Some(s) => s == "Bool".to_owned(),
                    None => panic!("failed at assert")
                }
            },
            Command::CheckSat => true,
            Command::GetModel => true,
            Command::Push => true,
            Command::Pop => true,
        })
    }
}

fn well_formed_sort(sort: &String) -> bool {
    match sort.as_str() {
        "Bool"
        | "Int" => true,
        _ => false 
    }
}

// return the sort of the term if it is well formed, otherwise None
pub fn well_formed_term(tbl: &TypeTable, t: &Term) -> Option<String> {
    let arg_sorts: Vec<String> = t.peek_args()
    .into_iter()
    .inspect(|x| debug!("checking {}", x))
    .map(|a| well_formed_term(tbl, a)
    .expect("term not well-formed!"))
    .collect();

    match t.peek_name().as_str() {
        // boolean
        "and"
        | "or"
        | "=>"
        | "not" => {
            let result = arg_sorts.into_iter().fold(true, |r, s| r && s == "Bool".to_owned());
            if result {
                Some("Bool".to_owned())
            } else {
                None
            }
        },
        "true"
        | "false" => Some("Bool".to_owned()),
        // boolean return, integer arguments
        ">"
        | ">="
        | "<"
        | "<=" => {
            let result = arg_sorts.into_iter().fold(true, |r, s| r && s == "Int".to_owned());
            if result {
                Some("Bool".to_owned())
            } else {
                None
            }
        },
        // integer return
        "+"
        | "-"
        | "*" => {
            let result = arg_sorts.into_iter().fold(true, |r, s| r && s == "Int".to_owned());
            if result {
                Some("Int".to_owned())
            } else {
                None
            }
        }
        // polymorphic
        "=" => {
            let sort = arg_sorts[0].clone();
            let result = arg_sorts.into_iter().fold(true, |r, s| r && s == sort);
            if result {
                debug!{"= of sort {}", sort};
                Some("Bool".to_owned())
            } else {
                None
            }
        }
        "ite" => {
            let sort = arg_sorts[1].clone();
            if sort == arg_sorts[2] {
                debug!{"ite of sort {}", sort};
                Some(sort)
            } else {
                None
            }
        }
        symbol => {
            match tbl.get(symbol){
                Some((exp_asorts, exp_rsort)) => {
                    assert_eq!(exp_asorts.len(), arg_sorts.len());
                    let mut result = true;
                    for i in 0..arg_sorts.len() {
                        result = result && exp_asorts[i] == arg_sorts[i];
                    }
                    if result {
                        debug!("name: {} exp_sort: {}", symbol, exp_rsort);
                        Some(exp_rsort.clone())
                    } else {
                        None
                    }
                },
                None => match symbol.parse::<i64>() {
                    Ok(_) => {
                        debug!("symbol: {} Int", symbol); 
                        Some("Int".to_owned())
                    }
                    Err(_) => None
                }
            }
        },
    }
}

#[cfg(test)]
mod test {
    use super::Context;
    use crate::term::integer::{mk_sub};
    use crate::term::{mk_const, mk_app};

    #[test]
    fn test_well_formed() {
        let mut q = Context::new();
        q.set_logic("QF_LIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let node_n1 = mk_const("1");
        let node_1 = mk_const("1");
        let a1 = mk_app("f", vec! [mk_sub(vec![node_n1]), node_1]);
        q.assert(a1);
        println!("{}", q.well_formed());
        // assert!(q.well_formed())
    }
}