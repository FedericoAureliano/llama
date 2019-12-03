use crate::ctx::{Context};
use crate::ctx::sort::{Sort};
use crate::qry::{Query, Command};

impl Query {
    pub fn well_formed(&self) -> bool {
        self.into_iter().fold(true, |r, c| r && 
        match c {
            Command::SetLogic => true,
            Command::Declare(n) => self.ctx.get_decl(n.as_str()).is_some(),
            Command::Define(n) => {
                let sigs = self.ctx.get_decl(n.as_str()).expect("definition must have unique declaration");
                for (params, rsort) in sigs {
                    let mut ctx = Context::new();
                    ctx.update_logic(self.ctx.get_logic());
                    for (n, s) in params {
                        ctx.add_decl(n.as_str(), vec![], *s);
                    }
                    let body = self.ctx.get_body(n).expect("definition must have body");
                    return rsort == ctx.get_sort(body).expect("body must be well formed")
                };
                false
            },
            Command::Assert(t) => self.ctx.get_sort(t).expect("assertion not well formed") == &Sort::Bool,
            Command::CheckSat => true,
            Command::GetModel => true,
            Command::Push => true,
            Command::Pop => true,
        })
    }
}

#[cfg(test)]
mod test {
    use super::Query;
    use crate::ast::integer::{mk_sub};
    use crate::ast::{mk_const, mk_app};

    #[test]
    fn test_well_formed() {
        let mut q = Query::new();
        q.set_logic("QF_UFLIA");
        q.declare_fun("f", vec! ["Int", "Int"], "Bool");
        let node_n1 = mk_const("1");
        let node_1 = mk_const("1");
        let a1 = mk_app("f", vec! [mk_sub(vec![node_n1]), node_1]);
        q.assert(a1);
        println!("{}", q.well_formed());
        assert!(q.well_formed())
    }
}