use std::collections::{HashMap};

use pest::Parser;
use pest::error::Error;
use pest::iterators::Pair;

use crate::ast::{Term, mk_app};
use crate::ctx::{Solution};
use crate::ctx::sort::{Sort, to_sort};
use crate::qry::{Query};
use crate::rwr::rename;

#[derive(Parser)]
#[grammar = "pst/synth.pest"]
struct SynthParser;

impl Query {
    fn parse_fapp(&self, pair: Pair<Rule>) -> Result<Term, Error<Rule>> {
        match pair.as_rule() {
            Rule::fapp => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_span().as_str();
                let mut args : Vec<Term> = vec! [];
                for i in inner {
                    args.push(self.parse_fapp(i)?)
                }
                Ok(mk_app(func, args))
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting function application!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_command(&mut self, pair: Pair<Rule>) -> Result<(), Error<Rule>> {
        match pair.as_rule() {
            Rule::setlogic => {
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();
                self.set_logic(&name);
                Ok(())
            }
            Rule::declare => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();

                let mut sorts = vec! []; 
                for s in inner {
                    sorts.push(s.as_span().as_str());
                }

                let rsort = sorts.pop().unwrap();
                self.declare_fun(&name, sorts, rsort);
                Ok(())
            }
            Rule::define => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }

                let body = self.parse_fapp(defn.pop().unwrap())?;
                let rsort = defn.pop().unwrap().as_span().as_str();
                let params = defn.into_iter().map(|r| match r.as_rule() {
                    Rule::param => {
                        let mut inner = r.into_inner();
                        let name = inner.next().unwrap().as_span().as_str();
                        let sort = inner.next().unwrap().as_span().as_str();
                        (name, sort)
                    },
                    _ => panic!("must be a param rule!")
                }).collect();
                self.define_fun(&name, params, rsort, body);
                Ok(())
            }
            Rule::checksat => {self.check_sat(); Ok(())},
            Rule::getmodel => {self.get_model(); Ok(())},
            Rule::assert => {
                let node = self.parse_fapp(pair.into_inner().next().unwrap())?;
                self.assert(node);
                Ok(())
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_model(&self, pair: Pair<Rule>) -> Result<(String, (Vec<(String, Sort)>, Sort, Term)), Error<Rule>> {
        match pair.as_rule() {
            // this is slightly different from command parsing above
            // - we do not define
            // - we produce String rather than &str
            Rule::define => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }

                let body = self.parse_fapp(defn.pop().unwrap())?;
                let rsort = defn.pop().unwrap().as_span().as_str();
                let params = defn.into_iter().map(|r| match r.as_rule() {
                    Rule::param => {
                        let mut inner = r.into_inner();
                        let name = inner.next().unwrap().as_span().as_str().to_owned();
                        let sort = to_sort(inner.next().unwrap().as_span().as_str());
                        (name, sort)
                    },
                    _ => panic!("must be a param rule!")
                }).collect();
                Ok((name, (params, to_sort(rsort), body)))
            }
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    pub fn parse_query(&mut self, file: &str) -> Result<(), Error<Rule>> {
        let syntax = SynthParser::parse(Rule::query, file).expect("failed to read!");    
        let mut empty = false;
        for r in syntax {
            self.parse_command(r)?;
            empty = true
        };
        // self.well_formed();
        assert!(empty, "problem with grammar: query is empty!");
        Ok(())
    }

    pub fn parse_answer(&self, file: &str) -> Result<Solution, Error<Rule>> {
        let syntax = SynthParser::parse(Rule::query, file).expect("failed to read!");
        let mut sol = Solution::new();
        for r in syntax {
            let (name, (params, rsort, body)) = self.parse_model(r)?;
            
            let (exp_params, exp_rsort) = self.peek_ctx()
                .get_decl(name.as_str())
                .expect("definition must have been declared!")
                .first().expect("unreachable");

            assert!(exp_rsort == &rsort, "expected return sorts must be the same");
            assert!(exp_params.len() == params.len(), "paramaters must match in length");
            let mut rewrite: HashMap<String, String> = HashMap::new();
            for i in 0..params.len() {
                assert!(params[i].1 == exp_params[i].1, "paramater sorts must match");
                rewrite.insert(params[i].0.clone(), exp_params[i].0.clone());
            }
            let nbody = rename(&rewrite, body);
            sol.insert(name, nbody);
        };
        Ok(sol)
    }
}

#[cfg(test)]
mod test {
    use super::Query;

    #[test]
    fn test_parse_query() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
        assert_eq!(unparsed_file, format!("{}", q));
    }

    #[test]
    fn test_parse_answer() {
        use std::fs;
        let unparsed_file = fs::read_to_string("tests/data/qfuflia.smt2").expect("cannot read file");
        let mut q = Query::new();
        q.parse_query(&unparsed_file).unwrap();
        let unparsed_file = fs::read_to_string("tests/data/qfuflia_result.smt2").expect("cannot read file");
        let sol = q.parse_answer(&unparsed_file).unwrap();
        let x_term = sol.get("x").expect("couldn't find x");
        assert_eq!("8", format!("{}", x_term));
        let f_term = sol.get("f").expect("couldn't find f");
        assert_eq!("(- 1)", format!("{}", f_term));
    }
}