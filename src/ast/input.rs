use pest::Parser;
use pest::error::Error;

use crate::ast::Query;
use crate::ast::ASTNode;

#[derive(Parser)]
#[grammar = "pest/synth.pest"]
struct SynthParser;

pub fn parse_synth_file(file: &str) -> Result<Query, Error<Rule>> {
    use pest::iterators::Pair;
    let mut q = Query::new();
    // TODO: why does this fail silently?
    let smtlib = SynthParser::parse(Rule::query, file).expect("failed to read!");

    fn parse_fapp(pair: Pair<Rule>, q : &mut Query) -> Result<ASTNode, Error<Rule>> {
        match pair.as_rule() {
            Rule::fapp => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_span().as_str();
                let mut args : Vec<ASTNode> = vec! [];
                for i in inner {
                    args.push(parse_fapp(i, q)?)
                }
                Ok(q.apply(func, args))
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting function application!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_param(pair: Pair<Rule>) -> Result<((String, String)), Error<Rule>> {
        match pair.as_rule() {
            Rule::param => {
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();
                let sort = inner.next().unwrap().as_span().as_str().to_owned();
                Ok((name, sort))
            },
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "expecting function application!".to_owned(),
                    }, pair.as_span())),
        }
    }

    fn parse_query(pair: Pair<Rule>, q : &mut Query) -> Result<(), Error<Rule>>{
        match pair.as_rule() {
            Rule::setlogic => {
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();
                q.set_logic(name);
                Ok(())
            }
            Rule::declare => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();

                let mut sorts = vec! []; 
                for s in inner {
                    sorts.push(s.as_span().as_str().to_owned());
                }

                let rsort = sorts.pop().unwrap();
                q.declare_fun(&name, sorts, rsort);
                Ok(())
            }
            Rule::define => { 
                let mut inner = pair.into_inner();
                let name = inner.next().unwrap().as_span().as_str().to_owned();

                let mut defn = vec! []; 
                for s in inner {
                    defn.push(s);
                }

                let body = parse_fapp(defn.pop().unwrap(), q)?;
                let rsort = defn.pop().unwrap().as_span().as_str().to_owned();
                let params = defn.into_iter().map(|r| parse_param(r).expect("something wrong with parameter pair")).collect();
                q.define_fun(&name, params, rsort, body);
                Ok(())
            }
            Rule::checksat => {q.check_sat(); Ok(())},
            Rule::getmodel => {q.get_model(); Ok(())},
            Rule::assert => {
                let node = parse_fapp(pair.into_inner().next().unwrap(), q)?;
                q.assert(node);
                Ok(())
            },
            Rule::push => {q.push(); Ok(())},
            Rule::pop => {q.pop(); Ok(())},
            _ => Err(Error::new_from_span(pest::error::ErrorVariant::CustomError{
                        message: "command not supported!".to_owned(),
                    }, pair.as_span())),
        }
    }

    let mut empty = false;
    for r in smtlib {
        parse_query(r, &mut q)?;
        empty = true
    };
    
    assert!(empty, "problem with grammar: query is empty!");
    Ok(q)
}

#[test]
fn test_read() {
    use std::fs;
    let unparsed_file = fs::read_to_string("examples/qfuflia.smt2").expect("cannot read file");
    let q = SynthParser::parse(Rule::query, &unparsed_file);
    println!("{:?}", q.unwrap());
}

#[test]
fn test_parse() {
    use std::fs;
    let unparsed_file = fs::read_to_string("examples/qfuflia.smt2").expect("cannot read file");
    let q = parse_synth_file(&unparsed_file).unwrap();
    assert_eq!(unparsed_file, format!("{}", q));
}