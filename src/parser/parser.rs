use std::cell::RefCell;
use std::mem;

use crate::parser::ast;
use crate::parser::ast::Elem::*;
use crate::parser::ast::*;
use crate::parser::error::{ParseError, ParseErrorAndPos};

use crate::parser::interner::*;

use crate::parser::lexer::position::{Position, Span};
use crate::parser::lexer::reader::Reader;
use crate::parser::lexer::token::*;
use crate::parser::lexer::File as LexerFile;
use crate::parser::lexer::*;

pub struct Parser<'a> {
    lexer: Lexer,
    token: Token,
    id_generator: &'a NodeIdGenerator,
    interner: &'a mut Interner,
    ast: &'a mut Ast,
    param_idx: u32,
    in_class_or_module: bool,
    parse_struct_lit: bool,
    last_end: Option<u32>,
}

type ExprResult = Result<Box<Expr>, ParseErrorAndPos>;
type StmtResult = Result<Box<Stmt>, ParseErrorAndPos>;
type StmtOrExprResult = Result<StmtOrExpr, ParseErrorAndPos>;

enum StmtOrExpr {
    Stmt(Box<Stmt>),
    Expr(Box<Expr>),
}

impl<'a> Parser<'a> {
    pub fn new(
        reader: Reader,
        id_generator: &'a NodeIdGenerator,
        ast: &'a mut Ast,
        interner: &'a mut Interner,
    ) -> Parser<'a> {
        let token = Token::new(TokenKind::End, Position::new(1, 1), Span::invalid());
        let lexer = Lexer::new(reader);

        let parser = Parser {
            lexer,
            token,
            id_generator,
            interner,
            param_idx: 0,
            in_class_or_module: false,
            parse_struct_lit: true,
            ast,
            last_end: Some(0),
        };

        parser
    }

    fn generate_id(&mut self) -> NodeId {
        self.id_generator.next()
    }

    pub fn parse(mut self) -> Result<LexerFile, ParseErrorAndPos> {
        self.init()?;
        let mut elements = vec![];

        while !self.token.is_eof() {
            self.parse_top_level_element(&mut elements)?;
        }

        let file = self.lexer.file();

        self.ast.files.push(ast::File {
            path: file.name.clone(),
            elements,
        });

        Ok(file)
    }

    fn init(&mut self) -> Result<(), ParseErrorAndPos> {
        self.advance_token()?;

        Ok(())
    }

    fn parse_top_level_element(
        &mut self,
        elements: &mut Vec<Elem>,
    ) -> Result<(), ParseErrorAndPos> {
        let modifiers = self.parse_annotations()?;

        match self.token.kind {
            TokenKind::Module => {
                self.ban_modifiers(&modifiers)?;
                let module = self.parse_module()?;
                elements.push(ElemModule(module));
            }

            _ => {
                let msg = ParseError::ExpectedTopLevelElement(self.token.name());
                return Err(ParseErrorAndPos::new(self.token.position, msg));
            }
        }

        Ok(())
    }

    fn parse_enum(&mut self) -> Result<Enum, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Enum)?.position;
        let name = self.expect_identifier()?;

        self.expect_token(TokenKind::LBrace)?;
        let values = self.parse_comma_list(TokenKind::RBrace, |p| p.parse_identifier())?;
        let span = self.span_from(start);

        Ok(Enum {
            id: self.generate_id(),
            pos,
            span,
            name,
            values,
        })
    }

    fn parse_const(&mut self) -> Result<Constant, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Const)?.position;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.expect_token(TokenKind::Eq)?;
        let expr = self.parse_expression()?;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Constant {
            id: self.generate_id(),
            pos,
            span,
            name,
            data_type: ty,
            expr,
        })
    }

    fn parse_module(&mut self) -> Result<Module, ParseErrorAndPos> {
        let pos = self.expect_token(TokenKind::Module)?.position;
        let ident = self.expect_identifier()?;
        let mut module = Module {
            id: self.generate_id(),
            name: ident,
            pos: pos,
            inputs: Vec::new(),
            variables: Vec::new(),
            constants: Vec::new(),
            enums: Vec::new(),
            functions: Vec::new(),
            procedures: Vec::new(),
            invariants: Vec::new(),
            init: None,
            next: None,
            control: None,
        };

        self.in_class_or_module = true;
        self.parse_module_body(&mut module)?;
        self.in_class_or_module = false;

        Ok(module)
    }

    fn parse_type_params(&mut self) -> Result<Option<Vec<TypeParam>>, ParseErrorAndPos> {
        if self.token.is(TokenKind::LBracket) {
            self.advance_token()?;
            let params = self.parse_comma_list(TokenKind::RBracket, |p| p.parse_type_param())?;

            Ok(Some(params))
        } else {
            Ok(None)
        }
    }

    fn parse_type_param(&mut self) -> Result<TypeParam, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        let name = self.expect_identifier()?;

        let bounds = if self.token.is(TokenKind::Colon) {
            self.advance_token()?;

            let mut bounds = Vec::new();

            loop {
                bounds.push(self.parse_type()?);

                if self.token.is(TokenKind::Add) {
                    self.advance_token()?;
                } else {
                    break;
                }
            }

            bounds
        } else {
            Vec::new()
        };

        let span = self.span_from(start);

        Ok(TypeParam {
            name,
            span,
            pos,
            bounds,
        })
    }

    fn parse_module_body(&mut self, module: &mut Module) -> Result<(), ParseErrorAndPos> {
        if !self.token.is(TokenKind::LBrace) {
            return Ok(());
        }

        self.advance_token()?;

        while !self.token.is(TokenKind::RBrace) {
            let modifiers = self.parse_annotations()?;

            match self.token.kind {
                TokenKind::Input => {
                    self.ban_modifiers(&modifiers)?;

                    let field = self.parse_field()?;
                    module.inputs.push(field);
                }

                TokenKind::Var => {
                    self.ban_modifiers(&modifiers)?;

                    let field = self.parse_field()?;
                    module.variables.push(field);
                }

                TokenKind::Const => {
                    self.ban_modifiers(&modifiers)?;
                    let xconst = self.parse_const()?;
                    module.constants.push(xconst);
                }
    
                TokenKind::Enum => {
                    self.ban_modifiers(&modifiers)?;
                    let xenum = self.parse_enum()?;
                    module.enums.push(xenum);
                }

                TokenKind::Function => {
                    let mods = &[
                        Modifier::Synthesis,
                    ];
                    self.restrict_modifiers(&modifiers, mods)?;

                    let fct = self.parse_function(&modifiers)?;
                    module.functions.push(fct);
                }

                TokenKind::Procedure => {
                    let mods = &[
                    ];
                    self.restrict_modifiers(&modifiers, mods)?;

                    let fct = self.parse_procedure(&modifiers)?;
                    module.procedures.push(fct);
                }

                TokenKind::Invariant => {
                    self.ban_modifiers(&modifiers)?;

                    let spec = self.parse_invariant()?;
                    module.invariants.push(spec);
                }

                TokenKind::Init => {
                    self.ban_modifiers(&modifiers)?;

                    let block = self.parse_init()?;
                    module.init = Some(Box::new(block));
                }

                TokenKind::Next => {
                    self.ban_modifiers(&modifiers)?;

                    let block = self.parse_next()?;
                    module.next = Some(Box::new(block));
                }

                TokenKind::Control => {
                    self.ban_modifiers(&modifiers)?;

                    let block = self.parse_control()?;
                    module.control = Some(Box::new(block));
                }

                _ => {
                    return Err(ParseErrorAndPos::new(
                        self.token.position,
                        ParseError::ExpectedModuleElement(self.token.name()),
                    ))
                },
            }
        }

        self.advance_token()?;
        Ok(())
    }

    fn parse_annotations(&mut self) -> Result<Modifiers, ParseErrorAndPos> {
        let mut modifiers = Modifiers::new();
        loop {
            if !self.token.is(TokenKind::At) {
                break;
            }
            self.advance_token()?;
            let ident = self.expect_identifier()?;
            let modifier = match self.interner.str(ident).as_str() {
                "synthesis" => Modifier::Synthesis,
                _ => {
                    return Err(ParseErrorAndPos::new(
                        self.token.position,
                        ParseError::UnknownAnnotation(self.token.to_string()),
                    ));
                }
            };

            if modifiers.contains(modifier) {
                return Err(ParseErrorAndPos::new(
                    self.token.position,
                    ParseError::RedundantAnnotation(self.token.name()),
                ));
            }

            modifiers.add(modifier, self.token.position, self.token.span);
        }

        Ok(modifiers)
    }

    fn ban_modifiers(&mut self, modifiers: &Modifiers) -> Result<(), ParseErrorAndPos> {
        self.restrict_modifiers(modifiers, &[])
    }

    fn restrict_modifiers(
        &mut self,
        modifiers: &Modifiers,
        restrict: &[Modifier],
    ) -> Result<(), ParseErrorAndPos> {
        for modifier in modifiers.iter() {
            if !restrict.contains(&modifier.value) {
                return Err(ParseErrorAndPos::new(
                    modifier.pos,
                    ParseError::MisplacedAnnotation(modifier.value.name().into()),
                ));
            }
        }

        Ok(())
    }

    fn parse_field(&mut self) -> Result<Field, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        let reassignable = if self.token.is(TokenKind::Var) {
            self.expect_token(TokenKind::Var)?;

            true
        } else {
            self.expect_token(TokenKind::Input)?;

            false
        };

        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let data_type = self.parse_type()?;

        let expr = if self.token.is(TokenKind::Eq) {
            self.expect_token(TokenKind::Eq)?;
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Field {
            id: self.generate_id(),
            name,
            pos,
            span,
            data_type,
            primary_ctor: false,
            expr,
            reassignable,
        })
    }

    fn parse_invariant(&mut self) -> Result<Invariant, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        self.expect_token(TokenKind::Invariant)?;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let expr = Some(self.parse_expression()?);

        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Invariant {
            id: self.generate_id(),
            name,
            pos,
            span,
            expr,
        })
    }

    fn parse_procedure(&mut self, _modifiers: &Modifiers) -> Result<Procedure, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Procedure)?.position;
        let ident = self.expect_identifier()?;
        let type_params = self.parse_type_params()?;
        let params = self.parse_procedure_params()?;
        let return_type = self.parse_procedure_type()?;
        let block = self.parse_procedure_block()?;
        let span = self.span_from(start);

        Ok(Procedure {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            params,
            return_type,
            block,
            type_params,
        })
    }

    fn parse_function(&mut self, modifiers: &Modifiers) -> Result<Function, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Function)?.position;
        let ident = self.expect_identifier()?;
        let type_params = self.parse_type_params()?;
        let params = self.parse_procedure_params()?;
        let return_type = self.parse_procedure_type()?;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Function {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            to_synthesize: modifiers.contains(Modifier::Synthesis),
            params,
            return_type,
            type_params,
        })
    }

    fn parse_init(&mut self) -> Result<Init, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Init)?.position;
        let block = self.parse_procedure_block()?;
        let span = self.span_from(start);

        Ok(Init {
            id: self.generate_id(),
            pos,
            span,
            block,
        })
    }

    fn parse_next(&mut self) -> Result<Next, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Next)?.position;
        let block = self.parse_procedure_block()?;
        let span = self.span_from(start);

        Ok(Next {
            id: self.generate_id(),
            pos,
            span,
            block,
        })
    }

    fn parse_control(&mut self) -> Result<Control, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Control)?.position;
        let block = self.parse_procedure_block()?;
        let span = self.span_from(start);

        Ok(Control {
            id: self.generate_id(),
            pos,
            span,
            block,
        })
    }

    fn parse_procedure_params(&mut self) -> Result<Vec<Param>, ParseErrorAndPos> {
        self.expect_token(TokenKind::LParen)?;
        self.param_idx = 0;

        let params = self.parse_comma_list(TokenKind::RParen, |p| {
            p.param_idx += 1;

            p.parse_procedure_param()
        })?;

        Ok(params)
    }

    fn parse_comma_list<F, R>(
        &mut self,
        stop: TokenKind,
        mut parse: F,
    ) -> Result<Vec<R>, ParseErrorAndPos>
    where
        F: FnMut(&mut Parser) -> Result<R, ParseErrorAndPos>,
    {
        let mut data = vec![];
        let mut comma = true;

        while !self.token.is(stop.clone()) && !self.token.is_eof() {
            if !comma {
                return Err(ParseErrorAndPos::new(
                    self.token.position,
                    ParseError::ExpectedToken(TokenKind::Comma.name().into(), self.token.name()),
                ));
            }

            let entry = parse(self)?;
            data.push(entry);

            comma = self.token.is(TokenKind::Comma);
            if comma {
                self.advance_token()?;
            }
        }

        self.expect_token(stop)?;

        Ok(data)
    }

    fn parse_procedure_param(&mut self) -> Result<Param, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;

        let reassignable = if self.token.is(TokenKind::Var) {
            self.advance_token()?;

            true
        } else {
            false
        };

        let name = self.expect_identifier()?;

        self.expect_token(TokenKind::Colon)?;
        let data_type = self.parse_type()?;
        let span = self.span_from(start);

        Ok(Param {
            id: self.generate_id(),
            idx: self.param_idx - 1,
            reassignable,
            name,
            pos,
            span,
            data_type,
        })
    }

    fn parse_procedure_type(&mut self) -> Result<Option<Type>, ParseErrorAndPos> {
        if self.token.is(TokenKind::Colon) {
            self.advance_token()?;
            let ty = self.parse_type()?;

            Ok(Some(ty))
        } else {
            Ok(None)
        }
    }

    fn parse_procedure_block(&mut self) -> Result<Option<Box<ExprBlockType>>, ParseErrorAndPos> {
        if self.token.is(TokenKind::Semicolon) {
            self.advance_token()?;

            Ok(None)
        } else if self.token.is(TokenKind::Eq) {
            let expr = self.parse_procedure_block_expression()?;

            Ok(Some(expr))
        } else {
            let block = self.parse_block()?;

            if let Expr::ExprBlock(block_type) = *block {
                Ok(Some(Box::new(block_type)))
            } else {
                unreachable!()
            }
        }
    }

    fn parse_procedure_block_expression(&mut self) -> Result<Box<ExprBlockType>, ParseErrorAndPos> {
        self.expect_token(TokenKind::Eq)?;

        match self.token.kind {
            TokenKind::Return => {
                let stmt = self.parse_return()?;
                Ok(Box::new(ExprBlockType {
                    id: self.generate_id(),
                    pos: stmt.pos(),
                    span: stmt.span(),
                    stmts: vec![stmt],
                    expr: None,
                }))
            }

            _ => {
                let expr = self.parse_expression()?;
                self.expect_token(TokenKind::Semicolon)?;
                Ok(Box::new(ExprBlockType {
                    id: self.generate_id(),
                    pos: expr.pos(),
                    span: expr.span(),
                    stmts: Vec::new(),
                    expr: Some(expr),
                }))
            }
        }
    }

    fn parse_type(&mut self) -> Result<Type, ParseErrorAndPos> {
        match self.token.kind {
            TokenKind::Identifier(_) => {
                let pos = self.token.position;
                let start = self.token.span.start();
                let name = self.expect_identifier()?;

                let params = if self.token.is(TokenKind::LBracket) {
                    self.advance_token()?;
                    self.parse_comma_list(TokenKind::RBracket, |p| Ok(Box::new(p.parse_type()?)))?
                } else {
                    Vec::new()
                };

                let span = self.span_from(start);
                Ok(Type::create_basic(
                    self.generate_id(),
                    pos,
                    span,
                    name,
                    params,
                ))
            }

            TokenKind::LParen => {
                let start = self.token.span.start();
                let token = self.advance_token()?;
                let subtypes = self.parse_comma_list(TokenKind::RParen, |p| {
                    let ty = p.parse_type()?;

                    Ok(Box::new(ty))
                })?;

                if self.token.is(TokenKind::Arrow) {
                    self.advance_token()?;
                    let ret = Box::new(self.parse_type()?);
                    let span = self.span_from(start);

                    Ok(Type::create_lambda(
                        self.generate_id(),
                        token.position,
                        span,
                        subtypes,
                        ret,
                    ))
                } else {
                    let span = self.span_from(start);
                    Ok(Type::create_tuple(
                        self.generate_id(),
                        token.position,
                        span,
                        subtypes,
                    ))
                }
            }

            _ => Err(ParseErrorAndPos::new(
                self.token.position,
                ParseError::ExpectedType(self.token.name()),
            )),
        }
    }

    fn parse_var(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let reassignable = if self.token.is(TokenKind::Input) {
            false
        } else if self.token.is(TokenKind::Var) {
            true
        } else {
            panic!("input or var expected")
        };

        let pos = self.advance_token()?.position;
        let ident = self.expect_identifier()?;
        let data_type = self.parse_var_type()?;
        let expr = self.parse_var_assignment()?;

        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_var(
            self.generate_id(),
            pos,
            span,
            ident,
            reassignable,
            data_type,
            expr,
        )))
    }

    fn parse_var_type(&mut self) -> Result<Option<Type>, ParseErrorAndPos> {
        if self.token.is(TokenKind::Colon) {
            self.advance_token()?;

            Ok(Some(self.parse_type()?))
        } else {
            Ok(None)
        }
    }

    fn parse_var_assignment(&mut self) -> Result<Option<Box<Expr>>, ParseErrorAndPos> {
        if self.token.is(TokenKind::Eq) {
            self.expect_token(TokenKind::Eq)?;
            let expr = self.parse_expression()?;

            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    fn parse_block_stmt(&mut self) -> StmtResult {
        let block = self.parse_block()?;
        Ok(Box::new(Stmt::create_expr(
            self.generate_id(),
            block.pos(),
            block.span(),
            block,
        )))
    }

    fn parse_block(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::LBrace)?.position;
        let mut stmts = vec![];
        let mut expr = None;

        while !self.token.is(TokenKind::RBrace) && !self.token.is_eof() {
            let stmt_or_expr = self.parse_statement_or_expression()?;

            match stmt_or_expr {
                StmtOrExpr::Stmt(stmt) => stmts.push(stmt),
                StmtOrExpr::Expr(curr_expr) => {
                    if curr_expr.needs_semicolon() {
                        expr = Some(curr_expr);
                        break;
                    } else if !self.token.is(TokenKind::RBrace) {
                        stmts.push(Box::new(Stmt::create_expr(
                            self.generate_id(),
                            curr_expr.pos(),
                            curr_expr.span(),
                            curr_expr,
                        )));
                    } else {
                        expr = Some(curr_expr);
                    }
                }
            }
        }

        self.expect_token(TokenKind::RBrace)?;
        let span = self.span_from(start);

        Ok(Box::new(Expr::create_block(
            self.generate_id(),
            pos,
            span,
            stmts,
            expr,
        )))
    }

    fn parse_statement_or_expression(&mut self) -> StmtOrExprResult {
        match self.token.kind {
            TokenKind::Input | TokenKind::Var => Ok(StmtOrExpr::Stmt(self.parse_var()?)),
            TokenKind::While => Ok(StmtOrExpr::Stmt(self.parse_while()?)),
            TokenKind::Break => Ok(StmtOrExpr::Stmt(self.parse_break()?)),
            TokenKind::Continue => Ok(StmtOrExpr::Stmt(self.parse_continue()?)),
            TokenKind::Return => Ok(StmtOrExpr::Stmt(self.parse_return()?)),
            TokenKind::Else => Err(ParseErrorAndPos::new(
                self.token.position,
                ParseError::MisplacedElse,
            )),
            TokenKind::For => Ok(StmtOrExpr::Stmt(self.parse_for()?)),
            _ => {
                let expr = self.parse_expression()?;

                if self.token.is(TokenKind::Semicolon) {
                    self.expect_token(TokenKind::Semicolon)?;
                    let span = self.span_from(expr.span().start());

                    Ok(StmtOrExpr::Stmt(Box::new(Stmt::create_expr(
                        self.generate_id(),
                        expr.pos(),
                        span,
                        expr,
                    ))))
                } else {
                    Ok(StmtOrExpr::Expr(expr))
                }
            }
        }
    }

    fn parse_if(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::If)?.position;

        let cond = self.parse_expression_no_struct_lit()?;

        let then_block = self.parse_block()?;

        let else_block = if self.token.is(TokenKind::Else) {
            self.advance_token()?;

            if self.token.is(TokenKind::If) {
                Some(self.parse_if()?)
            } else {
                Some(self.parse_block()?)
            }
        } else {
            None
        };

        let span = self.span_from(start);

        Ok(Box::new(Expr::create_if(
            self.generate_id(),
            pos,
            span,
            cond,
            then_block,
            else_block,
        )))
    }

    fn parse_for(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::For)?.position;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::In)?;
        let expr = self.parse_expression_no_struct_lit()?;
        let block = self.parse_block_stmt()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_for(
            self.generate_id(),
            pos,
            span,
            name,
            expr,
            block,
        )))
    }

    fn parse_while(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::While)?.position;
        let expr = self.parse_expression_no_struct_lit()?;
        let block = self.parse_block_stmt()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_while(
            self.generate_id(),
            pos,
            span,
            expr,
            block,
        )))
    }

    fn parse_break(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Break)?.position;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_break(self.generate_id(), pos, span)))
    }

    fn parse_continue(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Continue)?.position;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_continue(
            self.generate_id(),
            pos,
            span,
        )))
    }

    fn parse_return(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Return)?.position;
        let expr = if self.token.is(TokenKind::Semicolon) {
            None
        } else {
            let expr = self.parse_expression()?;
            Some(expr)
        };

        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_return(
            self.generate_id(),
            pos,
            span,
            expr,
        )))
    }

    fn parse_expression(&mut self) -> ExprResult {
        self.parse_expression_struct_lit(true)
    }

    fn parse_expression_no_struct_lit(&mut self) -> ExprResult {
        self.parse_expression_struct_lit(false)
    }

    fn parse_expression_struct_lit(&mut self, struct_lit: bool) -> ExprResult {
        let old = self.parse_struct_lit;
        self.parse_struct_lit = struct_lit;

        let result = match self.token.kind {
            TokenKind::LBrace => self.parse_block(),
            TokenKind::If => self.parse_if(),
            _ => self.parse_binary(0),
        };

        self.parse_struct_lit = old;

        result
    }

    fn parse_binary(&mut self, precedence: u32) -> ExprResult {
        let start = self.token.span.start();
        let mut left = self.parse_unary()?;

        loop {
            let right_precedence = match self.token.kind {
                TokenKind::Or => 1,
                TokenKind::And => 2,
                TokenKind::Eq | TokenKind::AddEq => 3,
                TokenKind::EqEq
                | TokenKind::Ne
                | TokenKind::Lt
                | TokenKind::Le
                | TokenKind::Gt
                | TokenKind::Ge => 4,
                TokenKind::EqEqEq | TokenKind::NeEqEq => 5,
                TokenKind::BitOr | TokenKind::BitAnd | TokenKind::Caret => 6,
                TokenKind::LtLt | TokenKind::GtGt | TokenKind::GtGtGt => 7,
                TokenKind::Add | TokenKind::Sub => 8,
                TokenKind::Mul | TokenKind::Div | TokenKind::Mod => 9,
                _ => {
                    return Ok(left);
                }
            };

            if precedence >= right_precedence {
                return Ok(left);
            }

            let tok = self.advance_token()?;

            left = match tok.kind {
                _ => {
                    let right = self.parse_binary(right_precedence)?;
                    self.create_binary(tok, start, left, right)
                }
            };
        }
    }

    fn parse_unary(&mut self) -> ExprResult {
        match self.token.kind {
            TokenKind::Add | TokenKind::Sub | TokenKind::Not => {
                let start = self.token.span.start();
                let tok = self.advance_token()?;
                let op = match tok.kind {
                    TokenKind::Add => UnOp::Plus,
                    TokenKind::Sub => UnOp::Neg,
                    TokenKind::Not => UnOp::Not,
                    _ => unreachable!(),
                };

                let expr = self.parse_primary()?;
                let span = self.span_from(start);
                Ok(Box::new(Expr::create_un(
                    self.generate_id(),
                    tok.position,
                    span,
                    op,
                    expr,
                )))
            }

            _ => self.parse_primary(),
        }
    }

    fn parse_primary(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let mut left = self.parse_factor()?;

        loop {
            left = match self.token.kind {
                TokenKind::Dot => {
                    let tok = self.advance_token()?;
                    let rhs = self.parse_factor()?;
                    let span = self.span_from(start);

                    Box::new(Expr::create_dot(
                        self.generate_id(),
                        tok.position,
                        span,
                        left,
                        rhs,
                    ))
                }

                TokenKind::LParen => {
                    let tok = self.advance_token()?;
                    let args =
                        self.parse_comma_list(TokenKind::RParen, |p| p.parse_expression())?;
                    let span = self.span_from(start);

                    Box::new(Expr::create_call(
                        self.generate_id(),
                        tok.position,
                        span,
                        left,
                        args,
                    ))
                }

                TokenKind::LBracket => {
                    let tok = self.advance_token()?;
                    let types = self.parse_comma_list(TokenKind::RBracket, |p| p.parse_type())?;
                    let span = self.span_from(start);

                    Box::new(Expr::create_type_param(
                        self.generate_id(),
                        tok.position,
                        span,
                        left,
                        types,
                    ))
                }

                TokenKind::Sep => {
                    let tok = self.advance_token()?;
                    let rhs = self.parse_factor()?;
                    let span = self.span_from(start);

                    Box::new(Expr::create_path(
                        self.generate_id(),
                        tok.position,
                        span,
                        left,
                        rhs,
                    ))
                }

                _ => {
                    return Ok(left);
                }
            }
        }
    }

    fn create_binary(
        &mut self,
        tok: Token,
        start: u32,
        left: Box<Expr>,
        right: Box<Expr>,
    ) -> Box<Expr> {
        let op = match tok.kind {
            TokenKind::Eq => BinOp::Assign,
            TokenKind::Or => BinOp::Or,
            TokenKind::And => BinOp::And,
            TokenKind::EqEq => BinOp::Cmp(CmpOp::Eq),
            TokenKind::Ne => BinOp::Cmp(CmpOp::Ne),
            TokenKind::Lt => BinOp::Cmp(CmpOp::Lt),
            TokenKind::Le => BinOp::Cmp(CmpOp::Le),
            TokenKind::Gt => BinOp::Cmp(CmpOp::Gt),
            TokenKind::Ge => BinOp::Cmp(CmpOp::Ge),
            TokenKind::EqEqEq => BinOp::Cmp(CmpOp::Is),
            TokenKind::NeEqEq => BinOp::Cmp(CmpOp::IsNot),
            TokenKind::BitOr => BinOp::BitOr,
            TokenKind::BitAnd => BinOp::BitAnd,
            TokenKind::Caret => BinOp::BitXor,
            TokenKind::Add => BinOp::Add,
            TokenKind::Sub => BinOp::Sub,
            TokenKind::Mul => BinOp::Mul,
            TokenKind::Div => BinOp::Div,
            TokenKind::Mod => BinOp::Mod,
            TokenKind::LtLt => BinOp::ShiftL,
            TokenKind::GtGt => BinOp::ArithShiftR,
            TokenKind::GtGtGt => BinOp::LogicalShiftR,
            _ => panic!("unimplemented token {:?}", tok),
        };

        let span = self.span_from(start);

        Box::new(Expr::create_bin(
            self.generate_id(),
            tok.position,
            span,
            op,
            left,
            right,
        ))
    }

    fn parse_factor(&mut self) -> ExprResult {
        match self.token.kind {
            TokenKind::LParen => self.parse_parentheses(),
            TokenKind::LBrace => self.parse_block(),
            TokenKind::If => self.parse_if(),
            TokenKind::LitChar(_) => self.parse_lit_char(),
            TokenKind::LitInt(_, _, _) => self.parse_lit_int(),
            TokenKind::LitFloat(_, _) => self.parse_lit_float(),
            TokenKind::StringTail(_) | TokenKind::StringExpr(_) => self.parse_string(),
            TokenKind::Identifier(_) => self.parse_identifier(),
            TokenKind::True => self.parse_bool_literal(),
            TokenKind::False => self.parse_bool_literal(),
            TokenKind::BitOr | TokenKind::Or => self.parse_lambda(),
            _ => Err(ParseErrorAndPos::new(
                self.token.position,
                ParseError::ExpectedFactor(self.token.name().clone()),
            )),
        }
    }

    fn parse_identifier(&mut self) -> ExprResult {
        let pos = self.token.position;
        let span = self.token.span;
        let name = self.expect_identifier()?;

        Ok(Box::new(Expr::create_ident(
            self.generate_id(),
            pos,
            span,
            name,
            None,
        )))
    }

    fn parse_parentheses(&mut self) -> ExprResult {
        let pos = self.token.position;
        let start = self.token.span.start();
        self.expect_token(TokenKind::LParen)?;
        let expr = self.parse_expression()?;

        if self.token.kind == TokenKind::Comma {
            let mut values = vec![expr];
            let span;

            loop {
                self.expect_token(TokenKind::Comma)?;

                if self.token.kind == TokenKind::RParen {
                    self.advance_token()?;
                    span = self.span_from(start);
                    break;
                }

                let expr = self.parse_expression()?;
                values.push(expr);

                if self.token.kind == TokenKind::RParen {
                    self.advance_token()?;
                    span = self.span_from(start);
                    break;
                }
            }

            Ok(Box::new(Expr::create_tuple(
                self.generate_id(),
                pos,
                span,
                values,
            )))
        } else {
            self.expect_token(TokenKind::RParen)?;

            Ok(expr)
        }
    }

    fn parse_lit_char(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;
        let pos = tok.position;

        if let TokenKind::LitChar(val) = tok.kind {
            Ok(Box::new(Expr::create_lit_char(
                self.generate_id(),
                pos,
                span,
                val,
            )))
        } else {
            unreachable!();
        }
    }

    fn parse_lit_int(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;
        let pos = tok.position;

        if let TokenKind::LitInt(value, base, suffix) = tok.kind {
            let filtered = value.chars().filter(|&ch| ch != '_').collect::<String>();
            let parsed = u64::from_str_radix(&filtered, base.num());

            match parsed {
                Ok(num) => {
                    let expr =
                        Expr::create_lit_int(self.generate_id(), pos, span, num, base, suffix);
                    Ok(Box::new(expr))
                }

                _ => {
                    let bits = match suffix {
                        IntSuffix::Byte => "byte",
                        IntSuffix::Int => "int",
                        IntSuffix::Long => "long",
                    };

                    Err(ParseErrorAndPos::new(
                        pos,
                        ParseError::NumberOverflow(bits.into()),
                    ))
                }
            }
        } else {
            unreachable!();
        }
    }

    fn parse_lit_float(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;
        let pos = tok.position;

        if let TokenKind::LitFloat(value, suffix) = tok.kind {
            let filtered = value.chars().filter(|&ch| ch != '_').collect::<String>();
            let parsed = filtered.parse::<f64>();

            if let Ok(num) = parsed {
                let expr = Expr::create_lit_float(self.generate_id(), pos, span, num, suffix);
                return Ok(Box::new(expr));
            }
        }

        unreachable!()
    }

    fn parse_string(&mut self) -> ExprResult {
        let span = self.token.span;
        let string = self.advance_token()?;

        match string.kind {
            TokenKind::StringTail(value) => Ok(Box::new(Expr::create_lit_str(
                self.generate_id(),
                string.position,
                span,
                value,
            ))),

            TokenKind::StringExpr(value) => {
                let start = self.token.span.start();
                let mut parts: Vec<Box<Expr>> = Vec::new();
                parts.push(Box::new(Expr::create_lit_str(
                    self.generate_id(),
                    string.position,
                    span,
                    value,
                )));

                loop {
                    let expr = self.parse_expression()?;
                    parts.push(expr);

                    if !self.token.is(TokenKind::RBrace) {
                        return Err(ParseErrorAndPos::new(
                            self.token.position,
                            ParseError::UnclosedStringTemplate,
                        ));
                    }

                    let token = self.lexer.read_string_continuation()?;
                    self.advance_token_with(token);

                    let pos = self.token.position;
                    let span = self.token.span;

                    let (value, finished) = match self.token.kind {
                        TokenKind::StringTail(ref value) => (value.clone(), true),
                        TokenKind::StringExpr(ref value) => (value.clone(), false),
                        _ => unreachable!(),
                    };

                    parts.push(Box::new(Expr::create_lit_str(
                        self.generate_id(),
                        pos,
                        span,
                        value,
                    )));

                    self.advance_token()?;

                    if finished {
                        break;
                    }
                }

                let span = self.span_from(start);

                Ok(Box::new(Expr::create_template(
                    self.generate_id(),
                    string.position,
                    span,
                    parts,
                )))
            }

            _ => unreachable!(),
        }
    }

    fn parse_bool_literal(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;
        let value = tok.is(TokenKind::True);

        Ok(Box::new(Expr::create_lit_bool(
            self.generate_id(),
            tok.position,
            span,
            value,
        )))
    }

    fn parse_lambda(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let tok = self.advance_token()?;

        let params = if tok.kind == TokenKind::Or {
            // nothing to do
            Vec::new()
        } else {
            self.param_idx = 0;
            self.parse_comma_list(TokenKind::BitOr, |p| {
                p.param_idx += 1;
                p.parse_procedure_param()
            })?
        };

        let ret = if self.token.is(TokenKind::Arrow) {
            self.advance_token()?;
            Some(Box::new(self.parse_type()?))
        } else {
            None
        };

        let block = self.parse_block_stmt()?;
        let span = self.span_from(start);

        Ok(Box::new(Expr::create_lambda(
            self.generate_id(),
            tok.position,
            span,
            params,
            ret,
            block,
        )))
    }

    fn expect_identifier(&mut self) -> Result<Name, ParseErrorAndPos> {
        let tok = self.advance_token()?;

        if let TokenKind::Identifier(ref value) = tok.kind {
            let interned = self.interner.intern(value);
            Ok(interned)
        } else {
            Err(ParseErrorAndPos::new(
                tok.position,
                ParseError::ExpectedIdentifier(tok.name()),
            ))
        }
    }

    fn expect_semicolon(&mut self) -> Result<Token, ParseErrorAndPos> {
        self.expect_token(TokenKind::Semicolon)
    }

    fn expect_token(&mut self, kind: TokenKind) -> Result<Token, ParseErrorAndPos> {
        if self.token.kind == kind {
            let token = self.advance_token()?;

            Ok(token)
        } else {
            Err(ParseErrorAndPos::new(
                self.token.position,
                ParseError::ExpectedToken(kind.name().into(), self.token.name()),
            ))
        }
    }

    fn advance_token(&mut self) -> Result<Token, ParseErrorAndPos> {
        let token = self.lexer.read_token()?;
        Ok(self.advance_token_with(token))
    }

    fn advance_token_with(&mut self, token: Token) -> Token {
        self.last_end = if self.token.span.is_valid() {
            Some(self.token.span.end())
        } else {
            None
        };

        mem::replace(&mut self.token, token)
    }

    fn span_from(&self, start: u32) -> Span {
        Span::new(start, self.last_end.unwrap() - start)
    }
}

#[derive(Clone, Debug)]
struct Delegation {
    pub pos: Position,
    pub args: Vec<Box<Expr>>,
}

#[derive(Debug)]
pub struct NodeIdGenerator {
    value: RefCell<usize>,
}

impl NodeIdGenerator {
    pub fn new() -> NodeIdGenerator {
        NodeIdGenerator {
            value: RefCell::new(1),
        }
    }

    pub fn next(&self) -> NodeId {
        let value = *self.value.borrow();
        *self.value.borrow_mut() += 1;

        NodeId(value)
    }
}
