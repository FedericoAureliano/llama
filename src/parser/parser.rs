use std::cell::RefCell;
use std::mem;

use crate::parser::ast;
use crate::parser::ast::Elem::*;
use crate::parser::ast::*;
use crate::parser::builder::Builder;
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
            TokenKind::Procedure => {
                self.restrict_modifiers(
                    &modifiers,
                    &[
                        Modifier::Internal,
                        Modifier::Optimize,
                        Modifier::OptimizeImmediately,
                        Modifier::Test,
                        Modifier::Cannon,
                    ],
                )?;
                let fct = self.parse_procedure(&modifiers)?;
                elements.push(ElemProcedure(fct));
            }

            TokenKind::Class => {
                self.restrict_modifiers(
                    &modifiers,
                    &[
                        Modifier::Abstract,
                        Modifier::Open,
                        Modifier::Internal,
                        Modifier::Cannon,
                    ],
                )?;
                let class = self.parse_class(&modifiers)?;
                elements.push(ElemClass(class));
            }

            TokenKind::Struct => {
                self.ban_modifiers(&modifiers)?;
                let struc = self.parse_struct()?;
                elements.push(ElemStruct(struc))
            }

            TokenKind::Trait => {
                self.ban_modifiers(&modifiers)?;
                let xtrait = self.parse_trait()?;
                elements.push(ElemTrait(xtrait));
            }

            TokenKind::Impl => {
                self.ban_modifiers(&modifiers)?;
                let ximpl = self.parse_impl()?;
                elements.push(ElemImpl(ximpl));
            }

            TokenKind::Module => {
                self.ban_modifiers(&modifiers)?;
                let module = self.parse_module()?;
                elements.push(ElemModule(module));
            }

            TokenKind::Input | TokenKind::Var => {
                self.ban_modifiers(&modifiers)?;
                self.parse_global(elements)?;
            }

            TokenKind::Const => {
                self.ban_modifiers(&modifiers)?;
                let xconst = self.parse_const()?;
                elements.push(ElemConst(xconst));
            }

            TokenKind::Enum => {
                self.ban_modifiers(&modifiers)?;
                let xenum = self.parse_enum()?;
                elements.push(ElemEnum(xenum));
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

    fn parse_const(&mut self) -> Result<Const, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Const)?.position;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.expect_token(TokenKind::Eq)?;
        let expr = self.parse_expression()?;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Const {
            id: self.generate_id(),
            pos,
            span,
            name,
            data_type: ty,
            expr,
        })
    }

    fn parse_impl(&mut self) -> Result<Impl, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Impl)?.position;
        let type_params = self.parse_type_params()?;

        let type_name = self.parse_type()?;

        let (class_type, trait_type) = if self.token.is(TokenKind::For) {
            self.advance_token()?;
            let class_type = self.parse_type()?;

            (class_type, Some(type_name))
        } else {
            (type_name, None)
        };

        self.expect_token(TokenKind::LBrace)?;

        let mut methods = Vec::new();

        while !self.token.is(TokenKind::RBrace) {
            let modifiers = self.parse_annotations()?;
            let mods = &[Modifier::Static, Modifier::Internal, Modifier::Cannon];
            self.restrict_modifiers(&modifiers, mods)?;

            methods.push(self.parse_procedure(&modifiers)?);
        }

        self.expect_token(TokenKind::RBrace)?;
        let span = self.span_from(start);

        Ok(Impl {
            id: self.generate_id(),
            pos,
            span,
            type_params,
            trait_type,
            class_type,
            methods,
        })
    }

    fn parse_global(&mut self, elements: &mut Vec<Elem>) -> Result<(), ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        let reassignable = self.token.is(TokenKind::Var);

        self.advance_token()?;
        let name = self.expect_identifier()?;

        self.expect_token(TokenKind::Colon)?;
        let data_type = self.parse_type()?;

        let expr = if self.token.is(TokenKind::Eq) {
            self.advance_token()?;

            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect_semicolon()?;
        let span = self.span_from(start);

        let global = Global {
            id: self.generate_id(),
            name,
            pos,
            span,
            data_type,
            reassignable,
            expr,
        };

        elements.push(ElemGlobal(global));

        Ok(())
    }

    fn parse_trait(&mut self) -> Result<Trait, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Trait)?.position;
        let ident = self.expect_identifier()?;

        self.expect_token(TokenKind::LBrace)?;

        let mut methods = Vec::new();

        while !self.token.is(TokenKind::RBrace) {
            let modifiers = self.parse_annotations()?;
            let mods = &[Modifier::Static];
            self.restrict_modifiers(&modifiers, mods)?;

            methods.push(self.parse_procedure(&modifiers)?);
        }

        self.expect_token(TokenKind::RBrace)?;
        let span = self.span_from(start);

        Ok(Trait {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            methods,
        })
    }

    fn parse_struct(&mut self) -> Result<Struct, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Struct)?.position;
        let ident = self.expect_identifier()?;

        self.expect_token(TokenKind::LBrace)?;
        let fields = self.parse_comma_list(TokenKind::RBrace, |p| p.parse_struct_field())?;
        let span = self.span_from(start);

        Ok(Struct {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            fields,
        })
    }

    fn parse_struct_field(&mut self) -> Result<StructField, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        let ident = self.expect_identifier()?;

        self.expect_token(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let span = self.span_from(start);

        Ok(StructField {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            data_type: ty,
        })
    }

    fn parse_class(&mut self, modifiers: &Modifiers) -> Result<Class, ParseErrorAndPos> {
        let start = self.token.span.start();
        let has_open = modifiers.contains(Modifier::Open);
        let internal = modifiers.contains(Modifier::Internal);
        let is_abstract = modifiers.contains(Modifier::Abstract);

        let pos = self.expect_token(TokenKind::Class)?.position;
        let ident = self.expect_identifier()?;
        let type_params = self.parse_type_params()?;

        let mut cls = Class {
            id: self.generate_id(),
            name: ident,
            pos,
            span: Span::invalid(),
            has_open,
            internal,
            is_abstract,
            has_constructor: false,
            parent_class: None,
            constructor: None,
            fields: Vec::new(),
            methods: Vec::new(),
            initializers: Vec::new(),
            type_params,
        };

        self.in_class_or_module = true;
        let ctor_params = self.parse_constructor(&mut cls)?;

        let use_cannon = modifiers.contains(Modifier::Cannon);

        cls.parent_class = self.parse_class_parent()?;

        self.parse_class_body(&mut cls)?;
        let span = self.span_from(start);

        cls.constructor = Some(self.generate_constructor(&mut cls, ctor_params, use_cannon));
        cls.span = span;
        self.in_class_or_module = false;

        Ok(cls)
    }

    fn parse_class_parent(&mut self) -> Result<Option<ParentClass>, ParseErrorAndPos> {
        if self.token.is(TokenKind::Colon) {
            self.advance_token()?;

            let start = self.token.span.start();
            let pos = self.token.position;
            let name = self.expect_identifier()?;
            let type_params = self.parse_class_parent_type_params()?;
            let params = self.parse_parent_class_params()?;
            let span = self.span_from(start);

            Ok(Some(ParentClass::new(name, pos, span, type_params, params)))
        } else {
            Ok(None)
        }
    }

    fn parse_class_parent_type_params(&mut self) -> Result<Vec<Type>, ParseErrorAndPos> {
        let mut types = Vec::new();

        if self.token.is(TokenKind::LBracket) {
            self.advance_token()?;
            types = self.parse_comma_list(TokenKind::RBracket, |p| p.parse_type())?;
        }

        Ok(types)
    }

    fn parse_module(&mut self) -> Result<Module, ParseErrorAndPos> {
        let pos = self.expect_token(TokenKind::Module)?.position;
        let ident = self.expect_identifier()?;
        let mut module = Module {
            id: self.generate_id(),
            name: ident,
            pos: pos,
            inputs: Vec::new(),
            vars: Vec::new(),
            functions: Vec::new(),
            procedures: Vec::new(),
            invs: Vec::new(),
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

    fn parse_parent_class_params(&mut self) -> Result<Vec<Box<Expr>>, ParseErrorAndPos> {
        if !self.token.is(TokenKind::LParen) {
            return Ok(Vec::new());
        }

        self.expect_token(TokenKind::LParen)?;

        let params = self.parse_comma_list(TokenKind::RParen, |p| p.parse_expression())?;

        Ok(params)
    }

    fn parse_constructor(
        &mut self,
        cls: &mut Class,
    ) -> Result<Vec<ConstructorParam>, ParseErrorAndPos> {
        if !self.token.is(TokenKind::LParen) {
            return Ok(Vec::new());
        }

        self.expect_token(TokenKind::LParen)?;
        cls.has_constructor = true;

        let params =
            self.parse_comma_list(TokenKind::RParen, |p| p.parse_constructor_param(cls))?;

        Ok(params)
    }

    fn parse_constructor_param(
        &mut self,
        cls: &mut Class,
    ) -> Result<ConstructorParam, ParseErrorAndPos> {
        let start = self.token.span.start();
        let field = self.token.is(TokenKind::Var) || self.token.is(TokenKind::Input);
        let reassignable = self.token.is(TokenKind::Var);

        // consume var and let
        if field {
            self.advance_token()?;
        }

        let pos = self.token.position;
        let name = self.expect_identifier()?;

        self.expect_token(TokenKind::Colon)?;
        let data_type = self.parse_type()?;

        let span = self.span_from(start);

        if field {
            cls.fields.push(Field {
                id: self.generate_id(),
                name,
                pos,
                span,
                data_type: data_type.clone(),
                primary_ctor: true,
                expr: None,
                reassignable,
            })
        }

        Ok(ConstructorParam {
            name,
            pos,
            span,
            data_type,
            field,
            reassignable,
        })
    }

    fn parse_class_body(&mut self, cls: &mut Class) -> Result<(), ParseErrorAndPos> {
        if !self.token.is(TokenKind::LBrace) {
            return Ok(());
        }

        self.advance_token()?;

        while !self.token.is(TokenKind::RBrace) {
            let modifiers = self.parse_annotations()?;

            match self.token.kind {
                TokenKind::Procedure => {
                    let mods = &[
                        Modifier::Abstract,
                        Modifier::Internal,
                        Modifier::Open,
                        Modifier::Override,
                        Modifier::Final,
                        Modifier::Pub,
                        Modifier::Static,
                        Modifier::Cannon,
                    ];
                    self.restrict_modifiers(&modifiers, mods)?;

                    let fct = self.parse_procedure(&modifiers)?;
                    cls.methods.push(fct);
                }

                TokenKind::Var | TokenKind::Input => {
                    self.ban_modifiers(&modifiers)?;

                    let field = self.parse_field()?;
                    cls.fields.push(field);
                }

                _ => {
                    let initializer = self.parse_statement()?;
                    cls.initializers.push(initializer);
                }
            }
        }

        self.advance_token()?;
        Ok(())
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
                    module.vars.push(field);
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
                    module.invs.push(spec);
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
                "abstract" => Modifier::Abstract,
                "open" => Modifier::Open,
                "override" => Modifier::Override,
                "final" => Modifier::Final,
                "internal" => Modifier::Internal,
                "pub" => Modifier::Pub,
                "static" => Modifier::Static,
                "optimize" => Modifier::Optimize,
                "test" => Modifier::Test,
                "cannon" => Modifier::Cannon,
                "optimize_immediately" => Modifier::OptimizeImmediately,
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

    fn parse_invariant(&mut self) -> Result<Spec, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.token.position;
        self.expect_token(TokenKind::Invariant)?;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let expr = Some(self.parse_expression()?);

        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Spec {
            id: self.generate_id(),
            name,
            pos,
            span,
            expr,
        })
    }

    fn parse_procedure(&mut self, modifiers: &Modifiers) -> Result<Procedure, ParseErrorAndPos> {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Procedure)?.position;
        let ident = self.expect_identifier()?;
        let type_params = self.parse_type_params()?;
        let params = self.parse_procedure_params()?;
        let throws = self.parse_throws()?;
        let return_type = self.parse_procedure_type()?;
        let block = self.parse_procedure_block()?;
        let span = self.span_from(start);

        Ok(Procedure {
            id: self.generate_id(),
            name: ident,
            pos,
            span,
            method: self.in_class_or_module,
            has_open: modifiers.contains(Modifier::Open),
            has_override: modifiers.contains(Modifier::Override),
            has_final: modifiers.contains(Modifier::Final),
            has_optimize: modifiers.contains(Modifier::Optimize),
            has_optimize_immediately: modifiers.contains(Modifier::OptimizeImmediately),
            is_pub: modifiers.contains(Modifier::Pub),
            is_static: modifiers.contains(Modifier::Static),
            internal: modifiers.contains(Modifier::Internal),
            is_abstract: modifiers.contains(Modifier::Abstract),
            is_constructor: false,
            is_test: modifiers.contains(Modifier::Test),
            use_cannon: modifiers.contains(Modifier::Cannon),
            params,
            throws,
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

    fn parse_throws(&mut self) -> Result<bool, ParseErrorAndPos> {
        if self.token.is(TokenKind::Throws) {
            self.advance_token()?;

            return Ok(true);
        }

        Ok(false)
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
            TokenKind::Throw => {
                let stmt = self.parse_throw()?;
                Ok(Box::new(ExprBlockType {
                    id: self.generate_id(),
                    pos: stmt.pos(),
                    span: stmt.span(),
                    stmts: vec![stmt],
                    expr: None,
                }))
            }

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
            TokenKind::CapitalThis => {
                let pos = self.token.position;
                let span = self.token.span;
                self.advance_token()?;
                Ok(Type::create_self(self.generate_id(), pos, span))
            }

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

                    Ok(Type::create_fct(
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

    fn parse_statement(&mut self) -> StmtResult {
        let stmt_or_expr = self.parse_statement_or_expression()?;

        match stmt_or_expr {
            StmtOrExpr::Stmt(stmt) => Ok(stmt),
            StmtOrExpr::Expr(expr) => {
                if expr.needs_semicolon() {
                    Err(self.expect_semicolon().unwrap_err())
                } else {
                    Ok(Box::new(Stmt::create_expr(
                        self.generate_id(),
                        expr.pos(),
                        expr.span(),
                        expr,
                    )))
                }
            }
        }
    }

    fn parse_throw(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Throw)?.position;
        let expr = self.parse_expression()?;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_throw(
            self.generate_id(),
            pos,
            span,
            expr,
        )))
    }

    fn parse_defer(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Defer)?.position;
        let expr = self.parse_expression()?;
        self.expect_semicolon()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_defer(
            self.generate_id(),
            pos,
            span,
            expr,
        )))
    }

    fn parse_do(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Do)?.position;
        let try_block = self.parse_block_stmt()?;
        let mut catch_blocks = Vec::new();

        while self.token.is(TokenKind::Catch) {
            catch_blocks.push(self.parse_catch()?);
        }

        let finally_block = if self.token.is(TokenKind::Finally) {
            Some(self.parse_finally()?)
        } else {
            None
        };

        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_do(
            self.generate_id(),
            pos,
            span,
            try_block,
            catch_blocks,
            finally_block,
        )))
    }

    fn parse_catch(&mut self) -> Result<CatchBlock, ParseErrorAndPos> {
        let id = self.generate_id();
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Catch)?.position;
        let name = self.expect_identifier()?;
        self.expect_token(TokenKind::Colon)?;
        let data_type = self.parse_type()?;
        let block = self.parse_block_stmt()?;
        let span = self.span_from(start);

        Ok(CatchBlock::new(id, name, pos, span, data_type, block))
    }

    fn parse_finally(&mut self) -> Result<FinallyBlock, ParseErrorAndPos> {
        self.expect_token(TokenKind::Finally)?;
        let block = self.parse_block_stmt()?;

        Ok(FinallyBlock::new(block))
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
            TokenKind::Loop => Ok(StmtOrExpr::Stmt(self.parse_loop()?)),
            TokenKind::Break => Ok(StmtOrExpr::Stmt(self.parse_break()?)),
            TokenKind::Continue => Ok(StmtOrExpr::Stmt(self.parse_continue()?)),
            TokenKind::Return => Ok(StmtOrExpr::Stmt(self.parse_return()?)),
            TokenKind::Else => Err(ParseErrorAndPos::new(
                self.token.position,
                ParseError::MisplacedElse,
            )),
            TokenKind::Throw => Ok(StmtOrExpr::Stmt(self.parse_throw()?)),
            TokenKind::Defer => Ok(StmtOrExpr::Stmt(self.parse_defer()?)),
            TokenKind::Do => Ok(StmtOrExpr::Stmt(self.parse_do()?)),
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

    fn parse_loop(&mut self) -> StmtResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Loop)?.position;
        let block = self.parse_block_stmt()?;
        let span = self.span_from(start);

        Ok(Box::new(Stmt::create_loop(
            self.generate_id(),
            pos,
            span,
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
                TokenKind::Is | TokenKind::As => 10,
                _ => {
                    return Ok(left);
                }
            };

            if precedence >= right_precedence {
                return Ok(left);
            }

            let tok = self.advance_token()?;

            left = match tok.kind {
                TokenKind::Is | TokenKind::As => {
                    let is = tok.is(TokenKind::Is);

                    let right = Box::new(self.parse_type()?);
                    let span = self.span_from(start);
                    let expr =
                        Expr::create_conv(self.generate_id(), tok.position, span, left, right, is);

                    Box::new(expr)
                }

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
            TokenKind::Nil => self.parse_nil(),
            TokenKind::This => self.parse_this(),
            TokenKind::Super => self.parse_super(),
            TokenKind::Try => self.parse_try(),
            TokenKind::TryForce | TokenKind::TryOpt => self.parse_try_op(),
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

    fn parse_try_op(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let tok = self.advance_token()?;
        let exp = self.parse_expression()?;

        let mode = if tok.is(TokenKind::TryForce) {
            TryMode::Force
        } else {
            TryMode::Opt
        };

        let span = self.span_from(start);

        Ok(Box::new(Expr::create_try(
            self.generate_id(),
            tok.position,
            span,
            exp,
            mode,
        )))
    }

    fn parse_try(&mut self) -> ExprResult {
        let start = self.token.span.start();
        let pos = self.expect_token(TokenKind::Try)?.position;
        let exp = self.parse_expression()?;

        let mode = if self.token.is(TokenKind::Else) {
            self.advance_token()?;
            let alt_exp = self.parse_expression()?;

            TryMode::Else(alt_exp)
        } else {
            TryMode::Normal
        };

        let span = self.span_from(start);

        Ok(Box::new(Expr::create_try(
            self.generate_id(),
            pos,
            span,
            exp,
            mode,
        )))
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

    fn parse_this(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;

        Ok(Box::new(Expr::create_this(
            self.generate_id(),
            tok.position,
            span,
        )))
    }

    fn parse_super(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;

        Ok(Box::new(Expr::create_super(
            self.generate_id(),
            tok.position,
            span,
        )))
    }

    fn parse_nil(&mut self) -> ExprResult {
        let span = self.token.span;
        let tok = self.advance_token()?;

        Ok(Box::new(Expr::create_nil(
            self.generate_id(),
            tok.position,
            span,
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

    fn generate_constructor(
        &mut self,
        cls: &mut Class,
        ctor_params: Vec<ConstructorParam>,
        use_cannon: bool,
    ) -> Procedure {
        let builder = Builder::new(self.id_generator);
        let mut block = builder.build_block();

        if let Some(ref parent_class) = cls.parent_class {
            let expr = Expr::create_delegation(
                self.generate_id(),
                parent_class.pos,
                parent_class.span,
                parent_class.params.clone(),
            );

            block.add_expr(Box::new(expr));
        }

        for param in ctor_params.iter().filter(|param| param.field) {
            let this = builder.build_this();
            let lhs = builder.build_dot(this, builder.build_ident(param.name));
            let rhs = builder.build_ident(param.name);
            let ass = builder.build_assign(lhs, rhs);

            block.add_expr(ass);
        }

        for field in cls.fields.iter().filter(|field| field.expr.is_some()) {
            let this = builder.build_this();
            let lhs = builder.build_dot(this, builder.build_ident(field.name));
            let ass = builder.build_assign(lhs, field.expr.as_ref().unwrap().clone());

            block.add_expr(ass);
        }

        block.add_stmts(mem::replace(&mut cls.initializers, Vec::new()));

        let mut fct = builder.build_fct(cls.name);

        for field in &ctor_params {
            fct.add_param(field.name, field.data_type.clone());
        }

        fct.is_method(true)
            .is_public(true)
            .use_cannon(use_cannon)
            .constructor(true)
            .block(block.build());

        fct.build()
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
