use crate::parser::ast::*;
use crate::parser::ast::Expr::*;
use crate::parser::ast::Stmt::*;
use crate::parser::interner::{ArcStr, Interner, Name};

macro_rules! dump {
    ($self_:ident, $($message:tt)*) => {{
        for _ in 0..($self_.indent*2) {
            print!(" ");
        }

        println!($($message)*);
    }};
}

pub fn dump(ast: &Ast, interner: &Interner) {
    let mut dumper = AstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_ast(ast);
}

pub fn dump_procedure(prcd: &Procedure, interner: &Interner) {
    let mut dumper = AstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_procedure(prcd);
}

pub fn dump_expr<'a>(expr: &'a Expr, interner: &'a Interner) {
    let mut dumper = AstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_expr(expr);
}

pub fn dump_stmt<'a>(stmt: &'a Stmt, interner: &'a Interner) {
    let mut dumper = AstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_stmt(stmt);
}

struct AstDumper<'a> {
    interner: &'a Interner,
    indent: u32,
}

impl<'a> AstDumper<'a> {
    fn dump_ast(&mut self, ast: &Ast) {
        for f in &ast.files {
            dump!(self, "file {}", &f.path);

            self.indent(|d| {
                d.dump_file(f);
            })
        }
    }

    fn dump_file(&mut self, f: &File) {
        for el in &f.elements {
            match *el {
                ElemProcedure(ref fct) => self.dump_procedure(fct),
                ElemModule(ref module) => self.dump_module(module),
                ElemEnum(ref xenum) => self.dump_enum(xenum),
                ElemInit(ref xinit) => self.dump_init(xinit),
                ElemNext(ref xnext) => self.dump_next(xnext),
                ElemControl(ref xcontrol) => self.dump_control(xcontrol),
            }
        }
    }

    fn dump_enum(&mut self, xenum: &Enum) {
        dump!(
            self,
            "enum {} @ {} {}",
            self.str(xenum.name),
            xenum.pos,
            xenum.id
        );

        self.indent(|d| {
            for value in &xenum.values {
                d.dump_expr(value)
            }
        });
    }

    fn dump_module(&mut self, modu: &Module) {
        dump!(
            self,
            "module {} @ {} {}",
            self.str(modu.name),
            modu.pos,
            modu.id
        );

        self.indent(|d| {
            if !modu.inputs.is_empty() {
                dump!(d, "inputs");
                d.indent(|d| {
                    for input in &modu.inputs {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.outputs.is_empty() {
                dump!(d, "outputs");
                d.indent(|d| {
                    for input in &modu.outputs {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.variables.is_empty() {
                dump!(d, "variables");
                d.indent(|d| {
                    for var in &modu.variables {
                        d.dump_field(var);
                    }
                });
            };

            if !modu.constants.is_empty() {
                dump!(d, "constants");
                d.indent(|d| {
                    for input in &modu.constants {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.functions.is_empty() {
                dump!(d, "functions");
                d.indent(|d| {
                    for func in &modu.functions {
                        d.dump_function(func);
                    }
                });
            };

            if !modu.procedures.is_empty() {
                dump!(d, "procedures");
                d.indent(|d| {
                    for prcd in &modu.procedures {
                        d.dump_procedure(prcd);
                    }
                });
            };

            if modu.init.is_some() || modu.next.is_some() {
                dump!(d, "transition system");
            };

            if let Some(ref init) = &modu.init {
                d.indent(|d| d.dump_init(init));
            };

            if let Some(ref next) = &modu.next {
                d.indent(|d| d.dump_next(next));
            };

            if !modu.theorems.is_empty() || !modu.lemmas.is_empty() {
                dump!(d, "specification");
                d.indent(|d| {
                    for prcd in &modu.theorems {
                        d.dump_property(prcd);
                    }
                });
                d.indent(|d| {
                    for prcd in &modu.lemmas {
                        d.dump_property(prcd);
                    }
                });
            };

            if let Some(ref control) = &modu.control {
                d.dump_control(control);
            };
        });
    }

    fn dump_field(&mut self, field: &Field) {
        dump!(
            self,
            "`{}` {} @ {} {}",
            field.data_type.to_string(self.interner),
            self.str(field.name),
            field.pos,
            field.id
        );
    }

    fn dump_property(&mut self, inv: &Property) {
        dump!(
            self,
            "{} @ {} {}",
            self.str(inv.name),
            inv.pos,
            inv.id
        );
        self.indent(|d| {
            let ref expr = inv.expr;
            d.dump_expr(expr);
        });
    }

    fn dump_function(&mut self, fct: &Function) {
        dump!(self, "{} @ {} {}", self.str(fct.name), fct.pos, fct.id);

        self.indent(|d| {
            dump!(d, "to synthesize = {}", fct.to_synthesize);
            dump!(d, "params");
            d.indent(|d| {
                if !fct.params.is_empty() {
                    for param in &fct.params {
                        d.dump_param(param);
                    }
                }
            });

            if let Some(ref ty) = fct.return_type {
                let name = ty.to_string(d.interner);
                let pos = ty.pos();
                let id = ty.id();
                dump!(d, "returns `{}` @ {} {}", name, pos, id);
            };
        });
    }

    fn dump_procedure(&mut self, fct: &Procedure) {
        dump!(self, "{} @ {} {}", self.str(fct.name), fct.pos, fct.id);

        self.indent(|d| {

            if !fct.params.is_empty() {
                dump!(d, "params");
                for param in &fct.params {
                    d.indent(|d| d.dump_param(param));
                }
            };

            if !fct.returns.is_empty() {
                dump!(d, "returns");
                for p in &fct.returns {
                    d.indent(|d| d.dump_param(p));
                }
            };

            if !fct.modifies.is_empty() {
                let str_mods : Vec<ArcStr> = fct.modifies.iter().map(|p| d.str(*p)).collect();
                dump!(d, "modifies {}", str_mods.join(", "));
            };

            dump!(d, "executes");
            if let Some(ref block) = fct.block {
                d.indent(|d| d.dump_expr_block(block));
            }
        });
    }

    fn dump_param(&mut self, param: &Param) {
        dump!(
            self,
            "`{}` {} @ {} {}",
            param.data_type.to_string(self.interner),
            self.str(param.name),
            param.pos,
            param.id
        );
    }

    fn dump_type(&mut self, ty: &Type) {
        dump!(
            self,
            "type `{}` @ {} {}",
            ty.to_string(self.interner),
            ty.pos(),
            ty.id()
        );
    }

    fn dump_stmt(&mut self, stmt: &Stmt) {
        match *stmt {
            StmtAssert(ref ass) => self.dump_stmt_assert(ass),
            StmtAssume(ref ass) => self.dump_stmt_assume(ass),
            StmtCall(ref cal) => self.dump_stmt_call(cal),
            StmtHavoc(ref hav) => self.dump_stmt_havoc(hav),
            StmtReturn(ref ret) => self.dump_stmt_return(ret),
            StmtBreak(ref stmt) => self.dump_stmt_break(stmt),
            StmtContinue(ref stmt) => self.dump_stmt_continue(stmt),
            StmtExpr(ref expr) => self.dump_stmt_expr(expr),
            StmtVar(ref stmt) => self.dump_stmt_var(stmt),
            StmtWhile(ref stmt) => self.dump_stmt_while(stmt),
            StmtFor(ref stmt) => self.dump_stmt_for(stmt),
        }
    }

    fn dump_stmt_call(&mut self, stmt: &StmtCallType) {
        dump!(
            self,
            "call {} @ {} {}",
            self.str(stmt.func),
            stmt.pos,
            stmt.id
        );
        if !stmt.rets.is_empty() {
            let str_rets : Vec<ArcStr> = stmt.rets.iter().map(|p| self.str(*p)).collect();
            self.indent(|d| dump!(d, "into {}",  str_rets.join(", ")));
        };
        if !stmt.args.is_empty() {
            self.indent(|d| { 
                dump!(d, "with args");
                d.indent(|d| {
                    for arg in &stmt.args {
                        d.dump_expr(arg);
                    }
                });
            });
        };
    }

    fn dump_stmt_havoc(&mut self, stmt: &StmtHavocType) {
        dump!(
            self,
            "havoc {} @ {} {}",
            self.str(stmt.name),
            stmt.pos,
            stmt.id
        );
    }

    fn dump_stmt_var(&mut self, stmt: &StmtVarType) {
        dump!(
            self,
            "let {} @ {} {}",
            self.str(stmt.name),
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            dump!(d, "type");
            d.indent(|d| {
                if let Some(ref ty) = stmt.data_type {
                    d.dump_type(ty);
                } else {
                    dump!(d, "<no type given>");
                }
            });

            dump!(d, "expr");
            d.indent(|d| {
                if let Some(ref expr) = stmt.expr {
                    d.dump_expr(expr);
                } else {
                    dump!(d, "<no expr given>");
                }
            });
        });
    }

    fn dump_stmt_assume(&mut self, stmt: &StmtAssumeType) {
        dump!(
            self,
            "assume @ {} {}",
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            let ref expr = stmt.expr;
            d.dump_expr(expr);
        });
    }

    fn dump_stmt_assert(&mut self, stmt: &StmtAssertType) {
        dump!(
            self,
            "assert @ {} {}",
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            let ref expr = stmt.expr;
            d.dump_expr(expr);
        });
    }

    fn dump_stmt_for(&mut self, stmt: &StmtForType) {
        dump!(self, "for @ {} {}", stmt.pos, stmt.id);

        self.indent(|d| {
            dump!(d, "name {:?}", stmt.name);
            dump!(d, "cond");
            d.indent(|d| {
                d.dump_expr(&stmt.expr);
            });
            dump!(d, "body");
            d.indent(|d| {
                d.dump_stmt(&stmt.block);
            });
        });
    }

    fn dump_stmt_while(&mut self, stmt: &StmtWhileType) {
        dump!(self, "while @ {} {}", stmt.pos, stmt.id);

        self.indent(|d| {
            dump!(d, "cond");
            d.indent(|d| {
                d.dump_expr(&stmt.cond);
            });

            dump!(d, "body");
            d.indent(|d| {
                d.dump_stmt(&stmt.block);
            });
        });
    }

    fn dump_stmt_expr(&mut self, stmt: &StmtExprType) {
        self.dump_expr(&stmt.expr);
    }

    fn dump_stmt_return(&mut self, ret: &StmtReturnType) {
        dump!(self, "return @ {} {}", ret.pos, ret.id);

        self.indent(|d| {
            if let Some(ref expr) = ret.expr {
                d.dump_expr(expr);
            } else {
                dump!(d, "<nothing>");
            }
        });
    }

    fn dump_stmt_break(&mut self, stmt: &StmtBreakType) {
        dump!(self, "break @ {} {}", stmt.pos, stmt.id);
    }

    fn dump_stmt_continue(&mut self, stmt: &StmtContinueType) {
        dump!(self, "continue @ {} {}", stmt.pos, stmt.id);
    }

    fn dump_expr(&mut self, expr: &Expr) {
        match *expr {
            ExprUn(ref un) => self.dump_expr_un(un),
            ExprBin(ref bin) => self.dump_expr_bin(bin),
            ExprDot(ref field) => self.dump_expr_dot(field),
            ExprLitChar(ref lit) => self.dump_expr_lit_char(lit),
            ExprLitInt(ref lit) => self.dump_expr_lit_int(lit),
            ExprLitFloat(ref lit) => self.dump_expr_lit_float(lit),
            ExprLitStr(ref lit) => self.dump_expr_lit_str(lit),
            ExprTemplate(ref tmpl) => self.dump_expr_template(tmpl),
            ExprLitBool(ref lit) => self.dump_expr_lit_bool(lit),
            ExprIdent(ref ident) => self.dump_expr_ident(ident),
            ExprCall(ref call) => self.dump_expr_call(call),
            ExprTypeParam(ref expr) => self.dump_expr_type_param(expr),
            ExprPath(ref path) => self.dump_expr_path(path),
            ExprDelegation(ref call) => self.dump_expr_delegation(call),
            ExprConv(ref expr) => self.dump_expr_conv(expr),
            ExprLambda(ref expr) => self.dump_expr_lambda(expr),
            ExprBlock(ref expr) => self.dump_expr_block(expr),
            ExprIf(ref expr) => self.dump_expr_if(expr),
            ExprTuple(ref expr) => self.dump_expr_tuple(expr),
        }
    }

    fn dump_expr_block(&mut self, block: &ExprBlockType) {
        dump!(
            self,
            "block ({} statement(s)) @ {} {}",
            block.stmts.len(),
            block.pos,
            block.id
        );

        self.indent(|d| {
            for stmt in &block.stmts {
                d.dump_stmt(stmt);
            }
        });

        dump!(self, "block end");
    }

    fn dump_init(&mut self, block: &Init) {
        self.indent(|d| {
            dump!(d, "init @ {} {}", block.pos, block.id);
            if let Some(ref block) = block.block {
                d.indent(|d| d.dump_expr_block(block));
            }
        });
    }

    fn dump_next(&mut self, block: &Next) {
        self.indent(|d| {
            dump!(d, "next @ {} {}", block.pos, block.id);
            if let Some(ref block) = block.block {
                d.indent(|d| d.dump_expr_block(block));
            }
        });
    }

    fn dump_control(&mut self, block: &Control) {
        dump!(self, "control @ {} {}", block.pos, block.id);
        if let Some(ref block) = block.block {
            self.indent(|d| d.dump_expr_block(block));
        }
    }

    fn dump_expr_if(&mut self, expr: &ExprIfType) {
        dump!(self, "if @ {} {}", expr.pos, expr.id);

        self.indent(|d| {
            d.indent(|d| {
                d.dump_expr(&expr.cond);
            });
            dump!(d, "then");
            d.indent(|d| {
                d.dump_expr(&expr.then_block);
            });
            dump!(d, "else");
            d.indent(|d| {
                d.dump_expr(&expr.then_block);
            });
        });
    }

    fn dump_expr_conv(&mut self, expr: &ExprConvType) {
        self.indent(|d| d.dump_expr(&expr.object));
        let op = if expr.is { "is" } else { "as" };
        dump!(self, "{} @ {} {}", op, expr.pos, expr.id);
        self.indent(|d| d.dump_type(&expr.data_type));
    }

    fn dump_expr_delegation(&mut self, expr: &ExprDelegationType) {
        dump!(self, "super @ {} {}", expr.pos, expr.id);

        self.indent(|d| {
            for arg in &expr.args {
                d.dump_expr(arg);
            }
        });
    }

    fn dump_expr_lit_char(&mut self, lit: &ExprLitCharType) {
        dump!(
            self,
            "lit char {} {} @ {} {}",
            lit.value,
            lit.value as u32,
            lit.pos,
            lit.id
        );
    }

    fn dump_expr_lit_int(&mut self, lit: &ExprLitIntType) {
        dump!(self, "lit int {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_lit_float(&mut self, lit: &ExprLitFloatType) {
        dump!(self, "lit float {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_lit_str(&mut self, lit: &ExprLitStrType) {
        dump!(self, "lit string {:?} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_template(&mut self, tmpl: &ExprTemplateType) {
        dump!(self, "template @ {} {}", tmpl.pos, tmpl.id);
        self.indent(|d| {
            for part in &tmpl.parts {
                d.dump_expr(part)
            }
        });
    }

    fn dump_expr_lit_bool(&mut self, lit: &ExprLitBoolType) {
        dump!(self, "lit bool {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_ident(&mut self, ident: &ExprIdentType) {
        dump!(
            self,
            "ident {} @ {} {}",
            self.str(ident.name),
            ident.pos,
            ident.id
        );
    }

    fn dump_expr_un(&mut self, expr: &ExprUnType) {
        dump!(self, "unary {:?} @ {} {}", expr.op, expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.opnd));
    }

    fn dump_expr_bin(&mut self, expr: &ExprBinType) {
        dump!(self, "binary {:?} @ {} {}", expr.op, expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.lhs));
        self.indent(|d| d.dump_expr(&expr.rhs));
    }

    fn dump_expr_lambda(&mut self, expr: &ExprLambdaType) {
        dump!(self, "lambda @ {} {}", expr.pos, expr.id);
        self.indent(|d| d.dump_stmt(&expr.block));
    }

    fn dump_expr_tuple(&mut self, expr: &ExprTupleType) {
        dump!(self, "tuple @ {} {}", expr.pos, expr.id);
        self.indent(|d| {
            for expr in &expr.values {
                d.dump_expr(expr);
            }
        });
    }

    fn dump_expr_dot(&mut self, expr: &ExprDotType) {
        self.indent(|d| d.dump_expr(&expr.rhs));
        dump!(self, "dot @ {} {}", expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.lhs));
    }

    fn dump_expr_path(&mut self, expr: &ExprPathType) {
        self.indent(|d| d.dump_expr(&expr.rhs));
        dump!(self, "path (::) @ {} {}", expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.lhs));
    }

    fn dump_expr_call(&mut self, expr: &ExprCallType) {
        dump!(self, "function application @ {} {}", expr.pos, expr.id);

        self.indent(|d| {
            d.indent(|d| {
                d.dump_expr(&expr.callee);
                d.indent(|d| {
                    for arg in &expr.args {
                        d.dump_expr(arg);
                    }
                })
            });
        });
    }

    fn dump_expr_type_param(&mut self, expr: &ExprTypeParamType) {
        dump!(self, "type param @ {} {}", expr.pos, expr.id);

        self.indent(|d| {
            dump!(d, "callee");
            d.indent(|d| d.dump_expr(&expr.callee));

            for arg in &expr.args {
                d.dump_type(arg);
            }
        });
    }

    fn indent<F>(&mut self, fct: F)
    where
        F: Fn(&mut AstDumper) -> (),
    {
        let old = self.indent;
        self.indent = old + 1;

        fct(self);

        self.indent = old;
    }

    fn str(&self, name: Name) -> ArcStr {
        self.interner.str(name)
    }
}
