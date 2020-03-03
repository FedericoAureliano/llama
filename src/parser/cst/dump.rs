use crate::parser::cst::*;
use crate::parser::interner::{ArcStr, Interner, Name};

macro_rules! dump {
    ($self_:ident, $($message:tt)*) => {{
        for _ in 0..($self_.indent*2) {
            print!(" ");
        }

        println!($($message)*);
    }};
}

pub fn dump(cst: &Cst, interner: &Interner) {
    let mut dumper = CstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_cst(cst);
}

pub fn dump_procedure(prcd: &ProcedureDeclCst, interner: &Interner) {
    let mut dumper = CstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_procedure(prcd);
}

pub fn dump_expr<'a>(expr: &'a ExprCst, interner: &'a Interner) {
    let mut dumper = CstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_expr(expr);
}

pub fn dump_stmt<'a>(stmt: &'a StmtCst, interner: &'a Interner) {
    let mut dumper = CstDumper {
        interner,
        indent: 0,
    };

    dumper.dump_stmt(stmt);
}

struct CstDumper<'a> {
    interner: &'a Interner,
    indent: u32,
}

impl<'a> CstDumper<'a> {
    fn dump_cst(&mut self, cst: &Cst) {
        for m in &cst.modules {
            self.dump_module(m)
        }
    }

    fn dump_module(&mut self, modu: &ModuleCst) {
        dump!(
            self,
            "module: {} @ {} {}",
            self.str(modu.name),
            modu.pos,
            modu.id
        );

        self.indent(|d| {
            if !modu.types.is_empty() {
                dump!(d, "types:");
                d.indent(|d| {
                    for typ in &modu.types {
                        d.dump_type_decl(typ);
                    }
                });
            };

            if !modu.inputs.is_empty() {
                dump!(d, "inputs:");
                d.indent(|d| {
                    for input in &modu.inputs {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.outputs.is_empty() {
                dump!(d, "outputs:");
                d.indent(|d| {
                    for input in &modu.outputs {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.variables.is_empty() {
                dump!(d, "variables:");
                d.indent(|d| {
                    for var in &modu.variables {
                        d.dump_field(var);
                    }
                });
            };

            if !modu.constants.is_empty() {
                dump!(d, "constants:");
                d.indent(|d| {
                    for input in &modu.constants {
                        d.dump_field(input);
                    }
                });
            };

            if !modu.macros.is_empty() {
                dump!(d, "definitions:");
                d.indent(|d| {
                    for func in &modu.macros {
                        d.dump_definition(func);
                    }
                });
            };

            if !modu.functions.is_empty() {
                dump!(d, "functions:");
                d.indent(|d| {
                    for func in &modu.functions {
                        d.dump_function(func);
                    }
                });
            };

            if !modu.procedures.is_empty() {
                dump!(d, "procedures:");
                d.indent(|d| {
                    for prcd in &modu.procedures {
                        d.dump_procedure(prcd);
                    }
                });
            };

            if modu.init.is_some() || modu.next.is_some() {
                dump!(d, "transition system:");
            };

            if let Some(ref init) = &modu.init {
                d.indent(|d| d.dump_init(init));
            };

            if let Some(ref next) = &modu.next {
                d.indent(|d| d.dump_next(next));
            };

            if !modu.theorems.is_empty() || !modu.lemmas.is_empty() {
                dump!(d, "specification:");
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

    fn dump_field(&mut self, field: &FieldDeclCst) {
        dump!(
            self,
            "`{}` {} @ {} {}",
            field.data_type.to_string(self.interner),
            self.str(field.name),
            field.pos,
            field.id
        );
        if let Some(e) = &field.expr {
            self.indent(|d| {
                d.dump_expr(e);
            })
        }
    }

    fn dump_property(&mut self, inv: &PropertyDeclCst) {
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

    fn dump_definition(&mut self, fct: &MacroDeclCst) {
        dump!(self, "{} @ {} {}", self.str(fct.name), fct.pos, fct.id);

        self.indent(|d| {
            dump!(d, "parameters:");
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
                dump!(d, "return type: `{}` @ {} {}", name, pos, id);
            };

            dump!(d, "body:");
            d.indent(|d| {
                d.dump_expr(&fct.expr);
            })
        });
    }

    fn dump_function(&mut self, fct: &FunctionDeclCst) {
        dump!(self, "{} @ {} {}", self.str(fct.name), fct.pos, fct.id);

        self.indent(|d| {
            dump!(d, "to synthesize = {}", fct.to_synthesize);
            dump!(d, "parameters:");
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
                dump!(d, "return type: `{}` @ {} {}", name, pos, id);
            };
        });
    }

    fn dump_procedure(&mut self, fct: &ProcedureDeclCst) {
        dump!(self, "{} @ {} {}", self.str(fct.name), fct.pos, fct.id);

        self.indent(|d| {

            if !fct.params.is_empty() {
                dump!(d, "parameters:");
                for param in &fct.params {
                    d.indent(|d| d.dump_param(param));
                }
            };

            if !fct.returns.is_empty() {
                dump!(d, "returns:");
                for p in &fct.returns {
                    d.indent(|d| d.dump_param(p));
                }
            };

            if !fct.modifies.is_empty() {
                let str_mods : Vec<ArcStr> = fct.modifies.iter().map(|p| d.str(p.name)).collect();
                dump!(d, "modifies: {}", str_mods.join(", "));
            };

            if !fct.requires.is_empty() {
                dump!(d, "requires:");
                for p in &fct.requires {
                    d.indent(|d| d.dump_stmt_assume(p));
                }
            };

            if !fct.ensures.is_empty() {
                dump!(d, "ensures");
                for p in &fct.ensures {
                    d.indent(|d| d.dump_stmt_assert(p));
                }
            };

            dump!(d, "executes:");
            if let Some(ref block) = fct.block {
                d.indent(|d| d.dump_expr_block(block));
            }
        });
    }

    fn dump_param(&mut self, param: &ParamCst) {
        dump!(
            self,
            "`{}` {} @ {} {}",
            param.data_type.to_string(self.interner),
            self.str(param.name),
            param.pos,
            param.id
        );
    }

    fn dump_type_decl(&mut self, ty: &TypeDeclCst) {
        dump!(
            self,
            "{} @ {} {}",
            ty.to_string(self.interner),
            ty.pos(),
            ty.id()
        );
    }

    fn dump_type_ident(&mut self, ty: &TypeIdentCst) {
        dump!(
            self,
            "{} @ {} {}",
            ty.to_string(self.interner),
            ty.pos(),
            ty.id()
        );
    }

    fn dump_stmt(&mut self, stmt: &StmtCst) {
        match *stmt {
            StmtCst::Induction(ref sim) => self.dump_stmt_induction(sim),
            StmtCst::Simulate(ref sim) => self.dump_stmt_simulate(sim),
            StmtCst::Assert(ref ass) => self.dump_stmt_assert(ass),
            StmtCst::Assume(ref ass) => self.dump_stmt_assume(ass),
            StmtCst::Call(ref cal) => self.dump_stmt_call(cal),
            StmtCst::Havoc(ref hav) => self.dump_stmt_havoc(hav),
            StmtCst::Expr(ref expr) => self.dump_stmt_expr(expr),
            StmtCst::Var(ref stmt) => self.dump_stmt_var(stmt),
            StmtCst::While(ref stmt) => self.dump_stmt_while(stmt),
        }
    }

    fn dump_stmt_call(&mut self, stmt: &CallStmtCst) {
        dump!(
            self,
            "call {} @ {} {}",
            self.str(stmt.func),
            stmt.pos,
            stmt.id
        );
        if !stmt.rets.is_empty() {
            let str_rets : Vec<ArcStr> = stmt.rets.iter().map(|p| self.str(p.name)).collect();
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

    fn dump_stmt_havoc(&mut self, stmt: &HavocStmtCst) {
        dump!(
            self,
            "havoc {} @ {} {}",
            self.str(stmt.name),
            stmt.pos,
            stmt.id
        );
    }

    fn dump_stmt_var(&mut self, stmt: &VarStmtCst) {
        dump!(
            self,
            "let {} @ {} {}",
            self.str(stmt.name),
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            dump!(d, "type:");
            d.indent(|d| {
                if let Some(ref ty) = stmt.data_type {
                    d.dump_type_ident(ty);
                } else {
                    dump!(d, "<no type given>");
                }
            });

            dump!(d, "expr:");
            d.indent(|d| {
                if let Some(ref expr) = stmt.expr {
                    d.dump_expr(expr);
                } else {
                    dump!(d, "<no expr given>");
                }
            });
        });
    }

    fn dump_stmt_assume(&mut self, stmt: &PredicateStmtCst) {
        dump!(
            self,
            "assume: @ {} {}",
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            let ref expr = stmt.expr;
            d.dump_expr(expr);
        });
    }

    fn dump_stmt_assert(&mut self, stmt: &PredicateStmtCst) {
        dump!(
            self,
            "assert: @ {} {}",
            stmt.pos,
            stmt.id
        );

        self.indent(|d| {
            let ref expr = stmt.expr;
            d.dump_expr(expr);
        });
    }

    fn dump_stmt_simulate(&mut self, stmt: &SimulateStmtCst) {
        dump!(
            self,
            "simulate {} {} @ {} {}",
            stmt.steps,
            if stmt.steps > 1 {"steps"} else {"step"},
            stmt.pos,
            stmt.id,
        );
    }

    fn dump_stmt_induction(&mut self, stmt: &InductionStmtCst) {
        dump!(
            self,
            "induction {} {} @ {} {}",
            stmt.steps,
            if stmt.steps > 1 {"steps"} else {"step"},
            stmt.pos,
            stmt.id,
        );
    }

    fn dump_stmt_while(&mut self, stmt: &WhileStmtCst) {
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

    fn dump_stmt_expr(&mut self, stmt: &ExprStmtCst) {
        self.dump_expr(&stmt.expr);
    }

    fn dump_expr(&mut self, expr: &ExprCst) {
        match *expr {
            ExprCst::Un(ref un) => self.dump_expr_un(un),
            ExprCst::Bin(ref bin) => self.dump_expr_bin(bin),
            ExprCst::Dot(ref field) => self.dump_expr_dot(field),
            ExprCst::LitInt(ref lit) => self.dump_expr_lit_int(lit),
            ExprCst::LitFloat(ref lit) => self.dump_expr_lit_float(lit),
            ExprCst::LitBitVec(ref lit) => self.dump_expr_lit_bitvec(lit),
            ExprCst::LitBool(ref lit) => self.dump_expr_lit_bool(lit),
            ExprCst::Ident(ref ident) => self.dump_expr_ident(ident),
            ExprCst::Call(ref call) => self.dump_expr_call(call),
            ExprCst::Extract(ref deref) => self.dump_expr_extract(deref),
            ExprCst::Block(ref expr) => self.dump_expr_block(expr),
            ExprCst::If(ref expr) => self.dump_expr_if(expr),
            ExprCst::Tuple(ref expr) => self.dump_expr_tuple(expr),
        }
    }

    fn dump_expr_block(&mut self, block: &BlockCst) {
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

    fn dump_init(&mut self, block: &TransitionSystemBlockCst) {
        self.indent(|d| {
            dump!(d, "init @ {} {}", block.pos, block.id);
            d.indent(|d| d.dump_expr_block(&*block.block));
        });
    }

    fn dump_next(&mut self, block: &TransitionSystemBlockCst) {
        self.indent(|d| {
            dump!(d, "next @ {} {}", block.pos, block.id);
            d.indent(|d| d.dump_expr_block(&*block.block));
        });
    }

    fn dump_control(&mut self, block: &TransitionSystemBlockCst) {
        dump!(self, "control @ {} {}", block.pos, block.id);
        self.indent(|d| d.dump_expr_block(&*block.block));
    }

    fn dump_expr_if(&mut self, expr: &IfExprCst) {
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

    fn dump_expr_lit_int(&mut self, lit: &LitIntExprCst) {
        dump!(self, "lit int {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_lit_float(&mut self, lit: &LitFloatExprCst) {
        dump!(self, "lit float {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_lit_bitvec(&mut self, lit: &LitBitVecExprCst) {
        let mut val : Vec<String> = lit.value.iter().map(|v| format!("{}", if v {1} else {0})).collect();
        val.reverse();
        dump!(self, "lit bitvec {} @ {} {}", val.join(""), lit.pos, lit.id);
    }

    fn dump_expr_lit_bool(&mut self, lit: &LitBoolExprCst) {
        dump!(self, "lit bool {} @ {} {}", lit.value, lit.pos, lit.id);
    }

    fn dump_expr_ident(&mut self, ident: &NameCst) {
        dump!(
            self,
            "ident {} @ {} {}",
            self.str(ident.name),
            ident.pos,
            ident.id
        );
    }

    fn dump_expr_un(&mut self, expr: &UnExprCst) {
        dump!(self, "unary {:?} @ {} {}", expr.op, expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.opnd));
    }

    fn dump_expr_bin(&mut self, expr: &BinExprCst) {
        dump!(self, "binary {:?} @ {} {}", expr.op, expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.lhs));
        self.indent(|d| d.dump_expr(&expr.rhs));
    }

    fn dump_expr_tuple(&mut self, expr: &TupleExprCst) {
        dump!(self, "tuple @ {} {}", expr.pos, expr.id);
        self.indent(|d| {
            for expr in &expr.values {
                d.dump_expr(expr);
            }
        });
    }

    fn dump_expr_dot(&mut self, expr: &DotExprCst) {
        self.indent(|d| d.dump_expr(&expr.rhs));
        dump!(self, "dot @ {} {}", expr.pos, expr.id);
        self.indent(|d| d.dump_expr(&expr.lhs));
    }

    fn dump_expr_extract(&mut self, expr: &ExtractExprCst) {
        dump!(self, "extract @ {} {}", expr.pos, expr.id);

        self.indent(|d| {
            d.indent(|d| {
                d.dump_expr(&expr.array);
                d.indent(|d| {
                    for arg in &expr.args {
                        d.dump_expr(arg);
                    }
                })
            });
        });
    }

    fn dump_expr_call(&mut self, expr: &CallExprCst) {
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

    fn indent<F>(&mut self, fct: F)
    where
        F: Fn(&mut CstDumper) -> (),
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
