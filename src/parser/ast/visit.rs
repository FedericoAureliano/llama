use crate::parser::ast::*;
use crate::parser::ast::Expr::*;
use crate::parser::ast::Stmt::*;
use crate::parser::ast::Type::*;

pub trait Visitor<'v>: Sized {
    fn visit_ast(&mut self, a: &'v Ast) {
        walk_ast(self, a);
    }

    fn visit_file(&mut self, a: &'v File) {
        walk_file(self, a);
    }

    fn visit_module(&mut self, m: &'v Module) {
        walk_module(self, m);
    }

    fn visit_init(&mut self, m: &'v Init) {
        walk_init(self, m);
    }

    fn visit_next(&mut self, m: &'v Next) {
        walk_next(self, m);
    }

    fn visit_control(&mut self, m: &'v Control) {
        walk_control(self, m);
    }

    fn visit_enum(&mut self, e: &'v Enum) {
        walk_enum(self, e);
    }

    fn visit_method(&mut self, m: &'v Procedure) {
        walk_procedure(self, m);
    }

    fn visit_field(&mut self, p: &'v Field) {
        walk_field(self, p);
    }

    fn visit_procedure(&mut self, f: &'v Procedure) {
        walk_procedure(self, f);
    }

    fn visit_param(&mut self, p: &'v Param) {
        walk_param(self, p);
    }

    fn visit_return(&mut self, p: &'v Param) {
        walk_return(self, p);
    }

    fn visit_type(&mut self, t: &'v Type) {
        walk_type(self, t);
    }

    fn visit_stmt(&mut self, s: &'v Stmt) {
        walk_stmt(self, s);
    }

    fn visit_expr(&mut self, e: &'v Expr) {
        walk_expr(self, e);
    }
}

pub fn walk_ast<'v, V: Visitor<'v>>(v: &mut V, a: &'v Ast) {
    for f in &a.files {
        v.visit_file(f);
    }
}

pub fn walk_file<'v, V: Visitor<'v>>(v: &mut V, f: &'v File) {
    for e in &f.elements {
        match *e {
            ElemProcedure(ref f) => v.visit_procedure(f),
            ElemModule(ref m) => v.visit_module(m),
            ElemEnum(ref e) => v.visit_enum(e),
            ElemInit(ref e) => v.visit_init(e),
            ElemNext(ref e) => v.visit_next(e),
            ElemControl(ref e) => v.visit_control(e),
        }
    }
}

pub fn walk_module<'v, V: Visitor<'v>>(v: &mut V, m: &'v Module) {
    for f in &m.inputs {
        v.visit_field(f);
    }

    for f in &m.variables {
        v.visit_field(f);
    }

    for m in &m.procedures {
        v.visit_method(m);
    }

    // TODO: visit specs
    // TODO: visit init
    // TODO: visit next
    // TODO: visit control
}

pub fn walk_init<'v, V: Visitor<'v>>(v: &mut V, m: &'v Init) {
    if let Some(ref block) = m.block {
        for stmt in &block.stmts {
            v.visit_stmt(stmt);
        }

        if let Some(ref value) = block.expr {
            v.visit_expr(value);
        }
    }
}

pub fn walk_next<'v, V: Visitor<'v>>(v: &mut V, m: &'v Next) {
    if let Some(ref block) = m.block {
        for stmt in &block.stmts {
            v.visit_stmt(stmt);
        }

        if let Some(ref value) = block.expr {
            v.visit_expr(value);
        }
    }
}

pub fn walk_control<'v, V: Visitor<'v>>(v: &mut V, m: &'v Control) {
    if let Some(ref block) = m.block {
        for stmt in &block.stmts {
            v.visit_stmt(stmt);
        }

        if let Some(ref value) = block.expr {
            v.visit_expr(value);
        }
    }
}

pub fn walk_enum<'v, V: Visitor<'v>>(_v: &mut V, _e: &'v Enum) {
    // nothing to do
}

pub fn walk_field<'v, V: Visitor<'v>>(v: &mut V, f: &'v Field) {
    v.visit_type(&f.data_type);
}

pub fn walk_procedure<'v, V: Visitor<'v>>(v: &mut V, f: &'v Procedure) {
    for p in &f.params {
        v.visit_param(p);
    }

    for p in &f.returns {
        v.visit_return(p);
    }

    if let Some(ref block) = f.block {
        for stmt in &block.stmts {
            v.visit_stmt(stmt);
        }

        if let Some(ref value) = block.expr {
            v.visit_expr(value);
        }
    }
}

pub fn walk_param<'v, V: Visitor<'v>>(v: &mut V, p: &'v Param) {
    v.visit_type(&p.data_type);
}

pub fn walk_return<'v, V: Visitor<'v>>(v: &mut V, p: &'v Param) {
    v.visit_type(&p.data_type);
}

pub fn walk_type<'v, V: Visitor<'v>>(v: &mut V, t: &'v Type) {
    match *t {
        TypeBasic(_) => {}
        TypeTuple(ref tuple) => {
            for ty in &tuple.subtypes {
                v.visit_type(ty);
            }
        }

        TypeLambda(ref fct) => {
            for ty in &fct.params {
                v.visit_type(ty);
            }

            v.visit_type(&fct.ret);
        }
    }
}

pub fn walk_stmt<'v, V: Visitor<'v>>(v: &mut V, s: &'v Stmt) {
    match *s {
        StmtVar(ref value) => {
            if let Some(ref ty) = value.data_type {
                v.visit_type(ty);
            }

            if let Some(ref e) = value.expr {
                v.visit_expr(e);
            }
        }

        StmtFor(ref value) => {
            v.visit_expr(&value.expr);
            v.visit_stmt(&value.block);
        }

        StmtWhile(ref value) => {
            v.visit_expr(&value.cond);
            v.visit_stmt(&value.block);
        }

        StmtExpr(ref value) => {
            v.visit_expr(&value.expr);
        }

        StmtReturn(ref value) => {
            if let Some(ref e) = value.expr {
                v.visit_expr(e);
            }
        }
        StmtBreak(_) => {}
        StmtContinue(_) => {}
    }
}

pub fn walk_expr<'v, V: Visitor<'v>>(v: &mut V, e: &'v Expr) {
    match *e {
        ExprUn(ref value) => {
            v.visit_expr(&value.opnd);
        }

        ExprBin(ref value) => {
            v.visit_expr(&value.lhs);
            v.visit_expr(&value.rhs);
        }

        ExprCall(ref call) => {
            v.visit_expr(&call.callee);

            for arg in &call.args {
                v.visit_expr(arg);
            }
        }

        ExprTypeParam(ref expr) => {
            v.visit_expr(&expr.callee);

            for arg in &expr.args {
                v.visit_type(arg);
            }
        }

        ExprPath(ref path) => {
            v.visit_expr(&path.lhs);
            v.visit_expr(&path.rhs);
        }

        ExprDelegation(ref call) => {
            for arg in &call.args {
                v.visit_expr(arg);
            }
        }

        ExprDot(ref value) => {
            v.visit_expr(&value.lhs);
            v.visit_expr(&value.rhs);
        }

        ExprConv(ref value) => {
            v.visit_expr(&value.object);
            v.visit_type(&value.data_type);
        }

        ExprLambda(ref value) => {
            for param in &value.params {
                v.visit_type(&param.data_type);
            }

            if let Some(ref ret) = value.ret {
                v.visit_type(ret);
            }

            v.visit_stmt(&value.block);
        }

        ExprBlock(ref value) => {
            for stmt in &value.stmts {
                v.visit_stmt(stmt);
            }

            if let Some(ref expr) = value.expr {
                v.visit_expr(expr);
            }
        }

        ExprTemplate(ref value) => {
            for part in &value.parts {
                v.visit_expr(part);
            }
        }

        ExprIf(ref value) => {
            v.visit_expr(&value.cond);
            v.visit_expr(&value.then_block);

            if let Some(ref b) = value.else_block {
                v.visit_expr(b);
            }
        }

        ExprTuple(ref value) => {
            for expr in &value.values {
                v.visit_expr(expr);
            }
        }
        ExprLitChar(_) => {}
        ExprLitInt(_) => {}
        ExprLitFloat(_) => {}
        ExprLitStr(_) => {}
        ExprLitBool(_) => {}
        ExprIdent(_) => {}
    }
}
