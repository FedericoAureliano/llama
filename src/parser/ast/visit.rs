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

    fn visit_init(&mut self, m: &'v TransitionSystemBlock) {
        walk_init(self, m);
    }

    fn visit_next(&mut self, m: &'v TransitionSystemBlock) {
        walk_next(self, m);
    }

    fn visit_control(&mut self, m: &'v TransitionSystemBlock) {
        walk_control(self, m);
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

    fn visit_enum(&mut self, e: &'v Enum) {
        walk_enum(self, e);
    }
}

pub fn walk_ast<'v, V: Visitor<'v>>(v: &mut V, a: &'v Ast) {
    for f in &a.files {
        v.visit_file(f);
    }
}

pub fn walk_file<'v, V: Visitor<'v>>(v: &mut V, f: &'v File) {
    for m in &f.modules {
        v.visit_module(m)
    }
}

pub fn walk_module<'v, V: Visitor<'v>>(v: &mut V, m: &'v Module) {

    for t in &m.types {
        v.visit_type(t);
    }

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

pub fn walk_init<'v, V: Visitor<'v>>(v: &mut V, m: &'v TransitionSystemBlock) {
    for stmt in &m.block.stmts {
        v.visit_stmt(stmt);
    }
}

pub fn walk_next<'v, V: Visitor<'v>>(v: &mut V, m: &'v TransitionSystemBlock) {
    for stmt in &m.block.stmts {
        v.visit_stmt(stmt);
    }
}

pub fn walk_control<'v, V: Visitor<'v>>(v: &mut V, m: &'v TransitionSystemBlock) {
    for stmt in &m.block.stmts {
        v.visit_stmt(stmt);
    }
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
        BasicType(_) => {}

        TypeAlias(ref alias) => {
            v.visit_type(&alias.alias);
        }

        EnumType(ref e) => {
            v.visit_enum(e);
        }

        TupleType(ref tuple) => {
            for ty in &tuple.subtypes {
                v.visit_type(ty);
            }
        }
    }
}

pub fn walk_stmt<'v, V: Visitor<'v>>(v: &mut V, s: &'v Stmt) {
    match *s {
        // TODO: how to walk call, havoc, assume, assert, simulate?
        StmtInduction(_) => {}
        StmtSimulate(_) => {}
        StmtAssert(_) => {}
        StmtAssume(_) => {}
        StmtCall(_) => {}
        StmtHavoc(_) => {}
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
    }
}

pub fn walk_enum<'v, V: Visitor<'v>>(_v: &mut V, _e: &'v Enum) {
    // nothing to do
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

        ExprExtract(ref deref) => {
            v.visit_expr(&deref.array);

            for arg in &deref.args {
                v.visit_expr(arg);
            }
        }

        ExprDot(ref value) => {
            v.visit_expr(&value.lhs);
            v.visit_expr(&value.rhs);
        }

        ExprBlock(ref value) => {
            for stmt in &value.stmts {
                v.visit_stmt(stmt);
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
        ExprLitInt(_) => {}
        ExprLitFloat(_) => {}
        ExprLitBitVec(_) => {}
        ExprLitBool(_) => {}
        ExprIdent(_) => {}
    }
}
