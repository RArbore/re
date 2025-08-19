use arena::{Arena, BrandedArenaId};

use crate::interner::{IdentifierId, StringInterner};

pub type ParseExprId<'a> = BrandedArenaId<ParseExpr<'a>>;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParseExpr<'a> {
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
    Identifier(IdentifierId),
    List(&'a [ParseExprId<'a>]),
}

fn dump_parse_expr<'a, 'b>(
    s: &mut String,
    expr: ParseExprId<'a>,
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) {
    match arena.get(expr) {
        ParseExpr::BoolLit(lit) => *s += &format!("{}", lit),
        ParseExpr::FixedLit(lit) => *s += &format!("{}", lit),
        ParseExpr::FloatLit(lit) => *s += &format!("{}", lit),
        ParseExpr::Identifier(id) => *s += interner.get(*id),
        ParseExpr::List(exprs) => {
            *s += "(";
            if !exprs.is_empty() {
                dump_parse_expr(s, exprs[0], arena, interner);
                for expr in &exprs[1..] {
                    *s += " ";
                    dump_parse_expr(s, *expr, arena, interner);
                }
            }
            *s += ")";
        }
    }
}

pub fn dump_parse_exprs<'a, 'b>(
    exprs: &[ParseExprId<'a>],
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) -> String {
    let mut s = String::new();
    if !exprs.is_empty() {
        dump_parse_expr(&mut s, exprs[0], arena, interner);
        for expr in &exprs[1..] {
            s += " ";
            dump_parse_expr(&mut s, *expr, arena, interner);
        }
    }
    s
}

pub type AbstractExprId<'a> = BrandedArenaId<AbstractExpr<'a>>;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AbstractExpr<'a> {
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
    UseIdentifier(IdentifierId),
    Apply(AbstractExprId<'a>, &'a [AbstractExprId<'a>]),
    Abstract(&'a [IdentifierId], AbstractExprId<'a>),
    Let(IdentifierId, AbstractExprId<'a>, AbstractExprId<'a>),
    Define(IdentifierId, AbstractExprId<'a>),
    IfElse(AbstractExprId<'a>, AbstractExprId<'a>, AbstractExprId<'a>),
}

fn dump_abstract_expr<'a, 'b>(
    s: &mut String,
    expr: AbstractExprId<'a>,
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) {
    match arena.get(expr) {
        AbstractExpr::BoolLit(lit) => *s += &format!("{}", lit),
        AbstractExpr::FixedLit(lit) => *s += &format!("{}", lit),
        AbstractExpr::FloatLit(lit) => *s += &format!("{}", lit),
        AbstractExpr::UseIdentifier(id) => *s += interner.get(*id),
        AbstractExpr::Apply(func, args) => {
            *s += "(";
            dump_abstract_expr(s, *func, arena, interner);
            for expr in *args {
                *s += " ";
                dump_abstract_expr(s, *expr, arena, interner);
            }
            *s += ")";
        }
        AbstractExpr::Abstract(params, body) => {
            *s += "(";
            for param in *params {
                *s += interner.get(*param);
                *s += " ";
            }
            *s += ". ";
            dump_abstract_expr(s, *body, arena, interner);
            *s += ")";
        }
        AbstractExpr::Let(binder, binding, in_expr) => {
            *s += "(let ";
            *s += interner.get(*binder);
            *s += " ";
            dump_abstract_expr(s, *binding, arena, interner);
            *s += " ";
            dump_abstract_expr(s, *in_expr, arena, interner);
            *s += ")";
        }
        AbstractExpr::Define(binder, binding) => {
            *s += "(def ";
            *s += interner.get(*binder);
            *s += " ";
            dump_abstract_expr(s, *binding, arena, interner);
            *s += ")";
        }
        AbstractExpr::IfElse(cond, true_expr, false_expr) => {
            *s += "(? ";
            dump_abstract_expr(s, *cond, arena, interner);
            *s += " ";
            dump_abstract_expr(s, *true_expr, arena, interner);
            *s += " ";
            dump_abstract_expr(s, *false_expr, arena, interner);
            *s += ")";
        }
    }
}

pub fn dump_abstract_exprs<'a, 'b>(
    exprs: &[AbstractExprId<'a>],
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) -> String {
    let mut s = String::new();
    if !exprs.is_empty() {
        dump_abstract_expr(&mut s, exprs[0], arena, interner);
        for expr in &exprs[1..] {
            s += " ";
            dump_abstract_expr(&mut s, *expr, arena, interner);
        }
    }
    s
}
