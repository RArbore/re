use arena::{Arena, BrandedArenaId};

use crate::interner::{IdentifierId, StringInterner};

pub type ExprId<'a> = BrandedArenaId<Expr<'a>>;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Expr<'a> {
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
    Identifier(IdentifierId),
    List(&'a [ExprId<'a>]),
}

fn dump_expr<'a, 'b>(
    s: &mut String,
    expr: ExprId<'a>,
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) {
    match arena.get(expr) {
        Expr::BoolLit(lit) => *s += &format!("{}", lit),
        Expr::FixedLit(lit) => *s += &format!("{}", lit),
        Expr::FloatLit(lit) => *s += &format!("{}", lit),
        Expr::Identifier(id) => *s += interner.get(*id),
        Expr::List(exprs) => {
            *s += "(";
            if !exprs.is_empty() {
                dump_expr(s, exprs[0], arena, interner);
                for expr in &exprs[1..] {
                    *s += " ";
                    dump_expr(s, *expr, arena, interner);
                }
            }
            *s += ")";
        }
    }
}

pub fn dump_exprs<'a, 'b>(
    exprs: &[ExprId<'a>],
    arena: &'b Arena<'a>,
    interner: &StringInterner,
) -> String {
    let mut s = String::new();
    if !exprs.is_empty() {
        dump_expr(&mut s, exprs[0], arena, interner);
        for expr in &exprs[1..] {
            s += " ";
            dump_expr(&mut s, *expr, arena, interner);
        }
    }
    s
}
