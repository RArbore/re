use arena::BrandedArenaId;

use crate::interner::IdentifierId;

type ExprId<'a> = BrandedArenaId<Expr<'a>>;

pub enum Expr<'a> {
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
    Use(IdentifierId, &'a [ExprId<'a>]),
    Def(IdentifierId, &'a [IdentifierId], ExprId<'a>),
}
