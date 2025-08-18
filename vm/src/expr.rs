use arena::BrandedArenaId;

use crate::interner::IdentifierId;

type ExprId<'a> = BrandedArenaId<Expr<'a>>;

pub enum Expr<'a> {
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
    Apply(IdentifierId, &'a [ExprId<'a>]),
    Abstract(IdentifierId, &'a [IdentifierId], ExprId<'a>),
}
