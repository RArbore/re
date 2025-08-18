use arena::{Arena, BrandedArena};

use crate::expr::Expr;

pub fn parse<'a>(text: &str, arena: Arena<'a>) -> BrandedArena<'a, Expr<'a>> {
    todo!()
}
