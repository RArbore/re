use arena::{Arena, BrandedArenaId};

use crate::expr::{Expr, ExprId};
use crate::interner::{IdentifierId, StringInterner};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token {
    LeftParen,
    RightParen,
    Identifier(IdentifierId),
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
}

fn lex<'a, 'b>(text: &str, arena: &'b mut Arena<'a>, interner: &mut StringInterner) -> &'a [Token] {
    arena.collect_fn(|pf| {
        let mut iden_buffer = String::new();
        let mut handle_iden =
            |iden_buffer: &mut String, pf: &mut dyn FnMut(Token) -> BrandedArenaId<Token>| {
                if let Ok(lit) = iden_buffer.parse::<bool>() {
                    pf(Token::BoolLit(lit));
                } else if let Ok(lit) = iden_buffer.parse::<i64>() {
                    pf(Token::FixedLit(lit));
                } else if let Ok(lit) = iden_buffer.parse::<f64>() {
                    pf(Token::FloatLit(lit));
                } else {
                    let id = interner.intern(&iden_buffer);
                    pf(Token::Identifier(id));
                }
                iden_buffer.clear();
            };
        for c in text.chars() {
            if c.is_whitespace() {
                if !iden_buffer.is_empty() {
                    handle_iden(&mut iden_buffer, pf);
                }
            } else if c == '(' {
                if !iden_buffer.is_empty() {
                    handle_iden(&mut iden_buffer, pf);
                }
                pf(Token::LeftParen);
            } else if c == ')' {
                if !iden_buffer.is_empty() {
                    handle_iden(&mut iden_buffer, pf);
                }
                pf(Token::RightParen);
            } else {
                iden_buffer.push(c);
            }
        }
        if !iden_buffer.is_empty() {
            handle_iden(&mut iden_buffer, pf);
        }
    })
}

pub fn parse<'a, 'b>(
    text: &str,
    arena: &'b mut Arena<'a>,
    interner: &mut StringInterner,
) -> &'a [ExprId<'a>] {
    let tokens = lex(text, arena, interner);
    let mut expr_stack: Vec<ExprId<'a>> = vec![];
    let mut paren_stack = vec![];

    let mut tokens = tokens.into_iter().peekable();
    while let Some(token) = tokens.next() {
        match token {
            Token::LeftParen => {
                paren_stack.push(expr_stack.len());
            }
            Token::RightParen => {
                let old_len = paren_stack.pop().expect("too many right parentheses");
                let exprs = arena.collect_fn(|pf| {
                    for expr in &expr_stack[old_len..] {
                        pf(*expr);
                    }
                });
                let list_expr = arena.alloc(Expr::List(exprs));
                expr_stack.truncate(old_len);
                expr_stack.push(list_expr);
            }
            Token::Identifier(id) => {
                expr_stack.push(arena.alloc(Expr::Identifier(*id)));
            }
            Token::BoolLit(lit) => {
                expr_stack.push(arena.alloc(Expr::BoolLit(*lit)));
            }
            Token::FixedLit(lit) => {
                expr_stack.push(arena.alloc(Expr::FixedLit(*lit)));
            }
            Token::FloatLit(lit) => {
                expr_stack.push(arena.alloc(Expr::FloatLit(*lit)));
            }
        }
    }

    assert!(paren_stack.is_empty(), "not enough right parentheses");
    arena.collect(expr_stack.into_iter())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::dump_exprs;

    #[test]
    fn simple_lex() {
        let mut buf = [0u64; 38];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 13];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn x y (+ x y)) (print (fn 42 24))";
        let tokens = lex(text, &mut arena, &mut interner);
        assert_eq!(
            tokens,
            &[
                Token::LeftParen,
                Token::Identifier(interner.intern("def")),
                Token::Identifier(interner.intern("fn")),
                Token::Identifier(interner.intern("x")),
                Token::Identifier(interner.intern("y")),
                Token::LeftParen,
                Token::Identifier(interner.intern("+")),
                Token::Identifier(interner.intern("x")),
                Token::Identifier(interner.intern("y")),
                Token::RightParen,
                Token::RightParen,
                Token::LeftParen,
                Token::Identifier(interner.intern("print")),
                Token::LeftParen,
                Token::Identifier(interner.intern("fn")),
                Token::FixedLit(42),
                Token::FixedLit(24),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn simple_parse() {
        let mut buf = [0u64; 200];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 13];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn x y (+ x y)) (print (fn 42 24))";
        let exprs = parse(text, &mut arena, &mut interner);
        let dumped_text = dump_exprs(exprs, &arena, &interner);
        assert_eq!(text, dumped_text);
    }
}
