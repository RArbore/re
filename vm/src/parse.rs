use arena::{Arena, BrandedArenaId};

use crate::expr::Expr;
use crate::interner::{IdentifierId, StringInterner};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token {
    Define,
    LeftParen,
    RightParen,
    Identifier(IdentifierId),
    BoolLit(bool),
    FixedLit(i64),
    FloatLit(f64),
}

pub fn lex<'a, 'b>(
    text: &str,
    arena: &'b mut Arena<'a>,
    interner: &mut StringInterner,
) -> &'b [Token] {
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
                } else if iden_buffer == "def" {
                    pf(Token::Define);
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

pub fn parse<'a>(text: &str, arena: &mut Arena<'a>, interner: StringInterner) {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_lex() {
        let mut buf = [0u64; 38];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 10];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn x y (+ x y)) (print (fn 3.141 6.283))";
        let tokens = lex(text, &mut arena, &mut interner);
        assert_eq!(
            tokens,
            &[
                Token::LeftParen,
                Token::Define,
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
                Token::FloatLit(3.141),
                Token::FloatLit(6.283),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }
}
