use arena::{Arena, BrandedArenaId};

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
    Do(&'a [AbstractExprId<'a>]),
}

impl<'a> AbstractExpr<'a> {
    pub fn try_bool(&self) -> Option<bool> {
        if let AbstractExpr::BoolLit(lit) = self {
            Some(*lit)
        } else {
            None
        }
    }

    pub fn try_fixed(&self) -> Option<i64> {
        if let AbstractExpr::FixedLit(lit) = self {
            Some(*lit)
        } else {
            None
        }
    }

    pub fn try_float(&self) -> Option<f64> {
        if let AbstractExpr::FloatLit(lit) = self {
            Some(*lit)
        } else {
            None
        }
    }
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
        AbstractExpr::Do(steps) => {
            *s += "(do";
            for expr in *steps {
                *s += " ";
                dump_abstract_expr(s, *expr, arena, interner);
            }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileError {
    TooManyRightParentheses,
    TooFewRightParentheses,
    KeywordCantBeIdentifier(IdentifierId),
    EmptyList,
    MalformedDo,
    MalformedLet,
    MalformedDef,
    MalformedIfElse,
    MalformedAbstract,
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
) -> Result<&'a [ParseExprId<'a>], CompileError> {
    let tokens = lex(text, arena, interner);
    let mut expr_stack: Vec<ParseExprId<'a>> = vec![];
    let mut paren_stack = vec![];

    let mut tokens = tokens.into_iter().peekable();
    while let Some(token) = tokens.next() {
        match token {
            Token::LeftParen => {
                paren_stack.push(expr_stack.len());
            }
            Token::RightParen => {
                let old_len = paren_stack
                    .pop()
                    .ok_or(CompileError::TooManyRightParentheses)?;
                let exprs = arena.collect_fn(|pf| {
                    for expr in &expr_stack[old_len..] {
                        pf(*expr);
                    }
                });
                let list_expr = arena.alloc(ParseExpr::List(exprs));
                expr_stack.truncate(old_len);
                expr_stack.push(list_expr);
            }
            Token::Identifier(id) => {
                expr_stack.push(arena.alloc(ParseExpr::Identifier(*id)));
            }
            Token::BoolLit(lit) => {
                expr_stack.push(arena.alloc(ParseExpr::BoolLit(*lit)));
            }
            Token::FixedLit(lit) => {
                expr_stack.push(arena.alloc(ParseExpr::FixedLit(*lit)));
            }
            Token::FloatLit(lit) => {
                expr_stack.push(arena.alloc(ParseExpr::FloatLit(*lit)));
            }
        }
    }

    if paren_stack.is_empty() {
        Ok(arena.collect_exact(expr_stack.into_iter()))
    } else {
        Err(CompileError::TooFewRightParentheses)
    }
}

struct Checker {
    dot_iden: IdentifierId,
    let_iden: IdentifierId,
    def_iden: IdentifierId,
    question_iden: IdentifierId,
    do_iden: IdentifierId,
}

impl Checker {
    fn check_expr<'a, 'b>(
        &self,
        parsed: ParseExprId<'a>,
        arena: &'b Arena<'a>,
        interner: &mut StringInterner,
    ) -> Result<AbstractExprId<'a>, CompileError> {
        let expr = match arena.get(parsed) {
            ParseExpr::BoolLit(lit) => arena.alloc(AbstractExpr::BoolLit(*lit)),
            ParseExpr::FixedLit(lit) => arena.alloc(AbstractExpr::FixedLit(*lit)),
            ParseExpr::FloatLit(lit) => arena.alloc(AbstractExpr::FloatLit(*lit)),
            ParseExpr::Identifier(id) => {
                if *id == self.dot_iden {
                    return Err(CompileError::KeywordCantBeIdentifier(self.dot_iden));
                }
                if *id == self.let_iden {
                    return Err(CompileError::KeywordCantBeIdentifier(self.let_iden));
                }
                if *id == self.def_iden {
                    return Err(CompileError::KeywordCantBeIdentifier(self.def_iden));
                }
                if *id == self.question_iden {
                    return Err(CompileError::KeywordCantBeIdentifier(self.question_iden));
                }
                if *id == self.do_iden {
                    return Err(CompileError::KeywordCantBeIdentifier(self.do_iden));
                }
                arena.alloc(AbstractExpr::UseIdentifier(*id))
            }
            ParseExpr::List(exprs) => {
                if exprs.is_empty() {
                    return Err(CompileError::EmptyList);
                }
                if *arena.get(exprs[0]) == ParseExpr::Identifier(self.do_iden) {
                    if exprs.len() == 1 {
                        return Err(CompileError::MalformedDo);
                    }
                    let steps: Result<Vec<_>, _> = exprs[1..]
                        .into_iter()
                        .map(|expr| self.check_expr(*expr, arena, interner))
                        .collect();
                    let steps = arena.collect_exact(steps?.into_iter());
                    arena.alloc(AbstractExpr::Do(steps))
                } else if *arena.get(exprs[0]) == ParseExpr::Identifier(self.let_iden) {
                    if exprs.len() != 4 {
                        return Err(CompileError::MalformedLet);
                    }
                    let ParseExpr::Identifier(binder) = arena.get(exprs[1]) else {
                        return Err(CompileError::MalformedLet);
                    };
                    let binding = self.check_expr(exprs[2], arena, interner)?;
                    let in_expr = self.check_expr(exprs[3], arena, interner)?;
                    arena.alloc(AbstractExpr::Let(*binder, binding, in_expr))
                } else if *arena.get(exprs[0]) == ParseExpr::Identifier(self.def_iden) {
                    if exprs.len() != 3 {
                        return Err(CompileError::MalformedDef);
                    }
                    let ParseExpr::Identifier(binder) = arena.get(exprs[1]) else {
                        return Err(CompileError::MalformedDef);
                    };
                    let binding = self.check_expr(exprs[2], arena, interner)?;
                    arena.alloc(AbstractExpr::Define(*binder, binding))
                } else if *arena.get(exprs[0]) == ParseExpr::Identifier(self.question_iden) {
                    if exprs.len() != 4 {
                        return Err(CompileError::MalformedIfElse);
                    }
                    let cond_expr = self.check_expr(exprs[1], arena, interner)?;
                    let true_expr = self.check_expr(exprs[2], arena, interner)?;
                    let false_expr = self.check_expr(exprs[3], arena, interner)?;
                    arena.alloc(AbstractExpr::IfElse(cond_expr, true_expr, false_expr))
                } else if exprs.len() >= 2
                    && *arena.get(exprs[exprs.len() - 2]) == ParseExpr::Identifier(self.dot_iden)
                {
                    let params: Result<Vec<_>, _> = exprs[0..exprs.len() - 2]
                        .into_iter()
                        .map(|expr| {
                            let ParseExpr::Identifier(param) = arena.get(*expr) else {
                                return Err(CompileError::MalformedAbstract);
                            };
                            Ok(*param)
                        })
                        .collect();
                    let params = arena.collect_exact(params?.into_iter());
                    let body_expr = self.check_expr(*exprs.last().unwrap(), arena, interner)?;
                    arena.alloc(AbstractExpr::Abstract(params, body_expr))
                } else if exprs.len() == 1 {
                    self.check_expr(exprs[0], arena, interner)?
                } else {
                    let func_expr = self.check_expr(exprs[0], arena, interner)?;
                    let arg_exprs: Result<Vec<_>, _> = exprs[1..]
                        .into_iter()
                        .map(|parsed| self.check_expr(*parsed, arena, interner))
                        .collect();
                    let arg_exprs = arena.collect_exact(arg_exprs?.into_iter());
                    arena.alloc(AbstractExpr::Apply(func_expr, arg_exprs))
                }
            }
        };
        Ok(expr)
    }
}

pub fn check<'a, 'b>(
    parsed: &'a [ParseExprId<'a>],
    arena: &'b Arena<'a>,
    interner: &mut StringInterner,
) -> Result<&'a [AbstractExprId<'a>], CompileError> {
    let checker = Checker {
        dot_iden: interner.intern("."),
        let_iden: interner.intern("let"),
        def_iden: interner.intern("def"),
        question_iden: interner.intern("?"),
        do_iden: interner.intern("do"),
    };
    let mut abstract_exprs = vec![];
    for id in parsed {
        abstract_exprs.push(checker.check_expr(*id, arena, interner)?);
    }
    Ok(arena.collect_exact(abstract_exprs.into_iter()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_lex() {
        let mut buf = [0u64; 44];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 14];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn (x y . (+ x y))) (print (fn 42 24))";
        let tokens = lex(text, &mut arena, &mut interner);
        assert_eq!(
            tokens,
            &[
                Token::LeftParen,
                Token::Identifier(interner.intern("def")),
                Token::Identifier(interner.intern("fn")),
                Token::LeftParen,
                Token::Identifier(interner.intern("x")),
                Token::Identifier(interner.intern("y")),
                Token::Identifier(interner.intern(".")),
                Token::LeftParen,
                Token::Identifier(interner.intern("+")),
                Token::Identifier(interner.intern("x")),
                Token::Identifier(interner.intern("y")),
                Token::RightParen,
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
        let mut string_buf = [0u8; 14];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn (x y . (+ x y))) (print (fn 42 24))";
        let parse_exprs = parse(text, &mut arena, &mut interner).unwrap();
        let dumped_text = dump_parse_exprs(parse_exprs, &arena, &interner);
        assert_eq!(text, dumped_text);
    }

    #[test]
    fn simple_check() {
        let mut buf = [0u64; 200];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 20];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn (x y . (+ x y))) (print (fn 42 24))";
        let parse_exprs = parse(text, &mut arena, &mut interner).unwrap();
        let abstract_exprs = check(parse_exprs, &mut arena, &mut interner).unwrap();
        let dumped_text = dump_abstract_exprs(abstract_exprs, &arena, &interner);
        assert_eq!(text, dumped_text);
    }

    #[test]
    fn failing_compile() {
        let mut buf = [0u64; 1000];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 30];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);
        let text = "(def fn (x y . (+ x y))) (print (fn 42 24)";
        assert_eq!(
            parse(text, &mut arena, &mut interner),
            Err(CompileError::TooFewRightParentheses)
        );
        let text = "(def fn (x y . (+ x y))) (print (fn 42 24)))";
        assert_eq!(
            parse(text, &mut arena, &mut interner),
            Err(CompileError::TooManyRightParentheses)
        );
        let text = "(def fn (x y . z (+ x y))) (print (fn 42 24))";
        assert_eq!(
            check(
                parse(text, &mut arena, &mut interner).unwrap(),
                &mut arena,
                &mut interner
            ),
            Err(CompileError::KeywordCantBeIdentifier(interner.intern(".")))
        );
        let text = "(def fn (x (+ z y) . (+ x y))) (print (fn 42 24))";
        assert_eq!(
            check(
                parse(text, &mut arena, &mut interner).unwrap(),
                &mut arena,
                &mut interner
            ),
            Err(CompileError::MalformedAbstract)
        );
        let text = "(def fn (x y . ())) (print (fn 42 24))";
        assert_eq!(
            check(
                parse(text, &mut arena, &mut interner).unwrap(),
                &mut arena,
                &mut interner
            ),
            Err(CompileError::EmptyList)
        );
        let text = "(def (+ x z) (x y . (+ x y))) (print (fn 42 24))";
        assert_eq!(
            check(
                parse(text, &mut arena, &mut interner).unwrap(),
                &mut arena,
                &mut interner
            ),
            Err(CompileError::MalformedDef)
        );
        let text = "(do)";
        assert_eq!(
            check(
                parse(text, &mut arena, &mut interner).unwrap(),
                &mut arena,
                &mut interner
            ),
            Err(CompileError::MalformedDo)
        );
    }
}
