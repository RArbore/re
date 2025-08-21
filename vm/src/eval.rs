use core::iter::zip;
use core::mem::take;

use arena::Arena;

use crate::expr::{AbstractExpr, AbstractExprId};
use crate::interner::{IdentifierId, StringInterner};

pub struct Env<'a> {
    iden_to_expr: Vec<Vec<AbstractExprId<'a>>>,

    plus_id: IdentifierId,
    minus_id: IdentifierId,
    equals_equals_id: IdentifierId,
}

impl<'a> Env<'a> {
    pub fn new(interner: &mut StringInterner) -> Self {
        Env {
            iden_to_expr: vec![vec![]; interner.num_idens()],
            plus_id: interner.intern("+"),
            minus_id: interner.intern("-"),
            equals_equals_id: interner.intern("=="),
        }
    }

    pub fn eval(&mut self, arena: &mut Arena<'a>, expr: AbstractExprId<'a>) -> AbstractExprId<'a> {
        match arena.get(expr) {
            AbstractExpr::BoolLit(_) | AbstractExpr::FixedLit(_) | AbstractExpr::FloatLit(_) => {
                expr
            }
            AbstractExpr::UseIdentifier(iden) => {
                if let Some(concrete_expr) = self.iden_to_expr[iden.idx()].last() {
                    self.eval(arena, *concrete_expr)
                } else {
                    expr
                }
            }
            AbstractExpr::Apply(func, args) => {
                let new_func = self.eval(arena, *func);
                if let AbstractExpr::Abstract(params, body) = arena.get(new_func) {
                    assert_eq!(params.len(), args.len());
                    for (param_iden, arg_expr) in zip(params.into_iter(), args.into_iter()) {
                        let new_arg_expr = self.eval(arena, *arg_expr);
                        self.iden_to_expr[param_iden.idx()].push(new_arg_expr);
                    }
                    let new_body = self.eval(arena, *body);
                    for param_iden in params.into_iter() {
                        self.iden_to_expr[param_iden.idx()].pop();
                    }
                    new_body
                } else if let AbstractExpr::UseIdentifier(func_name) = arena.get(new_func)
                    && let Some(result) = self.try_builtin(arena, *func_name, *args)
                {
                    result
                } else if new_func != *func {
                    arena.alloc(AbstractExpr::Apply(new_func, args))
                } else {
                    expr
                }
            }
            AbstractExpr::Abstract(params, body) => {
                let extracted_env: Vec<_> = params
                    .into_iter()
                    .map(|param_iden| take(&mut self.iden_to_expr[param_iden.idx()]))
                    .collect();
                let new_body = self.eval(arena, *body);
                let new_expr = if *body != new_body {
                    arena.alloc(AbstractExpr::Abstract(params, new_body))
                } else {
                    expr
                };
                for (param_iden, bindings) in zip(params.into_iter(), extracted_env.into_iter()) {
                    self.iden_to_expr[param_iden.idx()] = bindings;
                }
                new_expr
            }
            AbstractExpr::Let(binder, binding, in_expr) => {
                let new_binding = self.eval(arena, *binding);
                self.iden_to_expr[binder.idx()].push(new_binding);
                let new_in_expr = self.eval(arena, *in_expr);
                self.iden_to_expr[binder.idx()].pop();
                new_in_expr
            }
            AbstractExpr::Define(binder, binding) => {
                let new_binding = self.eval(arena, *binding);
                self.iden_to_expr[binder.idx()].push(new_binding);
                new_binding
            }
            AbstractExpr::IfElse(cond, true_expr, false_expr) => {
                let new_cond = self.eval(arena, *cond);
                if let AbstractExpr::BoolLit(lit) = arena.get(new_cond) {
                    if *lit {
                        self.eval(arena, *true_expr)
                    } else {
                        self.eval(arena, *false_expr)
                    }
                } else {
                    expr
                }
            }
        }
    }

    fn try_builtin(
        &mut self,
        arena: &mut Arena<'a>,
        func: IdentifierId,
        args: &'a [AbstractExprId<'a>],
    ) -> Option<AbstractExprId<'a>> {
        if func == self.equals_equals_id && args.len() == 2 {
            let lhs = self.eval(arena, args[0]);
            let rhs = self.eval(arena, args[1]);
            Some(arena.alloc(AbstractExpr::BoolLit(arena.get(lhs) == arena.get(rhs))))
        } else if func == self.plus_id && args.len() == 2 {
            let lhs = self.eval(arena, args[0]);
            let rhs = self.eval(arena, args[1]);
            if let (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) =
                (arena.get(lhs), arena.get(rhs))
            {
                Some(arena.alloc(AbstractExpr::FixedLit(lhs + rhs)))
            } else if let (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) =
                (arena.get(lhs), arena.get(rhs))
            {
                Some(arena.alloc(AbstractExpr::FloatLit(lhs + rhs)))
            } else {
                None
            }
        } else if func == self.minus_id && args.len() == 2 {
            let lhs = self.eval(arena, args[0]);
            let rhs = self.eval(arena, args[1]);
            if let (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) =
                (arena.get(lhs), arena.get(rhs))
            {
                Some(arena.alloc(AbstractExpr::FixedLit(lhs - rhs)))
            } else if let (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) =
                (arena.get(lhs), arena.get(rhs))
            {
                Some(arena.alloc(AbstractExpr::FloatLit(lhs - rhs)))
            } else {
                None
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::expr::{check, dump_abstract_exprs, parse};

    #[test]
    fn simple_eval() {
        let mut buf = [0u64; 2000];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 20];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);

        let programs = &[
            "((x y . x) 42 24)",
            "(let x 73 x)",
            "(? true 3 5)",
            "(let x false (? x x 7))",
            "(def x 42.3) x",
            "(def f (x . (? x 0.1 0.9))) (f false)",
            "(+ 4 3)",
            "(- 4 3)",
            "(== 4 3)",
        ];
        let evals = &["42", "73", "3", "7", "42.3", "0.9", "7", "1", "false"];

        for (text, correct) in zip(programs, evals) {
            let parse_exprs = parse(text, &mut arena, &mut interner).unwrap();
            let abstract_exprs = check(parse_exprs, &mut arena, &mut interner).unwrap();
            assert!(!abstract_exprs.is_empty());
            let mut env = Env::new(&mut interner);
            let mut evaled = env.eval(&mut arena, abstract_exprs[0]);
            for expr in &abstract_exprs[1..] {
                evaled = env.eval(&mut arena, *expr);
            }
            let dumped_text = dump_abstract_exprs(&[evaled], &arena, &interner);
            assert_eq!(&dumped_text, *correct);
        }
    }
}
