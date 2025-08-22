use core::iter::zip;
use core::mem::take;
use std::collections::HashMap;

use arena::Arena;

use crate::expr::{AbstractExpr, AbstractExprId};
use crate::interner::{IdentifierId, StringInterner};

pub struct Env<'a, 'b> {
    iden_to_expr: Vec<Vec<AbstractExprId<'a>>>,

    builtins: HashMap<
        IdentifierId,
        Box<dyn FnMut(&mut Arena<'a>, &[AbstractExprId<'a>]) -> Option<AbstractExprId<'a>> + 'b>,
    >,
}

impl<'a, 'b> Env<'a, 'b> {
    pub fn new(interner: &mut StringInterner) -> Self {
        Env {
            iden_to_expr: vec![vec![]; interner.num_idens()],
            builtins: HashMap::new(),
        }
    }

    pub fn register_bindings<I>(&mut self, functions: I)
    where
        I: Iterator<
            Item = (
                IdentifierId,
                Box<
                    dyn FnMut(&mut Arena<'a>, &[AbstractExprId<'a>]) -> Option<AbstractExprId<'a>>
                        + 'b,
                >,
            ),
        >,
    {
        self.builtins.extend(functions);
    }

    pub fn eval(&mut self, arena: &mut Arena<'a>, expr: AbstractExprId<'a>) -> AbstractExprId<'a> {
        match arena.get(expr) {
            AbstractExpr::BoolLit(_) | AbstractExpr::FixedLit(_) | AbstractExpr::FloatLit(_) => {
                expr
            }
            AbstractExpr::UseIdentifier(iden) => {
                if let Some(concrete_expr) = self.iden_to_expr[iden.idx()].last() {
                    self.eval(arena, *concrete_expr)
                } else if self.builtins.contains_key(iden) {
                    let func_ref = self.builtins.get_mut(iden).unwrap();
                    if let Some(result) = func_ref(arena, &[]) {
                        result
                    } else {
                        expr
                    }
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
                    return new_body;
                } else if let AbstractExpr::UseIdentifier(func_name) = arena.get(new_func)
                    && self.builtins.contains_key(func_name)
                {
                    let new_args: Vec<_> =
                        args.into_iter().map(|id| self.eval(arena, *id)).collect();
                    let func_ref = self.builtins.get_mut(func_name).unwrap();
                    if let Some(result) = func_ref(arena, &new_args) {
                        return result;
                    }
                }

                if new_func != *func {
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
            AbstractExpr::Do(steps) => {
                let mut recent = self.eval(arena, steps[0]);
                for step in &steps[1..] {
                    recent = self.eval(arena, *step);
                }
                recent
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::expr::{check, dump_abstract_exprs, parse};

    #[test]
    fn eval() {
        let mut buf = [0u64; 2000];
        let mut arena = Arena::new_backed(&mut buf);
        let mut string_buf = [0u8; 30];
        let string_arena = Arena::new_backed(&mut string_buf);
        let mut interner = StringInterner::new(&string_arena);

        let programs = &[
            "((x y . x) 42 24)",
            "(let x 73 x)",
            "(do (? true 3 5))",
            "(let x false (? x x 7))",
            "(def x 42.3) x",
            "(do (def f (x . (? x 0.1 0.9))) (f false))",
            "(+ 4 3)",
            "(- 4 3)",
            "(== 4.3 3.0)",
            "(== 3 3)",
            "(def f (x . (? (== x 0) 1 (* x (f (- x 1)))))) (f 7)",
            "(let f (x . (? (== x 0) 0 (+ x (f (- x 1))))) (f 7))",
            "(do inc inc inc inc)",
        ];
        let evals = &[
            "42", "73", "3", "7", "42.3", "0.9", "7", "1", "false", "true", "5040", "28", "3",
        ];

        fn plus_func<'a>(
            arena: &mut Arena<'a>,
            args: &[AbstractExprId<'a>],
        ) -> Option<AbstractExprId<'a>> {
            if args.len() != 2 {
                return None;
            }

            match (arena.get(args[0]), arena.get(args[1])) {
                (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FixedLit(lhs + rhs)))
                }
                (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FloatLit(lhs + rhs)))
                }
                _ => None,
            }
        }

        fn minus_func<'a>(
            arena: &mut Arena<'a>,
            args: &[AbstractExprId<'a>],
        ) -> Option<AbstractExprId<'a>> {
            if args.len() != 2 {
                return None;
            }

            match (arena.get(args[0]), arena.get(args[1])) {
                (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FixedLit(lhs - rhs)))
                }
                (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FloatLit(lhs - rhs)))
                }
                _ => None,
            }
        }

        fn times_func<'a>(
            arena: &mut Arena<'a>,
            args: &[AbstractExprId<'a>],
        ) -> Option<AbstractExprId<'a>> {
            if args.len() != 2 {
                return None;
            }

            match (arena.get(args[0]), arena.get(args[1])) {
                (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FixedLit(lhs * rhs)))
                }
                (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::FloatLit(lhs * rhs)))
                }
                _ => None,
            }
        }

        fn equals_equals_func<'a>(
            arena: &mut Arena<'a>,
            args: &[AbstractExprId<'a>],
        ) -> Option<AbstractExprId<'a>> {
            if args.len() != 2 {
                return None;
            }

            match (arena.get(args[0]), arena.get(args[1])) {
                (AbstractExpr::FixedLit(lhs), AbstractExpr::FixedLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::BoolLit(lhs == rhs)))
                }
                (AbstractExpr::FloatLit(lhs), AbstractExpr::FloatLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::BoolLit(lhs == rhs)))
                }
                (AbstractExpr::BoolLit(lhs), AbstractExpr::BoolLit(rhs)) => {
                    Some(arena.alloc(AbstractExpr::BoolLit(lhs == rhs)))
                }
                _ => None,
            }
        }

        for (text, correct) in zip(programs, evals) {
            let mut inc = 0;
            let inc_gen_func = |arena: &mut Arena, _args: &[AbstractExprId]| {
                let expr = arena.alloc(AbstractExpr::FixedLit(inc));
                inc += 1;
                Some(expr)
            };
            let builtins = vec![
                (interner.intern("+"), Box::new(plus_func) as _),
                (interner.intern("-"), Box::new(minus_func) as _),
                (interner.intern("*"), Box::new(times_func) as _),
                (interner.intern("=="), Box::new(equals_equals_func) as _),
                (interner.intern("inc"), Box::new(inc_gen_func) as _),
            ];
            let parse_exprs = parse(text, &mut arena, &mut interner).unwrap();
            let abstract_exprs = check(parse_exprs, &mut arena, &mut interner).unwrap();
            assert!(!abstract_exprs.is_empty());
            let mut env = Env::new(&mut interner);
            env.register_bindings(builtins.into_iter());
            let mut evaled = env.eval(&mut arena, abstract_exprs[0]);
            for expr in &abstract_exprs[1..] {
                evaled = env.eval(&mut arena, *expr);
            }
            let dumped_text = dump_abstract_exprs(&[evaled], &arena, &interner);
            assert_eq!(&dumped_text, *correct);
        }
    }
}
