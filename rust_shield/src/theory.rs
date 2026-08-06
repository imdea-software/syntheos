//! Parser and Z3 compiler for the theory atoms held in a mealy machine's
//! transtab, e.g. `(< (+ FETCH_w 200) w)`. These are plain Lisp-style
//! s-expressions (SMT-LIB syntax), so parsing happens in two independent
//! steps: first a generic s-expression tree (this has no idea what `<` or
//! `w` mean), then a second pass that interprets that tree as an arithmetic
//! comparison, looking up each variable's declared type along the way.

use std::collections::HashMap;

use z3::ast::{Ast, Bool, Int, Real};
use z3::Context;

use crate::error::ShieldError;

#[derive(Debug, Clone)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Parses one s-expression, consuming the whole string.
pub fn parse(input: &str) -> Result<SExpr, ShieldError> {
    // `replace` allocates a new `String` - bind it before splitting, so the
    // borrowed `&str` tokens have somewhere to point that outlives them.
    let spaced = input.replace('(', " ( ").replace(')', " ) ");
    let tokens: Vec<&str> = spaced.split_whitespace().collect();
    let mut pos = 0;
    let expr = parse_expr(&tokens, &mut pos)?;
    if pos != tokens.len() {
        return Err(ShieldError::new(format!("trailing input after expression: {input}")));
    }
    Ok(expr)
}

fn parse_expr(tokens: &[&str], pos: &mut usize) -> Result<SExpr, ShieldError> {
    let token = *tokens.get(*pos).ok_or_else(|| ShieldError::new("unexpected end of expression"))?;
    *pos += 1;
    if token == "(" {
        let mut items = Vec::new();
        loop {
            match tokens.get(*pos) {
                Some(&")") => {
                    *pos += 1;
                    break;
                }
                Some(_) => items.push(parse_expr(tokens, pos)?),
                None => return Err(ShieldError::new("unmatched '('")),
            }
        }
        Ok(SExpr::List(items))
    } else if token == ")" {
        Err(ShieldError::new("unexpected ')'"))
    } else {
        Ok(SExpr::Atom(token.to_string()))
    }
}

/// Collects the names of every variable (as opposed to number or operator)
/// referenced anywhere in `expr`, appending them to `out`.
pub fn variable_names(expr: &SExpr, out: &mut Vec<String>) {
    match expr {
        SExpr::Atom(s) if is_identifier(s) => out.push(s.clone()),
        SExpr::Atom(_) => {}
        SExpr::List(items) => items.iter().for_each(|item| variable_names(item, out)),
    }
}

fn is_identifier(s: &str) -> bool {
    s.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
}

/// A variable can be declared `Int` or `Real`; arithmetic combining both is
/// promoted to `Real` (mirrors what Z3 itself does for mixed arithmetic).
enum Num<'ctx> {
    Int(Int<'ctx>),
    Real(Real<'ctx>),
}

impl<'ctx> Num<'ctx> {
    fn as_real(&self) -> Real<'ctx> {
        match self {
            Num::Int(i) => i.to_real(),
            Num::Real(r) => r.clone(),
        }
    }
}

fn compile_term<'ctx>(
    expr: &SExpr,
    ctx: &'ctx Context,
    var_types: &HashMap<String, String>,
) -> Result<Num<'ctx>, ShieldError> {
    match expr {
        SExpr::Atom(s) => compile_atom(s, ctx, var_types),
        SExpr::List(items) => compile_arith(items, ctx, var_types),
    }
}

fn compile_atom<'ctx>(
    s: &str,
    ctx: &'ctx Context,
    var_types: &HashMap<String, String>,
) -> Result<Num<'ctx>, ShieldError> {
    if let Ok(i) = s.parse::<i64>() {
        return Ok(Num::Int(Int::from_i64(ctx, i)));
    }
    if s.parse::<f64>().is_ok() {
        let real = Real::from_real_str(ctx, s, "1").ok_or_else(|| ShieldError::new(format!("bad numeral: {s}")))?;
        return Ok(Num::Real(real));
    }

    let base = strip_fetch(s);
    let ty = var_types.get(base).ok_or_else(|| ShieldError::new(format!("unknown variable: {s}")))?;
    match ty.as_str() {
        "Int" => Ok(Num::Int(Int::new_const(ctx, s))),
        "Real" => Ok(Num::Real(Real::new_const(ctx, s))),
        other => Err(ShieldError::new(format!("unhandled type: {other}"))),
    }
}

/// Strips repeated `FETCH_` (previous-value) prefixes to find the name a
/// variable was actually declared under, e.g. `FETCH_FETCH_w` -> `w`.
fn strip_fetch(name: &str) -> &str {
    let mut base = name;
    while let Some(stripped) = base.strip_prefix("FETCH_") {
        base = stripped;
    }
    base
}

fn compile_arith<'ctx>(
    items: &[SExpr],
    ctx: &'ctx Context,
    var_types: &HashMap<String, String>,
) -> Result<Num<'ctx>, ShieldError> {
    let (op, args) = items.split_first().ok_or_else(|| ShieldError::new("empty expression"))?;
    let op = as_operator(op)?;

    // Unary minus (`(- 200)`) negates its single argument, unlike n-ary `-`
    // (`(- a b)` = a - b), so it needs its own case.
    if op == "-" && args.len() == 1 {
        return Ok(match compile_term(&args[0], ctx, var_types)? {
            Num::Int(i) => Num::Int(i.unary_minus()),
            Num::Real(r) => Num::Real(r.unary_minus()),
        });
    }

    let operands = args
        .iter()
        .map(|arg| compile_term(arg, ctx, var_types))
        .collect::<Result<Vec<_>, _>>()?;

    if operands.iter().all(|n| matches!(n, Num::Int(_))) {
        let ints: Vec<Int> = operands
            .into_iter()
            .map(|n| match n {
                Num::Int(i) => i,
                Num::Real(_) => unreachable!("just checked all operands are Int"),
            })
            .collect();
        let refs: Vec<&Int> = ints.iter().collect();
        Ok(Num::Int(match op {
            "+" => Int::add(ctx, &refs),
            "-" => Int::sub(ctx, &refs),
            "*" => Int::mul(ctx, &refs),
            other => return Err(ShieldError::new(format!("unhandled operator: {other}"))),
        }))
    } else {
        let reals: Vec<Real> = operands.iter().map(Num::as_real).collect();
        let refs: Vec<&Real> = reals.iter().collect();
        Ok(Num::Real(match op {
            "+" => Real::add(ctx, &refs),
            "-" => Real::sub(ctx, &refs),
            "*" => Real::mul(ctx, &refs),
            other => return Err(ShieldError::new(format!("unhandled operator: {other}"))),
        }))
    }
}

fn as_operator(expr: &SExpr) -> Result<&str, ShieldError> {
    match expr {
        SExpr::Atom(s) => Ok(s.as_str()),
        SExpr::List(_) => Err(ShieldError::new("expected an operator, got a list")),
    }
}

/// Compiles a full theory atom, e.g. `(< (+ FETCH_w 200) w)`, into a Z3
/// boolean.
pub fn compile<'ctx>(
    expr: &SExpr,
    ctx: &'ctx Context,
    var_types: &HashMap<String, String>,
) -> Result<Bool<'ctx>, ShieldError> {
    let SExpr::List(items) = expr else {
        return Err(ShieldError::new("expected a relational expression"));
    };
    let [op, lhs, rhs] = items.as_slice() else {
        return Err(ShieldError::new("expected a binary relation"));
    };
    let op = as_operator(op)?;
    let lhs = compile_term(lhs, ctx, var_types)?;
    let rhs = compile_term(rhs, ctx, var_types)?;

    let (lhs, rhs) = match (&lhs, &rhs) {
        (Num::Int(_), Num::Int(_)) => (lhs, rhs),
        _ => (Num::Real(lhs.as_real()), Num::Real(rhs.as_real())),
    };
    match (lhs, rhs) {
        (Num::Int(a), Num::Int(b)) => relate(op, &a, &b),
        (Num::Real(a), Num::Real(b)) => relate(op, &a, &b),
        _ => unreachable!("just promoted both sides to the same variant"),
    }
}

/// `Int` and `Real` each provide `lt`/`le`/`gt`/`ge` as inherent methods (not
/// through a shared trait from the `z3` crate), so this trait exists purely
/// to let `relate` below be written once instead of once per numeric type.
trait Relational<'ctx>: Ast<'ctx> + Sized {
    fn lt(&self, other: &Self) -> Bool<'ctx>;
    fn le(&self, other: &Self) -> Bool<'ctx>;
    fn gt(&self, other: &Self) -> Bool<'ctx>;
    fn ge(&self, other: &Self) -> Bool<'ctx>;
}

impl<'ctx> Relational<'ctx> for Int<'ctx> {
    fn lt(&self, other: &Self) -> Bool<'ctx> {
        Int::lt(self, other)
    }
    fn le(&self, other: &Self) -> Bool<'ctx> {
        Int::le(self, other)
    }
    fn gt(&self, other: &Self) -> Bool<'ctx> {
        Int::gt(self, other)
    }
    fn ge(&self, other: &Self) -> Bool<'ctx> {
        Int::ge(self, other)
    }
}

impl<'ctx> Relational<'ctx> for Real<'ctx> {
    fn lt(&self, other: &Self) -> Bool<'ctx> {
        Real::lt(self, other)
    }
    fn le(&self, other: &Self) -> Bool<'ctx> {
        Real::le(self, other)
    }
    fn gt(&self, other: &Self) -> Bool<'ctx> {
        Real::gt(self, other)
    }
    fn ge(&self, other: &Self) -> Bool<'ctx> {
        Real::ge(self, other)
    }
}

fn relate<'ctx, T: Relational<'ctx>>(op: &str, a: &T, b: &T) -> Result<Bool<'ctx>, ShieldError> {
    Ok(match op {
        "<" => a.lt(b),
        "<=" => a.le(b),
        ">" => a.gt(b),
        ">=" => a.ge(b),
        "=" => a._eq(b),
        other => return Err(ShieldError::new(format!("unhandled relation: {other}"))),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::{Config, SatResult, Solver};

    fn var_types() -> HashMap<String, String> {
        [("w".to_string(), "Int".to_string()), ("r".to_string(), "Real".to_string())].into()
    }

    fn is_sat(ctx: &Context, cond: &Bool) -> bool {
        let solver = Solver::new(ctx);
        solver.assert(cond);
        solver.check() == SatResult::Sat
    }

    #[test]
    fn parses_nested_sexpr() {
        match parse("(< (+ FETCH_w 200) w)").unwrap() {
            SExpr::List(items) => assert_eq!(items.len(), 3),
            other => panic!("expected a list: {other:?}"),
        }
    }

    #[test]
    fn collects_variable_names_but_not_operators_or_numbers() {
        let expr = parse("(< (+ FETCH_w 200) w)").unwrap();
        let mut names = Vec::new();
        variable_names(&expr, &mut names);
        assert_eq!(names, vec!["FETCH_w".to_string(), "w".to_string()]);
    }

    #[test]
    fn compiles_int_comparison() {
        let ctx = Context::new(&Config::new());
        let cond = compile(&parse("(< w 3500)").unwrap(), &ctx, &var_types()).unwrap();

        let solver = Solver::new(&ctx);
        solver.assert(&cond);
        solver.assert(&Int::new_const(&ctx, "w")._eq(&Int::from_i64(&ctx, 100)));
        assert_eq!(solver.check(), SatResult::Sat);

        solver.assert(&Int::new_const(&ctx, "w")._eq(&Int::from_i64(&ctx, 4000)));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn mixes_int_and_real_by_promoting_to_real() {
        let ctx = Context::new(&Config::new());
        let cond = compile(&parse("(< w r)").unwrap(), &ctx, &var_types()).unwrap();

        let solver = Solver::new(&ctx);
        solver.assert(&cond);
        solver.assert(&Int::new_const(&ctx, "w")._eq(&Int::from_i64(&ctx, 1)));
        solver.assert(&Real::new_const(&ctx, "r")._eq(&Real::from_real_str(&ctx, "3", "2").unwrap()));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn unary_minus_negates_a_single_argument() {
        let ctx = Context::new(&Config::new());
        let cond = compile(&parse("(< w (- 200))").unwrap(), &ctx, &var_types()).unwrap();
        assert!(is_sat(&ctx, &Bool::and(&ctx, &[&cond, &Int::new_const(&ctx, "w")._eq(&Int::from_i64(&ctx, -300))])));
        assert!(!is_sat(&ctx, &Bool::and(&ctx, &[&cond, &Int::new_const(&ctx, "w")._eq(&Int::from_i64(&ctx, -100))])));
    }

    #[test]
    fn rejects_unknown_variable() {
        let ctx = Context::new(&Config::new());
        assert!(compile(&parse("(< bogus 1)").unwrap(), &ctx, &var_types()).is_err());
    }
}
