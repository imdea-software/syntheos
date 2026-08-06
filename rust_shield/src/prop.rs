//! Parser for the flat propositional formulas over literal ids that appear
//! in a saved mealy machine's YAML, e.g. `0&!1` (literal 0 and not literal
//! 1). `&` binds tighter than `|`, and `!` binds tightest of all.
//!
//! This is a small hand-written recursive-descent parser: one function per
//! precedence level, each calling the next-tighter-binding level for its
//! operands. That's the standard way to turn a grammar with precedence into
//! code without a parser-generator dependency.

use std::collections::HashMap;

use z3::ast::Bool;
use z3::Context;

use crate::error::ShieldError;

/// A parsed propositional formula. `Lit` holds the literal's id, which is
/// later looked up in a transtab to find out what it actually means.
#[derive(Debug, Clone)]
pub enum Prop {
    True,
    False,
    Lit(u32),
    Not(Box<Prop>),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
}

#[derive(Debug, PartialEq)]
enum Token {
    True,
    False,
    Number(u32),
    And,
    Or,
    Not,
    LParen,
    RParen,
}

fn tokenize(input: &str) -> Result<Vec<Token>, ShieldError> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ' ' => {
                chars.next();
            }
            '&' => {
                tokens.push(Token::And);
                chars.next();
            }
            '|' => {
                tokens.push(Token::Or);
                chars.next();
            }
            '!' => {
                tokens.push(Token::Not);
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            't' => {
                tokens.push(Token::True);
                chars.next();
            }
            'f' => {
                tokens.push(Token::False);
                chars.next();
            }
            '0'..='9' => {
                let mut digits = String::new();
                while let Some(&d) = chars.peek() {
                    if d.is_ascii_digit() {
                        digits.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Number(digits.parse().unwrap()));
            }
            other => return Err(ShieldError::new(format!("unexpected character '{other}' in formula: {input}"))),
        }
    }
    Ok(tokens)
}

/// Parses `input`, consuming the whole string.
pub fn parse(input: &str) -> Result<Prop, ShieldError> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    let prop = parse_or(&tokens, &mut pos)?;
    if pos != tokens.len() {
        return Err(ShieldError::new(format!("trailing input in formula: {input}")));
    }
    Ok(prop)
}

// expr := and_expr ('|' and_expr)*
fn parse_or(tokens: &[Token], pos: &mut usize) -> Result<Prop, ShieldError> {
    let mut left = parse_and(tokens, pos)?;
    while tokens.get(*pos) == Some(&Token::Or) {
        *pos += 1;
        let right = parse_and(tokens, pos)?;
        left = Prop::Or(Box::new(left), Box::new(right));
    }
    Ok(left)
}

// and_expr := unary ('&' unary)*
fn parse_and(tokens: &[Token], pos: &mut usize) -> Result<Prop, ShieldError> {
    let mut left = parse_unary(tokens, pos)?;
    while tokens.get(*pos) == Some(&Token::And) {
        *pos += 1;
        let right = parse_unary(tokens, pos)?;
        left = Prop::And(Box::new(left), Box::new(right));
    }
    Ok(left)
}

// unary := '!' unary | atom
fn parse_unary(tokens: &[Token], pos: &mut usize) -> Result<Prop, ShieldError> {
    if tokens.get(*pos) == Some(&Token::Not) {
        *pos += 1;
        return Ok(Prop::Not(Box::new(parse_unary(tokens, pos)?)));
    }
    parse_atom(tokens, pos)
}

// atom := 't' | 'f' | NUMBER | '(' expr ')'
fn parse_atom(tokens: &[Token], pos: &mut usize) -> Result<Prop, ShieldError> {
    let prop = match tokens.get(*pos) {
        Some(Token::True) => Prop::True,
        Some(Token::False) => Prop::False,
        Some(Token::Number(n)) => Prop::Lit(*n),
        Some(Token::LParen) => {
            *pos += 1;
            let inner = parse_or(tokens, pos)?;
            if tokens.get(*pos) != Some(&Token::RParen) {
                return Err(ShieldError::new("expected ')'"));
            }
            inner
        }
        other => return Err(ShieldError::new(format!("unexpected token: {other:?}"))),
    };
    *pos += 1;
    Ok(prop)
}

/// Lowers a `Prop` into a Z3 boolean, replacing each literal id with its
/// theory formula from `transtab` (as built by [`crate::theory`]).
pub fn to_z3<'ctx>(
    prop: &Prop,
    ctx: &'ctx Context,
    transtab: &HashMap<u32, Bool<'ctx>>,
) -> Result<Bool<'ctx>, ShieldError> {
    Ok(match prop {
        Prop::True => Bool::from_bool(ctx, true),
        Prop::False => Bool::from_bool(ctx, false),
        Prop::Lit(id) => transtab
            .get(id)
            .ok_or_else(|| ShieldError::new(format!("literal {id} has no entry in the transtab")))?
            .clone(),
        Prop::Not(p) => to_z3(p, ctx, transtab)?.not(),
        Prop::And(a, b) => Bool::and(ctx, &[&to_z3(a, ctx, transtab)?, &to_z3(b, ctx, transtab)?]),
        Prop::Or(a, b) => Bool::or(ctx, &[&to_z3(a, ctx, transtab)?, &to_z3(b, ctx, transtab)?]),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::Ast;
    use z3::Config;

    #[test]
    fn and_binds_tighter_than_or() {
        // "0&1|2" should parse as (0&1)|2, not 0&(1|2).
        match parse("0&1|2").unwrap() {
            Prop::Or(l, r) => {
                assert!(matches!(*l, Prop::And(_, _)));
                assert!(matches!(*r, Prop::Lit(2)));
            }
            other => panic!("expected an Or at the top: {other:?}"),
        }
    }

    #[test]
    fn not_binds_tighter_than_and() {
        match parse("!0&1").unwrap() {
            Prop::And(l, r) => {
                assert!(matches!(*l, Prop::Not(_)));
                assert!(matches!(*r, Prop::Lit(1)));
            }
            other => panic!("expected an And at the top: {other:?}"),
        }
    }

    #[test]
    fn parens_override_precedence() {
        match parse("0&(1|2)").unwrap() {
            Prop::And(l, r) => {
                assert!(matches!(*l, Prop::Lit(0)));
                assert!(matches!(*r, Prop::Or(_, _)));
            }
            other => panic!("expected an And at the top: {other:?}"),
        }
    }

    #[test]
    fn evaluates_against_a_transtab() {
        let ctx = Context::new(&Config::new());
        let transtab: HashMap<u32, Bool> = [(0, Bool::from_bool(&ctx, true)), (1, Bool::from_bool(&ctx, false))].into();
        let formula = to_z3(&parse("0&!1").unwrap(), &ctx, &transtab).unwrap();
        assert_eq!(formula.simplify().as_bool(), Some(true));
    }

    #[test]
    fn rejects_trailing_input() {
        assert!(parse("0)").is_err());
    }

    #[test]
    fn rejects_unknown_literal() {
        let ctx = Context::new(&Config::new());
        let transtab: HashMap<u32, Bool> = HashMap::new();
        assert!(to_z3(&parse("0").unwrap(), &ctx, &transtab).is_err());
    }
}
