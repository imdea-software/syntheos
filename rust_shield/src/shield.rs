//! The runtime shield: given a mealy machine (the controller Syntheos
//! synthesized), play it safely. On each step it takes the environment's
//! actual move plus the system's proposed move and, if that combination
//! isn't a legal edge out of the current game node, substitutes a legal one
//! instead.

use std::collections::HashMap;

use z3::ast::{Ast, Bool, Int, Real};
use z3::{Context, SatResult, Solver};

use crate::error::ShieldError;
use crate::value::Value;

/// One entry of a mealy machine's `variables:` list.
pub struct Variable {
    pub name: String,
    pub kind: String, // "Int" or "Real"
    pub owner: String, // "system" or "environment"
}

/// An edge out of a `Node`: `condition` is env-play AND sys-play already
/// lowered to a single Z3 boolean (built once, up front, since the mealy
/// machine never changes at runtime - unlike the Python version there's no
/// need to cache a lazily-computed value here).
pub struct Edge<'ctx> {
    pub condition: Bool<'ctx>,
    pub target: usize,
}

pub struct Node<'ctx> {
    pub edges: Vec<Edge<'ctx>>,
}

pub struct Shield<'ctx> {
    ctx: &'ctx Context,
    variables: Vec<Variable>,
    nodes: Vec<Node<'ctx>>,
    current: usize,
}

impl<'ctx> Shield<'ctx> {
    pub fn new(ctx: &'ctx Context, variables: Vec<Variable>, nodes: Vec<Node<'ctx>>) -> Self {
        Shield { ctx, variables, nodes, current: 0 }
    }

    /// Finds an edge out of the current node consistent with the
    /// environment's actual values and (as much as possible of) the
    /// system's proposed values, advances the shield to that edge's target
    /// node, and returns the full system response to play. `None` if no
    /// edge accepts even a freely-chosen system response.
    pub fn protect(
        &mut self,
        env: &HashMap<String, Value>,
        proposal: &HashMap<String, Value>,
    ) -> Result<Option<HashMap<String, Value>>, ShieldError> {
        for edge in &self.nodes[self.current].edges {
            let response = self.try_edge(edge, env, proposal)?;
            if let Some(response) = response {
                self.current = edge.target;
                return Ok(Some(response));
            }
        }
        Ok(None)
    }

    fn try_edge(
        &self,
        edge: &Edge<'ctx>,
        env: &HashMap<String, Value>,
        proposal: &HashMap<String, Value>,
    ) -> Result<Option<HashMap<String, Value>>, ShieldError> {
        let solver = Solver::new(self.ctx);
        solver.assert(&edge.condition);
        for (name, value) in env.iter().chain(proposal.iter()) {
            solver.assert(&self.fixed_to(name, value)?);
        }

        if solver.check() != SatResult::Sat {
            return Ok(None);
        }
        let model = solver.get_model().expect("solver reported sat, so it has a model");
        Ok(Some(self.system_response(&model)?))
    }

    /// A Z3 constraint pinning the variable named `name` to `value`.
    fn fixed_to(&self, name: &str, value: &Value) -> Result<Bool<'ctx>, ShieldError> {
        match self.type_of(name)? {
            "Int" => {
                let n = match value {
                    Value::Int(n) => *n,
                    other => return Err(ShieldError::new(format!("{name} is Int, got {other:?}"))),
                };
                Ok(Int::new_const(self.ctx, name)._eq(&Int::from_i64(self.ctx, n)))
            }
            "Real" => {
                let r = match value {
                    Value::Real(r) => *r,
                    Value::Int(n) => *n as f64,
                    other => return Err(ShieldError::new(format!("{name} is Real, got {other:?}"))),
                };
                let literal = Real::from_real_str(self.ctx, &r.to_string(), "1")
                    .ok_or_else(|| ShieldError::new(format!("bad real value for {name}: {r}")))?;
                Ok(Real::new_const(self.ctx, name)._eq(&literal))
            }
            other => Err(ShieldError::new(format!("unhandled type: {other}"))),
        }
    }

    /// The model's value for every system variable, defaulting unconstrained
    /// ones to whatever Z3 picks (any value works for those - the game
    /// doesn't care, since nothing in the formula depends on them).
    fn system_response(&self, model: &z3::Model<'ctx>) -> Result<HashMap<String, Value>, ShieldError> {
        let mut response = HashMap::new();
        for v in self.variables.iter().filter(|v| v.owner == "system") {
            let value = match v.kind.as_str() {
                "Int" => {
                    let evaluated = model
                        .eval(&Int::new_const(self.ctx, v.name.as_str()), true)
                        .ok_or_else(|| ShieldError::new(format!("model has no value for {}", v.name)))?;
                    Value::Int(evaluated.as_i64().ok_or_else(|| ShieldError::new("non-integral model value"))?)
                }
                "Real" => {
                    let evaluated = model
                        .eval(&Real::new_const(self.ctx, v.name.as_str()), true)
                        .ok_or_else(|| ShieldError::new(format!("model has no value for {}", v.name)))?;
                    let (num, den) = evaluated.as_real().ok_or_else(|| ShieldError::new("non-rational model value"))?;
                    Value::Real(num as f64 / den as f64)
                }
                other => return Err(ShieldError::new(format!("unhandled type: {other}"))),
            };
            response.insert(v.name.clone(), value);
        }
        Ok(response)
    }

    fn type_of(&self, name: &str) -> Result<&str, ShieldError> {
        let mut base = name;
        while let Some(stripped) = base.strip_prefix("FETCH_") {
            base = stripped;
        }
        self.variables
            .iter()
            .find(|v| v.name == base)
            .map(|v| v.kind.as_str())
            .ok_or_else(|| ShieldError::new(format!("unknown variable: {name}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::Config;

    // Two nodes, two edges: node0 -[e>0 & x>5]-> node1, node0 -[e<=0 &
    // x<=5]-> node0 (a self-loop). Mirrors the Python test suite's
    // `build_two_edge_shield`.
    fn two_edge_shield(ctx: &Context) -> Shield<'_> {
        let e = Int::new_const(ctx, "e");
        let x = Int::new_const(ctx, "x");
        let five = Int::from_i64(ctx, 5);
        let zero = Int::from_i64(ctx, 0);

        let forward = Edge { condition: Bool::and(ctx, &[&e.gt(&zero), &x.gt(&five)]), target: 1 };
        let selfloop = Edge { condition: Bool::and(ctx, &[&e.le(&zero), &x.le(&five)]), target: 0 };

        let variables = vec![
            Variable { name: "e".into(), kind: "Int".into(), owner: "environment".into() },
            Variable { name: "x".into(), kind: "Int".into(), owner: "system".into() },
        ];
        Shield::new(ctx, variables, vec![Node { edges: vec![forward, selfloop] }, Node { edges: vec![] }])
    }

    fn ints(pairs: &[(&str, i64)]) -> HashMap<String, Value> {
        pairs.iter().map(|(k, v)| (k.to_string(), Value::Int(*v))).collect()
    }

    #[test]
    fn accepts_a_valid_proposal_and_advances_node() {
        let ctx = Context::new(&Config::new());
        let mut shield = two_edge_shield(&ctx);
        let response = shield.protect(&ints(&[("e", 10)]), &ints(&[("x", 7)])).unwrap();
        assert_eq!(response, Some(ints(&[("x", 7)])));
        assert_eq!(shield.current, 1);
    }

    #[test]
    fn takes_selfloop_when_env_is_nonpositive() {
        let ctx = Context::new(&Config::new());
        let mut shield = two_edge_shield(&ctx);
        let response = shield.protect(&ints(&[("e", -3)]), &ints(&[("x", 2)])).unwrap();
        assert_eq!(response, Some(ints(&[("x", 2)])));
        assert_eq!(shield.current, 0);
    }

    #[test]
    fn rejects_invalid_proposal_but_falls_back_to_free_choice() {
        let ctx = Context::new(&Config::new());
        let mut shield = two_edge_shield(&ctx);

        // x=-100 satisfies neither edge (x>5 fails; x<=5 holds, but that
        // edge also needs e<=0, which is false here).
        assert_eq!(shield.protect(&ints(&[("e", 10)]), &ints(&[("x", -100)])).unwrap(), None);

        // Falling back to an unconstrained system choice must still find
        // *some* legal x satisfying the forward edge's x>5.
        let fallback = shield.protect(&ints(&[("e", 10)]), &HashMap::new()).unwrap().unwrap();
        assert!(matches!(fallback.get("x"), Some(Value::Int(n)) if *n > 5));
        assert_eq!(shield.current, 1);
    }

    #[test]
    fn type_of_strips_fetch_prefix() {
        let ctx = Context::new(&Config::new());
        let shield = two_edge_shield(&ctx);
        assert_eq!(shield.type_of("x").unwrap(), "Int");
        assert_eq!(shield.type_of("FETCH_x").unwrap(), "Int");
        assert_eq!(shield.type_of("FETCH_FETCH_x").unwrap(), "Int");
        assert!(shield.type_of("unknown").is_err());
    }
}
