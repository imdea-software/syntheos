//! Loads a mealy machine saved by `syntheos --save-mealy` (a YAML file
//! shaped like a spec, with `transtab`/`nodes` filled in) into a runnable
//! [`Shield`].

use std::collections::HashMap;
use std::fs;

use serde::Deserialize;
use z3::Context;

use crate::error::ShieldError;
use crate::shield::{Edge, Node, Shield, Variable};
use crate::{prop, theory};

#[derive(Deserialize)]
struct VariableData {
    name: String,
    #[serde(rename = "type")]
    kind: String,
    owner: String,
}

#[derive(Deserialize)]
struct EdgeData {
    envplay: String,
    sysplay: String,
    outnoden: usize,
}

#[derive(Deserialize)]
struct MealyFile {
    variables: Vec<VariableData>,
    transtab: HashMap<String, String>,
    nodes: Vec<Vec<EdgeData>>,
}

/// Returns the shield (positioned at the machine's start node) and the
/// maximum `FETCH_` nesting depth used anywhere in the machine's formulas -
/// callers need that depth to know how many past plays to keep around.
pub fn load<'ctx>(ctx: &'ctx Context, path: &str) -> Result<(Shield<'ctx>, usize), ShieldError> {
    let text = fs::read_to_string(path)?;
    let mealy: MealyFile = serde_yaml::from_str(&text)?;

    let var_types: HashMap<String, String> =
        mealy.variables.iter().map(|v| (v.name.clone(), v.kind.clone())).collect();

    let theory_exprs: HashMap<u32, theory::SExpr> = mealy
        .transtab
        .iter()
        .map(|(id, formula)| -> Result<(u32, theory::SExpr), ShieldError> {
            let id = id.parse().map_err(|_| ShieldError::new(format!("bad transtab id: {id}")))?;
            Ok((id, theory::parse(formula)?))
        })
        .collect::<Result<_, _>>()?;

    let max_fetch_depth = max_fetch_depth(theory_exprs.values());

    let transtab: HashMap<u32, z3::ast::Bool<'ctx>> = theory_exprs
        .iter()
        .map(|(id, expr)| Ok((*id, theory::compile(expr, ctx, &var_types)?)))
        .collect::<Result<_, ShieldError>>()?;

    let nodes = mealy
        .nodes
        .into_iter()
        .map(|edges| build_node(edges, ctx, &transtab))
        .collect::<Result<_, _>>()?;

    let variables: Vec<Variable> = mealy
        .variables
        .into_iter()
        .map(|v| Variable { name: v.name, kind: v.kind, owner: v.owner })
        .collect();

    Ok((Shield::new(ctx, variables, nodes), max_fetch_depth))
}

fn build_node<'ctx>(
    edges: Vec<EdgeData>,
    ctx: &'ctx Context,
    transtab: &HashMap<u32, z3::ast::Bool<'ctx>>,
) -> Result<Node<'ctx>, ShieldError> {
    let edges = edges
        .into_iter()
        .map(|edge| {
            let env_play = prop::to_z3(&prop::parse(&edge.envplay)?, ctx, transtab)?;
            let sys_play = prop::to_z3(&prop::parse(&edge.sysplay)?, ctx, transtab)?;
            let condition = z3::ast::Bool::and(ctx, &[&env_play, &sys_play]);
            Ok(Edge { condition, target: edge.outnoden })
        })
        .collect::<Result<_, ShieldError>>()?;
    Ok(Node { edges })
}

fn max_fetch_depth<'a>(exprs: impl Iterator<Item = &'a theory::SExpr>) -> usize {
    let mut names = Vec::new();
    for expr in exprs {
        theory::variable_names(expr, &mut names);
    }
    names.iter().map(|name| fetch_depth(name)).max().unwrap_or(0)
}

fn fetch_depth(name: &str) -> usize {
    let mut depth = 0;
    let mut rest = name;
    while let Some(stripped) = rest.strip_prefix("FETCH_") {
        depth += 1;
        rest = stripped;
    }
    depth
}
