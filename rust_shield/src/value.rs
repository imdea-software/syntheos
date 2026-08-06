use serde::{Deserialize, Serialize};

/// A concrete value for an environment/system variable, as read from a
/// play's JSON or written back into one.
///
/// `#[serde(untagged)]` makes this deserialize/serialize as a plain JSON
/// scalar (e.g. `7`, `2.5`, `true`, `"idle"`) instead of a tagged object like
/// `{"Int": 7}`. On the way in, serde tries each variant in order and keeps
/// the first that fits - so `Int` must come before `Real`, or a whole number
/// like `7` would parse as the float `7.0` instead of the integer `7`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Real(f64),
    Str(String),
}
