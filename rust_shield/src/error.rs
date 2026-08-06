use std::fmt;

/// Any user-facing failure: a malformed mealy file, a parse error in one of
/// its embedded formulas, or bad input on stdin.
///
/// Rust has no exceptions - functions that can fail return `Result<T,
/// ShieldError>`, and callers propagate failure with `?` instead of a
/// try/catch.
#[derive(Debug)]
pub struct ShieldError(String);

impl ShieldError {
    pub fn new(message: impl Into<String>) -> Self {
        ShieldError(message.into())
    }
}

impl fmt::Display for ShieldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for ShieldError {}

// `?` converts an error type to the function's return type via `From`. These
// impls are what let `?` turn an I/O or (de)serialization failure straight
// into a `ShieldError` everywhere in this crate.
impl From<std::io::Error> for ShieldError {
    fn from(err: std::io::Error) -> Self {
        ShieldError::new(err.to_string())
    }
}

impl From<serde_json::Error> for ShieldError {
    fn from(err: serde_json::Error) -> Self {
        ShieldError::new(err.to_string())
    }
}

impl From<serde_yaml::Error> for ShieldError {
    fn from(err: serde_yaml::Error) -> Self {
        ShieldError::new(err.to_string())
    }
}
