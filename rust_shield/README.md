# rust_shield

A Rust rewrite of [shield](../shield): a standalone runtime shield for a
Mealy machine synthesized by [Syntheos](..). Given a mealy machine saved via
`syntheos --save-mealy`, it reads environment/proposed-system plays from
stdin (one JSON `[env_play, sys_play]` pair per line) and prints the safe
system response to play instead, one JSON object per line.

## Usage

```
cargo run --release -- --mealy path/to/mealy.yaml < plays.jsonl
```

## Development

Needs [Rust](https://rustup.rs) and Z3 (`brew install z3` on macOS - see
`.cargo/config.toml` for how the build finds it).

```
cargo build
cargo test
```

## Code tour

- `main.rs` - the CLI: reads plays from stdin, tracks the last few plays for
  `FETCH_` (previous-value) lookups, prints responses.
- `mealy.rs` - loads a mealy machine's YAML into a `Shield`.
- `prop.rs` - parses the small propositional formulas over literal ids that
  label a mealy machine's edges (e.g. `0&!1`).
- `theory.rs` - parses and compiles the arithmetic atoms a literal expands to
  (e.g. `(< (+ FETCH_w 200) w)`) into Z3 expressions.
- `shield.rs` - the actual shield: walk the mealy machine's graph, and for
  each step ask Z3 for an edge (and a concrete system response) consistent
  with what actually happened.
- `value.rs`, `error.rs` - small shared types.

Solving is delegated to [Z3](https://github.com/Z3Prover/z3) via the `z3`
crate rather than reimplemented, so the rest of the code above can stay
straightforward Rust.
