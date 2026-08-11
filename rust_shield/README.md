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

Needs [Rust](https://rustup.rs) and Z3. On macOS: `brew install z3`, then run
`./setup-z3.sh` once to generate `.cargo/config.toml` (machine-specific -
depends on where Homebrew put things - so it's gitignored, not committed).
On Linux, installing your distro's Z3 dev package (e.g. `apt install
libz3-dev`) is normally enough on its own, since it lands on the compiler's
default search path.

(Finding Z3 is split across two places for a reason: `build.rs` computes the
*linker* path automatically on every build - this crate is the final binary,
so its own build script can just tell the linker where to look. The *header*
path can't be done that way: it's read by a different crate's (`z3-sys`)
build script, and Cargo has no channel for one crate's build script to hand
an env var to another's - so that one has to already be sitting in
`.cargo/config.toml` before `cargo build` even starts, which is what
`setup-z3.sh` is for.)

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
- `build.rs` - points the linker at Homebrew's Z3, when present.

Solving is delegated to [Z3](https://github.com/Z3Prover/z3) via the `z3`
crate rather than reimplemented, so the rest of the code above can stay
straightforward Rust.
