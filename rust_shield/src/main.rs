//! The `rust_shield` command: read environment/proposed-system plays from
//! stdin (one JSON `[env_play, sys_play]` pair per line) and print the safe
//! system response to play instead, one JSON object per line.

mod error;
mod mealy;
mod prop;
mod shield;
mod theory;
mod value;

use std::collections::{HashMap, VecDeque};
use std::io::{self, BufRead, Write};

use error::ShieldError;
use value::Value;

fn main() {
    if let Err(err) = run() {
        eprintln!("Error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), ShieldError> {
    let mealy_path = parse_args()?;

    let config = z3::Config::new();
    let ctx = z3::Context::new(&config);
    let (mut shield, max_fetch_depth) = mealy::load(&ctx, &mealy_path)?;

    process_plays(&mut shield, max_fetch_depth)
}

fn parse_args() -> Result<String, ShieldError> {
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--mealy" {
            return args.next().ok_or_else(|| ShieldError::new("--mealy requires a path"));
        }
    }
    Err(ShieldError::new("usage: rust_shield --mealy <path-to-mealy.yaml>"))
}

/// Reads plays from stdin until EOF, shielding each one and printing the
/// safe response Syntheos's mealy machine settled on.
fn process_plays(shield: &mut shield::Shield, max_fetch_depth: usize) -> Result<(), ShieldError> {
    let stdin = io::stdin();
    let mut stdout = io::stdout().lock();

    // The last `max_fetch_depth` plays, oldest first, so a formula's
    // `FETCH_x` (previous value of `x`) can be resolved by prefixing keys
    // from a past play and folding them into the current one.
    let mut prev_plays: VecDeque<HashMap<String, Value>> = VecDeque::new();

    for line in stdin.lock().lines() {
        let line = line?;
        let (env_play, sys_play): (HashMap<String, Value>, HashMap<String, Value>) = serde_json::from_str(&line)?;

        let mut full_env = env_play.clone();
        for (steps_back, play) in prev_plays.iter().rev().enumerate() {
            let prefix = "FETCH_".repeat(steps_back + 1);
            for (name, value) in play {
                full_env.insert(format!("{prefix}{name}"), value.clone());
            }
        }

        let mut response = shield.protect(&full_env, &sys_play)?;
        if response.is_none() {
            eprintln!("The proposed response was not valid");
            response = shield.protect(&full_env, &HashMap::new())?;
        }
        writeln!(stdout, "{}", serde_json::to_string(&response)?)?;

        if max_fetch_depth > 0 {
            let mut full_play = env_play;
            full_play.extend(response.unwrap_or_default());
            if prev_plays.len() == max_fetch_depth {
                prev_plays.pop_front();
            }
            prev_plays.push_back(full_play);
        }
    }
    Ok(())
}
