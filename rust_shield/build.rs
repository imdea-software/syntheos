use std::process::Command;

/// The one piece of "where is Z3" that a build script *can* handle: the
/// linker search path. `rust_shield` is a binary crate, so this crate's own
/// compile step is the final link of the whole program - a
/// `cargo:rustc-link-search` printed here lands directly in that link
/// command, no separate setup step needed.
///
/// (The other piece, z3-sys's `Z3_SYS_Z3_HEADER` env var, can't be handled
/// this way: it's read by a *different* crate's build script, which Cargo
/// runs as its own process with no channel for us to hand it an env var.
/// That one still has to live in `.cargo/config.toml` - see setup-z3.sh.)
fn main() {
    let Ok(output) = Command::new("brew").args(["--prefix", "z3"]).output() else {
        return; // no Homebrew - assume the system's default paths already work (true on most Linux distros)
    };
    if !output.status.success() {
        return;
    }
    let prefix = String::from_utf8_lossy(&output.stdout);
    println!("cargo:rustc-link-search=native={}/lib", prefix.trim());
}
