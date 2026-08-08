use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let lib_dir = manifest_dir.join("../zig-out/lib");
    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=static=zevm");
    // zevm's own `ECRECOVER` precompile calls real libsecp256k1 too (see
    // the root build.zig's doc comment); `libzevm.a` references its symbols
    // but doesn't bundle them. Linked by exact path, not `-l secp256k1`,
    // since `-L` search order would resolve that to the *other*
    // `libsecp256k1.a` that the `secp256k1` crate's own `secp256k1-sys`
    // build script produces (same filename, different library).
    println!(
        "cargo:rustc-link-arg={}",
        lib_dir.join("libsecp256k1.a").display()
    );
    println!("cargo:rerun-if-changed={}", lib_dir.join("libzevm.a").display());
    println!("cargo:rerun-if-changed={}", lib_dir.join("libsecp256k1.a").display());
}
