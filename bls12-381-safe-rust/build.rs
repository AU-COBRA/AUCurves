// Build script for BLS12-381 safe-rust crate.
//
// When nasm is available: assembles CryptOpt mul/square and links them,
// replacing the Rust stubs for _bls12_mul and _bls12_square.
// When nasm is not available: falls back to pure-Rust stubs (slower).

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let script = manifest.join("build.sh");

    let status = Command::new("sh")
        .arg(&script)
        .env("OUT_DIR", &out_dir)
        .current_dir(&manifest)
        .status();

    match status {
        Ok(s) if s.success() => {
            println!("cargo:rustc-link-search=native={}", out_dir.display());
            println!("cargo:rustc-link-lib=static=bls12_leaves");
            println!("cargo:rustc-cfg=feature=\"cryptopt\"");
        }
        _ => {
            eprintln!("cargo:warning=build.sh failed (nasm missing?), using Rust stub leaf ops");
        }
    }

    println!("cargo:rerun-if-changed=build.sh");
    println!("cargo:rerun-if-changed=generated/bls12_mul_cryptopt.asm");
    println!("cargo:rerun-if-changed=generated/bls12_square_cryptopt.asm");
    println!("cargo:rerun-if-changed=generated/jasmin_aliases.s");
}
