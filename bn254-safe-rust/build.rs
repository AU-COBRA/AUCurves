// Thin wrapper around build.sh — all real work lives in the shell script
// for auditability. This file's only job is to:
//   1. Run build.sh with $OUT_DIR pointing at Cargo's per-build output dir
//   2. Tell Cargo to link the resulting libbn254_leaves.a
//
// Read build.sh to see what actually happens. It's 6 tool invocations.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    // `jasmin` is set below as a cfg, not declared in [features], because it
    // reflects whether build.sh succeeded rather than anything the caller
    // chooses.  Declare it to --check-cfg so it does not read as a typo.
    println!("cargo:rustc-check-cfg=cfg(feature, values(\"jasmin\"))");

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
            println!("cargo:rustc-link-lib=static=bn254_leaves");
            println!("cargo:rustc-cfg=feature=\"jasmin\"");
        }
        _ => {
            eprintln!("cargo:warning=build.sh failed (jasminc/nasm missing?), using stub leaf ops");
        }
    }

    println!("cargo:rerun-if-changed=build.sh");
    println!("cargo:rerun-if-changed=generated/bn254_leaves.jazz");
    println!("cargo:rerun-if-changed=generated/bn254_mul_cryptopt.asm");
    println!("cargo:rerun-if-changed=generated/jasmin_aliases.s");
}
