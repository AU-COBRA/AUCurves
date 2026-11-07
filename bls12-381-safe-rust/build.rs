// Build script for the BLS12-381 safe-rust crate.  All real work lives in
// build.sh (read it); this file runs it with $OUT_DIR and links the archive.
//
// - nasm available: CryptOpt mul/square replace the Rust stubs for
//   _bls12_mul and _bls12_square (cfg feature "cryptopt", set here).
//   BLS12_LEAVES=rust skips this and keeps the Rust stubs (to measure them).
// - feature "jasmin": build.sh also compiles the Jasmin tower and group
//   modules with jasminc ($JASMINC, default `jasminc`); failure is an error.
//   The leaves mul/square are then the Jasmin leaves of
//   generated/bls12_leaves_live.jazz on both paths (no CryptOpt linked),
//   or CryptOpt's with BLS12_JASMIN_LEAVES=cryptopt.  (cfg feature
//   "cryptopt" below means: mul/square come from the assembled leaves, so
//   the Rust stubs are not compiled.)

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(feature, values(\"cryptopt\"))");
    // libjade's SHAKE-128 (src/shake128.rs) is linked only when its assembly
    // generated/shake128.s is present (build.sh assembles it then).
    println!("cargo:rustc-check-cfg=cfg(shake128_jade)");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let script = manifest.join("build.sh");
    let jasmin = env::var_os("CARGO_FEATURE_JASMIN").is_some();
    let rust_leaves = env::var("BLS12_LEAVES").map(|v| v == "rust").unwrap_or(false);

    for f in ["build.sh", "generated/bls12_mul_cryptopt.asm", "generated/bls12_square_cryptopt.asm",
              "generated/jasmin_aliases.s", "generated/bls12_tower_regptr.jazz",
              "generated/bls12_group_regptr.jazz", "generated/bls12_leaves_live.jazz",
              "generated/bls12_tower_regptr_ffi.jazz", "generated/bls12_group_regptr_ffi.jazz"] {
        println!("cargo:rerun-if-changed={}", f);
    }
    println!("cargo:rerun-if-env-changed=BLS12_LEAVES");
    println!("cargo:rerun-if-env-changed=JASMINC");
    // feature `jasmin`: BLS12_JASMIN_LEAVES=jasmin (default) | cryptopt, see build.sh
    println!("cargo:rerun-if-env-changed=BLS12_JASMIN_LEAVES");

    if rust_leaves {
        assert!(!jasmin, "feature `jasmin` needs the CryptOpt leaves; unset BLS12_LEAVES");
        eprintln!("cargo:warning=BLS12_LEAVES=rust: Rust stub leaf ops");
        return;
    }
    let status = Command::new("sh")
        .arg(&script)
        .env("OUT_DIR", &out_dir)
        .env("BLS12_JASMIN", if jasmin { "1" } else { "0" })
        .current_dir(&manifest)
        .status();
    match status {
        Ok(s) if s.success() => {
            println!("cargo:rustc-link-search=native={}", out_dir.display());
            println!("cargo:rustc-link-lib=static=bls12_leaves");
            println!("cargo:rustc-cfg=feature=\"cryptopt\"");
            if manifest.join("generated/shake128.s").exists() {
                println!("cargo:rustc-cfg=shake128_jade");
            }
        }
        _ => {
            assert!(!jasmin, "feature `jasmin`: build.sh failed (jasminc / nasm / as missing?)");
            eprintln!("cargo:warning=build.sh failed (nasm missing?), using Rust stub leaf ops");
        }
    }
}
