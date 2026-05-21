//! Build script for the BLS12-377 safe-rust crate.
//!
//! Two optional acceleration paths:
//!
//! * `jasmin_leaves` (default off): assembles the .s files in `asm/`
//!   produced by the verified rust_cmd_ed -> bedrock2 -> Jasmin
//!   pipeline at AUCurves/src/Jasmin/extractions/BLS12_377.v +
//!   bls377_main.ml driver.  When this feature is on, the
//!   `_bls377_{add,sub,select_znz}` extern symbols are provided by
//!   the Jasmin-emitted assembly instead of the Rust extern_shim in
//!   `lib.rs` (the shim is gated `cfg(not(feature="jasmin_leaves"))`).
//!
//!   Working leaves emitted by jasminc 2026.03.1:
//!     bls377_add, bls377_sub, bls377_select_znz.
//!
//!   Blocked (jasminc register-allocation failure on 6-limb body):
//!     bls377_mul, bls377_square, bls377_felem_copy (empty .s).
//!   These continue to come from the Rust extern_shim.
//!
//!   See AUCurves/HAND_WRITTEN_AUDIT.md and the build.rs comment in
//!   curve25519-jasmin-rs for the same pattern at fe25519 scale.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());

    if env::var("CARGO_FEATURE_JASMIN_LEAVES").is_ok() {
        // Assemble each .s file in asm/ + the aliases shim, then
        // archive into a static lib so the linker resolves the
        // _bls377_* extern symbols against it.
        let asm_dir = manifest.join("asm");
        let mut objects: Vec<PathBuf> = Vec::new();

        for fname in &["bls377_add", "bls377_sub", "bls377_select_znz",
                       "jasmin_aliases"] {
            let s_src = asm_dir.join(format!("{fname}.s"));
            let s_obj = out_dir.join(format!("b2j_{fname}.o"));
            if !s_src.exists() {
                panic!("missing asm input: {}", s_src.display());
            }
            let status = Command::new("as")
                .arg(&s_src).arg("-o").arg(&s_obj)
                .status().expect("as (GNU assembler) not found");
            assert!(status.success(), "as failed on {}", s_src.display());
            objects.push(s_obj);
            println!("cargo:rerun-if-changed={}", s_src.display());
        }

        let lib = out_dir.join("libbls377_jasmin_leaves.a");
        let mut ar = Command::new("ar");
        ar.arg("rcs").arg(&lib);
        for obj in &objects { ar.arg(obj); }
        let status = ar.status().expect("ar not found");
        assert!(status.success(), "ar failed");

        println!("cargo:rustc-link-search=native={}", out_dir.display());
        println!("cargo:rustc-link-lib=static=bls377_jasmin_leaves");
        // Tell rustc to treat _bls377_* as undefined-here so the
        // archive's symbols get linked.  Cargo's default behavior
        // already searches static libs for unresolved externs.
    }

    println!("cargo:rerun-if-changed=build.rs");
    // No-op when jasmin_leaves is off: defaults to the Rust extern_shim.
    let _ = Path::new("asm");
}
