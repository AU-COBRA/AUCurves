//! Build script for the P-384 safe-Rust crate.
//!
//! Optionally links the two CryptOpt-superoptimized field leaves in
//! `generated/` and sets `cfg(p384_cryptopt_asm)`, which makes `fp_mul` and
//! `fp_square` in `src/lib.rs` route to them instead of to fiat-rust.
//!
//! The link happens only when ALL of the following hold:
//!
//!   * target arch is x86-64 (the assembly is System-V x86-64),
//!   * the build HOST supports BMI2 and ADX (the assembly uses `mulx`,
//!     `adcx`, `adox`), and the build is not cross-compiling, so host
//!     support implies target support,
//!   * `nasm` and `ar` are on PATH and the assembly builds.
//!
//! Otherwise the crate falls back to the fiat-rust leaves and behaves
//! exactly as it did before, with no assembly in the binary.  Set
//! `P384_NO_CRYPTOPT=1` in the environment to force the fallback.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.sh");
    println!("cargo:rerun-if-changed=generated/p384_mul_cryptopt.asm");
    println!("cargo:rerun-if-changed=generated/p384_square_cryptopt.asm");
    println!("cargo:rerun-if-env-changed=P384_NO_CRYPTOPT");
    println!("cargo:rustc-check-cfg=cfg(p384_cryptopt_asm)");

    if env::var_os("P384_NO_CRYPTOPT").is_some() {
        println!("cargo:warning=P384_NO_CRYPTOPT set; using fiat-rust field leaves");
        return;
    }

    // The assembly is x86-64 System-V.  Refuse to link it into anything else,
    // and refuse when cross-compiling, because the CPU-feature probe below
    // can only speak for the host.
    let target = env::var("TARGET").unwrap_or_default();
    let host = env::var("HOST").unwrap_or_default();
    if target != host || !target.starts_with("x86_64") || !target.contains("linux") {
        return;
    }

    // `mulx` is BMI2; `adcx`/`adox` are ADX.  Without both, the assembly
    // would fault with SIGILL on first call.
    if !(std::is_x86_feature_detected!("bmi2") && std::is_x86_feature_detected!("adx")) {
        println!(
            "cargo:warning=host lacks BMI2/ADX; using fiat-rust field leaves for P-384"
        );
        return;
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());

    let status = Command::new("sh")
        .arg(manifest.join("build.sh"))
        .env("OUT_DIR", &out_dir)
        .current_dir(&manifest)
        .status();

    match status {
        Ok(s) if s.success() => {
            println!("cargo:rustc-link-search=native={}", out_dir.display());
            println!("cargo:rustc-link-lib=static=p384_cryptopt");
            println!("cargo:rustc-cfg=p384_cryptopt_asm");
        }
        _ => {
            println!(
                "cargo:warning=build.sh failed (nasm missing?); \
                 using fiat-rust field leaves for P-384"
            );
        }
    }
}
