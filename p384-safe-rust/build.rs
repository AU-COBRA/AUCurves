//! Build script for the P-384 safe-Rust crate.
//!
//! Chooses the implementation behind `fp_mul` and `fp_square` in
//! `src/lib.rs`.  The group law, the scalar multiplications and everything
//! else in the crate are the same in every configuration.
//!
//! # Field configurations, in order of precedence
//!
//! 1. `P384_NO_CRYPTOPT` set (any value): the fiat-rust leaves.  No assembly
//!    is linked, whatever else is set.
//! 2. `P384_S2N_FIELD=<path>` set: s2n-bignum's Montgomery multiply and
//!    square, `cfg(p384_s2n_field)`.  The path selects the form:
//!      * `*.a`: a static archive providing `bignum_montmul_p384` and
//!        `bignum_montsqr_p384`, e.g. s2n-bignum's `x86/libs2nbignum.a`;
//!      * `*.o`: an object file providing the same two symbols;
//!      * `*.s`: an assembly file providing `bignum_montmul_p384_encoded`
//!        only, assembled here with `as`.  This additionally sets
//!        `cfg(p384_s2n_montmul_only)`, under which `fp_square(x)` is
//!        `montmul(x, x)`.
//!    A set but unusable `P384_S2N_FIELD` (missing file, unknown extension,
//!    non-x86-64-Linux target, cross build, host without BMI2/ADX, assembler
//!    failure, `.s` without the expected symbol) FAILS THE BUILD.  The
//!    variable is an explicit request, and a silent fallback would let a
//!    benchmark report another configuration's numbers under this name.
//! 3. Otherwise: the CryptOpt assembly in `generated/`, `cfg(p384_cryptopt_asm)`,
//!    when the target is x86-64 Linux, the build is native, the host has BMI2
//!    and ADX, and `nasm` builds it; the fiat-rust leaves when any of these
//!    fails.
//!
//! The crate carries no path into another repository: the s2n-bignum
//! artifact is whatever `P384_S2N_FIELD` names.

use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.sh");
    println!("cargo:rerun-if-changed=generated/p384_mul_cryptopt.asm");
    println!("cargo:rerun-if-changed=generated/p384_square_cryptopt.asm");
    println!("cargo:rerun-if-env-changed=P384_NO_CRYPTOPT");
    println!("cargo:rerun-if-env-changed=P384_S2N_FIELD");
    println!("cargo:rustc-check-cfg=cfg(p384_cryptopt_asm)");
    println!("cargo:rustc-check-cfg=cfg(p384_s2n_field)");
    println!("cargo:rustc-check-cfg=cfg(p384_s2n_montmul_only)");

    if env::var_os("P384_NO_CRYPTOPT").is_some() {
        if env::var_os("P384_S2N_FIELD").is_some() {
            println!(
                "cargo:warning=P384_NO_CRYPTOPT and P384_S2N_FIELD both set; \
                 P384_NO_CRYPTOPT takes precedence: using fiat-rust field leaves"
            );
        } else {
            println!("cargo:warning=P384_NO_CRYPTOPT set; using fiat-rust field leaves");
        }
        return;
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());

    if let Some(path) = env::var_os("P384_S2N_FIELD") {
        s2n_field(Path::new(&path), &manifest, &out_dir);
        return;
    }

    if !native_x86_64_linux_with_bmi2_adx() {
        return;
    }

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

/// True when assembly using `mulx`/`adcx`/`adox` may be linked: a native
/// (non-cross) x86-64 Linux build on a host with BMI2 and ADX.  The CPU probe
/// speaks only for the host, hence the refusal to cross-compile; without both
/// features the assembly faults with SIGILL on first call.
fn native_x86_64_linux_with_bmi2_adx() -> bool {
    let target = env::var("TARGET").unwrap_or_default();
    let host = env::var("HOST").unwrap_or_default();
    if target != host || !target.starts_with("x86_64") || !target.contains("linux") {
        return false;
    }
    if !(std::is_x86_feature_detected!("bmi2") && std::is_x86_feature_detected!("adx")) {
        println!("cargo:warning=host lacks BMI2/ADX; using fiat-rust field leaves for P-384");
        return false;
    }
    true
}

/// Links the s2n-bignum field kernels named by `P384_S2N_FIELD`, or panics.
fn s2n_field(path: &Path, manifest: &Path, out_dir: &Path) {
    let path = if path.is_absolute() { path.to_path_buf() } else { manifest.join(path) };
    println!("cargo:rerun-if-changed={}", path.display());

    if !path.is_file() {
        panic!("P384_S2N_FIELD={}: no such file", path.display());
    }
    if !native_x86_64_linux_with_bmi2_adx() {
        panic!(
            "P384_S2N_FIELD is set, but the s2n-bignum kernels need a native \
             x86-64 Linux build on a host with BMI2 and ADX"
        );
    }

    // Every form ends as `$OUT_DIR/libp384_s2n_field.a`.
    let archive = out_dir.join("libp384_s2n_field.a");
    let _ = fs::remove_file(&archive);

    let ext = path.extension().and_then(OsStr::to_str).unwrap_or("");
    let montmul_only = match ext {
        "a" => {
            fs::copy(&path, &archive).unwrap_or_else(|e| {
                panic!("P384_S2N_FIELD: copying {} failed: {e}", path.display())
            });
            false
        }
        "o" => {
            run(Command::new("ar").arg("rcs").arg(&archive).arg(&path), "ar");
            false
        }
        "s" => {
            let text = fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("P384_S2N_FIELD: reading {} failed: {e}", path.display())
            });
            if !text.lines().any(|l| {
                let mut w = l.split_whitespace();
                w.next() == Some(".globl") && w.next() == Some("bignum_montmul_p384_encoded")
            }) {
                panic!(
                    "P384_S2N_FIELD={}: a `.s` source must define the global symbol \
                     `bignum_montmul_p384_encoded`",
                    path.display()
                );
            }
            let obj = out_dir.join("p384_s2n_montmul_encoded.o");
            run(Command::new("as").arg("--64").arg("-o").arg(&obj).arg(&path), "as");
            run(Command::new("ar").arg("rcs").arg(&archive).arg(&obj), "ar");
            true
        }
        _ => panic!(
            "P384_S2N_FIELD={}: expected a `.a` archive, a `.o` object or a `.s` \
             source",
            path.display()
        ),
    };

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=p384_s2n_field");
    println!("cargo:rustc-cfg=p384_s2n_field");
    if montmul_only {
        println!("cargo:rustc-cfg=p384_s2n_montmul_only");
    }
    println!(
        "cargo:warning=P-384 field leaves: s2n-bignum {} from {}",
        if montmul_only { "montmul (encoded; square = montmul(x, x))" } else { "montmul + montsqr" },
        path.display()
    );
}

fn run(cmd: &mut Command, tool: &str) {
    match cmd.status() {
        Ok(s) if s.success() => {}
        Ok(s) => panic!("P384_S2N_FIELD: `{tool}` exited with {s}"),
        Err(e) => panic!("P384_S2N_FIELD: cannot run `{tool}`: {e}"),
    }
}
