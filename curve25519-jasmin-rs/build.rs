//! Build script: compile Jasmin .jazz and CryptOpt .asm to object files.
//!
//! Jasmin (full X25519 scalarmult, field ops): jasminc -> .s -> as -> .o
//! CryptOpt (mul, square): nasm -> .o
//!
//! Requires: jasminc, as (GNU), nasm

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Jasmin source files (compiled via jasminc -> as)
const JASMIN_FUNCS: &[&str] = &[
    // Full X25519 scalar multiplication (pure libjade path)
    "scalarmult",
    // CryptOpt-style inlined mul/sqr (same algorithm, optimized schedule)
    "scalarmult_cryptopt",
    // Individual field op exports (for hybrid Rust-ladder path)
    "curve25519_field_ops",
    // Vendored libjade SHA-512 (amd64/ref) — exports
    // `jade_hash_sha512_amd64_ref(hash, input, input_length)`.
    "sha512",
    // Vendored libjade SHA-256 (amd64/ref) — exports
    // `jade_hash_sha256_amd64_ref(hash, input, input_length)`.
    "sha256",
    // Vendored formosa-mlkem (amd64/ref) — exports
    // `jade_kem_mlkem_mlkem768_amd64_ref_{keypair,enc,dec,keypair_derand,enc_derand}`.
    // EasyCrypt-verified Jasmin compiler.
    "mlkem768",
];

/// CryptOpt superoptimized assembly (compiled via nasm)
const CRYPTOPT_FUNCS: &[&str] = &[
    "fiat_curve25519_solinas_mul",
    "fiat_curve25519_solinas_square",
];

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut objects = Vec::new();

    // Jasmin: .jazz -> jasminc -> .s -> as -> .o
    let jazz_dir = Path::new("jazz");
    for func in JASMIN_FUNCS {
        let jazz = jazz_dir.join(format!("{func}.jazz"));
        let asm = out_dir.join(format!("{func}.s"));
        let obj = out_dir.join(format!("{func}.o"));

        // Use jasminc from opam if not in PATH
        let jasminc = std::env::var("JASMINC")
            .unwrap_or_else(|_| "jasminc".to_string());
        let status = Command::new(&jasminc)
            .arg(&jazz).arg("-o").arg(&asm)
            .status().expect("jasminc not found — set JASMINC env var");
        assert!(status.success(), "jasminc failed on {}", jazz.display());

        let status = Command::new("as")
            .arg(&asm).arg("-o").arg(&obj)
            .status().expect("as not found");
        assert!(status.success(), "as failed on {}", asm.display());

        objects.push(obj);
        println!("cargo:rerun-if-changed={}", jazz.display());
    }
    // Rerun if any included Jasmin .jinc changes.
    for entry in std::fs::read_dir(jazz_dir).expect("jazz dir") {
        let p = entry.expect("jazz entry").path();
        if p.extension().map(|e| e == "jinc").unwrap_or(false) {
            println!("cargo:rerun-if-changed={}", p.display());
        }
    }

    // Optional: jasminc_leaves feature.  Compiles ed25519_xyzt_copy.jazz
    // (hand-written .jazz for the 200-byte copy leaf, but matching the
    // function name + signature emitted by the verified rust_cmd_ed ->
    // Jasmin.expr.cmd pipeline at
    // AUCurves/src/Jasmin/ExtractXyztCopyReal.v).
    let jasminc_leaves_active = env::var("CARGO_FEATURE_JASMINC_LEAVES").is_ok();
    if jasminc_leaves_active {
        let func = "ed25519_xyzt_copy";
        let jazz = jazz_dir.join(format!("{func}.jazz"));
        let asm = out_dir.join(format!("{func}.s"));
        let obj = out_dir.join(format!("{func}.o"));
        let jasminc = std::env::var("JASMINC")
            .unwrap_or_else(|_| "jasminc".to_string());
        let status = Command::new(&jasminc)
            .arg(&jazz).arg("-o").arg(&asm)
            .status().expect("jasminc not found — set JASMINC env var");
        assert!(status.success(), "jasminc failed on {}", jazz.display());
        let status = Command::new("as")
            .arg(&asm).arg("-o").arg(&obj)
            .status().expect("as not found");
        assert!(status.success(), "as failed on {}", asm.display());
        objects.push(obj);
        println!("cargo:rerun-if-changed={}", jazz.display());
    }

    // CryptOpt: .asm (NASM Intel syntax) -> nasm -> .o
    let co_dir = Path::new("cryptopt");
    for func in CRYPTOPT_FUNCS {
        let nasm_src = co_dir.join(format!("{func}.asm"));
        let obj = out_dir.join(format!("{func}.o"));

        let status = Command::new("nasm")
            .args(["-f", "elf64"])
            .arg("-o").arg(&obj)
            .arg(&nasm_src)
            .status().expect("nasm not found");
        assert!(status.success(), "nasm failed on {}", nasm_src.display());

        objects.push(obj);
        println!("cargo:rerun-if-changed={}", nasm_src.display());
    }

    // Fiat-crypto C backend: x25519_fiat.c (includes fiat_curve25519_64.c)
    let c_dir = Path::new("c");
    let c_src = c_dir.join("x25519_fiat.c");
    let c_obj = out_dir.join("x25519_fiat.o");
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let status = Command::new(&cc)
        .args(["-O3", "-march=native", "-c", "-o"])
        .arg(&c_obj)
        .arg(&c_src)
        .arg(format!("-I{}", c_dir.display()))
        .status().expect("C compiler not found");
    assert!(status.success(), "cc failed on {}", c_src.display());
    objects.push(c_obj);
    println!("cargo:rerun-if-changed={}", c_src.display());
    println!("cargo:rerun-if-changed=c/fiat_curve25519_64.c");

    // Bedrock2 ToCString extraction: x25519_bedrock2.c (full verified chain)
    let b2_src = c_dir.join("x25519_bedrock2.c");
    let b2_obj = out_dir.join("x25519_bedrock2.o");
    let status = Command::new(&cc)
        .args(["-O3", "-march=native", "-c", "-o"])
        .arg(&b2_obj)
        .arg(&b2_src)
        .status().expect("C compiler not found");
    assert!(status.success(), "cc failed on {}", b2_src.display());
    objects.push(b2_obj);
    println!("cargo:rerun-if-changed={}", b2_src.display());

    // Bedrock2 -> Jasmin-compiled field ops (partial: 7/11 functions that
    // pass jasminc's register allocator + asmgen).  Each .s is the output
    // of `x25519_64_main --func <name>` with our extraction pipeline:
    //   bedrock2 cmd -> tr_cmd (Qed) -> polish_func (30 Qed) ->
    //     to_jasmin_cmd (17 Qed, 2 ident axioms) ->
    //     Jasmin Compile.compile (jasminc, Rocq-verified) -> x86-64
    // Blocked on register pressure: fe25519_mul, fe25519_square,
    //   fe25519_to_bytes, fe25519_from_bytes.
    // Blocked on var-conflict: ladderstep, montladder, x25519, x25519_base.
    let asm_dir = Path::new("asm");
    // When `cryptopt_leaves` is active, the bedrock2-Jasmin 5×64
    // `fe25519_add` / `fe25519_sub` symbols collide with the 4×64
    // CryptOpt shim's `fe25519_*` `#[unsafe(no_mangle)]` exports.
    // The b2j path is only exercised by the `bedrock2_jasmin::*` API in
    // tests, so we drop those two .s files (and only those two) when
    // the cryptopt feature is on.
    let cryptopt_active = env::var("CARGO_FEATURE_CRYPTOPT_LEAVES").is_ok();
    let b2_jasmin_funcs: Vec<&str> = if cryptopt_active {
        vec!["fe25519_scmula24", "felem_cswap", "fe25519_copy",
             "fe25519_from_word", "clamp_64"]
    } else {
        vec!["fe25519_add", "fe25519_sub", "fe25519_scmula24",
             "felem_cswap", "fe25519_copy", "fe25519_from_word",
             "clamp_64"]
    };
    for fname in b2_jasmin_funcs {
        let s_src = asm_dir.join(format!("{fname}.s"));
        let s_obj = out_dir.join(format!("b2j_{fname}.o"));
        if s_src.exists() {
            let status = Command::new("as")
                .arg(&s_src).arg("-o").arg(&s_obj)
                .status().expect("as not found");
            assert!(status.success(), "as failed on {}", s_src.display());
            objects.push(s_obj);
            println!("cargo:rerun-if-changed={}", s_src.display());
        }
    }

    // Archive all .o into a static lib
    let lib = out_dir.join("libcurve25519_jasmin_asm.a");
    let mut ar = Command::new("ar");
    ar.arg("rcs").arg(&lib);
    for obj in &objects { ar.arg(obj); }
    let status = ar.status().expect("ar not found");
    assert!(status.success(), "ar failed");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=curve25519_jasmin_asm");
}
