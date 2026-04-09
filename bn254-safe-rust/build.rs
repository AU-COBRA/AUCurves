use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let jazz = manifest.join("generated/bn254_leaves.jazz");

    // Check if jasminc is available
    let jasminc = env::var("JASMINC").unwrap_or_else(|_| "jasminc".to_string());

    let asm = out_dir.join("bn254_leaves.s");
    let obj = out_dir.join("bn254_leaves.o");

    // Step 1: jasminc -auto-spill → .s
    let status = Command::new(&jasminc)
        .arg("-auto-spill")
        .arg(&jazz)
        .arg("-o")
        .arg(&asm)
        .status();

    match status {
        Ok(s) if s.success() => {
            // Step 2: as → .o
            let as_status = Command::new("as")
                .arg(&asm)
                .arg("-o")
                .arg(&obj)
                .status()
                .expect("failed to run assembler");
            assert!(as_status.success(), "assembler failed");

            // Step 3: tell cargo to link the object file
            println!("cargo:rustc-link-search=native={}", out_dir.display());
            // Assemble the alias shim
            let alias_s = manifest.join("generated/jasmin_aliases.s");
            let alias_o = out_dir.join("jasmin_aliases.o");
            let alias_status = Command::new("as")
                .arg(&alias_s)
                .arg("-o")
                .arg(&alias_o)
                .status()
                .expect("failed to assemble aliases");
            assert!(alias_status.success(), "alias assembly failed");

            // CryptOpt-optimized bn254_mul (NASM intel syntax)
            // Verified equivalent to fiat-crypto reference via SMT
            let cryptopt_asm = manifest.join("generated/bn254_mul_cryptopt.asm");
            let cryptopt_obj = out_dir.join("bn254_mul_cryptopt.o");
            let cryptopt_alias = out_dir.join("bn254_mul_cryptopt_wrapper.s");
            // Generate AT&T-syntax wrapper that aliases bn254_mul → fiat_bn254_mul
            std::fs::write(&cryptopt_alias,
                ".text\n.global bn254_mul\nbn254_mul: jmp fiat_bn254_mul\n").unwrap();
            let cryptopt_alias_o = out_dir.join("bn254_mul_cryptopt_wrapper.o");
            let aw_status = Command::new("as")
                .arg(&cryptopt_alias).arg("-o").arg(&cryptopt_alias_o)
                .status().expect("failed to assemble cryptopt wrapper");
            assert!(aw_status.success());
            // Assemble CryptOpt NASM
            let nasm_status = Command::new("nasm")
                .arg("-f").arg("elf64")
                .arg(&cryptopt_asm)
                .arg("-o").arg(&cryptopt_obj)
                .status();
            let use_cryptopt = matches!(nasm_status, Ok(s) if s.success());
            if use_cryptopt {
                eprintln!("cargo:warning=using CryptOpt-optimized bn254_mul");
            } else {
                eprintln!("cargo:warning=nasm failed, falling back to Jasmin bn254_mul");
            }

            // Rename Jasmin's bn254_mul → bn254_mul_jasmin so the CryptOpt
            // version can claim the bn254_mul symbol without conflict.
            let obj_filtered = if use_cryptopt {
                let renamed = out_dir.join("bn254_leaves_renamed.o");
                let oc_status = Command::new("objcopy")
                    .arg("--redefine-sym=bn254_mul=bn254_mul_jasmin")
                    .arg(&obj)
                    .arg(&renamed)
                    .status()
                    .expect("failed to run objcopy");
                if oc_status.success() { renamed } else { obj.clone() }
            } else {
                obj.clone()
            };

            // Create a static lib from all .o files
            let lib = out_dir.join("libbn254_leaves.a");
            let mut ar_cmd = Command::new("ar");
            ar_cmd.arg("rcs").arg(&lib).arg(&obj_filtered).arg(&alias_o);
            if use_cryptopt {
                ar_cmd.arg(&cryptopt_obj).arg(&cryptopt_alias_o);
            }
            let ar_status = ar_cmd.status().expect("failed to run ar");
            assert!(ar_status.success(), "ar failed");
            println!("cargo:rustc-link-lib=static=bn254_leaves");

            // Enable the jasmin feature so stubs are excluded
            println!("cargo:rustc-cfg=feature=\"jasmin\"");
        }
        _ => {
            // jasminc not available — use stubs
            eprintln!("cargo:warning=jasminc not found, using stub leaf ops");
        }
    }

    println!("cargo:rerun-if-changed=generated/bn254_leaves.jazz");
    println!("cargo:rerun-if-changed=build.rs");
}
