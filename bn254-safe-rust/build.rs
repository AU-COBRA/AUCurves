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

            // Create a static lib from both .o files
            let lib = out_dir.join("libbn254_leaves.a");
            let ar_status = Command::new("ar")
                .arg("rcs")
                .arg(&lib)
                .arg(&obj)
                .arg(&alias_o)
                .status()
                .expect("failed to run ar");
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
