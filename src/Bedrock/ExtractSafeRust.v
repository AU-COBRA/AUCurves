(** * ExtractSafeRust: Extract safe Rust wrappers to .rs files.
 *
 * Uses Rocq's [Redirect] command to write the generated Rust code
 * to standalone files for inclusion in Rust crates.
 *
 * Two layers are emitted:
 *   - Outer SAFE wrapper module ([bls12_381_safe.rs], [bn254_safe.rs]):
 *     newtype field types + [extern "C"] declarations + safe [pub fn]
 *     wrappers using [&T] / [&mut T] references. Built from a manually
 *     curated [wrapper_spec] list — independent of any bedrock2 source.
 *
 *   - Inner UNSAFE module ([bn254_pairing_inner.rs]): bedrock2 →
 *     unsafe Rust translation of the actual function bodies, via
 *     [ToRustString.rust_module]. The [extern "C"] symbols in the
 *     outer wrapper resolve to these.
 *
 * Path B (rust + jasmin, no C) takes both: outer + inner from this
 * extraction, leaf Fp ops swapped out for jasmin assembly via build.rs.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.
Require Import Bedrock.ToSafeRustString.
Require Import Bedrock.ToRustString.

(** Print BLS12-381 safe wrappers. *)
Redirect "bls12_381_safe.rs" Eval vm_compute in bls12_381_safe_rust.

(** Print BN254 safe wrappers. *)
Redirect "bn254_safe.rs" Eval vm_compute in bn254_safe_rust.

(* ================================================================ *)
(* Inner unsafe-Rust extraction (Path B)                              *)
(* ================================================================ *)

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Just the leaf Fp ops. *)
Definition bn254_leaf_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

(** Full tower: Fp base + Fp2 wrappers + Fp6/Fp12/pairing pipeline.
    Same list as [BN254_Extract.all_funcs] minus [Fp2_zero]/[Fp2_one]
    (which call [bn254_from_word] — never synthesized in [bn254_prime.v]).
    [vm_compute] resolves all Module Fp12 references to ground terms,
    so the [Extraction] command sees no nested modules. *)
(** [Fp2_inv] is excluded: it calls [bn254_inv] which is never
    synthesized in [bn254_prime.v]. The pairing pipeline does NOT use
    Fp2 inversion — [Fp12_inv] uses a conjugate/norm approach that
    avoids it.  [bn254_opp] and [bn254_Fp2_opp] are provided as
    small Rust implementations in [rust_prelude_opp] below. *)
Definition bn254_all_funcs_raw : list function_t :=
  bn254_leaf_funcs ++
  [ Fp2_felem_copy; Fp2_add; Fp2_sub;
    Fp2_mul; Fp2_sqr ] ++
  BN254_Pairing.bn254_all_pairing_funcs.

Definition bn254_all_funcs : list function_t :=
  Eval vm_compute in bn254_all_funcs_raw.

(** BN254-specific opp implementations needed by the pairing pipeline.
    These are not synthesized by fiat-crypto but are trivially correct:
    opp(x) = p - x where p is the BN254 prime. *)
(** Implementations / stubs for functions called by the tower but not
    synthesized by fiat-crypto's bedrock2 [Derive] steps. *)
Definition bn254_opp_prelude : string :=
  "const BN254_P: [u64; 4] = [0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];" ++ LF ++ LF ++
  "#[no_mangle]" ++ LF ++
  "pub unsafe extern ""C"" fn bn254_opp(out: u64, x: u64) {" ++ LF ++
  "    let mut borrow: u64 = 0;" ++ LF ++
  "    for i in 0..4 {" ++ LF ++
  "        let pi = BN254_P[i];" ++ LF ++
  "        let xi = _br2_load((x as *const u8).wrapping_add((i * 8) as usize) as *const usize);" ++ LF ++
  "        let (d, b1) = pi.overflowing_sub(xi);" ++ LF ++
  "        let (d2, b2) = d.overflowing_sub(borrow);" ++ LF ++
  "        _br2_store((out as *const u8).wrapping_add((i * 8) as usize) as *mut usize, d2);" ++ LF ++
  "        borrow = (b1 as u64) + (b2 as u64);" ++ LF ++
  "    }" ++ LF ++
  "}" ++ LF ++ LF ++
  "#[no_mangle]" ++ LF ++
  "pub unsafe extern ""C"" fn bn254_Fp2_opp(out: u64, x: u64) {" ++ LF ++
  "    bn254_opp(out, x);" ++ LF ++
  "    bn254_opp(out.wrapping_add(32), x.wrapping_add(32));" ++ LF ++
  "}" ++ LF ++ LF ++
  "/// Store a single u64 word into limb 0, zero the rest (4-limb field element)." ++ LF ++
  "#[no_mangle]" ++ LF ++
  "pub unsafe extern ""C"" fn bn254_from_word(out: u64, w: u64) {" ++ LF ++
  "    _br2_store(out as *mut usize, w);" ++ LF ++
  "    _br2_store((out as *const u8).wrapping_add(8) as *mut usize, 0);" ++ LF ++
  "    _br2_store((out as *const u8).wrapping_add(16) as *mut usize, 0);" ++ LF ++
  "    _br2_store((out as *const u8).wrapping_add(24) as *mut usize, 0);" ++ LF ++
  "}" ++ LF ++ LF ++
  "/// Fp inversion via Fermat's little theorem: x^(p-2) mod p." ++ LF ++
  "/// Uses a simple square-and-multiply chain with bn254_mul/bn254_square." ++ LF ++
  "#[no_mangle]" ++ LF ++
  "pub unsafe extern ""C"" fn bn254_inv(out: u64, x: u64) {" ++ LF ++
  "    // p-2 as big-endian bit string (254 bits)." ++ LF ++
  "    // We use a right-to-left binary method." ++ LF ++
  "    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];" ++ LF ++
  "    let mut base = [0u64; 4];" ++ LF ++
  "    let mut result = [0u64; 4];" ++ LF ++
  "    // Copy x into base" ++ LF ++
  "    for i in 0..4 { base[i] = _br2_load((x as *const u8).wrapping_add((i*8) as usize) as *const usize); }" ++ LF ++
  "    // result = 1 (Montgomery form: to_mont(1)). Actually start with x and adjust." ++ LF ++
  "    // Simpler: result = x, then do p-3 more squarings. But Fermat needs exact p-2." ++ LF ++
  "    // Use bn254_from_word to set result = 1 (NOT Montgomery form — this is raw 1)." ++ LF ++
  "    // For Montgomery: 1_mont = R mod p. We need the Montgomery representation." ++ LF ++
  "    // R = 2^256 mod p for BN254 = 0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb" ++ LF ++
  "    result = [0xac96341c4ffffffb, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f];" ++ LF ++
  "    let bp = base.as_ptr() as u64;" ++ LF ++
  "    let rp = result.as_mut_ptr() as u64;" ++ LF ++
  "    for limb_idx in 0..4 {" ++ LF ++
  "        let mut bits = p_minus_2[limb_idx];" ++ LF ++
  "        for _ in 0..64 {" ++ LF ++
  "            if bits & 1 == 1 {" ++ LF ++
  "                bn254_mul(rp, rp, bp);" ++ LF ++
  "            }" ++ LF ++
  "            bn254_square(bp, bp);" ++ LF ++
  "            bits >>= 1;" ++ LF ++
  "        }" ++ LF ++
  "    }" ++ LF ++
  "    // Copy result to out" ++ LF ++
  "    for i in 0..4 { _br2_store((out as *const u8).wrapping_add((i*8) as usize) as *mut usize, result[i]); }" ++ LF ++
  "}" ++ LF ++ LF ++
  "/// Fp2 inversion: (a+bu)^(-1) = conj / norm, norm = a^2 + b^2 (beta=-1)." ++ LF ++
  "#[no_mangle]" ++ LF ++
  "pub unsafe extern ""C"" fn bn254_Fp2_inv(out: u64, x: u64) {" ++ LF ++
  "    let mut asq = [0u64; 4];" ++ LF ++
  "    let mut bsq = [0u64; 4];" ++ LF ++
  "    let mut norm = [0u64; 4];" ++ LF ++
  "    let ap = asq.as_mut_ptr() as u64;" ++ LF ++
  "    let bp = bsq.as_mut_ptr() as u64;" ++ LF ++
  "    let np = norm.as_mut_ptr() as u64;" ++ LF ++
  "    bn254_square(ap, x);" ++ LF ++
  "    bn254_square(bp, x.wrapping_add(32));" ++ LF ++
  "    bn254_add(np, ap, bp);" ++ LF ++
  "    bn254_inv(np, np);" ++ LF ++
  "    bn254_mul(out, x, np);" ++ LF ++
  "    bn254_opp(ap, x.wrapping_add(32));" ++ LF ++
  "    bn254_mul(out.wrapping_add(32), ap, np);" ++ LF ++
  "}" ++ LF ++ LF.

(** OCaml extraction.
    The Coq pretty-printer stack-overflows on bedrock2 bodies because of
    O(n²) string concatenation in [String.append]; piping [rust_func]
    through OCaml's native strings emits the same text in linear time. *)
From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "src/Bedrock/bn254_rust_extracted"
  bn254_leaf_funcs bn254_all_funcs rust_func rust_prelude bn254_opp_prelude.
