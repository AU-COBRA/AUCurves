(** * Verified safe-Rust tower generator for BW6-761 (12 limbs).
 *
 * Mirror of [bls24_509_safe_tower_main.ml].  Applies the Coq-verified
 * [safe_rust_module] from [ToSafeRustBody.v] to [bw6_tower_funcs]
 * (= aggregated Fp3 + Fp6 + helpers + Miller loop + final
 * exponentiation list from [BW6_761_Extract], stripped of the base
 * Fp ops because those come from the hand-shimmed leaves wiring
 * `fiat-crypto/fiat-rust/src/bw6_761_64.rs` + the safegcd-rs
 * Bernstein-Yang inverter).
 *
 * Translation correctness: [SafeRustSimulation.safe_cmd_correct].
 *
 * Hand-written portion (heredoc below): 9 [extern "C"] declarations +
 * 9 safe Rust pointer-cast wrappers for the leaf Fp ops.  Note that
 * the BW6-761 prime is 761 bits / 12×u64 limbs, so the rd/wr helpers
 * are sized accordingly (vs BLS12-377's 6 limbs and BLS24-509's 8).
 *
 * Usage:
 *   ./bw6_761_safe_tower <output.rs>
 *)

open Bw6_761_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  (* 12 = Zpos (XO (XO (XI XH)))  (binary 1100).  WordByWordMontgomery.n
     derives limb count from the prime: BW6-761 is 761 bits → 12 ×
     64-bit words. *)
  let n = Zpos (XO (XO (XI XH))) in
  let funcs = bw6_tower_funcs in
  let n_tower = Stdlib.List.length funcs in
  Printf.eprintf "[bw6_761_safe_tower] %d tower functions, 12 limbs\n" n_tower;
  let decls = ocaml_string (bw6_761_type_decls n) in
  let bodies = ocaml_string (bw6_761_safe_rust_module n funcs) in
  let leaf_wrappers = {|
unsafe extern "C" {
    fn _bw6_761_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_square(o: *mut u64, x: *const u64);
    fn _bw6_761_opp(o: *mut u64, x: *const u64);
    fn _bw6_761_felem_copy(o: *mut u64, x: *const u64);
    fn _bw6_761_from_word(o: *mut u64, w: u64);
    fn _bw6_761_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bw6_761_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bw6_761_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_square(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_opp(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_from_word(o: &mut Fp, w: u64) { unsafe { _bw6_761_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bw6_761_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bw6_761_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_inv(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }
/// Zero out an Fp.  Used by Fp3/Fp6 `_zero` constructors emitted by
/// the verified tower.  No leaf-level `_zero` symbol is generated
/// (fiat-rust doesn't expose one), so we provide it in safe Rust.
#[inline] pub fn bw6_761_zero(o: &mut Fp) { *o = Fp::zero(); }
/// Canonical Montgomery `1` for BW6-761.  Reuses `from_word(1)`
/// (which goes through fiat-rust's `to_montgomery` under the hood).
#[inline] pub fn bw6_761_one(o: &mut Fp) { bw6_761_from_word(o, 1u64); }

/// Constant-time select on Fp3 (3-limb tower over Fp).
/// [GenericCubic.CE_funcs] doesn't emit a `_select_znz` entry, but
/// the `QE_funcs`-generated `bw6_761_Fp6_select_znz` body recurses
/// into it.  Componentwise call to the Fp leaf select.
#[inline] pub fn bw6_761_Fp3_select_znz(out: &mut Fp3, c: u64, x: &Fp3, y: &Fp3) {
    bw6_761_select_znz(&mut out.c0, c, &x.c0, &y.c0);
    bw6_761_select_znz(&mut out.c1, c, &x.c1, &y.c1);
    bw6_761_select_znz(&mut out.c2, c, &x.c2, &y.c2);
}

/// Inverse in Fp6 = Fp3[w]/(w^2 - zeta).  No closed bedrock2 body
/// exists for Fp6_inv (the [GenericQuadratic.QE_funcs] list does not
/// include inv — same constraint as BLS24's Fp2/Fp4/Fp8 layers).
/// We use the standard norm trick over Fp3:
///   inv(a + b·w) = (a − b·w) / (a² − zeta·b²)
/// where zeta is the Fp6 non-residue, encoded by
/// [bw6_761_Fp3_mul_by_zeta] (the verified emitter for "multiply by
/// zeta in Fp3").  Called by the verified [bw6_final_exp_easy] body.
pub fn bw6_761_Fp6_inv(out: &mut Fp6, x: &Fp6) {
    let mut a_sq = Fp3::zero();
    let mut b_sq = Fp3::zero();
    let mut zeta_b_sq = Fp3::zero();
    let mut norm = Fp3::zero();
    let mut norm_inv = Fp3::zero();
    bw6_761_Fp3_square(&mut a_sq, &x.c0);
    bw6_761_Fp3_square(&mut b_sq, &x.c1);
    bw6_761_Fp3_mul_by_zeta(&mut zeta_b_sq, &b_sq);
    bw6_761_Fp3_sub(&mut norm, &a_sq, &zeta_b_sq);
    bw6_761_Fp3_inv(&mut norm_inv, &norm);
    bw6_761_Fp3_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp3::zero();
    bw6_761_Fp3_opp(&mut neg_c1, &x.c1);
    bw6_761_Fp3_mul(&mut out.c1, &neg_c1, &norm_inv);
}

|} in
  let text = decls ^ leaf_wrappers ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bw6_761_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
