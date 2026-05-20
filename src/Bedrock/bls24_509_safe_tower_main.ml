(** * Verified safe-Rust tower generator for BLS24-509 (8 limbs).
 *
 * Mirror of bls12_377_safe_tower_main.ml.  Applies the Coq-verified
 * [safe_rust_module] from [ToSafeRustBody.v] to [bls24_tower_funcs]
 * (= aggregated Fp/Fp2/Fp4/Fp8/Fp24/MillerLoop/FinalExp/pairing list
 * from BLS24_509_Extract).
 *
 * Usage:
 *   ./bls24_509_safe_tower <output.rs>
 *)

open Bls24_509_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  (* 8 = Zpos (XO (XO (XO XH)))  (binary 1000).  BLS24-509: 509 bits
     padded to 512 → 8 × 64-bit words. *)
  let n = Zpos (XO (XO (XO XH))) in
  let funcs = bls24_tower_funcs in
  let n_tower = Stdlib.List.length funcs in
  Printf.eprintf "[bls24_509_safe_tower] %d tower functions, 8 limbs\n" n_tower;
  let decls = ocaml_string (bls24_509_type_decls n) in
  let bodies = ocaml_string (bls24_509_safe_rust_module n funcs) in
  let leaf_wrappers = {|
unsafe extern "C" {
    fn _bls24_509_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_square(o: *mut u64, x: *const u64);
    fn _bls24_509_opp(o: *mut u64, x: *const u64);
    fn _bls24_509_felem_copy(o: *mut u64, x: *const u64);
    fn _bls24_509_from_word(o: *mut u64, w: u64);
    fn _bls24_509_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bls24_509_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bls24_509_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_square(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_opp(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_from_word(o: &mut Fp, w: u64) { unsafe { _bls24_509_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bls24_509_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bls24_509_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_inv(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }
/// Zero out an Fp.  Used by Fp2/.../Fp24 `_zero` constructors emitted
/// by the verified tower.  Not in the extern-C leaf set (Jasmin
/// doesn't generate a `_zero` symbol — it just emits the [u64;n] of
/// zeros), so we provide it as a safe-Rust definition here.
#[inline] pub fn bls24_509_zero(o: &mut Fp) { *o = Fp::zero(); }
/// Canonical Montgomery `1` for BLS24-509.  Reuses `from_word(1)`
/// (which goes through Jasmin's `to_montgomery` if needed).
#[inline] pub fn bls24_509_one(o: &mut Fp) { bls24_509_from_word(o, 1u64); }

/// Inverse in Fp2.  No closed bedrock2 body exists for BLS24's Fp2
/// (the [BLS24_509_MillerLoop_proof.v] only ships a [spec_of_]
/// instance).  We use the standard norm trick:
///   inv(a + b·u) = (a − b·u) / (a² − β·b²)
/// where β is the Fp2 non-residue (encoded in the bedrock2 emission
/// of `bls24_Fp2_mul_by_nr`: that helper computes `out := β · in` in
/// the base field Fp).
pub fn bls24_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut a_sq = Fp::zero();
    let mut b_sq = Fp::zero();
    let mut nr_b_sq = Fp::zero();
    let mut norm = Fp::zero();
    let mut norm_inv = Fp::zero();
    bls24_509_square(&mut a_sq, &x.c0);
    bls24_509_square(&mut b_sq, &x.c1);
    // β · b² (uses the verified `bls24_Fp2_mul_by_nr` body emitted above).
    bls24_Fp2_mul_by_nr(&mut nr_b_sq, &b_sq);
    bls24_509_sub(&mut norm, &a_sq, &nr_b_sq);
    bls24_509_inv(&mut norm_inv, &norm);
    bls24_509_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp::zero();
    bls24_509_opp(&mut neg_c1, &x.c1);
    bls24_509_mul(&mut out.c1, &neg_c1, &norm_inv);
}

/// Inverse in Fp4 = Fp2[v]/(v² − ξ).  Norm trick over Fp2 with the
/// non-residue mul by ξ (= `bls24_Fp2_mul_xi`).
pub fn bls24_Fp4_inv(out: &mut Fp4, x: &Fp4) {
    let mut c0_sq = Fp2::zero();
    let mut c1_sq = Fp2::zero();
    let mut xi_c1_sq = Fp2::zero();
    let mut norm = Fp2::zero();
    let mut norm_inv = Fp2::zero();
    bls24_Fp2_mul(&mut c0_sq, &x.c0, &x.c0);
    bls24_Fp2_mul(&mut c1_sq, &x.c1, &x.c1);
    bls24_Fp2_mul_xi(&mut xi_c1_sq, &c1_sq);
    bls24_Fp2_sub(&mut norm, &c0_sq, &xi_c1_sq);
    bls24_Fp2_inv(&mut norm_inv, &norm);
    bls24_Fp2_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp2::zero();
    bls24_Fp2_opp(&mut neg_c1, &x.c1);
    bls24_Fp2_mul(&mut out.c1, &neg_c1, &norm_inv);
}

/// Inverse in Fp8 = Fp4[v']/(v'² − v).  Norm trick over Fp4 with the
/// non-residue mul by v (= `bls24_Fp4_mul_by_v`).
pub fn bls24_Fp8_inv(out: &mut Fp8, x: &Fp8) {
    let mut c0_sq = Fp4::zero();
    let mut c1_sq = Fp4::zero();
    let mut v_c1_sq = Fp4::zero();
    let mut norm = Fp4::zero();
    let mut norm_inv = Fp4::zero();
    bls24_Fp4_mul(&mut c0_sq, &x.c0, &x.c0);
    bls24_Fp4_mul(&mut c1_sq, &x.c1, &x.c1);
    bls24_Fp4_mul_by_v(&mut v_c1_sq, &c1_sq);
    bls24_Fp4_sub(&mut norm, &c0_sq, &v_c1_sq);
    bls24_Fp4_inv(&mut norm_inv, &norm);
    bls24_Fp4_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp4::zero();
    bls24_Fp4_opp(&mut neg_c1, &x.c1);
    bls24_Fp4_mul(&mut out.c1, &neg_c1, &norm_inv);
}

|} in
  let text = decls ^ leaf_wrappers ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bls24_509_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
