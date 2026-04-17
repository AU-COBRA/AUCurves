(** * Verified safe-Rust tower generator for BLS12-381 (6 limbs).
 *
 * Applies the Coq-verified [safe_rust_module] from [ToSafeRustBody.v]
 * to [bls12_tower_funcs] (= [BLS12_Pairing.bls12_all_pairing_funcs]).
 * Translation correctness: [SafeRustSimulation.safe_cmd_correct].
 *
 * Hand-written portion (heredoc below):
 *   - 9 [extern "C"] declarations + 9 safe Rust pointer-cast wrappers
 *     (leaf ops live in stubs.rs / Jasmin / CryptOpt)
 *   - Fp2 base wrappers (add/sub/mul/square/felem_copy/opp): BLS12
 *     bedrock2 sources only have WP proofs for these, not closed
 *     function bodies; bn254 has closed bodies in [bn254_Fp2.v] so
 *     they go through btranslate. Both encodings are equivalent and
 *     the wrappers are componentwise.
 *   - [bls12_Fp2_inv] (Fermat-style norm + componentwise mul, calls
 *     [_bls12_inv] from stubs.rs).
 *
 * Usage:
 *   ./bls12_safe_tower_main <output.rs>
 *)

open Bls12_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  let n = Zpos (XO (XI XH)) in  (* 6 limbs *)
  let funcs = bls12_tower_funcs in
  let n_tower = Stdlib.List.length funcs in
  Printf.eprintf "[bls12_safe_tower] %d tower functions, 6 limbs\n" n_tower;
  let decls = ocaml_string (type_decls n) in
  let bodies = ocaml_string (safe_rust_module n funcs) in
  let leaf_wrappers = {|
unsafe extern "C" {
    fn _bls12_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_square(o: *mut u64, x: *const u64);
    fn _bls12_opp(o: *mut u64, x: *const u64);
    fn _bls12_felem_copy(o: *mut u64, x: *const u64);
    fn _bls12_from_word(o: *mut u64, w: u64);
    fn _bls12_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bls12_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bls12_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_square(o: &mut Fp, x: &Fp) { unsafe { _bls12_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_opp(o: &mut Fp, x: &Fp) { unsafe { _bls12_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bls12_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_from_word(o: &mut Fp, w: u64) { unsafe { _bls12_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bls12_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bls12_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_Fp2_opp(o: &mut Fp2, x: &Fp2) { bls12_opp(&mut o.c0, &x.c0); bls12_opp(&mut o.c1, &x.c1); }
#[inline] pub fn bls12_Fp2_felem_copy(o: &mut Fp2, x: &Fp2) { bls12_felem_copy(&mut o.c0, &x.c0); bls12_felem_copy(&mut o.c1, &x.c1); }
#[inline] pub fn bls12_Fp2_add(o: &mut Fp2, x: &Fp2, y: &Fp2) { bls12_add(&mut o.c0, &x.c0, &y.c0); bls12_add(&mut o.c1, &x.c1, &y.c1); }
#[inline] pub fn bls12_Fp2_sub(o: &mut Fp2, x: &Fp2, y: &Fp2) { bls12_sub(&mut o.c0, &x.c0, &y.c0); bls12_sub(&mut o.c1, &x.c1, &y.c1); }
#[inline]
pub fn bls12_Fp2_mul(out: &mut Fp2, x: &Fp2, y: &Fp2) {
    let xv = *x; let yv = *y;
    let mut t0 = Fp::zero(); let mut t1 = Fp::zero();
    let mut t2 = Fp::zero(); let mut t3 = Fp::zero();
    bls12_mul(&mut t0, &xv.c0, &yv.c0);
    bls12_mul(&mut t1, &xv.c1, &yv.c1);
    bls12_mul(&mut t2, &xv.c0, &yv.c1);
    bls12_mul(&mut t3, &xv.c1, &yv.c0);
    bls12_sub(&mut out.c0, &t0, &t1);
    bls12_add(&mut out.c1, &t2, &t3);
}
#[inline]
pub fn bls12_Fp2_square(out: &mut Fp2, x: &Fp2) {
    let xv = *x; bls12_Fp2_mul(out, &xv, &xv);
}
#[inline]
pub fn bls12_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut asq = Fp::zero(); let mut bsq = Fp::zero(); let mut norm = Fp::zero();
    bls12_square(&mut asq, &x.c0); bls12_square(&mut bsq, &x.c1);
    bls12_add(&mut norm, &asq, &bsq);
    let n_copy = norm;
    unsafe { _bls12_inv(norm.0.as_mut_ptr(), n_copy.0.as_ptr()); }
    bls12_mul(&mut out.c0, &x.c0, &norm);
    let mut neg_b = Fp::zero(); bls12_opp(&mut neg_b, &x.c1);
    bls12_mul(&mut out.c1, &neg_b, &norm);
}
|} in
  let text = decls ^ leaf_wrappers ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bls12_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
