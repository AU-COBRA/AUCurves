(** * Verified safe-Rust tower generator for BN256 (5 limbs).
 *
 * Applies the Coq-verified [safe_rust_module] from [ToSafeRustBody.v]
 * to [bn256_tower_funcs] (= bn256 Fp2 base ops + bn256_all_pairing_funcs).
 * Translation correctness: [SafeRustSimulation.safe_cmd_correct].
 *
 * Hand-written portion (heredoc below): 9 [extern "C"] declarations +
 * 9 safe Rust pointer-cast wrappers for the leaf Fp ops.  Unlike BLS12,
 * NO Fp2 wrappers are needed — bn256_Fp2.v has closed function bodies
 * so all Fp2 ops go through btranslate.
 *
 * Usage:
 *   ./bn256_safe_tower_main <output.rs>
 *)

open Bn256_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  (* 4 = Zpos (XO (XO XH))  (binary 100).  WordByWordMontgomery.n derives
     limb count from the prime: BN256 is 256 bits exactly → 4 limbs. *)
  let n = Zpos (XO (XO XH)) in
  let funcs = bn256_tower_funcs in
  let n_tower = Stdlib.List.length funcs in
  Printf.eprintf "[bn256_safe_tower] %d tower functions, 4 limbs\n" n_tower;
  let decls = ocaml_string (type_decls n) in
  let bodies = ocaml_string (safe_rust_module n funcs) in
  let leaf_wrappers = {|
unsafe extern "C" {
    fn _bn256_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn256_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn256_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn256_square(o: *mut u64, x: *const u64);
    fn _bn256_opp(o: *mut u64, x: *const u64);
    fn _bn256_felem_copy(o: *mut u64, x: *const u64);
    fn _bn256_from_word(o: *mut u64, w: u64);
    fn _bn256_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bn256_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bn256_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn256_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn256_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn256_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn256_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn256_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn256_square(o: &mut Fp, x: &Fp) { unsafe { _bn256_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn256_opp(o: &mut Fp, x: &Fp) { unsafe { _bn256_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn256_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bn256_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn256_from_word(o: &mut Fp, w: u64) { unsafe { _bn256_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bn256_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn256_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn256_inv(o: &mut Fp, x: &Fp) { unsafe { _bn256_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }

|} in
  let text = decls ^ leaf_wrappers ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bn256_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
