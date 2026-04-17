(** * Verified safe-Rust tower generator for BN446 (7 limbs).
 *
 * Mirror of [bn256_safe_tower_main.ml]. bn446_Fp2.v has closed bodies
 * so all Fp2 ops go through btranslate; only 9 leaf wrappers are
 * hand-written.
 *
 * Usage:
 *   ./bn446_safe_tower_main <output.rs>
 *)

open Bn446_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  (* 7 = Zpos (XI (XI XH))  (binary 111) *)
  let n = Zpos (XI (XI XH)) in
  let funcs = bn446_tower_funcs in
  let n_tower = Stdlib.List.length funcs in
  Printf.eprintf "[bn446_safe_tower] %d tower functions, 7 limbs\n" n_tower;
  let decls = ocaml_string (type_decls n) in
  let bodies = ocaml_string (safe_rust_module n funcs) in
  let leaf_wrappers = {|
unsafe extern "C" {
    fn _bn446_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_square(o: *mut u64, x: *const u64);
    fn _bn446_opp(o: *mut u64, x: *const u64);
    fn _bn446_felem_copy(o: *mut u64, x: *const u64);
    fn _bn446_from_word(o: *mut u64, w: u64);
    fn _bn446_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bn446_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bn446_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_square(o: &mut Fp, x: &Fp) { unsafe { _bn446_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_opp(o: &mut Fp, x: &Fp) { unsafe { _bn446_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bn446_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_from_word(o: &mut Fp, w: u64) { unsafe { _bn446_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bn446_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn446_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_inv(o: &mut Fp, x: &Fp) { unsafe { _bn446_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }

|} in
  let text = decls ^ leaf_wrappers ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bn446_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
