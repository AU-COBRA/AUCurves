(** * Verified safe-Rust tower generator for BN254.
 *
 * This driver applies the Coq-verified [safe_rust_module] from
 * [ToSafeRustBody.v] to the BN254 function list. Unlike the old
 * [bn254_safe_tower.ml] (hand-written OCaml that reimplemented the
 * translation), this driver simply calls the EXTRACTED Coq function.
 * The translation is proven correct by [SafeRustSimulation.safe_cmd_correct].
 *
 * Usage:
 *   ./bn254_safe_tower_verified <output.rs>
 *)

open Bn254_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with
    | [_; o] -> o
    | _ -> Printf.eprintf "Usage: %s <output.rs>\n" Sys.argv.(0); exit 2
  in
  let n = Zpos (XO (XO XH)) in  (* 4 limbs *)
  let leaf_names = Stdlib.List.map (fun (n, _) -> ocaml_string n) bn254_leaf_funcs in
  let tower = Stdlib.List.filter
    (fun (n, _) -> not (Stdlib.List.mem (ocaml_string n) leaf_names))
    bn254_all_funcs in
  let n_tower = Stdlib.List.length tower in
  Printf.eprintf "[verified_safe_tower] %d tower functions\n" n_tower;
  let decls = ocaml_string (type_decls n) in
  let bodies = ocaml_string (safe_rust_module n tower) in
  (* LEAF WRAPPERS — the only hand-written Rust in this driver.
     These are NOT part of the verified tower (btranslate generates the
     51 tower functions above). They provide the interface to assembly
     leaves (Jasmin or fiat-crypto synthesized).

     TCB analysis:
     - 8 extern "C" decls: zero logic, just FFI name binding
     - 8 safe fn wrappers: zero logic, just pointer cast
     - bn254_Fp2_opp: 2 calls to bn254_opp — trivially correct
     - bn254_Fp2_inv: Fermat's Little Theorem with:
       * p-2 constant: derived from BN254 prime (verified)
       * Montgomery 1 = R mod p = 0xd35d438dc58f0d9d... (verified via Python)
       * Algorithm: standard norm-then-invert for Fp2 with beta=-1

     To eliminate: add bn254_Fp2_opp and bn254_Fp2_inv to the bedrock2
     function list (bn254_all_funcs_raw in ExtractSafeRust.v). Blocked
     on bn254_inv not being a synthesized leaf (fiat-crypto doesn't
     generate modular inversion). *)
  let leaf_wrappers = {|extern "C" {
    fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_mul(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_square(out: *mut u64, x: *const u64);
    fn _bn254_opp(out: *mut u64, x: *const u64);
    fn _bn254_felem_copy(out: *mut u64, x: *const u64);
    fn _bn254_from_word(out: *mut u64, w: u64);
    fn _bn254_select_znz(out: *mut u64, c: u64, x: *const u64, y: *const u64);
}
#[inline] pub fn bn254_add(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_add(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_sub(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_sub(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_mul(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_mul(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_square(out: &mut Fp, x: &Fp) { unsafe { _bn254_square(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_opp(out: &mut Fp, x: &Fp) { unsafe { _bn254_opp(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_felem_copy(out: &mut Fp, x: &Fp) { unsafe { _bn254_felem_copy(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_from_word(out: &mut Fp, w: u64) { unsafe { _bn254_from_word(out.0.as_mut_ptr(), w) } }
#[inline] pub fn bn254_select_znz(out: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn254_select_znz(out.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }

#[inline] pub fn bn254_Fp2_opp(out: &mut Fp2, x: &Fp2) { bn254_opp(&mut out.c0, &x.c0); bn254_opp(&mut out.c1, &x.c1); }

#[inline] pub fn bn254_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut asq = Fp::zero();
    let mut bsq = Fp::zero();
    let mut norm = Fp::zero();
    bn254_square(&mut asq, &x.c0);
    bn254_square(&mut bsq, &x.c1);
    bn254_add(&mut norm, &asq, &bsq);
    let mut base = norm;
    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];
    // Montgomery 1 = R mod p = 2^256 mod p (verified via Python)
    let mut result = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    for limb_idx in 0..4 {
        let mut bits = p_minus_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 { let r = result; bn254_mul(&mut result, &r, &base); }
            let b = base; bn254_square(&mut base, &b);
            bits >>= 1;
        }
    }
    norm = result;
    bn254_mul(&mut out.c0, &x.c0, &norm);
    let mut neg_b = Fp::zero();
    bn254_opp(&mut neg_b, &x.c1);
    bn254_mul(&mut out.c1, &neg_b, &norm);
}

|} in
  let text = decls ^ "\n" ^ leaf_wrappers ^ "\n" ^ bodies ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[verified_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
