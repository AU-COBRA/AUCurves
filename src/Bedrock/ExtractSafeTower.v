(** * Extract safe Rust tower for BN254, directly from Rocq. *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.BN254_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Tower functions: Fp2 base + all pairing funcs (Fp6/Fp12/miller/...).
    Excludes leaf Fp ops and Fp2_inv (needs bn254_inv). *)
Definition bn254_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr ].

Definition bn254_tower_funcs : list function_t :=
  Eval vm_compute in
    (bn254_fp2_funcs ++ BN254_Pairing.bn254_all_pairing_funcs).

Definition leaf_wrappers : string :=
  "extern ""C"" {" ++ LF ++
  "    fn _bn254_add(o: *mut u64, x: *const u64, y: *const u64);" ++ LF ++
  "    fn _bn254_sub(o: *mut u64, x: *const u64, y: *const u64);" ++ LF ++
  "    fn _bn254_mul(o: *mut u64, x: *const u64, y: *const u64);" ++ LF ++
  "    fn _bn254_square(o: *mut u64, x: *const u64);" ++ LF ++
  "    fn _bn254_opp(o: *mut u64, x: *const u64);" ++ LF ++
  "    fn _bn254_felem_copy(o: *mut u64, x: *const u64);" ++ LF ++
  "    fn _bn254_from_word(o: *mut u64, w: u64);" ++ LF ++
  "    fn _bn254_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);" ++ LF ++
  "}" ++ LF ++
  "#[inline] pub fn bn254_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_square(o: &mut Fp, x: &Fp) { unsafe { _bn254_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_opp(o: &mut Fp, x: &Fp) { unsafe { _bn254_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bn254_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_from_word(o: &mut Fp, w: u64) { unsafe { _bn254_from_word(o.0.as_mut_ptr(), w) } }" ++ LF ++
  "#[inline] pub fn bn254_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn254_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }" ++ LF ++
  "#[inline] pub fn bn254_Fp2_opp(o: &mut Fp2, x: &Fp2) { bn254_opp(&mut o.c0, &x.c0); bn254_opp(&mut o.c1, &x.c1); }" ++ LF ++
  "#[inline]" ++ LF ++
  "pub fn bn254_Fp2_inv(out: &mut Fp2, x: &Fp2) {" ++ LF ++
  "    let mut asq = Fp::zero();" ++ LF ++
  "    let mut bsq = Fp::zero();" ++ LF ++
  "    let mut norm = Fp::zero();" ++ LF ++
  "    bn254_square(&mut asq, &x.c0);" ++ LF ++
  "    bn254_square(&mut bsq, &x.c1);" ++ LF ++
  "    bn254_add(&mut norm, &asq, &bsq);" ++ LF ++
  "    // Fp inversion via Fermat: norm^(p-2)" ++ LF ++
  "    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];" ++ LF ++
  "    let mut base = norm;" ++ LF ++
  "    // Montgomery 1 = R mod p" ++ LF ++
  "    let mut result = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);" ++ LF ++
  "    for limb_idx in 0..4 {" ++ LF ++
  "        let mut bits = p_minus_2[limb_idx];" ++ LF ++
  "        for _ in 0..64 {" ++ LF ++
  "            if bits & 1 == 1 { let r = result; bn254_mul(&mut result, &r, &base); }" ++ LF ++
  "            let b = base; bn254_square(&mut base, &b);" ++ LF ++
  "            bits >>= 1;" ++ LF ++
  "        }" ++ LF ++
  "    }" ++ LF ++
  "    norm = result;" ++ LF ++
  "    bn254_mul(&mut out.c0, &x.c0, &norm);" ++ LF ++
  "    let mut neg_b = Fp::zero();" ++ LF ++
  "    bn254_opp(&mut neg_b, &x.c1);" ++ LF ++
  "    bn254_mul(&mut out.c1, &neg_b, &norm);" ++ LF ++
  "}" ++ LF ++ LF.

Definition bn254_safe_tower_rs : string :=
  Eval vm_compute in
    (type_decls 4 ++ leaf_wrappers ++ safe_rust_module 4 bn254_tower_funcs).

Redirect "bn254_safe_tower_rocq.rs" Eval vm_compute in bn254_safe_tower_rs.
