(** * BLS12_G1ArenaRust — the BLS12-381 G1 bedrock2 functions printed as safe Rust.

    Collects the bedrock2 functions behind the verified Pippenger MSM
    [BLS12_MSM.msm_bls12], the verified scalar multiplication
    [BLS12_G1_ScalarMul.g1_scalar_mul] and the a = 0 complete projective
    group law, instantiated at BLS12-381, and prints them with
    [ToSafeRustArena.rust_module].  The text is written to
    [bls12-381-safe-rust/src/g1_msm_extracted.rs] by
    [scripts/emit_bls12_g1_rust.sh] (driver [scripts/EmitBLS12G1Rust.v]),
    and [scripts/check_bls12_g1_extraction.sh] checks it byte for byte.

    Nothing in this file changes or re-proves verified code; it only
    names instances.  The functions and what backs them:

    - ["msm_bls12"]: [BLS12_MSM.msm_bls12] with callee names
      ["msm_curve_add"], ["msm_curve_double"], ["store_zero"].
      [BLS12_MSM_Closed.msm_bls12_closed] (Qed, closed) proves that, in
      an environment with exactly these bodies and the field-leaf
      contracts, it returns a triple projectively equal to sum k_i P_i
      for on-curve inputs; the chain is [BLS12_MSM.msm_bls12_prog_ok]
      (program order, no algebraic premise), [BLS12_MSM_Functional]
      ([msm_prog_rcb_correct], [wval_limbs]) and [BLS12_MSM_Wrappers]
      (the three callee contracts, discharged).
    - ["g1_scalar_mul"]: [BLS12_G1_ScalarMul.g1_scalar_mul] (double-and-add,
      most significant bit first, 256 bits) with the same three callees.
      [BLS12_MSM_Closed.g1_scalar_mul_closed] (Qed, closed) proves that it
      returns a triple projectively equal to k P for an on-curve P; the
      chain is [BLS12_G1_ScalarMul.g1_scalar_mul_ok] (program order) and
      [BLS12_G1_ScalarMul.smul_prog_rcb_correct] / [bits_limbs].
      It branches on the scalar bits (variable time): for public scalars only.
    - ["g1_scalar_mul_ct"]: [BLS12_G1_ScalarMulCT.g1_scalar_mul_ct], the
      constant-time variant (per bit: double, unconditional out-of-place
      ["curve_add"] into three caller scratch buffers, three ["ct_cswap"]);
      [BLS12_G1_CT_Closed.g1_scalar_mul_ct_closed] (Qed, closed): same
      conclusion as ["g1_scalar_mul"].
    - ["ct_cswap"]: [CtSwap.ct_cswap] at 6 words (fiat-crypto's
      felem_cswap generalised to n words), [CtSwap.ct_cswap_call] (Qed).
    - ["curve_add"]: [CurveAdd.ladderstep_body] — RCB 2015 Algorithm 7,
      the a = 0 complete homogeneous addition, derived by Rupicola;
      [CurveAdd.ladderstep_correct] (Qed).
    - ["curve_double_a0"]: [PointDoubleA0.rcb_double_a0_body] — RCB 2015
      Algorithm 9, complete homogeneous doubling;
      [PointDoubleA0.rcb_double_a0_correct] (Qed), and
      [rcb_double_a0_eq_ladderstep] (Qed) relates it to the addition.
    - ["store_zero"]: [StoreZero.store_zero_func] (writes (0 : 1 : 0));
      contract [StoreZero3OK] by [BLS12_MSM_Wrappers.store_zero_ok3].
    - ["bls12_three_b"]: [bls12_three_b.bls12_three_b] (Montgomery 3b),
      [bls12_three_b_ok] (Qed).
    - ["bls12_felem_copy"]: [bls12_felem_copy.bls12_felem_copy],
      [felem_copy_ok] (Qed).
    - ["msm_curve_add"]: [BLS12_MSM_MixedAdd.msm_curve_add_mixed] (also the
      callee of ["g1_scalar_mul"]): if the six words of Z2 are those of 1
      in the Montgomery representation (the affine input points of an
      MSM), RCB 2015 Algorithm 8, the complete mixed addition
      ([MixedAddA0.madd_a0_cmd], derived by Rupicola, outputs written
      once, after the last read of the inputs, so correct in place);
      otherwise a copy-out wrapper of ["curve_add"]: the derived body
      with stack temporaries as outputs, then copied into the output
      pointers, so that the MSM's aliased calls (output = first input)
      are well-defined whatever order the derived body writes its
      outputs in.  [CurveAddAliasedOK] holds for it by
      [BLS12_MSM_MixedAdd.msm_curve_add_mixed_ok] (via [RcbAnyOut], which
      re-derives the RCB bodies with unconstrained output buffers).
    - ["msm_curve_double"]: the copy-out wrapper DEFINED HERE for
      ["curve_double_a0"]; [CurveDoubleInplaceOK] by
      [BLS12_MSM_Wrappers.copy_out_double_ok].

    The field leaves ["bls12_mul"], ["bls12_add"], ["bls12_sub"] and the
    constant stores ["bls12_zero"], ["bls12_one"] are not printed: the
    Rust runtime routes them to the crate's own leaves
    ([bls12-381-safe-rust/src/bedrock_rt.rs]). *)

From Stdlib Require Import String List ZArith.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Import Bedrock.BLS12_G1_ScalarMulCT.
Require Import Bedrock.Group.CurveAdd.CtSwap.
Require Bedrock.BLS12_MSM_MixedAdd.
Require Import Bedrock.ToSafeRustArena.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Import ToSafeRustArena (function_t).

Section BLS12G1.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Definition g1_three_b_name : string := "bls12_three_b".

  Definition g1_curve_add : function_t :=
    ("curve_add", ladderstep_body (width:=64) (BW:=BW64) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)
       (field_parameters:=bls12_field_parameters) (field_representation:=bls12_frep)
       g1_three_b_name).

  Definition g1_curve_double_a0 : function_t :=
    ("curve_double_a0", rcb_double_a0_body (width:=64) (BW:=BW64) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)
       (field_parameters:=bls12_field_parameters) (field_representation:=bls12_frep)
       g1_three_b_name).

  Definition g1_store_zero : function_t :=
    store_zero_func (zero_name := "bls12_zero") (one_name := "bls12_one").

  Definition g1_three_b : function_t := ("bls12_three_b", bls12_three_b).

  Definition g1_felem_copy : function_t := ("bls12_felem_copy", bls12_felem_copy).

  Definition fbytes : Z := felem_size_in_bytes.

  (** Copy-out wrapper: [callee(ins..., tx, ty, tz); copy(outs, t)]. *)
  Definition copy_out_wrapper (name callee : string) (ins outs : list string)
    : function_t :=
    (name,
     (ins ++ outs, [],
      cmd.stackalloc "tx" fbytes
      (cmd.stackalloc "ty" fbytes
      (cmd.stackalloc "tz" fbytes
        (cmd.seq
          (cmd.call [] callee
             (List.map expr.var (ins ++ ["tx"; "ty"; "tz"])))
        (cmd.seq
          (cmd.call [] "bls12_felem_copy" [expr.var (nth 0 outs ""); expr.var "tx"])
        (cmd.seq
          (cmd.call [] "bls12_felem_copy" [expr.var (nth 1 outs ""); expr.var "ty"])
          (cmd.call [] "bls12_felem_copy" [expr.var (nth 2 outs ""); expr.var "tz"])))))))%list).

  (** The MSM's addition: RCB Algorithm 8 (mixed) when Z2 is the word list of 1, else the
      copy-out wrapper of [curve_add] (BLS12_MSM_MixedAdd.v). *)
  Definition msm_curve_add : function_t := BLS12_MSM_MixedAdd.msm_curve_add_mixed.

  Definition msm_curve_double : function_t :=
    copy_out_wrapper "msm_curve_double" "curve_double_a0"
      ["Xin"; "Yin"; "Zin"] ["Xout"; "Yout"; "Zout"].

  Definition g1_msm : function_t :=
    @msm_bls12 64 BW64 _ _ bls12_field_parameters bls12_frep
      "msm_curve_add" "msm_curve_double" "store_zero".

  Definition g1_smul : function_t :=
    g1_scalar_mul "msm_curve_add" "msm_curve_double" "store_zero".

  (** Constant-time scalar multiplication: the out-of-place ["curve_add"]
      into caller scratch, then three ["ct_cswap"] calls per bit. *)
  Definition g1_smul_ct : function_t :=
    g1_scalar_mul_ct "curve_add" "msm_curve_double" "store_zero".

  Definition g1_ct_cswap : function_t :=
    ("ct_cswap", ct_cswap (word:=BasicC64Semantics.word) felem_size_in_words).

  Definition bls12_g1_funcs : list function_t :=
    [g1_msm; g1_smul; msm_curve_add; msm_curve_double; g1_curve_add;
     g1_curve_double_a0; g1_store_zero; g1_three_b; g1_felem_copy;
     g1_smul_ct; g1_ct_cswap].
End BLS12G1.

Definition bls12_g1_rs_header : list string :=
  [ "//! Rocq-EMITTED safe Rust: BLS12-381 G1 Pippenger MSM, scalar";
    "//! multiplication and complete projective group law (bedrock2), printed by";
    "//! src/Bedrock/ToSafeRustArena.v from the function list";
    "//! [bls12_g1_funcs] of src/Bedrock/BLS12_G1ArenaRust.v.";
    "//!";
    "//! DO NOT EDIT.  Regenerate with scripts/emit_bls12_g1_rust.sh;";
    "//! scripts/check_bls12_g1_extraction.sh checks it byte for byte.";
    "//! Only the Rocq string quoting has been stripped.";
    "//!";
    "//! See src/Bedrock/BLS12_G1ArenaRust.v for the theorem behind each";
    "//! function and for what is not proved.";
    "";
    "#![allow(unused_mut, unused_variables, unused_assignments, unused_braces, non_snake_case)]";
    "";
    "use crate::bedrock_rt::*;" ].

Definition bls12_g1_rs : string :=
  ToSafeRustArena.rust_module bls12_g1_rs_header bls12_g1_funcs.
