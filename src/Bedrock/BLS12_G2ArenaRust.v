(** * BLS12_G2ArenaRust — the BLS12-381 G2 bedrock2 functions printed as safe Rust.

    The function list behind [bls12-381-safe-rust/src/g2_extracted.rs],
    printed with the trusted printer [ToSafeRustArena.rust_module] (the same
    printer as the G1 file [BLS12_G1ArenaRust.v]; it prints words and
    pointers, so Fp2 needs no change to it: an Fp2 element is 12 words at a
    pointer, c0 then c1).  Written by [scripts/emit_bls12_g2_rust.sh]
    (driver [scripts/EmitBLS12G2Rust.v]) and checked byte for byte by
    [scripts/check_bls12_g2_extraction.sh].

    - ["g2_curve_add"]: [CurveAddAF.af_curve_add_body] at [bls12_Fp2] —
      RCB 2015 Algorithm 7 over Fp2; [BLS12_G2_Closed.g2_curve_add_closed]
      (Qed, closed): equal to fiat-crypto's [Projective.add] on E'(Fp2).
    - ["g2_curve_double"]: [CurveAddAF.af_curve_double_body] at [bls12_Fp2] —
      Algorithm 9; [BLS12_G2_Closed.g2_curve_double_closed] (Qed, closed):
      equal to [Projective.add P P].
    - ["g2_scalar_mul"]: [BLS12_G2_ScalarMul.g2_scalar_mul_func] — double-and-add
      over the two in-place bodies below, most significant bit first,
      256 bits, from (0 : 3b' : 0); [BLS12_G2_ScalarMul.g2_scalar_mul_closed]
      (Qed, closed): projectively equal to k P for an on-curve P.
    - ["g2_curve_add_ip"], ["g2_curve_double_ip"]: [CurveAddAF.af_curve_add_ip_body]
      / [af_curve_double_ip_body] at [bls12_Fp2] — the same chains with the
      result written over the first point ([af_curve_add_ip_correct],
      [af_curve_double_ip_correct], Qed; equal to Alg. 7 / 9 by
      [af_add_ip_eq] / [af_double_ip_eq]).
    - ["g2_scalar_mul_ct"]: [BLS12_G2_ScalarMulCT.g2_scalar_mul_ct_func],
      the constant-time variant of ["g2_scalar_mul"] (per bit: in-place
      double, unconditional out-of-place ["g2_curve_add"] into three
      caller scratch buffers, three ["ct_cswap"]);
      [BLS12_G2_ScalarMulCT.g2_scalar_mul_ct_closed] (Qed, closed): same
      conclusion as [g2_scalar_mul_closed].  ["g2_scalar_mul"] branches on
      the scalar bits (variable time): for public scalars only.
    - ["ct_cswap"]: [CtSwap.ct_cswap] at 12 words (one Fp2 element),
      [CtSwap.ct_cswap_call] (Qed).
    - ["bls12_Fp2_three_b"]: [BLS12_G2_ThreeB.g2_three_b_body], 3b' = (12, 12)
      in Montgomery form; [g2_three_b_ok] (Qed).

    The Fp2 leaves ["bls12_Fp2_mul"], ["bls12_Fp2_add"], ["bls12_Fp2_sub"]
    are not printed: [bls12-381-safe-rust/src/bedrock_rt.rs] routes them to
    the crate's tower functions [tower::bls12_Fp2_mul/add/sub].  Their
    contracts ([AbstractField.binop_spec] at the Fp2 representation) are the
    premises of the closed theorems. *)

From Stdlib Require Import String List ZArith.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.BLS12_G2_ThreeB.
Require Import Bedrock.BLS12_G2_Closed.
Require Import Bedrock.BLS12_G2_ScalarMul.
Require Import Bedrock.BLS12_G2_ScalarMulCT.
Require Import Bedrock.ToSafeRustArena.
Import ListNotations.
Local Open Scope string_scope.

Import ToSafeRustArena (function_t).

Definition bls12_g2_funcs : list function_t :=
  [ ("g2_scalar_mul", g2_scalar_mul_func);
    ("g2_curve_add_ip", g2_add_ip_body);
    ("g2_curve_double_ip", g2_double_ip_body);
    ("g2_curve_add", g2_add_body);
    ("g2_curve_double", g2_double_body);
    ("bls12_Fp2_three_b", g2_three_b_body);
    ("g2_scalar_mul_ct", g2_scalar_mul_ct_func);
    ("ct_cswap", g2_ct_cswap_func) ].

Definition bls12_g2_rs_header : list string :=
  [ "//! Rocq-EMITTED safe Rust: BLS12-381 G2 scalar multiplication and complete";
    "//! projective group law over Fp2 (bedrock2), printed by src/Bedrock/ToSafeRustArena.v from the";
    "//! function list [bls12_g2_funcs] of src/Bedrock/BLS12_G2ArenaRust.v.";
    "//!";
    "//! DO NOT EDIT.  Regenerate with scripts/emit_bls12_g2_rust.sh;";
    "//! scripts/check_bls12_g2_extraction.sh checks it byte for byte.";
    "//! Only the Rocq string quoting has been stripped.";
    "//!";
    "//! See src/Bedrock/BLS12_G2ArenaRust.v for the theorem behind each";
    "//! function and for what is not proved.";
    "";
    "#![allow(unused_mut, unused_variables, unused_assignments, unused_braces, non_snake_case)]";
    "";
    "use crate::bedrock_rt::*;" ].

Definition bls12_g2_rs : string :=
  ToSafeRustArena.rust_module bls12_g2_rs_header bls12_g2_funcs.
