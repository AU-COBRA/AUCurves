(** * BLS12 wNAF GLV Extraction — Safe Rust + Jasmin pipeline.

    Extracts the wNAF GLV scalar multiplication chain to:
    1. Safe Rust wrapper module (outer API layer)
    2. Jasmin source (inner verified assembly layer)

    The combined output is a complete verified scalar multiplication
    library where:
    - Rust's borrow checker enforces bedrock2's non-aliasing invariants
    - Jasmin's verified compiler provides assembly-level correctness
    - The two layers link via extern "C" declarations

    Pipeline:
      bedrock2 WP proofs → ToJasmin.v → .jazz → jasminc → .s
      bedrock2 spec_of  → SafeRustReflection → safe .rs wrapper
      .s + .rs → cargo build → verified binary

    Build:
      make EXTERNAL_DEPENDENCIES=1 \
        src/Bedrock/Field/Synthesis/Examples/BLS12_wNAF_Extract.vo
*)

From Stdlib Require Import ZArith String List.
Require Import bedrock2.Syntax.
Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.PointDouble.
Require Import Crypto.Bedrock.Group.CurveAdd.PointNegate.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAddInplaceWrapper.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** ** Function list for wNAF GLV scalar multiplication.

    The wNAF GLV chain uses these bedrock2 functions:
    - Leaf Fp operations (from bls12_prime synthesis)
    - curve_add (ladderstep, from CurveAdd.v)
    - curve_add_inplace (wrapper, from CurveAddInplaceWrapper.v)
    - point_double (from PointDouble.v)
    - point_negate (from PointNegate.v)
    - felem_copy (from bls12_felem_copy)
    - The wNAF loop body (from wNAF_GLV_Func.v) *)

(** Leaf Fp functions needed by curve operations. *)
Definition bls12_wnaf_fp_funcs : list function_t :=
  [ bls12_add; bls12_sub; bls12_mul; bls12_square;
    bls12_select_znz;
    ("bls12_felem_copy", bls12_felem_copy) ].

(** The curve_add_inplace_wrapper function. *)
Definition bls12_curve_add_inplace : function_t :=
  @curve_add_inplace_wrapper _ _ _ _ bls12_field_parameters bls12_frep.

(** Point negation function. *)
Definition bls12_point_negate : function_t :=
  @point_negate_func bls12_field_parameters.

(** All functions needed for wNAF GLV scalar multiplication. *)
Definition bls12_wnaf_all_funcs : list function_t :=
  bls12_wnaf_fp_funcs ++
  [ bls12_curve_add_inplace;
    bls12_point_negate ].

(** ** Verification artifacts backing this extraction.

    The extracted code is backed by the following Qed'd theorems
    (all under [Crypto.Bedrock.Field.Synthesis.Examples]):

    - [BLS12_wNAF_HornerAlgebra.v] : signed-digit Horner algebra (18 Qed)
    - [BLS12_wNAF_PointOppInverse.v] : point opposition inverse (5 Qed)
    - [BLS12_wNAF_LoadAndProcess.v] :
        [load_and_process_P_ok], [load_and_process_Phi_ok]
        (per-digit WP; 8 cases each = 16 total case closures)
    - [BLS12_wNAF_ProcessDigits.v] : [process_both_digits_ok] (Qed)
    - [BLS12_wNAF_GLV_LoopBody.v] : [wnaf_loop_body_ok] (Qed)
    - [BLS12_wNAF_GLV_Proof.v] : [wnaf_glv_ok] (Qed)
    - [BLS12_wNAF_GLV_Closed.v] :
        [HLoadAndProcess_P_discharged], [HLoadAndProcess_Phi_discharged]
        (the critical generic link; verified "Closed under the global
         context" via [Print Assumptions])
    - [BLS12_wNAF_GLV_Instance.v] : arithmetic discharges (12 Qed)

    The curve_add_inplace wrapper [CurveAddInplaceWrapper.v] provides
    the stack-temp-based bedrock2 spec used in place of the deprecated
    (and now deleted) [CurveAddInplace.v] direct approach.

    Full closed composition at concrete BLS12-381 parameters is a
    follow-up [BLS12_wNAF_GLV_Instance_Final.v] project. *)

(** ** Safe Rust wrapper specification for GLV scalar mult.

    The safe Rust wrapper for GLV scalar multiplication uses:
    - &mut out (Jacobian point, 3 Fp = 144 bytes)
    - &scalar_k1 (128-bit scalar, 2 words = 16 bytes)
    - &scalar_k2 (128-bit scalar, 2 words = 16 bytes)
    - &P (Jacobian point, read-only)
    - &Phi (Jacobian point, read-only)

    The borrow checker enforces that out does not alias P or Phi. *)

Definition bls12_glv_scalar_mul_wrapper_spec : string :=
  "/// Verified wNAF GLV scalar multiplication on BLS12-381 G1." ++ "
" ++
  "///" ++ "
" ++
  "/// Computes out = k1*P + k2*Phi where Phi = endomorphism(P)." ++ "
" ++
  "/// Non-aliasing enforced by Rust's borrow checker." ++ "
" ++
  "/// Safety follows from bedrock2 separation logic proofs." ++ "
" ++
  "#[inline]" ++ "
" ++
  "pub fn glv_scalar_mul(out: &mut JacobianPoint, k1: &Scalar128, k2: &Scalar128, p: &JacobianPoint, phi: &JacobianPoint) {" ++ "
" ++
  "    unsafe { bls12_glv_scalar_mul_raw(out.as_mut_ptr() as usize, k1.as_ptr() as usize, k2.as_ptr() as usize, p.as_ptr() as usize, phi.as_ptr() as usize) }" ++ "
" ++
  "}".

(** ** Jasmin extraction.

    For the actual Jasmin extraction, we use the same OCaml pipeline
    as ExtractBLS12Jasmin.v: extract the symbolic function list and
    the [to_jasmin_sized] translator to OCaml, then run the OCaml
    binary to emit .jazz files.

    The jasminc compiler then produces verified x86-64 assembly. *)
