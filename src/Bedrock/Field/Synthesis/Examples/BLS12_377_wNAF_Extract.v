(** * BLS12-377 wNAF GLV Extraction.
    See [WNAF_GLV_STATUS.md] for full verification chain status.

    Reuses the entire verified wNAF chain from BLS12-381 (all 12 files
    are parameterized over field_parameters). Only the extraction layer
    and concrete function instantiations are curve-specific.

    The wNAF chain files (wNAF.v, BLS12_wNAF_HornerAlgebra.v,
    BLS12_wNAF_ProcessDigits.v, BLS12_wNAF_GLV_LoopBody.v,
    BLS12_wNAF_GLV_Proof.v, BLS12_wNAF_LoadAndProcess.v,
    BLS12_wNAF_GLV_Closed.v, BLS12_wNAF_GLV_Instance_Final.v)
    all accept BLS12-377 field parameters via their Section contexts. *)

From Stdlib Require Import ZArith String List.
Require Import bedrock2.Syntax.
Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.PointDouble.
Require Import Crypto.Bedrock.Group.CurveAdd.PointNegate.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAddInplaceWrapper.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** ** Function list for BLS12-377 wNAF GLV scalar multiplication. *)

(** Leaf Fp functions from bls12_377_prime synthesis. *)
Definition bls377_wnaf_fp_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

(** The curve_add_inplace_wrapper function for BLS12-377. *)
Definition bls377_curve_add_inplace : function_t :=
  @curve_add_inplace_wrapper _ _ _ _ bls377_field_parameters bls377_frep.

(** Point negation function for BLS12-377. *)
Definition bls377_point_negate : function_t :=
  @point_negate_func bls377_field_parameters.

(** All functions needed for BLS12-377 wNAF GLV scalar multiplication. *)
Definition bls377_wnaf_all_funcs : list function_t :=
  bls377_wnaf_fp_funcs ++
  [ bls377_curve_add_inplace;
    bls377_point_negate ].

(** ** Verification artifacts.

    The entire wNAF proof chain is shared with BLS12-381 via
    parametrized Sections. No BLS12-377-specific proofs are needed
    beyond the existing field_parameters instantiation.

    Concrete BLS12-377 wNAF GLV scalar multiplication uses:
    - bls377_wnaf_glv_func (from wNAF_GLV_Func.v, Section BLS12_377)
    - bls377_wnaf_all_funcs (above, leaf Fp + curve_add + point_negate)
    - All wNAF chain proofs (shared with BLS12-381)

    The felem_size_in_bytes for BLS12-377 is 48 (same as BLS12-381:
    6 limbs x 8 bytes), so the wNAF window-4 table addressing and
    all bedrock2 WP proofs apply without modification. *)
