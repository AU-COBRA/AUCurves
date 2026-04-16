(** * BN254 single-scalar wNAF extraction.

    Collects all bedrock2 functions needed for wNAF scalar multiplication
    on BN254 G1: Fp operations, curve add/double, point negate, store zero,
    and the wNAF loop itself.

    This does NOT use GLV (BN254 has no efficient endomorphism in our
    codebase). Instead it uses plain wNAF: signed-digit encoding reduces
    the number of non-zero digits from ~128 to ~32 (for w=4), giving
    ~1.4x speedup over binary scalar multiplication. *)

From Stdlib Require Import ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.BN254_G1.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_three_b.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BN254_wNAF.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  (** Curve add: aliased in-place variant using stack temporaries *)
  Definition bn254_curve_add_inplace : function_t :=
    ("curve_add",
     (["outx"; "in2x"; "outy"; "in2y"; "outz"; "in2z";
       "dstx"; "dsty"; "dstz"],
      []:list String.string,
      (* For now, use ladderstep directly. A proper inplace wrapper
         (CurveAddInplaceWrapper.v pattern) is needed for aliased calls. *)
      snd (snd bn254_G1_add))).

  (** Point negation: negate Y coordinate in-place *)
  Definition bn254_point_negate : function_t :=
    ("point_negate",
     (["py"],
      []:list String.string,
      cmd.call [] "opp" [expr.var "py"; expr.var "py"])).

  (** All BN254 wNAF functions *)
  Definition bn254_wnaf_all_funcs : list function_t :=
    [ bn254_mul; bn254_square; bn254_add; bn254_sub;
      bn254_select_znz;
      ("bn254_felem_copy", bn254_felem_copy);
      bn254_G1_add;
      bn254_point_negate;
      bn254_wnaf_single_func
    ].

End BN254_wNAF.
