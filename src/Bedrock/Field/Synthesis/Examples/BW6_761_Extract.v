(** * Aggregate BW6-761 pairing pipeline for extraction.
 *
 * Collects all bedrock2 function bodies needed to build the
 * BW6-761 optimal-ate pairing in safe Rust:
 *   - Fp base ops (add/sub/mul/square/opp/felem_copy + helpers)
 *   - Fp3 tower (cubic over Fp) via [GenericCubic.CE_funcs]
 *   - Fp6 tower (quadratic over Fp3) via [GenericQuadratic.QE_funcs]
 *   - Fp3 mul-by-nonresidue (mul-by-(-4))
 *   - Fp6 mul-by-nonresidue (mul-by-zeta in Fp3)
 *   - Miller loop body + helpers
 *   - Final exponentiation body + helpers
 *
 * Mirror of [BLS24_509_Extract.v].  The BW6-761 tower is shorter
 * (2 layers vs 4) and uses a CUBIC first extension (vs BLS24's
 * Fp2-Fp4-Fp8-Fp24 chain), but the aggregator pattern is the same.
 *
 * Caveat: the [BW6_761_MillerLoop_proof.v] proof file still
 * contains 5 Admits being closed by a sister agent; the BODY
 * functions used here come from [BW6_761_MillerLoop.v] (Qed-clean)
 * so extraction can proceed.  [BW6_761_FrobConsts.v] currently
 * ships placeholder Frobenius constants — see the README of
 * `bw6-761-safe-rust` for the deployment-blocker note.
 *)

From Stdlib Require Import Strings.String ZArith.ZArith.
Require Import bedrock2.ToCString bedrock2.Syntax.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoop.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FinalExp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Extract.
  Existing Instances
    bw6_prime_params bw6_prime_params_ok
    bw6_761_field_parameters bw6_761_ops
    bw6_Fp_repr bw6_Fp_repr_ok bw6_Fp_names
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok bw6_Fp3_names
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok bw6_Fp6_names.

  (* Base Fp: 6 functions (matches BLS24-509 layout).  Names come
     from [field_parameters_prefixed] with prefix "bw6_761_". *)
  Let fp_ops := bw6_761_ops.
  Definition bw6_fp_funcs : list function_t :=
    [ ("bw6_761_add", fp_ops.(add_op).(b2_func));
      ("bw6_761_sub", fp_ops.(sub_op).(b2_func));
      ("bw6_761_mul", fp_ops.(mul_op).(b2_func));
      ("bw6_761_square", fp_ops.(square_op).(b2_func));
      ("bw6_761_opp", fp_ops.(opp_op).(b2_func));
      ("bw6_761_felem_copy", fp_ops.(felem_copy_op).(b2_func)) ].

  (* Fp3 tower (cubic over Fp).  Uses [GenericCubic.CE_funcs]
     parameterised by the [bw6_761_mul_by_nr_n4] helper (multiply
     by -4 in Fp). *)
  Definition bw6_Fp3_funcs : list function_t :=
    GenericCubic.CE_funcs (CE_names:=bw6_Fp3_names) (base_names:=bw6_Fp_names)
      bw6_Fp_mul_by_nr_model "bw6_761_Fp3_" Fp_eq_dec
      bw6_Fp_mul_by_nr_name bw6_Fp_mul_by_nr_func.

  (* Fp6 tower (quadratic over Fp3).  Uses [GenericQuadratic.QE_funcs]
     parameterised by the [bw6_761_Fp3_mul_by_zeta] helper. *)
  Definition bw6_Fp6_funcs : list function_t :=
    GenericQuadratic.QE_funcs (QE_names:=bw6_Fp6_names) (base_names:=bw6_Fp3_names)
      bw6_zeta_in_Fp3 "bw6_761_Fp6_" Fp3_eq_dec bw6_Fp6_mul_by_nr_name.

  (* All BW6 functions: base + Fp3 tower + Fp6 tower +
     Fp6 mul-by-nr helper + Miller loop + Final exp.

     Note: [bw6_Fp3_funcs] (from [CE_funcs]) auto-includes
     [bw6_Fp_mul_by_nr_func] as its first entry (the cubic
     extension's Mul_by_nr_func slot — see GenericCubic.v line 327),
     so we do NOT re-add it here.

     [bw6_Fp6_funcs] (from [QE_funcs]) does NOT auto-include
     the quadratic nr helper, so we add [bw6_Fp3_mul_by_zeta_func]
     once. *)
  Definition bw6_all_funcs : list function_t :=
    bw6_fp_funcs ++
    bw6_Fp3_funcs ++
    bw6_Fp6_funcs ++
    [ bw6_Fp3_mul_by_zeta_func ] ++ (* bw6_761_Fp3_mul_by_zeta = Fp6 nr *)
    bw6_761_miller_loop_funcs ++
    bw6_final_exp_funcs.

End Extract.
