(** * Extract BLS24-509 complete pairing pipeline to C. *)

From Stdlib Require Import Strings.String ZArith.ZArith.
Require Import bedrock2.ToCString bedrock2.Syntax.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_MillerLoop.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_FinalExp.
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

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Extract.
  Existing Instances
    bls24_prime_params bls24_prime_params_ok
    bls24_509_field_parameters bls24_509_ops bls24_Fp_repr bls24_Fp_repr_ok
    bls24_Fp_names
    bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok bls24_Fp2_names
    bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok bls24_Fp4_names
    bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok bls24_Fp8_names
    bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok bls24_Fp24_names.

  (* Base Fp: 6 functions *)
  Let fp_ops := bls24_509_ops.
  Definition bls24_fp_funcs : list function_t :=
    [ ("bls24_509_add", fp_ops.(add_op).(b2_func));
      ("bls24_509_sub", fp_ops.(sub_op).(b2_func));
      ("bls24_509_mul", fp_ops.(mul_op).(b2_func));
      ("bls24_509_square", fp_ops.(square_op).(b2_func));
      ("bls24_509_opp", fp_ops.(opp_op).(b2_func));
      ("bls24_509_felem_copy", fp_ops.(felem_copy_op).(b2_func)) ].

  (* QE/CE tower functions via qualified access.
     QE_funcs implicit args (from About): width BW word mem BaseField base_fp base_repr QE_names base_names *)
  Definition bls24_Fp2_funcs : list function_t :=
    GenericQuadratic.QE_funcs (QE_names:=bls24_Fp2_names) (base_names:=bls24_Fp_names)
      bls24_beta "bls24_Fp2_" Fp_eq_dec bls24_Fp2_mul_by_nr_name.

  Definition bls24_Fp4_funcs : list function_t :=
    GenericQuadratic.QE_funcs (QE_names:=bls24_Fp4_names) (base_names:=bls24_Fp2_names)
      bls24_xi "bls24_Fp4_" Fp2_eq_dec bls24_Fp4_mul_by_nr_name.

  Definition bls24_Fp8_funcs : list function_t :=
    GenericQuadratic.QE_funcs (QE_names:=bls24_Fp8_names) (base_names:=bls24_Fp4_names)
      bls24_v_in_Fp4 "bls24_Fp8_" Fp4_eq_dec bls24_Fp8_mul_by_nr_name.

  Definition bls24_Fp24_funcs : list function_t :=
    GenericCubic.CE_funcs (CE_names:=bls24_Fp24_names) (base_names:=bls24_Fp8_names)
      bls24_Fp8_mul_by_w_model "bls24_Fp24_" Fp8_eq_dec
      bls24_Fp8_mul_by_w_name bls24_Fp8_mul_by_w_func.

  Definition bls24_all_funcs : list function_t :=
    bls24_fp_funcs ++
    bls24_Fp2_funcs ++
    bls24_Fp4_funcs ++
    bls24_Fp8_funcs ++
    bls24_Fp24_funcs ++
    (* bls24_Fp8_mul_by_w is already in CE_funcs, include only the others *)
    [bls24_Fp2_mul_by_nr_func; bls24_Fp2_mul_xi_func; bls24_Fp4_mul_by_v_func] ++
    bls24_miller_loop_funcs ++
    bls24_final_exp_funcs.

End Extract.

(* Apply stackalloc flattening to tower mul/sqr functions *)
Require Import Crypto.Bedrock.Jasmin.FlattenStackalloc.

Definition bls24_flatten_targets : list String.string :=
  ["bls24_Fp2_mul"; "bls24_Fp2_square";
   "bls24_Fp4_mul"; "bls24_Fp4_square";
   "bls24_Fp8_mul"; "bls24_Fp8_square";
   "bls24_Fp24_mul"; "bls24_Fp24_square";
   "bls24_Fp24_inv";
   "bls24_Fp4_mul_by_v"; "bls24_Fp8_mul_by_w";
   "bls24_Fp2_mul_xi"].

Definition bls24_optimized_funcs :=
  flatten_selected bls24_flatten_targets bls24_all_funcs.

(* Extract both original and optimized *)
Definition bls24_509_all_c :=
  Eval vm_compute in c_module bls24_all_funcs.

Definition bls24_509_opt_c :=
  Eval vm_compute in c_module bls24_optimized_funcs.

Redirect "bls24_509_pairing" Eval cbv in bls24_509_all_c.
Redirect "bls24_509_pairing_flat" Eval cbv in bls24_509_opt_c.

(* Jasmin output: use ToJasmin.v for the AST transformation,
   but generate text via a Python post-processor on the C output
   to avoid O(n²) string concatenation in vm_compute.
   See: apply_to_jasmin.py *)
