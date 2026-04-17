Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.BignumShift.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.CurveAddAlt.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Group.CurveAdd.LoopBody.
Require Import Bedrock.Group.CurveAdd.ScalarMult.

Require Import compiler.Pipeline.
From bedrock2 Require Import ToCString Bytedump.

Require Import bedrock2.Syntax.
Require Import compiler.MMIO.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.

From bedrock2 Require Import ToCString Bytedump.

Existing Instance bls12_field_names.
Existing Instance bls12_prime_parameters.
Existing Instance bls12_field_parameters.
Existing Instance bls12_field_representation.

(* for debugging *)
Definition bls12_add_mod := (c_module (bls12_add :: nil)).
Eval compute in bls12_add_mod.
Definition bls12_mul_mod := (c_module (bls12_mul :: nil)).
(* slow *)
(* Eval compute in bls12_mul_mod. *)
Definition bls12_zero_mod := (c_module (bls12_zero :: nil)).
Eval compute in bls12_zero_mod.
Definition bls12_one_mod := (c_module (bls12_one :: nil)).
Eval compute in bls12_one_mod.
Definition bls12_select_znz_mod := (c_module (bls12_select_znz :: nil)).
Eval compute in bls12_select_znz_mod.
Definition felem_copy_mod := (c_module (felem_copy_func :: nil)).
Eval compute in felem_copy_mod.
Definition store_zero_mod := (c_module (store_zero_func :: nil)).
Eval compute in store_zero_mod.
Definition shift_scalar_mod := (c_module (shift_scalar (width:=64) :: nil)).
Eval compute in shift_scalar_mod.

(* the names instantiated here should be collected in a GroupNames typeclass *)
(* also, they should parametrized in all implementations
   e.g. "group_cmov" is hardcoded in loop_body *)
Definition three_b_func_mod := (c_module (bls12_three_b :: nil)).
Eval compute in three_b_func_mod.
Definition cmov_alt_func_mod := (c_module (cmov_alt_func (group_cmov_alt:="group_cmov_alt") :: nil)).
Eval compute in cmov_alt_func_mod.
Definition curve_add_mod := (c_module (ladderstep_body "bls12_three_b" :: nil)).
Eval compute in curve_add_mod.
Definition curve_add_alt_mod := (c_module (curve_add_alt_func (curve_add_alt:="curve_add_alt") :: nil)).
Eval compute in curve_add_alt_mod.
Definition loop_body_func_mod := (c_module (loop_body_func "curve_add_alt" :: nil)).
Eval compute in loop_body_func_mod.
Definition scalar_mult_func_mod := (c_module (scalar_mult_func (scalar_words:=4) :: nil)).
Eval compute in scalar_mult_func_mod.

Definition c_test :=
  Eval vm_compute in
    c_module (bls12_add
                :: bls12_sub
                :: bls12_mul
                :: bls12_zero
                :: bls12_one
                :: bls12_select_znz
                :: felem_copy_func
                :: store_zero_func
                :: shift_scalar (width:=64)
                :: bls12_three_b
                :: cmov_alt_func (group_cmov_alt:="group_cmov_alt") (* set the name somewhere consistent *)
                :: ladderstep_body "bls12_three_b"
                :: curve_add_alt_func (curve_add_alt:="curve_add_alt")
                :: (loop_body_func "curve_add_alt")
                :: scalar_mult_func (scalar_words:=4)
                :: nil).

Redirect "G1" Eval cbv in c_test.
