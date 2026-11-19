(** * Extract the BLS12-377 GLV scalar multiplication to C. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_three_b.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_G1.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Base Fp functions needed by curve_add *)
Definition fp_base_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

(** Curve operations.  [store_zero_func] and [cmov_alt_func] take the field parameters as
    instances, which [bls12_377_prime] declares only inside its section, so they are given here as
    in [BLS12_377_G1].  [CondMoveGroup.cmov_alt_func] takes its function name as an implicit
    argument; "group_cmov_alt" is the name the GLV driver calls
    ([BLS12_377_GLV_ScalarMultBedrock.v]).  [store_zero_func] takes the names of the zero and
    one loaders implicitly; they follow the BLS12-381 names "bls12_zero"/"bls12_one"
    ([BLS12_G1ArenaRust.v]). *)
Section CurveFuncs.
  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bls377_field_parameters
    bls377_field_parameters_ok
    bls377_frep
    bls377_frep_ok.

  Definition group_cmov_alt_func : function_t :=
    cmov_alt_func (group_cmov_alt := "group_cmov_alt").

  Definition curve_funcs : list function_t :=
    [ bls377_G1_add;
      store_zero_func (zero_name := "bls377_zero") (one_name := "bls377_one");
      group_cmov_alt_func ].
End CurveFuncs.

(** The GLV Shamir function itself *)
(* Note: the actual bedrock2 function body is defined in
   BLS12_377_GLV_ScalarMultBedrock.v as glv_shamir_func.
   For extraction, we import it directly. *)

Definition glv_funcs : list function_t :=
  fp_base_funcs ++ curve_funcs.

Definition glv_c :=
  Eval vm_compute in c_module glv_funcs.

Redirect "bls377_glv_curve_ops" Eval cbv in glv_c.
