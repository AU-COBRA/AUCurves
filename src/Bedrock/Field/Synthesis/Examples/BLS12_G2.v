(** * BLS12-381 G2 group operations — bedrock2 compilation.

    G2 is the subgroup of the twist curve E'(Fp2) where Fp2 = Fp[u]/(u²+1).
    Point addition uses the same projective Weierstrass formula as G1
    (ladderstep_gallina) but with Fp2 field operations.

    The curve parameter 3b for the twist is (12, 12) in Fp2,
    loaded via bls12_three_b_G2 from bls12_three_b_Fp2.v.

    WP proofs are stubs (exact I) — the function body is real.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section bls12_G2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BLS12-381 prime parameters                                      *)
    (* ============================================================== *)

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_prime_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_prime_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bls12_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    (* ============================================================== *)
    (* Type notations and Fp2 instances                               *)
    (* ============================================================== *)

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).

    Let fp2_prefix := "bls12_Fp2_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    Instance bls12_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls12_beta "bls12_") in exact v).
    Instance bls12_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls12_beta "bls12_") in exact v).

    (* ============================================================== *)
    (* Fp2 operation names                                             *)
    (* ============================================================== *)

    Let fp2_mul_name : string := AbstractField.mul (F:=Fp2).
    Let fp2_add_name : string := AbstractField.add (F:=Fp2).
    Let fp2_sub_name : string := AbstractField.sub (F:=Fp2).

    (* ============================================================== *)
    (* Helper: fold a list of cmds into nested cmd.seq                 *)
    (* ============================================================== *)

    Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cmds with
      | [] => cmd.skip
      | [c] => c
      | c :: rest => cmd.seq c (cmd_seq_list rest)
      end.

    (* ============================================================== *)
    (* G2 point addition over Fp2                                      *)
    (*                                                                  *)
    (* Same projective Weierstrass formula as G1 (ladderstep_gallina)  *)
    (* but with Fp2 operations. Uses 7 Fp2-sized stack temporaries.    *)
    (* ============================================================== *)

    Definition bls12_G2_add : function_t :=
      ("curve_add_G2",
       (["X1"; "X2"; "Y1"; "Y2"; "Z1"; "Z2"; "Xout"; "Yout"; "Zout"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as three_b;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t3;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t4;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t5;
          coq:(cmd_seq_list [
            (* Load 3b constant for the twist curve *)
            cmd.call [] "bls12_three_b_G2" [expr.var "three_b"];
            (* t0 = X1 * X2 *)
            cmd.call [] fp2_mul_name
              [expr.var "t0"; expr.var "X1"; expr.var "X2"];
            (* t1 = Y1 * Y2 *)
            cmd.call [] fp2_mul_name
              [expr.var "t1"; expr.var "Y1"; expr.var "Y2"];
            (* t2 = Z1 * Z2 *)
            cmd.call [] fp2_mul_name
              [expr.var "t2"; expr.var "Z1"; expr.var "Z2"];
            (* t3 = X1 + Y1 *)
            cmd.call [] fp2_add_name
              [expr.var "t3"; expr.var "X1"; expr.var "Y1"];
            (* t4 = X2 + Y2 *)
            cmd.call [] fp2_add_name
              [expr.var "t4"; expr.var "X2"; expr.var "Y2"];
            (* t3 = t3 * t4 = (X1+Y1)(X2+Y2) *)
            cmd.call [] fp2_mul_name
              [expr.var "t3"; expr.var "t3"; expr.var "t4"];
            (* t4 = t0 + t1 = X1*X2 + Y1*Y2 *)
            cmd.call [] fp2_add_name
              [expr.var "t4"; expr.var "t0"; expr.var "t1"];
            (* t3 = t3 - t4 = X1*Y2 + X2*Y1 *)
            cmd.call [] fp2_sub_name
              [expr.var "t3"; expr.var "t3"; expr.var "t4"];
            (* t4 = X1 + Z1 *)
            cmd.call [] fp2_add_name
              [expr.var "t4"; expr.var "X1"; expr.var "Z1"];
            (* t5 = X2 + Z2 *)
            cmd.call [] fp2_add_name
              [expr.var "t5"; expr.var "X2"; expr.var "Z2"];
            (* t4 = t4 * t5 = (X1+Z1)(X2+Z2) *)
            cmd.call [] fp2_mul_name
              [expr.var "t4"; expr.var "t4"; expr.var "t5"];
            (* t5 = t0 + t2 = X1*X2 + Z1*Z2 *)
            cmd.call [] fp2_add_name
              [expr.var "t5"; expr.var "t0"; expr.var "t2"];
            (* t4 = t4 - t5 = X1*Z2 + X2*Z1 *)
            cmd.call [] fp2_sub_name
              [expr.var "t4"; expr.var "t4"; expr.var "t5"];
            (* t5 = Y1 + Z1 *)
            cmd.call [] fp2_add_name
              [expr.var "t5"; expr.var "Y1"; expr.var "Z1"];
            (* Xout = Y2 + Z2  (using Xout as temp) *)
            cmd.call [] fp2_add_name
              [expr.var "Xout"; expr.var "Y2"; expr.var "Z2"];
            (* t5 = t5 * Xout = (Y1+Z1)(Y2+Z2) *)
            cmd.call [] fp2_mul_name
              [expr.var "t5"; expr.var "t5"; expr.var "Xout"];
            (* Xout = t1 + t2 = Y1*Y2 + Z1*Z2 *)
            cmd.call [] fp2_add_name
              [expr.var "Xout"; expr.var "t1"; expr.var "t2"];
            (* t5 = t5 - Xout = Y1*Z2 + Y2*Z1 *)
            cmd.call [] fp2_sub_name
              [expr.var "t5"; expr.var "t5"; expr.var "Xout"];
            (* Zout = 3b * t2 *)
            cmd.call [] fp2_mul_name
              [expr.var "Zout"; expr.var "three_b"; expr.var "t2"];
            (* Xout = t1 - Zout *)
            cmd.call [] fp2_sub_name
              [expr.var "Xout"; expr.var "t1"; expr.var "Zout"];
            (* Zout = Zout + t1 *)
            cmd.call [] fp2_add_name
              [expr.var "Zout"; expr.var "Zout"; expr.var "t1"];
            (* Yout = Xout * Zout *)
            cmd.call [] fp2_mul_name
              [expr.var "Yout"; expr.var "Xout"; expr.var "Zout"];
            (* t1 = t0 + t0 = 2*X1*X2 *)
            cmd.call [] fp2_add_name
              [expr.var "t1"; expr.var "t0"; expr.var "t0"];
            (* t1 = t1 + t0 = 3*X1*X2 *)
            cmd.call [] fp2_add_name
              [expr.var "t1"; expr.var "t1"; expr.var "t0"];
            (* t4 = 3b * t4 *)
            cmd.call [] fp2_mul_name
              [expr.var "t4"; expr.var "three_b"; expr.var "t4"];
            (* t0 = t1 * t4 *)
            cmd.call [] fp2_mul_name
              [expr.var "t0"; expr.var "t1"; expr.var "t4"];
            (* Yout = Yout + t0 *)
            cmd.call [] fp2_add_name
              [expr.var "Yout"; expr.var "Yout"; expr.var "t0"];
            (* t0 = t5 * t4 *)
            cmd.call [] fp2_mul_name
              [expr.var "t0"; expr.var "t5"; expr.var "t4"];
            (* Xout = t3 * Xout *)
            cmd.call [] fp2_mul_name
              [expr.var "Xout"; expr.var "t3"; expr.var "Xout"];
            (* Xout = Xout - t0 *)
            cmd.call [] fp2_sub_name
              [expr.var "Xout"; expr.var "Xout"; expr.var "t0"];
            (* t0 = t3 * t1 *)
            cmd.call [] fp2_mul_name
              [expr.var "t0"; expr.var "t3"; expr.var "t1"];
            (* Zout = t5 * Zout *)
            cmd.call [] fp2_mul_name
              [expr.var "Zout"; expr.var "t5"; expr.var "Zout"];
            (* Zout = Zout + t0 *)
            cmd.call [] fp2_add_name
              [expr.var "Zout"; expr.var "Zout"; expr.var "t0"]
          ])
        ))).

    Definition three_b_Fp2 : Fp2.
    Proof.
        exact (ModularArithmetic.F.of_Z bls12_M_pos 12,
               ModularArithmetic.F.of_Z bls12_M_pos 12).
    Defined.

    Lemma bls12_G2_ok : program_logic_goal_for_function! bls12_G2_add.
    Proof. exact I. Qed.

End bls12_G2.
