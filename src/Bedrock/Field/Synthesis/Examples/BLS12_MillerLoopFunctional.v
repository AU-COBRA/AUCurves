(** * Functional correctness of bls12_miller_loop.

    A copy of the proof of [bls12_miller_loop_ok] (BLS12_MillerLoop.v) whose loop invariant
    also tracks the feval of f and T = (t_x, t_y):
      (feval f, (feval t_x, feval t_y)) =
        fold_left (step_model Q_x Q_y P_x P_y) (firstn (63 - v) Pairing.bls_x_bits)
                  (Fp12.fp12_one, (Q_x, Q_y)),
    with the loop body done by the fragment lemmas [miller_doubling_ok] and
    [miller_addition_ok] of BLS12_MillerStepFunctional.v.  The bedrock2 code is unchanged.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MakeLineFunctional.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp12Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFeval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_MillerLoopFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-381 prime parameters *)
    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Existing Instance BLS12_MillerStepFunctional.bls12_pf_params.

    Existing Instance BLS12_MillerStepFunctional.bls12_pf_params_ok.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp_rep.

    Existing Instance BLS12_MillerStepFunctional.bls12_Fp_rep_ok.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Existing Instance BLS12_MillerStepFunctional.bls12_Fp2_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp2_rep'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp6_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp6_rep'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp12_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp12_rep'.

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_add.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_sub.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_sqr.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_inv.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_opp.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_felem_copy.

    (* Fp12 operations *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_sqr.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_felem_copy.

    (* Fp operations needed by make_line *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_felem_copy.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_from_word.
    (* ============================================================ *)
    (* Pure lemmas for the functional invariant                      *)
    (* ============================================================ *)

    Local Notation Fp6_feval := (@AbstractField.feval _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp6_felem := (@AbstractField.felem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp_fsw' := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_fsw' := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_fsw' := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').

    Local Opaque BLS12_MillerStepFunctional.bls12_Fp_rep.

    Lemma Fp2_feval_app' (a b : Fp_felem) :
      List.length a = Fp_fsw' -> Fp2_feval (a ++ b) = (Fp_feval a, Fp_feval b).
    Proof.
      intros Ha.
      change (Fp2_feval (a ++ b)) with
        (Fp_feval (firstn Fp_fsw' (a ++ b)), Fp_feval (skipn Fp_fsw' (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Lemma Fp6_feval_app3' (a b c : Fp2_felem) :
      List.length a = Fp2_fsw' -> List.length b = Fp2_fsw' ->
      Fp6_feval (a ++ b ++ c) = ((Fp2_feval a, Fp2_feval b), Fp2_feval c).
    Proof.
      intros Ha Hb.
      change (Fp6_feval (a ++ b ++ c)) with
        ((Fp2_feval (firstn Fp2_fsw' (a ++ b ++ c)),
          Fp2_feval (firstn Fp2_fsw' (skipn Fp2_fsw' (a ++ b ++ c)))),
         Fp2_feval (skipn (2 * Fp2_fsw') (a ++ b ++ c))).
      assert (Hab : List.length (a ++ b) = (2 * Fp2_fsw')%nat).
      { rewrite length_app, Ha, Hb. lia. }
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hb).
      rewrite (app_assoc a b c).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hab).
      reflexivity.
    Qed.

    Lemma Fp12_feval_app' (a b : Fp6_felem) :
      List.length a = Fp6_fsw' -> Fp12_feval (a ++ b) = (Fp6_feval a, Fp6_feval b).
    Proof.
      intros Ha.
      change (Fp12_feval (a ++ b)) with
        (Fp6_feval (firstn Fp6_fsw' (a ++ b)), Fp6_feval (skipn Fp6_fsw' (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Local Notation word_feval z := (F.of_Z PrimeField.M_pos (@word.unsigned 64 word (word.of_Z z))).

    (** fp12_set_one: the 12 from_word results evaluate to Fp12.fp12_one. *)
    Lemma Fp12_feval_set_one (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : Fp_felem) :
      List.length w1 = Fp_fsw' -> List.length w2 = Fp_fsw' -> List.length w3 = Fp_fsw' ->
      List.length w4 = Fp_fsw' -> List.length w5 = Fp_fsw' -> List.length w6 = Fp_fsw' ->
      List.length w7 = Fp_fsw' -> List.length w8 = Fp_fsw' -> List.length w9 = Fp_fsw' ->
      List.length w10 = Fp_fsw' -> List.length w11 = Fp_fsw' ->
      Fp_feval w1 = word_feval 1 -> Fp_feval w2 = word_feval 0 -> Fp_feval w3 = word_feval 0 ->
      Fp_feval w4 = word_feval 0 -> Fp_feval w5 = word_feval 0 -> Fp_feval w6 = word_feval 0 ->
      Fp_feval w7 = word_feval 0 -> Fp_feval w8 = word_feval 0 -> Fp_feval w9 = word_feval 0 ->
      Fp_feval w10 = word_feval 0 -> Fp_feval w11 = word_feval 0 -> Fp_feval w12 = word_feval 0 ->
      Fp12_feval (((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6)) ++ ((w7 ++ w8) ++ (w9 ++ w10) ++ (w11 ++ w12)))
      = Fp12.fp12_one PrimeField.M_pos.
    Proof.
      intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
      assert (L12' : List.length (w1 ++ w2) = Fp2_fsw').
      { rewrite length_app, L1, L2. change Fp2_fsw' with (2 * Fp_fsw')%nat. lia. }
      assert (L34' : List.length (w3 ++ w4) = Fp2_fsw').
      { rewrite length_app, L3, L4. change Fp2_fsw' with (2 * Fp_fsw')%nat. lia. }
      assert (L78' : List.length (w7 ++ w8) = Fp2_fsw').
      { rewrite length_app, L7, L8. change Fp2_fsw' with (2 * Fp_fsw')%nat. lia. }
      assert (L910' : List.length (w9 ++ w10) = Fp2_fsw').
      { rewrite length_app, L9, L10. change Fp2_fsw' with (2 * Fp_fsw')%nat. lia. }
      assert (L6' : List.length ((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6)) = Fp6_fsw').
      { rewrite !length_app, L1, L2, L3, L4, L5, L6.
        change Fp6_fsw' with (3 * Fp2_fsw')%nat. change Fp2_fsw' with (2 * Fp_fsw')%nat. lia. }
      rewrite (Fp12_feval_app' ((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6))
                 ((w7 ++ w8) ++ (w9 ++ w10) ++ (w11 ++ w12)) L6').
      rewrite (Fp6_feval_app3' (w1 ++ w2) (w3 ++ w4) (w5 ++ w6) L12' L34').
      rewrite (Fp6_feval_app3' (w7 ++ w8) (w9 ++ w10) (w11 ++ w12) L78' L910').
      rewrite (Fp2_feval_app' w1 w2 L1), (Fp2_feval_app' w3 w4 L3), (Fp2_feval_app' w5 w6 L5),
        (Fp2_feval_app' w7 w8 L7), (Fp2_feval_app' w9 w10 L9), (Fp2_feval_app' w11 w12 L11).
      rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12.
      reflexivity.
    Qed.

    Local Transparent BLS12_MillerStepFunctional.bls12_Fp_rep.

    Lemma firstn_S_snoc {A} (l : list A) (k : nat) (d : A) :
      (k < List.length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
    Proof.
      revert k. induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia |].
      destruct k as [|k]; [reflexivity |].
      change (x :: firstn (S k) l = (x :: firstn k l) ++ [nth k l d]).
      cbn [List.length] in Hk. rewrite (IH k) by lia. reflexivity.
    Qed.

    Lemma bls_x_bits_length : List.length Pairing.bls_x_bits = 63%nat.
    Proof. vm_compute. reflexivity. Qed.


    (** One loop iteration on the fold. *)
    Lemma fold_firstn_S (qx qy : Fp2) (xp yp : Fp) (init : Fp12 * (Fp2 * Fp2)) (k : nat) :
      (k < 63)%nat ->
      fold_left (step_model qx qy xp yp) (firstn (S k) Pairing.bls_x_bits) init =
      step_model qx qy xp yp (fold_left (step_model qx qy xp yp) (firstn k Pairing.bls_x_bits) init)
        (nth k Pairing.bls_x_bits false).
    Proof.
      intros Hk. rewrite (firstn_S_snoc _ k false) by (rewrite bls_x_bits_length; lia).
      rewrite fold_left_app. reflexivity.
    Qed.

    Lemma inv_step_dbl (qx qy : Fp2) (xp yp : Fp) (init : Fp12 * (Fp2 * Fp2)) (k : nat)
      (F TX TY F' TX' TY' : _) :
      (k < 63)%nat -> nth k Pairing.bls_x_bits false = false ->
      (F, (TX, TY)) = fold_left (step_model qx qy xp yp) (firstn k Pairing.bls_x_bits) init ->
      F' = fst (dbl_model F TX TY xp yp) ->
      TX' = fst (snd (dbl_model F TX TY xp yp)) ->
      TY' = snd (snd (dbl_model F TX TY xp yp)) ->
      (F', (TX', TY')) = fold_left (step_model qx qy xp yp) (firstn (S k) Pairing.bls_x_bits) init.
    Proof.
      intros Hk Hbit HS HF HX HY.
      rewrite (fold_firstn_S qx qy xp yp init k Hk), <- HS, Hbit.
      unfold step_model.
      destruct (dbl_model F TX TY xp yp) as [f1 [x1 y1]].
      cbn [fst snd] in *. subst. reflexivity.
    Qed.

    Lemma inv_step_add (qx qy : Fp2) (xp yp : Fp) (init : Fp12 * (Fp2 * Fp2)) (k : nat)
      (F TX TY F1 TX1 TY1 F' TX' TY' : _) :
      (k < 63)%nat -> nth k Pairing.bls_x_bits false = true ->
      (F, (TX, TY)) = fold_left (step_model qx qy xp yp) (firstn k Pairing.bls_x_bits) init ->
      F1 = fst (dbl_model F TX TY xp yp) ->
      TX1 = fst (snd (dbl_model F TX TY xp yp)) ->
      TY1 = snd (snd (dbl_model F TX TY xp yp)) ->
      F' = fst (add_model F1 TX1 TY1 qx qy xp yp) ->
      TX' = fst (snd (add_model F1 TX1 TY1 qx qy xp yp)) ->
      TY' = snd (snd (add_model F1 TX1 TY1 qx qy xp yp)) ->
      (F', (TX', TY')) = fold_left (step_model qx qy xp yp) (firstn (S k) Pairing.bls_x_bits) init.
    Proof.
      intros Hk Hbit HS HF HX HY HF' HX' HY'.
      rewrite (fold_firstn_S qx qy xp yp init k Hk), <- HS, Hbit.
      unfold step_model.
      destruct (dbl_model F TX TY xp yp) as [f1 [x1 y1]].
      cbn [fst snd] in *. subst F1 TX1 TY1.
      destruct (add_model f1 x1 y1 qx qy xp yp) as [f2 [x2 y2]].
      cbn [fst snd] in *. subst. reflexivity.
    Qed.

    (** The loop bit: bit (v-1) of |x|, as computed by the loop body, is bit (63 - v) of
        [Pairing.bls_x_bits]. *)
    Lemma miller_bit_word (vi : nat) :
      (0 < vi <= 63)%nat ->
      @word.unsigned 64 word
        (word.and (word.sru (word.of_Z 0xd201000000010000)
                            (word.sub (word.of_Z (Z.of_nat vi)) (word.of_Z 1)))
                  (word.of_Z 1)) =
      (if nth (63 - vi) Pairing.bls_x_bits false then 1 else 0).
    Proof.
      intros Hvi.
      do 64 (destruct vi as [|vi]; [ first [ exfalso; lia | vm_compute; reflexivity ] |]).
      exfalso; lia.
    Qed.


    (* spec_of for bls12_make_line — needed by straightline_call *)
    Instance spec_of_bls12_make_line : spec_of "bls12_make_line" :=
      fnspec! "bls12_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp12_felem) (lam xt yt : Fp2_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight lam /\
          Fp2_bounded Fp2_tight xt /\
          Fp2_bounded Fp2_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp2 plam lam ⋆
            (FElem_Fp2 pxt xt ⋆
             (FElem_Fp2 pyt yt ⋆
              (FElem_Fp pxp xp ⋆
               (FElem_Fp pyp yp ⋆ Rr)))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp2 plam lam ⋆
              (FElem_Fp2 pxt xt ⋆
               (FElem_Fp2 pyt yt ⋆
                (FElem_Fp pxp xp ⋆
                 (FElem_Fp pyp yp ⋆ Rr)))))) mem' }.

    (* ============================================================ *)
    (* D1: bls12_miller_loop spec and proof                          *)
    (* ============================================================ *)

    Instance spec_of_bls12_miller_loop : spec_of "bls12_miller_loop" :=
      fnspec! "bls12_miller_loop" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight q_x /\
          Fp2_bounded Fp2_tight q_y /\
          Fp_bounded Fp_loose p_x /\
          Fp_bounded Fp_loose p_y /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    (* Loop invariant for the Miller loop.
       The measure v counts down from 63 to 0. At each iteration, the
       loop body decrements i by 1, so v = word.unsigned(i).
       The invariant asserts:
       - The trace is unchanged (no I/O)
       - All 7 stack-allocated FElems and 5 input FElems exist in memory
         with appropriate bounds
       - The locals map binds the expected variable names *)
    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) (old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp12_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp2_felem)
             (line_val : Fp12_felem),
        Fp12_bounded Fp12_tight f_val /\
        Fp2_bounded Fp2_tight tx_val /\
        Fp2_bounded Fp2_tight ty_val /\
        (FElem_Fp12 a_f f_val ⋆
         (FElem_Fp2 a_tx tx_val ⋆
          (FElem_Fp2 a_ty ty_val ⋆
           (FElem_Fp2 a_lam lam_val ⋆
            (FElem_Fp2 a_tmp1 tmp1_val ⋆
             (FElem_Fp2 a_tmp2 tmp2_val ⋆
              (FElem_Fp12 a_line line_val ⋆
               (FElem_Fp12 pout old_out ⋆
                (FElem_Fp p_px p_x ⋆
                 (FElem_Fp p_py p_y ⋆
                  (FElem_Fp2 p_qx q_x ⋆
                   (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* Helper lemma from generic *)
    Local Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew -> A mOld -> B mNew -> (A ⋆ B) m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    (* Aliases to generic tactics *)
    Local Ltac snd_from_word_ecancel H := BLS12_MillerGeneric.miller_snd_from_word_ecancel H.
    Local Ltac normalize_pairing_instances := BLS12_MillerGeneric.miller_normalize_pairing_instances.
    Local Ltac resolve_map_get := BLS12_MillerGeneric.miller_resolve_map_get.
    Local Ltac eval_expr_abstract := BLS12_MillerGeneric.miller_eval_expr_abstract.
    Local Ltac miller_straightline := BLS12_MillerGeneric.miller_straightline.
    Local Ltac eval_dexprs_abstract := BLS12_MillerGeneric.miller_eval_dexprs_abstract.

    (* Bounds and call tactics: use generic versions *)
    Local Ltac solve_miller_bounds := BLS12_MillerGeneric.miller_solve_bounds.
    Local Ltac wp_miller_call spec_hyp :=
      (* Use generic mcall with local resolve_map_get alias *)
      repeat miller_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ let H := fresh "Hcallee" in
        pose proof spec_hyp as H;
        eapply H;
        first
        [ wp_binop_precond solve_miller_bounds
        | wp_unop_precond solve_miller_bounds
        | ecancel_assumption_with_copy
        | split; ecancel_assumption_with_copy
        | repeat (first
            [ solve_miller_bounds
            | ecancel_assumption_with_copy
            | split ])
        ]
      | cbv beta; wp_postcall_auto
      ];
      try (unfold dlet.dlet; cbv beta);
      match goal with
      | Hrem : exists _, _ /\ _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hfeval := fresh "Hfeval" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hfeval [Hbound Hsep]]];
        try clear Hfeval
      | Hrem : exists _, _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hbound Hsep]]
      end.

    (* Word subtraction -- from generic *)
    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

    (* ============================================================ *)
    (* Functional spec and invariant                                 *)
    (* ============================================================ *)

    Definition miller_fold_model (qx qy : Fp2) (xp yp : Fp) (bits : list bool) :=
      fold_left (step_model qx qy xp yp) bits (Fp12.fp12_one PrimeField.M_pos, (qx, qy)).

    Lemma miller_fold_model_unfold qx qy xp yp bits :
      miller_fold_model qx qy xp yp bits =
      fold_left (step_model qx qy xp yp) bits (Fp12.fp12_one PrimeField.M_pos, (qx, qy)).
    Proof. reflexivity. Qed.

    Definition spec_of_bls12_miller_loop_functional : spec_of "bls12_miller_loop" :=
      fnspec! "bls12_miller_loop" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight q_x /\
          Fp2_bounded Fp2_tight q_y /\
          Fp_bounded Fp_loose p_x /\
          Fp_bounded Fp_loose p_y /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_feval out =
              fst (miller_fold_model (Fp2_feval q_x) (Fp2_feval q_y) (Fp_feval p_x) (Fp_feval p_y)
                     Pairing.bls_x_bits) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    Definition miller_loop_inv_f
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) (old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= 63)%nat /\
      exists (f_val : Fp12_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp2_felem)
             (line_val : Fp12_felem),
        (Fp12_feval f_val, (Fp2_feval tx_val, Fp2_feval ty_val)) =
          miller_fold_model (Fp2_feval q_x) (Fp2_feval q_y) (Fp_feval p_x) (Fp_feval p_y)
            (firstn (63 - v) Pairing.bls_x_bits) /\
        Fp12_bounded Fp12_tight f_val /\
        Fp2_bounded Fp2_tight tx_val /\
        Fp2_bounded Fp2_tight ty_val /\
        (FElem_Fp12 a_f f_val ⋆
         (FElem_Fp2 a_tx tx_val ⋆
          (FElem_Fp2 a_ty ty_val ⋆
           (FElem_Fp2 a_lam lam_val ⋆
            (FElem_Fp2 a_tmp1 tmp1_val ⋆
             (FElem_Fp2 a_tmp2 tmp2_val ⋆
              (FElem_Fp12 a_line line_val ⋆
               (FElem_Fp12 pout old_out ⋆
                (FElem_Fp p_px p_x ⋆
                 (FElem_Fp p_py p_y ⋆
                  (FElem_Fp2 p_qx q_x ⋆
                   (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* keep simpl/cbn of the WP proof away from the 63-step fold *)
    Local Opaque miller_fold_model Pairing.bls_x_bits.

    Lemma bls12_miller_loop_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_miller_loop" =
          Some (snd bls12_miller_loop))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2add : spec_of_Fp2_add functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls12_make_line" =
          Some (snd bls12_make_line))
        (HFp2mulfpEnv : map.get functions "bls12_Fp2_mul_fp" =
          Some (snd bls12_Fp2_mul_fp)),
      spec_of_bls12_miller_loop_functional functions.
    Proof.
      intros.
      unfold spec_of_bls12_miller_loop_functional.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
    Proof.
      (* === Function entry === *)
      eapply WeakestPreconditionProperties.start_func;
        [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_miller_loop. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Process 7 stackallocs === *)
      repeat straightline.

      (* Stackalloc 1: f (Fp12-sized) *)
      split. { apply Z_mod_mult. }
      intros a_f mStack_f mComb_f HanyF HsplitF.
      repeat straightline.

      (* Stackalloc 2: t_x (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tx mStack_tx mComb_tx HanyTx HsplitTx.
      repeat straightline.

      (* Stackalloc 3: t_y (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_ty mStack_ty mComb_ty HanyTy HsplitTy.
      repeat straightline.

      (* Stackalloc 4: lambda (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_lam mStack_lam mComb_lam HanyLam HsplitLam.
      repeat straightline.

      (* Stackalloc 5: tmp1 (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp1 mStack_tmp1 mComb_tmp1 HanyTmp1 HsplitTmp1.
      repeat straightline.

      (* Stackalloc 6: tmp2 (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp2 mStack_tmp2 mComb_tmp2 HanyTmp2 HsplitTmp2.
      repeat straightline.

      (* Stackalloc 7: line (Fp12-sized) *)
      split. { apply Z_mod_mult. }
      intros a_line mStack_line mComb_line HanyLine HsplitLine.

      (* Convert anybytes to FElems for all stack-allocated buffers *)
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
        wordok mapok a_f) as Hfb_f.
      unfold AbstractField.Placeholder in Hfb_f.
      pose proof (proj1 (Hfb_f mStack_f) HanyF) as [f_val Hfe_f]. clear Hfb_f.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tx) as Hfb_tx.
      unfold AbstractField.Placeholder in Hfb_tx.
      pose proof (proj1 (Hfb_tx mStack_tx) HanyTx) as [tx_val Hfe_tx]. clear Hfb_tx.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_ty) as Hfb_ty.
      unfold AbstractField.Placeholder in Hfb_ty.
      pose proof (proj1 (Hfb_ty mStack_ty) HanyTy) as [ty_val Hfe_ty]. clear Hfb_ty.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_lam) as Hfb_lam.
      unfold AbstractField.Placeholder in Hfb_lam.
      pose proof (proj1 (Hfb_lam mStack_lam) HanyLam) as [lam_val Hfe_lam]. clear Hfb_lam.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tmp1) as Hfb_tmp1.
      unfold AbstractField.Placeholder in Hfb_tmp1.
      pose proof (proj1 (Hfb_tmp1 mStack_tmp1) HanyTmp1) as [tmp1_val Hfe_tmp1]. clear Hfb_tmp1.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tmp2) as Hfb_tmp2.
      unfold AbstractField.Placeholder in Hfb_tmp2.
      pose proof (proj1 (Hfb_tmp2 mStack_tmp2) HanyTmp2) as [tmp2_val Hfe_tmp2]. clear Hfb_tmp2.

      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
        wordok mapok a_line) as Hfb_line.
      unfold AbstractField.Placeholder in Hfb_line.
      pose proof (proj1 (Hfb_line mStack_line) HanyLine) as [line_val Hfe_line]. clear Hfb_line.

      (* === Build master separation logic hypothesis ===
         After repeat straightline between stackallocs, the map.split
         hypotheses for stackallocs 1-6 have been destructed by
         straightline_cleanup. Only HsplitLine survives (no straightline
         after the last stackalloc). The intermediate memory "mem0" in
         HsplitLine is now a (potentially let-bound) chain of
         map.putmany containing mStack_f..mStack_tmp2 and the original
         input memory.

         Strategy: destruct HsplitLine to get
           mComb_line = putmany mem0 mStack_line
         Then build the 12-way sep by:
         1. Putting FElem_Fp12(a_line, line_val) on mStack_line
         2. For the remaining 11 FElems on mem0, use sep_from_split
            to peel off each stack buffer, building the sep from
            outside in. *)

      (* === Remaining proof ===
         The goal is a WP about the fully-expanded function body after
         7 stackallocs. The body consists of:
           12 from_word calls (fp12_set_one) + 2 fp2_copy calls
           + set i=63 + while loop + fp12_copy(out,f)
         followed by 7 stack deallocations.

         Context available:
         - HsplitLine : map.split mComb_line mem0 mStack_line
           (last stackalloc split; previous 6 were absorbed by
            straightline_cleanup into mem0)
         - Hfe_f : FElem_Fp12 a_f f_val mStack_f
         - Hfe_tx : FElem_Fp2 a_tx tx_val mStack_tx
         - Hfe_ty : FElem_Fp2 a_ty ty_val mStack_ty
         - Hfe_lam : FElem_Fp2 a_lam lam_val mStack_lam
         - Hfe_tmp1 : FElem_Fp2 a_tmp1 tmp1_val mStack_tmp1
         - Hfe_tmp2 : FElem_Fp2 a_tmp2 tmp2_val mStack_tmp2
         - Hfe_line : FElem_Fp12 a_line line_val mStack_line
         - Hsep : combined sep (arrays+input FElems) on mem0
         - Hbqx, Hbqy, Hbpx, Hbpy : bounds on inputs
         - HFp2mul...HFfromword, HMakeLine : callee specs

         The proof requires:
         A. Processing 14 initialization calls (mechanical, requires
            decomposing FElem_Fp12 into 12 FElem_Fp sub-components)
         B. Applying Loops.while_localsmap with miller_loop_inv
         C. Proving loop body preservation (the core algorithmic proof)
         D. Post-loop: fp12_copy + 7 stack deallocations
         E. Final postcondition *)

      (* === D1 proof: full miller loop body ===

         Context after 7 stackallocs + FElem_from_bytes:
         - Hsep on mem0: extended sep with input FElems + Rr + 6 array ptsto
           entries for stack buffers a_f through a_tmp2
         - HsplitLine: map.split mComb_line mem0 mStack_line
         - Hfe_f : FElem_Fp12 a_f f_val mStack_f
         - Hfe_tx/ty/lam/tmp1/tmp2 : FElem_Fp2 on mStack_*
         - Hfe_line : FElem_Fp12 a_line line_val mStack_line
         - length_stack* : length witnesses for each stack buffer

         The proof body: 12 from_word + 2 fp2_copy + set i=63 +
         while loop + fp12_copy(out,f) + 7 stack deallocations.

         Phase 1: Build master sep with FElem entries on mComb_line.
         Phase 2: Process 14 init calls (from_word + fp2_copy) + set i.
         Phase 3: Apply Loops.while_localsmap with miller_loop_inv.
         Phase 4: Post-loop fp12_copy + 7 stack deallocations. *)

      (* === Phase 1: Build master sep ===

         The array ptsto entries in Hsep describe the same memory regions
         as the FElem entries from FElem_from_bytes. To swap them, we
         destruct Hsep, replace array maps with FElem maps, and rebuild.

         But since the sub-maps are connected via let-bindings from
         straightline_stackalloc, we can use reflexivity after unfolding. *)

      (* Destruct Hsep to expose the 12 sub-components *)
      destruct Hsep as [m_s1 [mr1 [Hsplit1 [Hfe_out Hr1]]]].
      destruct Hr1 as [m_s2 [mr2 [Hsplit2 [Hfe_px Hr2]]]].
      destruct Hr2 as [m_s3 [mr3 [Hsplit3 [Hfe_py Hr3]]]].
      destruct Hr3 as [m_s4 [mr4 [Hsplit4 [Hfe_qx Hr4]]]].
      destruct Hr4 as [m_s5 [mr5 [Hsplit5 [Hfe_qy Hr5]]]].
      destruct Hr5 as [m_s6 [mr6 [Hsplit6 [Hrr Hr6]]]].
      destruct Hr6 as [m_s7 [mr7 [Hsplit7 [Harr_f Hr7]]]].
      destruct Hr7 as [m_s8 [mr8 [Hsplit8 [Harr_tx Hr8]]]].
      destruct Hr8 as [m_s9 [mr9 [Hsplit9 [Harr_ty Hr9]]]].
      destruct Hr9 as [m_s10 [mr10 [Hsplit10 [Harr_lam Hr10]]]].
      destruct Hr10 as [m_s11 [m_s12 [Hsplit11 [Harr_tmp1 Harr_tmp2]]]].

      (* The sub-maps m_s7..m_s12 are the same as mStack_f..mStack_tmp2
         because straightline_stackalloc built the sep using the original
         map.split witnesses. But they may not be definitionally equal due
         to let-bindings from straightline_cleanup. Use change to equate. *)
      (* Convert array ptsto entries back to anybytes, then to FElem.
         This gives FElem on the sub-maps from the destructed sep. *)

      (* Convert array ptsto entries back to anybytes, then to FElem.
         Use array_1_to_anybytes _ _ _ Harr to let Coq infer arguments. *)

      (* f buffer (Fp12) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_f) as Hany_f'.
      match goal with H : Datatypes.length stack = _ |- _ => rewrite H in Hany_f' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
        wordok mapok a_f) as Hfb_f'.
      unfold AbstractField.Placeholder in Hfb_f'.
      pose proof (proj1 (Hfb_f' m_s7) Hany_f') as [f_val' Hfe_f']. clear Hfb_f' Hany_f'.

      (* tx buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tx) as Hany_tx'.
      match goal with H : Datatypes.length stack0 = _ |- _ => rewrite H in Hany_tx' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tx) as Hfb_tx'.
      unfold AbstractField.Placeholder in Hfb_tx'.
      pose proof (proj1 (Hfb_tx' m_s8) Hany_tx') as [tx_val' Hfe_tx']. clear Hfb_tx' Hany_tx'.

      (* ty buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_ty) as Hany_ty'.
      match goal with H : Datatypes.length stack1 = _ |- _ => rewrite H in Hany_ty' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_ty) as Hfb_ty'.
      unfold AbstractField.Placeholder in Hfb_ty'.
      pose proof (proj1 (Hfb_ty' m_s9) Hany_ty') as [ty_val' Hfe_ty']. clear Hfb_ty' Hany_ty'.

      (* lam buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_lam) as Hany_lam'.
      match goal with H : Datatypes.length stack2 = _ |- _ => rewrite H in Hany_lam' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_lam) as Hfb_lam'.
      unfold AbstractField.Placeholder in Hfb_lam'.
      pose proof (proj1 (Hfb_lam' m_s10) Hany_lam') as [lam_val' Hfe_lam']. clear Hfb_lam' Hany_lam'.

      (* tmp1 buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp1) as Hany_tmp1'.
      match goal with H : Datatypes.length stack3 = _ |- _ => rewrite H in Hany_tmp1' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tmp1) as Hfb_tmp1'.
      unfold AbstractField.Placeholder in Hfb_tmp1'.
      pose proof (proj1 (Hfb_tmp1' m_s11) Hany_tmp1') as [tmp1_val' Hfe_tmp1']. clear Hfb_tmp1' Hany_tmp1'.

      (* tmp2 buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp2) as Hany_tmp2'.
      match goal with H : Datatypes.length stack4 = _ |- _ => rewrite H in Hany_tmp2' end.
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tmp2) as Hfb_tmp2'.
      unfold AbstractField.Placeholder in Hfb_tmp2'.
      pose proof (proj1 (Hfb_tmp2' m_s12) Hany_tmp2') as [tmp2_val' Hfe_tmp2']. clear Hfb_tmp2' Hany_tmp2'.

      (* Clear old array hypotheses *)
      clear Harr_f Harr_tx Harr_ty Harr_lam Harr_tmp1 Harr_tmp2.

      (* Now rebuild sep on mem0 with FElem entries on the CORRECT sub-maps *)
      eassert (Hsep_fe :
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp p_px p_x ⋆
          (FElem_Fp p_py p_y ⋆
           (FElem_Fp2 p_qx q_x ⋆
            (FElem_Fp2 p_qy q_y ⋆
             (Rr ⋆
              (FElem_Fp12 a_f f_val' ⋆
               (FElem_Fp2 a_tx tx_val' ⋆
                (FElem_Fp2 a_ty ty_val' ⋆
                 (FElem_Fp2 a_lam lam_val' ⋆
                  (FElem_Fp2 a_tmp1 tmp1_val' ⋆
                   FElem_Fp2 a_tmp2 tmp2_val'))))))))))) mem0).
      {
        exists m_s1, mr1. split. { exact Hsplit1. }
        split. { exact Hfe_out. }
        exists m_s2, mr2. split. { exact Hsplit2. }
        split. { exact Hfe_px. }
        exists m_s3, mr3. split. { exact Hsplit3. }
        split. { exact Hfe_py. }
        exists m_s4, mr4. split. { exact Hsplit4. }
        split. { exact Hfe_qx. }
        exists m_s5, mr5. split. { exact Hsplit5. }
        split. { exact Hfe_qy. }
        exists m_s6, mr6. split. { exact Hsplit6. }
        split. { exact Hrr. }
        exists m_s7, mr7. split. { exact Hsplit7. }
        split. { exact Hfe_f'. }
        exists m_s8, mr8. split. { exact Hsplit8. }
        split. { exact Hfe_tx'. }
        exists m_s9, mr9. split. { exact Hsplit9. }
        split. { exact Hfe_ty'. }
        exists m_s10, mr10. split. { exact Hsplit10. }
        split. { exact Hfe_lam'. }
        exists m_s11, m_s12. split. { exact Hsplit11. }
        split. { exact Hfe_tmp1'. }
        exact Hfe_tmp2'.
      }

      (* Build master sep on mComb_line *)
      eassert (Hmaster :
        (FElem_Fp12 a_f f_val' ⋆
         (FElem_Fp2 a_tx tx_val' ⋆
          (FElem_Fp2 a_ty ty_val' ⋆
           (FElem_Fp2 a_lam lam_val' ⋆
            (FElem_Fp2 a_tmp1 tmp1_val' ⋆
             (FElem_Fp2 a_tmp2 tmp2_val' ⋆
              (FElem_Fp12 a_line line_val ⋆
               (FElem_Fp12 pout old_out ⋆
                (FElem_Fp p_px p_x ⋆
                 (FElem_Fp p_py p_y ⋆
                  (FElem_Fp2 p_qx q_x ⋆
                   (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))) mComb_line).
      {
        pose proof (sep_from_split HsplitLine Hsep_fe Hfe_line) as Htmp.
        pose proof Htmp as H'. ecancel_assumption.
      }

      (* === Phase 2: Process init calls + loop + dealloc ===
         Now Hmaster has the 12-way sep on mComb_line.
         Unfold function body and process. *)

      unfold BLS12_Pairing.miller_loop_full_body.
      unfold BLS12_Pairing.cmd_seq_list.
      unfold BLS12_Pairing.fp12_set_one.
      unfold BLS12_Pairing.expr_fp12_c0, BLS12_Pairing.expr_fp12_c1,
             BLS12_Pairing.expr_fp6_c0, BLS12_Pairing.expr_fp6_c1,
             BLS12_Pairing.expr_fp6_c2, BLS12_Pairing.expr_fp_snd.

      (* === Phase 2+3+4: Init calls, loop, deallocation ===
         The function body after unfold is:
           12 from_word calls (fp12_set_one on a_f)
           2 fp2_copy calls (q_x→a_tx, q_y→a_ty)
           set i = 63
           while (i) { miller_loop_iteration }
           fp12_copy(out, f)
         followed by 7 stack deallocations.

         The init calls establish the loop invariant, the loop body preserves it
         (fragment lemmas), and the post-loop part handles the copy and deallocations. *)

      (* Offset notations *)
      Local Notation fp_felem_offset :=
        (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
      Local Notation fp6_felem_offset :=
        (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')).
      Local Notation fp6_c1_off :=
        (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).
      Local Notation fp6_c2_off :=
        (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).

      (* Split FElem_Fp12 a_f → 6 FElem_Fp2 *)
      eassert (Hf_sep : (FElem_Fp12 a_f f_val' ⋆ _) mComb_line).
      { pose proof Hmaster as H'. ecancel_assumption. }

      destruct Hf_sep as [m_f12 [m_f12_rest [Hsplit_f12 [Hfe_f12 Hf12_rest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_f f_val' m_f12 Hfe_f12)
        as Hf12_split.

      destruct Hf12_split as [m_d0 [m_d1 [Hsplit_d0d1 [Hfe_d0 Hfe_d1]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix a_f _ m_d0 Hfe_d0)
        as [m_c00 [m_c01_02 [Hsplit_c00 [Hfe_c00 Hc01_02]]]].
      destruct Hc01_02 as [m_c01 [m_c02 [Hsplit_c01_02 [Hfe_c01 Hfe_c02]]]].

      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix
        (word.add a_f (word.of_Z fp6_felem_offset)) _ m_d1 Hfe_d1)
        as [m_c10 [m_c11_12 [Hsplit_c10 [Hfe_c10 Hc11_12]]]].
      destruct Hc11_12 as [m_c11 [m_c12 [Hsplit_c11_12 [Hfe_c11 Hfe_c12]]]].

      destruct Hsplit_c00 as [Heq_c00 Hd_c00'].
      destruct Hsplit_c01_02 as [Heq_c01_02 Hd_c01_02'].
      destruct Hsplit_c10 as [Heq_c10 Hd_c10'].
      destruct Hsplit_c11_12 as [Heq_c11_12 Hd_c11_12'].
      destruct Hsplit_d0d1 as [Heq_d0d1 Hd_d0d1].
      destruct Hsplit_f12 as [Heq_f12 Hd_f12'].

      (* Normalize FElem types *)
      change (Fp2_field_parameters bls12_beta fp2_prefix)
        with bls12_Fp2_params' in Hfe_c00, Hfe_c01, Hfe_c02, Hfe_c10, Hfe_c11, Hfe_c12.
      change (Fp2_field_representation bls12_beta fp2_prefix)
        with bls12_Fp2_rep' in Hfe_c00, Hfe_c01, Hfe_c02, Hfe_c10, Hfe_c11, Hfe_c12.

      subst m_c01_02 m_c11_12 m_d0 m_d1 m_f12.
      rewrite ?map.putmany_assoc in Heq_f12.
      split_all_disjointness.

      (* Build expanded sep on mComb_line with 6 Fp2 sub-components of f *)
      eassert (Hsep_expanded :
        (FElem_Fp2 a_f (c0_felem (d0_felem f_val')) ⋆
         (FElem_Fp2 (word.add a_f fp6_c1_off) (c1_felem (d0_felem f_val')) ⋆
          (FElem_Fp2 (word.add a_f fp6_c2_off) (c2_felem (d0_felem f_val')) ⋆
           (FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem f_val')) ⋆
            (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off)
               (c1_felem (d1_felem f_val')) ⋆
             (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off)
                (c2_felem (d1_felem f_val')) ⋆
              (FElem_Fp2 a_tx tx_val' ⋆
               (FElem_Fp2 a_ty ty_val' ⋆
                (FElem_Fp2 a_lam lam_val' ⋆
                 (FElem_Fp2 a_tmp1 tmp1_val' ⋆
                  (FElem_Fp2 a_tmp2 tmp2_val' ⋆
                   (FElem_Fp12 a_line line_val ⋆
                    (FElem_Fp12 pout old_out ⋆
                     (FElem_Fp p_px p_x ⋆
                      (FElem_Fp p_py p_y ⋆
                       (FElem_Fp2 p_qx q_x ⋆
                        (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))))))))
        mComb_line).
      { subst mComb_line.
        rewrite <- ?map.putmany_assoc.
        exists m_c00, (map.putmany m_c01 (map.putmany m_c02
          (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c00 |].
        exists m_c01, (map.putmany m_c02
          (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c01 |].
        exists m_c02, (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c02 |].
        exists m_c10, (map.putmany m_c11 (map.putmany m_c12 m_f12_rest)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c10 |].
        exists m_c11, (map.putmany m_c12 m_f12_rest).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c11 |].
        exists m_c12, m_f12_rest.
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c12 |].
        exact Hf12_rest. }

      (* === Phase 2: Process 12 from_word + 2 fp2_copy + set i=63 ===
         Each pair of from_word calls targets one FElem_Fp2:
         split Fp2→2 Fp → process from_word fst → process from_word snd → join.
         Pattern identical to PairingHelpers.v calls 5-12 (lines 960-1130).

         Demonstrated below for calls 1-2 (c0.c0 of d0). *)

      (* === Phase 2: Process 12 from_word calls ===

         Demonstrated for call 1 (fst of c0.c0 of d0): *)
      eassert (Hpair1 : (FElem_Fp2 a_f (c0_felem (d0_felem f_val')) ⋆ _) mComb_line).
      { pose proof Hsep_expanded as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair1.

      (* The stack frames are in the separation hypotheses (Hsep_expanded, Hpair1),
         so the anybytes facts from the 7 stackallocs are stale.  Left in the
         context, straightline falls through to straightline_stackalloc on every
         cmd.call goal, which runs a failing ecancel_assumption search for each
         of them (over 3 h at the first from_word call).  The deallocation
         derives them again from FElem_to_bytes.  See docs/slow-proofs.md. *)
      clear HanyF HanyTx HanyTy HanyLam HanyTmp1 HanyTmp2 HanyLine.
      (* Now Hpair1 : (FElem_Fp a_f (fst_felem ...) ⋆
                         (FElem_Fp (a_f+fp_off) (snd_felem ...) ⋆ R)) mComb_line *)

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d0_felem f_val'))) _ tr).
           exact Hpair1. }
      intros t_fw1 m_fw1 rets_fw1 [Hrets_fw1 [Htr_fw1 [fw1 [Hfv_fw1 [Hb_fw1 Hsep_fw1]]]]].
      apply (@hide _) in Hfv_fw1.
      subst rets_fw1. symmetry in Htr_fw1. subst t_fw1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 2: from_word(a_f.d0.c0 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw1. }
      intros t_fw2 m_fw2 rets_fw2 [Hrets_fw2 [Htr_fw2 [fw2 [Hfv_fw2 [Hb_fw2 Hsep_fw2]]]]].
      apply (@hide _) in Hfv_fw2.
      subst rets_fw2. symmetry in Htr_fw2. subst t_fw2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 3-4: from_word on c1(d0) fst/snd --- *)
      repeat straightline.
      eassert (Hpair2 : (FElem_Fp2 (word.add a_f fp6_c1_off) (c1_felem (d0_felem f_val')) ⋆ _) m_fw2).
      { pose proof Hsep_fw2 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair2.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d0_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair2. }
      intros t_fw3 m_fw3 rets_fw3 [Hrets_fw3 [Htr_fw3 [fw3 [Hfv_fw3 [Hb_fw3 Hsep_fw3]]]]].
      apply (@hide _) in Hfv_fw3.
      subst rets_fw3. symmetry in Htr_fw3. subst t_fw3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw3. }
      intros t_fw4 m_fw4 rets_fw4 [Hrets_fw4 [Htr_fw4 [fw4 [Hfv_fw4 [Hb_fw4 Hsep_fw4]]]]].
      apply (@hide _) in Hfv_fw4.
      subst rets_fw4. symmetry in Htr_fw4. subst t_fw4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 5-6: from_word on c2(d0) fst/snd --- *)
      repeat straightline.
      eassert (Hpair3 : (FElem_Fp2 (word.add a_f fp6_c2_off) (c2_felem (d0_felem f_val')) ⋆ _) m_fw4).
      { pose proof Hsep_fw4 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair3.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d0_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair3. }
      intros t_fw5 m_fw5 rets_fw5 [Hrets_fw5 [Htr_fw5 [fw5 [Hfv_fw5 [Hb_fw5 Hsep_fw5]]]]].
      apply (@hide _) in Hfv_fw5.
      subst rets_fw5. symmetry in Htr_fw5. subst t_fw5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw5. }
      intros t_fw6 m_fw6 rets_fw6 [Hrets_fw6 [Htr_fw6 [fw6 [Hfv_fw6 [Hb_fw6 Hsep_fw6]]]]].
      apply (@hide _) in Hfv_fw6.
      subst rets_fw6. symmetry in Htr_fw6. subst t_fw6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 7-8: from_word on c0(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair4 : (FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem f_val')) ⋆ _) m_fw6).
      { pose proof Hsep_fw6 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair4.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair4. }
      intros t_fw7 m_fw7 rets_fw7 [Hrets_fw7 [Htr_fw7 [fw7 [Hfv_fw7 [Hb_fw7 Hsep_fw7]]]]].
      apply (@hide _) in Hfv_fw7.
      subst rets_fw7. symmetry in Htr_fw7. subst t_fw7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw7. }
      intros t_fw8 m_fw8 rets_fw8 [Hrets_fw8 [Htr_fw8 [fw8 [Hfv_fw8 [Hb_fw8 Hsep_fw8]]]]].
      apply (@hide _) in Hfv_fw8.
      subst rets_fw8. symmetry in Htr_fw8. subst t_fw8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 9-10: from_word on c1(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair5 : (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off) (c1_felem (d1_felem f_val')) ⋆ _) m_fw8).
      { pose proof Hsep_fw8 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair5.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair5. }
      intros t_fw9 m_fw9 rets_fw9 [Hrets_fw9 [Htr_fw9 [fw9 [Hfv_fw9 [Hb_fw9 Hsep_fw9]]]]].
      apply (@hide _) in Hfv_fw9.
      subst rets_fw9. symmetry in Htr_fw9. subst t_fw9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw9. }
      intros t_fw10 m_fw10 rets_fw10 [Hrets_fw10 [Htr_fw10 [fw10 [Hfv_fw10 [Hb_fw10 Hsep_fw10]]]]].
      apply (@hide _) in Hfv_fw10.
      subst rets_fw10. symmetry in Htr_fw10. subst t_fw10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 11-12: from_word on c2(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair6 : (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off) (c2_felem (d1_felem f_val')) ⋆ _) m_fw10).
      { pose proof Hsep_fw10 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair6.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair6. }
      intros t_fw11 m_fw11 rets_fw11 [Hrets_fw11 [Htr_fw11 [fw11 [Hfv_fw11 [Hb_fw11 Hsep_fw11]]]]].
      apply (@hide _) in Hfv_fw11.
      subst rets_fw11. symmetry in Htr_fw11. subst t_fw11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw11. }
      intros t_fw12 m_fw12 rets_fw12 [Hrets_fw12 [Htr_fw12 [fw12 [Hfv_fw12 [Hb_fw12 Hsep_fw12]]]]].
      apply (@hide _) in Hfv_fw12.
      subst rets_fw12. symmetry in Htr_fw12. subst t_fw12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Step 1: Extract Fp-level lengths from FElem predicates === *)
      Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
      Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
      Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
      Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).

      pose proof fun p v m (H : FElem_Fp p v m) =>
        @QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls12_pf_params bls12_Fp_rep p v m H
        as FpLen.

      (* Extract length for each fw from the sep *)
      assert (Hlen_fw1 : length fw1 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw1 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw2 : length fw2 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw2 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw3 : length fw3 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw3 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw4 : length fw4 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw4 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw5 : length fw5 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw5 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw6 : length fw6 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw6 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw7 : length fw7 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw7 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw8 : length fw8 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw8 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw9 : length fw9 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw9 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw10 : length fw10 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw10 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw11 : length fw11 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw11 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw12 : length fw12 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw12 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      clear FpLen.

      (* === Step 2: Chain-join Fp pairs into Fp2 === *)

      (* Join d0.c0: fw1 + fw2 *)
      eassert (Hsep_j1 : (FElem_Fp _ fw1 ⋆ (FElem_Fp _ fw2 ⋆ _)) m_fw12).
      { pose proof Hsep_fw12 as H'. ecancel_assumption. }
      apply FElem_Fp_join_in_sep in Hsep_j1; [| exact Hlen_fw1 | exact Hlen_fw2].

      (* Join d0.c1: fw3 + fw4 *)
      eassert (Hsep_j2 : (FElem_Fp _ fw3 ⋆ (FElem_Fp _ fw4 ⋆ _)) m_fw12).
      { pose proof Hsep_j1 as H'. ecancel_assumption. }
      eassert (Hsep_j2' : (FElem_Fp _ fw3 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw4 ⋆ _)) m_fw12).
      { exact Hsep_j2. }
      apply FElem_Fp_join_in_sep in Hsep_j2'; [| exact Hlen_fw3 | exact Hlen_fw4].

      (* Join d0.c2: fw5 + fw6 *)
      eassert (Hsep_j3 : (FElem_Fp _ fw5 ⋆ (FElem_Fp _ fw6 ⋆ _)) m_fw12).
      { pose proof Hsep_j2' as H'. ecancel_assumption. }
      eassert (Hsep_j3' : (FElem_Fp _ fw5 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw6 ⋆ _)) m_fw12).
      { exact Hsep_j3. }
      apply FElem_Fp_join_in_sep in Hsep_j3'; [| exact Hlen_fw5 | exact Hlen_fw6].

      (* Join d1.c0: fw7 + fw8 *)
      eassert (Hsep_j4 : (FElem_Fp _ fw7 ⋆ (FElem_Fp _ fw8 ⋆ _)) m_fw12).
      { pose proof Hsep_j3' as H'. ecancel_assumption. }
      eassert (Hsep_j4' : (FElem_Fp _ fw7 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw8 ⋆ _)) m_fw12).
      { exact Hsep_j4. }
      apply FElem_Fp_join_in_sep in Hsep_j4'; [| exact Hlen_fw7 | exact Hlen_fw8].

      (* Join d1.c1: fw9 + fw10 *)
      eassert (Hsep_j5 : (FElem_Fp _ fw9 ⋆ (FElem_Fp _ fw10 ⋆ _)) m_fw12).
      { pose proof Hsep_j4' as H'. ecancel_assumption. }
      eassert (Hsep_j5' : (FElem_Fp _ fw9 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw10 ⋆ _)) m_fw12).
      { exact Hsep_j5. }
      apply FElem_Fp_join_in_sep in Hsep_j5'; [| exact Hlen_fw9 | exact Hlen_fw10].

      (* Join d1.c2: fw11 + fw12 *)
      eassert (Hsep_j6 : (FElem_Fp _ fw11 ⋆ (FElem_Fp _ fw12 ⋆ _)) m_fw12).
      { pose proof Hsep_j5' as H'. ecancel_assumption. }
      eassert (Hsep_j6' : (FElem_Fp _ fw11 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw12 ⋆ _)) m_fw12).
      { exact Hsep_j6. }
      apply FElem_Fp_join_in_sep in Hsep_j6'; [| exact Hlen_fw11 | exact Hlen_fw12].

      (* === Steps 3-6: Join Fp2→Fp6→Fp12 and rebuild sep === *)

      (* Rearrange into [d0_3 * (d1_3 * rest)] to extract sub-memories *)
      eassert (Hsep_d0_ext :
        ((FElem_Fp2 a_f (fw1 ++ fw2) ⋆
          (FElem_Fp2 (word.add a_f fp6_c1_off) (fw3 ++ fw4) ⋆
           FElem_Fp2 (word.add a_f fp6_c2_off) (fw5 ++ fw6))) ⋆ _) m_fw12).
      { pose proof Hsep_j6' as H'. ecancel_assumption_impl. }
      destruct Hsep_d0_ext as [m_d0_3 [m_d0_rest [Hsplit_d0 [Hfe_d0_3 Hd0_rest]]]].

      eassert (Hd1_3_ext :
        ((FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (fw7 ++ fw8) ⋆
          (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off) (fw9 ++ fw10) ⋆
           FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off) (fw11 ++ fw12))) ⋆ _) m_d0_rest).
      { pose proof Hd0_rest as H'. ecancel_assumption_impl. }
      destruct Hd1_3_ext as [m_d1_3 [m_rest [Hsplit_d1 [Hfe_d1_3 Hrest]]]].

      (* Length facts for Fp2 *)
      assert (Hlen_d0c0_fp2 : length (fw1 ++ fw2) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw1, Hlen_fw2. reflexivity. }
      assert (Hlen_d0c1_fp2 : length (fw3 ++ fw4) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw3, Hlen_fw4. reflexivity. }
      assert (Hlen_d0c2_fp2 : length (fw5 ++ fw6) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw5, Hlen_fw6. reflexivity. }
      assert (Hlen_d1c0_fp2 : length (fw7 ++ fw8) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
      assert (Hlen_d1c1_fp2 : length (fw9 ++ fw10) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw9, Hlen_fw10. reflexivity. }
      assert (Hlen_d1c2_fp2 : length (fw11 ++ fw12) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw11, Hlen_fw12. reflexivity. }

      (* Build Fp6 for d0 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        a_f (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) m_d0_3
        Hlen_d0c0_fp2 Hlen_d0c1_fp2 Hlen_d0c2_fp2 Hfe_d0_3)
        as Hfe_d0'.

      (* Build Fp6 for d1 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        (word.add a_f (word.of_Z fp6_felem_offset))
        (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) m_d1_3
        Hlen_d1c0_fp2 Hlen_d1c1_fp2 Hlen_d1c2_fp2 Hfe_d1_3)
        as Hfe_d1'.

      (* Build Fp12 from d0 and d1 *)
      assert (Hlen_d0_fp6 : length ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw1, Hlen_fw2, Hlen_fw3, Hlen_fw4, Hlen_fw5, Hlen_fw6.
        reflexivity. }
      assert (Hlen_d1_fp6 : length ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_fw9, Hlen_fw10, Hlen_fw11, Hlen_fw12.
        reflexivity. }

      (* Build 2-way Fp6 sep *)
      destruct Hsplit_d0 as [Heq_d0 Hd_d0].
      destruct Hsplit_d1 as [Heq_d1 Hd_d1].
      set (m_fp12_j := map.putmany m_d0_3 m_d1_3).
      assert (Hsep_2fp6 : (FElem_Fp6 a_f ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ⋆
        FElem_Fp6 (word.add a_f (word.of_Z fp6_felem_offset))
          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))) m_fp12_j).
      { subst m_fp12_j. exists m_d0_3, m_d1_3.
        split; [split; [reflexivity |] |].
        { (* disjoint m_d0_3 m_d1_3:
             m_d0_rest = putmany m_d1_3 m_rest, disjoint m_d0_3 m_d0_rest,
             so disjoint m_d0_3 m_d1_3 *)
          subst m_d0_rest.
          exact (proj1 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0)). }
        split; [exact Hfe_d0' | exact Hfe_d1']. }

      pose proof (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
        a_f ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
        ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) m_fp12_j
        Hlen_d0_fp6 Hlen_d1_fp6 Hsep_2fp6)
        as Hfe_fp12_j.

      (* Rebuild full sep *)
      set (f_new := ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ++
                     ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))).
      eassert (Hsep_rejoined :
        (FElem_Fp12 a_f f_new ⋆
         (FElem_Fp2 a_tx tx_val' ⋆
          (FElem_Fp2 a_ty ty_val' ⋆
           (FElem_Fp2 a_lam lam_val' ⋆
            (FElem_Fp2 a_tmp1 tmp1_val' ⋆
             (FElem_Fp2 a_tmp2 tmp2_val' ⋆
              (FElem_Fp12 a_line line_val ⋆
               (FElem_Fp12 pout old_out ⋆
                (FElem_Fp p_px p_x ⋆
                 (FElem_Fp p_py p_y ⋆
                  (FElem_Fp2 p_qx q_x ⋆
                   (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))) m_fw12).
      { subst m_fw12 m_d0_rest m_fp12_j.
        exists (map.putmany m_d0_3 m_d1_3), m_rest.
        split; [split |].
        { (* m_fw12 = putmany (putmany m_d0_3 m_d1_3) m_rest
             Since m_fw12 = putmany m_d0_3 m_d0_rest = putmany m_d0_3 (putmany m_d1_3 m_rest)
             and putmany is associative... *)
          rewrite map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { exact (proj2 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0)). }
          { exact Hd_d1. } }
        split; [exact Hfe_fp12_j | exact Hrest]. }

      (* === fp2_copy: copy q_x → a_tx === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp2copy.
           pose proof Hsep_rejoined as Htmp_copy.
           split; ecancel_assumption_impl. }
      (* Use the EXACT same destruct pattern as proven from_word calls *)
      intros t_c1 m_c1 rets_c1 Hpost_c1.
      destruct Hpost_c1 as [Hrets_c1 [Htr_c1 Hsep_c1]].
      subst rets_c1. symmetry in Htr_c1. subst t_c1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === fp2_copy: copy q_y → a_ty === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp2copy.
           pose proof Hsep_c1 as Htmp_copy2.
           split; ecancel_assumption_impl. }
      intros t_c2 m_c2 rets_c2 Hpost_c2.
      destruct Hpost_c2 as [Hrets_c2 [Htr_c2 Hsep_c2]].
      subst rets_c2. symmetry in Htr_c2. subst t_c2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === set i = 63 === *)
      repeat straightline.

      (* === Loop === *)
      eapply Loops.while_localsmap
        with (v0 := 63%nat)
             (lt := Nat.lt)
             (invariant := miller_loop_inv_f a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
                      pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr).

      (* well_founded *)
      { exact lt_wf. }

      (* Initial invariant *)
      { unfold miller_loop_inv_f.
        split; [reflexivity |].
        split; [lia |].

        (* After 12 from_word (set_one on a_f) + 2 fp2_copy + set i=63:
           - a_f contains f_new (the identity element, tight bounded)
           - a_tx contains q_x (copied from input, tight bounded per Hbqx)
           - a_ty contains q_y (copied from input, tight bounded per Hbqy)
           - lam, tmp1, tmp2 contain initial values lam_val', tmp1_val', tmp2_val'
           - line contains line_val
           - All other FElems unchanged *)
        eexists f_new, _, _, lam_val', tmp1_val', tmp2_val', line_val.
        split.
        { (* feval: f = 1 (fp12_set_one), T = Q *)
          rewrite miller_fold_model_unfold.
          change (63 - 63)%nat with 0%nat. cbn [firstn fold_left].
          refine (f_equal2 pair _ eq_refl).
          subst f_new.
          destruct Hfv_fw1 as [Hfv_fw1]. destruct Hfv_fw2 as [Hfv_fw2].
          destruct Hfv_fw3 as [Hfv_fw3]. destruct Hfv_fw4 as [Hfv_fw4].
          destruct Hfv_fw5 as [Hfv_fw5]. destruct Hfv_fw6 as [Hfv_fw6].
          destruct Hfv_fw7 as [Hfv_fw7]. destruct Hfv_fw8 as [Hfv_fw8].
          destruct Hfv_fw9 as [Hfv_fw9]. destruct Hfv_fw10 as [Hfv_fw10].
          destruct Hfv_fw11 as [Hfv_fw11]. destruct Hfv_fw12 as [Hfv_fw12].
          exact (Fp12_feval_set_one fw1 fw2 fw3 fw4 fw5 fw6 fw7 fw8 fw9 fw10 fw11 fw12
                   Hlen_fw1 Hlen_fw2 Hlen_fw3 Hlen_fw4 Hlen_fw5 Hlen_fw6
                   Hlen_fw7 Hlen_fw8 Hlen_fw9 Hlen_fw10 Hlen_fw11
                   Hfv_fw1 Hfv_fw2 Hfv_fw3 Hfv_fw4 Hfv_fw5 Hfv_fw6
                   Hfv_fw7 Hfv_fw8 Hfv_fw9 Hfv_fw10 Hfv_fw11 Hfv_fw12). }
        (* Bounds *)
        split.
        { (* Fp12_bounded Fp12_tight f_new — from 12 from_word tight bounds *)
          subst f_new.
          (* Fp12_bounded = bounded on d0_felem /\ bounded on d1_felem.
             Fp6_bounded = bounded on c0/c1/c2.  Fp2_bounded = bounded on fst/snd.
             All reduce to Fp_bounded Fp_tight fwi. *)
          change Fp12_bounded with
            (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
                 (felem : list word) =>
              @AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' b (d0_felem felem) /\
              @AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' b (d1_felem felem));
            cbv beta.
          rewrite (@DodecicFieldExtensions.d0_felem_app _ _ _ _
            bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
            ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
            ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))
            Hlen_d0_fp6).
          rewrite (@DodecicFieldExtensions.d1_felem_app _ _ _ _
            bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
            ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
            ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))
            Hlen_d0_fp6).
          change (@AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep') with
            (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
                 (felem : list word) =>
              Fp2_bounded b (c0_felem felem) /\
              Fp2_bounded b (c1_felem felem) /\
              Fp2_bounded b (c2_felem felem));
            cbv beta.
          rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2).
          rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
          rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
          rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2).
          rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
          rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _
            bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
          (* Level 3: Fp2_bounded -> 2× Fp_bounded via fst/snd *)
          change Fp2_bounded with
            (fun (b : @AbstractField.bounds _ _ _ _ _ _ bls12_Fp_rep)
                 (ws : list word) =>
              Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws));
            cbv beta.
          unfold fst_felem, snd_felem,
            QuadraticFieldExtensionsSpecs.fst_felem,
            QuadraticFieldExtensionsSpecs.snd_felem.
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw1).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw1).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw3).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw3).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw5).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw5).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw7).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw7).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw9).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw9).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw11).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw11).
          split.
          { split.
            { split; [exact Hb_fw1 | exact Hb_fw2]. }
            split.
            { split; [exact Hb_fw3 | exact Hb_fw4]. }
            { split; [exact Hb_fw5 | exact Hb_fw6]. } }
          { split.
            { split; [exact Hb_fw7 | exact Hb_fw8]. }
            split.
            { split; [exact Hb_fw9 | exact Hb_fw10]. }
            { split; [exact Hb_fw11 | exact Hb_fw12]. } } }
        split.
        { (* Fp2_bounded Fp2_tight tx — q_x has tight bounds *)
          exact Hbqx. }
        split.
        { (* Fp2_bounded Fp2_tight ty — q_y has tight bounds *)
          exact Hbqy. }
        split.
        { (* Sep — the current sep matches the invariant *)
          ecancel_assumption. }
        (* Locals: map.get for each variable *)
        repeat split; repeat straightline. }

      (* Loop body *)
      { intros vi ti mi li Hinv.
        unfold miller_loop_inv_f in Hinv.
        destruct Hinv as [Htr_i [Hvi_le [f_vi [tx_vi [ty_vi [lam_vi [tmp1_vi [tmp2_vi [line_vi [Hfold_vi [Hbf_vi [Hbtx_vi [Hbty_vi [Hsep_vi [Hi_vi [Hf_vi [Htx_vi [Hty_vi [Hlam_vi [Htmp1_vi [Htmp2_vi [Hline_vi [Hout_vi [Hpx_vi [Hpy_vi [Hqx_vi Hqy_vi]]]]]]]]]]]]]]]]]]]]]]]]]].
        subst ti.

        (* Evaluate branch condition: expr.var "i" *)
        exists (word.of_Z (Z.of_nat vi)).
        split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          rewrite Hi_vi.
          exists (word.of_Z (Z.of_nat vi)).
          split; exact eq_refl. }
        split.
        { (* TRUE branch: one iteration, by the fragment lemmas *)
          intro Hne.
          rewrite miller_fold_model_unfold in Hfold_vi.
          assert (Hvi_pos : (0 < vi)%nat).
          { destruct vi; [exfalso; apply Hne; reflexivity | lia]. }
          pose proof (make_line_f_ok functions HMakeLine HFp2mul HFp2sub HFp2opp
                        HFp2mulfpEnv HFpmul HFpcopy HFfromword) as HMLf.
          rewrite miller_iteration_split.
          miller_straightline. (* cmd.seq *)
          miller_straightline. (* cmd.set "i" *)
          unfold dlet.dlet; cbv beta.
          eapply (miller_doubling_ok functions HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2copy
                    HFp12mul HFp12sqr HMLf
                    a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
                    f_vi tx_vi ty_vi lam_vi tmp1_vi tmp2_vi line_vi p_x p_y
                    (FElem_Fp12 pout old_out ⋆ (FElem_Fp2 p_qx q_x ⋆ (FElem_Fp2 p_qy q_y ⋆ Rr)))).
          1: exact Hbf_vi. 1: exact Hbtx_vi. 1: exact Hbty_vi. 1: exact Hbpx. 1: exact Hbpy.
          1: { ecancel_assumption. }
          1-9: (rewrite map.get_put_diff by congruence; assumption).
          intros mD fD txD tyD lamD t1D t2D lnD HfD HtxD HtyD _ _ HbfD HbtxD HbtyD HsD.
          rewrite miller_cond_cmd_eq. unfold miller_bit_cmd.
          miller_straightline. (* cmd.seq *)
          miller_straightline. (* cmd.set "bit" *)
          unfold dlet.dlet; cbv beta.
          miller_straightline. (* cmd.cond *)
          match goal with
          | |- (word.unsigned ?b <> 0 -> _) /\ _ =>
            replace b with (@word.and 64 word
                (word.sru (word.of_Z 0xd201000000010000)
                          (word.sub (word.of_Z (Z.of_nat vi)) (word.of_Z 1)))
                (word.of_Z 1)) by reflexivity
          end.
          rewrite (miller_bit_word vi ltac:(lia)).
          remember (nth (63 - vi) Pairing.bls_x_bits false) as bit eqn:Hbitv.
          split.
          { (* bit = 1: addition step *)
            intro HbitT. destruct bit; [| exfalso; apply HbitT; reflexivity].
            eapply (miller_addition_ok functions HFp2mul HFp2sub HFp2sqr HFp2inv HFp2copy
                      HFp12mul HMLf
                      a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py p_qx p_qy
                      fD txD tyD lamD t1D t2D lnD p_x p_y q_x q_y
                      (FElem_Fp12 pout old_out ⋆ Rr)).
            1: exact HbfD. 1: exact HbtxD. 1: exact HbtyD. 1: exact Hbpx. 1: exact Hbpy.
            1: exact Hbqx. 1: exact Hbqy.
            1: { ecancel_assumption. }
            1-11: (repeat (rewrite map.get_put_diff by congruence); assumption).
            intros mA fA txA tyA lamA t1A t2A lnA HfA HtxA HtyA _ _ HbfA HbtxA HbtyA HsA.
            exists (Nat.sub vi 1).
            split; [| lia].
            unfold miller_loop_inv_f.
            split; [reflexivity |]. split; [lia |].
            exists fA, txA, tyA, lamA, t1A, t2A, lnA.
            split.
            { rewrite miller_fold_model_unfold.
              replace (63 - (vi - 1))%nat with (S (63 - vi)) by lia.
              eapply inv_step_add;
                [ lia | symmetry; exact Hbitv | exact Hfold_vi
                | exact HfD | exact HtxD | exact HtyD | exact HfA | exact HtxA | exact HtyA ]. }
            split; [exact HbfA |]. split; [exact HbtxA |]. split; [exact HbtyA |].
            split; [ecancel_assumption |].
            split.
            { rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
              f_equal. etransitivity; [| exact (word_nat_sub1 vi Hvi_pos)]. reflexivity. }
            repeat (split; [repeat (rewrite map.get_put_diff by congruence); assumption |]).
            repeat (rewrite map.get_put_diff by congruence); assumption. }
          { (* bit = 0: skip *)
            intro HbitF. destruct bit; [discriminate HbitF |].
            miller_straightline. (* cmd.skip *)
            exists (Nat.sub vi 1).
            split; [| lia].
            unfold miller_loop_inv_f.
            split; [reflexivity |]. split; [lia |].
            exists fD, txD, tyD, lamD, t1D, t2D, lnD.
            split.
            { rewrite miller_fold_model_unfold.
              replace (63 - (vi - 1))%nat with (S (63 - vi)) by lia.
              eapply inv_step_dbl;
                [ lia | symmetry; exact Hbitv | exact Hfold_vi
                | exact HfD | exact HtxD | exact HtyD ]. }
            split; [exact HbfD |]. split; [exact HbtxD |]. split; [exact HbtyD |].
            split; [ecancel_assumption |].
            split.
            { rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
              f_equal. etransitivity; [| exact (word_nat_sub1 vi Hvi_pos)]. reflexivity. }
            repeat (split; [repeat (rewrite map.get_put_diff by congruence); assumption |]).
            repeat (rewrite map.get_put_diff by congruence); assumption. } }
        { (* FALSE branch: word.unsigned br = 0, postcondition *)
          intro Heq0.
          (* Heq0 tells us the loop exits. We don't need vi=0 explicitly. *)

          (* The post-loop goal is the WP for:
             cmd.call fp12_copy [out; f] + 7 deallocs *)

          (* Provide arguments for the call *)
          exists [pout; a_f].
          split.
          { (* dexprs mi li [expr.var "out"; expr.var "f"] [pout; a_f] *)
            cbv [dexprs list_map list_map_body
                 WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get].
            rewrite Hout_vi. rewrite Hf_vi.
            eexists. split; [exact eq_refl |].
            eexists. split; [exact eq_refl |].
            exact eq_refl. }

          (* fp12_copy(out, f) via Semantics.call *)
          eapply Semantics.weaken_call.
          1: { eapply HFp12copy.
               split; ecancel_assumption. }
          intros t_cp m_cp ? [Hrets_cp Hsep_cp].
          subst.
          destruct Hsep_cp as [Htr_cp Hsep_cp'].
          symmetry in Htr_cp. subst t_cp.

          (* Process return value *)
          exists li.
          split. { cbv [map.putmany_of_list_zip]. exact eq_refl. }

          (* === Stack deallocation (7 levels) + final postcondition === *)

          (* --- Dealloc level 1: line (Fp12-sized) --- *)
          eassert (Hline_sep : (_ ⋆ FElem_Fp12 a_line line_vi) m_cp).
          { pose proof Hsep_cp' as H'. ecancel_assumption. }
          destruct Hline_sep as [m_rest_line [m_line [[Heq_line Hd_line] [Hrest_line Hfline]]]].
          exists m_rest_line, m_line.
          split. { exact (AbstractField.FElem_to_bytes a_line line_vi m_line Hfline). }
          split. { split; [exact Heq_line | exact Hd_line]. }

          (* --- Dealloc level 2: tmp2 (Fp2-sized) --- *)
          eassert (Htmp2_sep : (_ ⋆ FElem_Fp2 a_tmp2 tmp2_vi) m_rest_line).
          { pose proof Hrest_line as H'. ecancel_assumption. }
          destruct Htmp2_sep as [m_rest_tmp2 [m_tmp2 [[Heq_tmp2 Hd_tmp2] [Hrest_tmp2 Hftmp2]]]].
          exists m_rest_tmp2, m_tmp2.
          split. { exact (AbstractField.FElem_to_bytes a_tmp2 tmp2_vi m_tmp2 Hftmp2). }
          split. { split; [exact Heq_tmp2 | exact Hd_tmp2]. }

          (* --- Dealloc level 3: tmp1 (Fp2-sized) --- *)
          eassert (Htmp1_sep : (_ ⋆ FElem_Fp2 a_tmp1 tmp1_vi) m_rest_tmp2).
          { pose proof Hrest_tmp2 as H'. ecancel_assumption. }
          destruct Htmp1_sep as [m_rest_tmp1 [m_tmp1 [[Heq_tmp1 Hd_tmp1] [Hrest_tmp1 Hftmp1]]]].
          exists m_rest_tmp1, m_tmp1.
          split. { exact (AbstractField.FElem_to_bytes a_tmp1 tmp1_vi m_tmp1 Hftmp1). }
          split. { split; [exact Heq_tmp1 | exact Hd_tmp1]. }

          (* --- Dealloc level 4: lambda (Fp2-sized) --- *)
          eassert (Hlam_sep : (_ ⋆ FElem_Fp2 a_lam lam_vi) m_rest_tmp1).
          { pose proof Hrest_tmp1 as H'. ecancel_assumption. }
          destruct Hlam_sep as [m_rest_lam [m_lam [[Heq_lam Hd_lam] [Hrest_lam Hflam]]]].
          exists m_rest_lam, m_lam.
          split. { exact (AbstractField.FElem_to_bytes a_lam lam_vi m_lam Hflam). }
          split. { split; [exact Heq_lam | exact Hd_lam]. }

          (* --- Dealloc level 5: t_y (Fp2-sized) --- *)
          eassert (Hty_sep : (_ ⋆ FElem_Fp2 a_ty ty_vi) m_rest_lam).
          { pose proof Hrest_lam as H'. ecancel_assumption. }
          destruct Hty_sep as [m_rest_ty [m_ty [[Heq_ty Hd_ty] [Hrest_ty Hfty]]]].
          exists m_rest_ty, m_ty.
          split. { exact (AbstractField.FElem_to_bytes a_ty ty_vi m_ty Hfty). }
          split. { split; [exact Heq_ty | exact Hd_ty]. }

          (* --- Dealloc level 6: t_x (Fp2-sized) --- *)
          eassert (Htx_sep : (_ ⋆ FElem_Fp2 a_tx tx_vi) m_rest_ty).
          { pose proof Hrest_ty as H'. ecancel_assumption. }
          destruct Htx_sep as [m_rest_tx [m_tx [[Heq_tx Hd_tx] [Hrest_tx Hftx]]]].
          exists m_rest_tx, m_tx.
          split. { exact (AbstractField.FElem_to_bytes a_tx tx_vi m_tx Hftx). }
          split. { split; [exact Heq_tx | exact Hd_tx]. }

          (* --- Dealloc level 7: f (Fp12-sized) --- *)
          eassert (Hf_sep : (_ ⋆ FElem_Fp12 a_f f_vi) m_rest_tx).
          { pose proof Hrest_tx as H'. ecancel_assumption. }
          destruct Hf_sep as [m_rest_f [m_f [[Heq_f Hd_f] [Hrest_f Hff]]]].
          exists m_rest_f, m_f.
          split. { exact (AbstractField.FElem_to_bytes a_f f_vi m_f Hff). }
          split. { split; [exact Heq_f | exact Hd_f]. }

          (* --- Final postcondition --- *)
          cbv [list_map list_map_body].
          split. { exact eq_refl. }
          split. { exact eq_refl. }
          exists f_vi.
          split.
          { assert (Hvi0 : vi = 0%nat).
            { rewrite word.unsigned_of_Z in Heq0. cbv [word.wrap] in Heq0.
              rewrite Z.mod_small in Heq0
                by (split; [apply Nat2Z.is_nonneg |]; apply Z.le_lt_trans with (m := 63); [apply (Nat2Z.inj_le vi 63); exact Hvi_le | vm_compute; reflexivity]).
              lia. }
            subst vi.
            rewrite firstn_all2 in Hfold_vi by (rewrite bls_x_bits_length; lia).
            exact (f_equal fst Hfold_vi). }
          split. { pose proof (@DodecicFieldExtensionsSpecs.Fp12_field_representation_ok
                     _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_Fp_rep_ok bls12_beta
                     bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix) as Hfp12_ok.
                   exact (@AbstractField.relax_bounds _ _ _ _ _ _ _ Hfp12_ok _ Hbf_vi). }
          exact Hrest_f. }
      }
    Qed.


    (* ============================================================ *)
    (* The fold model is Pairing.miller_loop                         *)
    (* ============================================================ *)

    Local Notation Fp6' := ((Fp2 * Fp2 * Fp2)%type).

    Lemma step_model_fold_eq
      (Hinv : forall a : Fp2, @AbstractField.Finv _ bls12_Fp2_params' a =
                              Pairing.fp2_inv PrimeField.M_pos a) :
      forall qx qy xp yp bits init,
        fold_left (step_model qx qy xp yp) bits init =
        fold_left (BLS12_Fp12Feval.bedrock2_miller_step PrimeField.M_pos qx qy xp yp) bits init.
    Proof.
      intros qx qy xp yp bits. induction bits as [|b bs IH]; intros init; [reflexivity |].
      cbn [fold_left]. rewrite (step_model_eq Hinv). apply IH.
    Qed.

    (** Under the Fp2-inverse bridge and the six Fp6 bridges of BLS12_PairingFeval.v, the
        value in the post of [bls12_miller_loop_functional_ok] is [Pairing.miller_loop]. *)
    Theorem miller_fold_model_eq_miller_loop
      (Hinv : forall a : Fp2, @AbstractField.Finv _ bls12_Fp2_params' a =
                              Pairing.fp2_inv PrimeField.M_pos a)
      (Hadd : forall a b : Fp6', Fp6.fp6_add PrimeField.M_pos a b = Pairing.fp6_add PrimeField.M_pos a b)
      (Hsub : forall a b : Fp6', Fp6.fp6_sub PrimeField.M_pos a b = Pairing.fp6_sub PrimeField.M_pos a b)
      (Hmul : forall a b : Fp6',
          Fp6.fp6_mul PrimeField.M_pos (F.of_Z PrimeField.M_pos (-1)) F.one F.one a b =
          Pairing.fp6_mul PrimeField.M_pos a b)
      (Hmulv : forall a : Fp6',
          Fp6.fp6_mul_by_v PrimeField.M_pos (F.of_Z PrimeField.M_pos (-1)) F.one F.one a =
          Pairing.fp6_mul_by_v PrimeField.M_pos a)
      (Hself : forall a : Fp6', Pairing.fp6_mul PrimeField.M_pos a a = Pairing.fp6_sqr PrimeField.M_pos a)
      (Hcross : forall a b : Fp6',
          Pairing.fp6_sub PrimeField.M_pos
            (Pairing.fp6_sub PrimeField.M_pos
               (Pairing.fp6_mul PrimeField.M_pos (Pairing.fp6_add PrimeField.M_pos a b)
                  (Pairing.fp6_add PrimeField.M_pos a b))
               (Pairing.fp6_mul PrimeField.M_pos a a))
            (Pairing.fp6_mul PrimeField.M_pos b b) =
          Pairing.fp6_add PrimeField.M_pos (Pairing.fp6_mul PrimeField.M_pos a b)
            (Pairing.fp6_mul PrimeField.M_pos a b)) :
      forall (P : Pairing.G1Affine PrimeField.M_pos) (Q : Pairing.G2Affine PrimeField.M_pos),
        Pairing.g1_infinity PrimeField.M_pos P = false ->
        Pairing.g2_infinity PrimeField.M_pos Q = false ->
        fst (miller_fold_model (Pairing.g2_x PrimeField.M_pos Q) (Pairing.g2_y PrimeField.M_pos Q)
               (Pairing.g1_x PrimeField.M_pos P) (Pairing.g1_y PrimeField.M_pos P)
               Pairing.bls_x_bits) =
        Pairing.miller_loop PrimeField.M_pos P Q.
    Proof.
      intros P Q HP HQ.
      rewrite miller_fold_model_unfold, (step_model_fold_eq Hinv).
      exact (BLS12_PairingFeval.bedrock2_miller_loop_eq PrimeField.M_pos
               Hadd Hsub Hmul Hmulv Hself Hcross P Q HP HQ).
    Qed.

End BLS12_MillerLoopFunctional.
