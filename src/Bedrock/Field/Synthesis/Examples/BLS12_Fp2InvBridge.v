(** * Fp2 inverse bridge for beta = -1.

    [QuadraticExtensions.invp2 p beta] (the Finv of the bedrock2 Fp2 instance
    [ext_Fp2_params beta]) equals [Pairing.fp2_inv p] whenever [beta = -1] and
    [-1] is not a square in [F p] (p prime, p = 3 mod 4).  Both functions give
    [(0, 0)] at [0] (F.inv 0 = 0), so the equation holds for every argument.

    [bls12_381_invp2_eq_fp2_inv] specialises it to the BLS12-381 prime.
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Algebra.Field.
Require Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Theory.BLS12Pairing.Pairing.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.

Local Open Scope Z_scope.

Section Fp2InvBridge.
  Variable p : positive.
  Hypothesis Hprime : Znumtheory.prime (Z.pos p).
  Variable beta : F p.
  Hypothesis Hbeta : beta = F.opp F.one.
  Hypothesis Hqnr : ~ (exists x : F p, F.mul x x = beta).

  Let ftfst := @Field.field_theory_for_stdlib_tactic
    (F p) (@eq (F p)) (@F.zero p) (@F.one p) (@F.opp p) (@F.add p)
    (@F.mul p) (@F.sub p) (@F.inv p) (@F.div p) (@F.field_modulo p Hprime).
  Add Field Fp_field_inv_bridge : ftfst.

  Local Lemma sq_zero (a : F p) : F.mul a a = F.zero -> a = F.zero.
  Proof.
    intros Ha.
    destruct (F.eq_dec a F.zero) as [|n]; [assumption|].
    exfalso. apply n.
    transitivity (F.mul (F.inv a) (F.mul a a)).
    - field. exact n.
    - rewrite Ha. ring.
  Qed.

  Local Lemma norm_nonzero (a0 a1 : F p) :
    a0 <> F.zero -> F.add (F.mul a0 a0) (F.mul a1 a1) <> F.zero.
  Proof.
    intros Ha0 Hn.
    destruct (F.eq_dec a1 F.zero) as [Ha1|Ha1].
    - subst a1. apply Ha0, sq_zero.
      transitivity (F.add (F.mul a0 a0) (F.mul F.zero F.zero)); [ring | exact Hn].
    - apply Hqnr. exists (F.mul a0 (F.inv a1)). rewrite Hbeta.
      transitivity (F.sub (F.mul (F.add (F.mul a0 a0) (F.mul a1 a1))
                                 (F.mul (F.inv a1) (F.inv a1))) F.one).
      + field. exact Ha1.
      + rewrite Hn. ring.
  Qed.

  Lemma invp2_eq_pairing_fp2_inv : forall a : F p * F p,
    QuadraticExtensions.invp2 p beta a = Pairing.fp2_inv p a.
  Proof.
    assert (Hm1 : F.opp (@F.one p) <> F.zero).
    { intros H. apply (F_1_neq_0 ftfst).
      transitivity (F.opp (F.opp (@F.one p))); [ring | rewrite H; ring]. }
    intros [a0 a1].
    cbv [QuadraticExtensions.invp2 Pairing.fp2_inv fst snd].
    destruct (F.eq_dec a0 F.zero) as [Ha0|Ha0].
    - (* a0 = 0: invp2 takes its first branch *)
      subst a0. rewrite F.to_Z_0, Z.eqb_refl, Hbeta.
      destruct (F.eq_dec a1 F.zero) as [Ha1|Ha1].
      + (* a = 0: both are (0, 0) since F.inv 0 = 0 *)
        subst a1.
        replace (F.mul F.zero (F.opp F.one)) with (@F.zero p) by ring.
        replace (F.add (F.mul F.zero F.zero) (F.mul F.zero F.zero)) with (@F.zero p) by ring.
        rewrite F.inv_0.
        change (F.of_Z p 0) with (@F.zero p).
        f_equal; ring.
      + replace (F.add (F.mul F.zero F.zero) (F.mul a1 a1)) with (F.mul a1 a1) by ring.
        f_equal.
        field. split; [exact Ha1 | exact Hm1].
    - (* a0 <> 0: the norm a0^2 + a1^2 is nonzero *)
      assert (Hz : (F.to_Z a0 =? 0) = false).
      { apply Z.eqb_neq. intros Hz. apply Ha0.
        apply F.eq_to_Z_iff. rewrite F.to_Z_0. exact Hz. }
      rewrite Hz, Hbeta.
      pose proof (norm_nonzero a0 a1 Ha0) as Hn.
      assert (Hd : F.sub a0 (F.div (F.mul (F.mul a1 a1) (F.opp F.one)) a0) <> F.zero).
      { intros Hd. apply Hn.
        transitivity (F.mul a0 (F.sub a0 (F.div (F.mul (F.mul a1 a1) (F.opp F.one)) a0))).
        - field. exact Ha0.
        - rewrite Hd. ring. }
      f_equal; field; repeat split; try assumption.
  Qed.
End Fp2InvBridge.

(** ** BLS12-381 *)

Definition bls12_381_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

Lemma bls12_381_beta_eq :
  F.of_Z bls12_381_M_pos (-1) = F.opp F.one.
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Lemma bls12_381_beta_qnr :
  ~ (exists x : F bls12_381_M_pos, F.mul x x = F.of_Z bls12_381_M_pos (-1)).
Proof.
  change (F.of_Z bls12_381_M_pos (-1))
    with (QuadraticExtensionsFiat.Quad_non_res bls12_381_M_pos).
  exact (QuadraticExtensionsFiat.beta_is_non_res bls12_381_M_pos
           prime_bls12_381 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
Qed.

Theorem bls12_381_invp2_eq_fp2_inv : forall a : F bls12_381_M_pos * F bls12_381_M_pos,
  QuadraticExtensions.invp2 bls12_381_M_pos (F.of_Z bls12_381_M_pos (-1)) a =
  Pairing.fp2_inv bls12_381_M_pos a.
Proof.
  apply invp2_eq_pairing_fp2_inv.
  - exact prime_bls12_381.
  - exact bls12_381_beta_eq.
  - exact bls12_381_beta_qnr.
Qed.
