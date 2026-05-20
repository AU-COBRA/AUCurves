(** * Discharge of [Secp256k1_FpInv_half.secp256k1_by_convergence_dfg_half] axiom.

    Mirror of [Fe25519_FpInv_proved.v] for Secp256k1.

    Composes:
    - [divsteps_secp256k1_half.secp256k1_half_certificate] — the convex-hull
      cert at N=590, axiomatized for parity with the BLS12-381 δ₀=1 cert
      in [divsteps_bls12.v].
    - [divsteps_bridge_half.convergence_monotone_half] — the O'Connor →
      BYInv convergence bridge for δ₀=1/2.

    Result: [secp256k1_by_convergence_dfg_half_proved] has the EXACT
    statement of [Secp256k1_FpInv_half.secp256k1_by_convergence_dfg_half];
    [Print Assumptions] of it reports a single axiom,
    [secp256k1_half_certificate] — same trust footing as Fe25519_FpInv_proved. *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def_half.
Require Import divsteps_base_half.
Require Import divsteps_theory_half.
Require Import divsteps_bridge_half.
Require Import divsteps_secp256k1_half.
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.
Require Import Bedrock.Field.Synthesis.Examples.Secp256k1_FpInv_half.

Local Open Scope Z_scope.

(** Bridge's [divstep_spec_half] and Fe25519_FpInv's are definitionally
    equal (identical bodies). *)
Lemma secp256k1_iter_divstep_dfg_half_eq : forall n d f g,
  divsteps_bridge_half.iter_divstep_dfg_half n d f g =
  Fe25519_FpInv.iter_divstep_dfg_half n d f g.
Proof. reflexivity. Qed.

Lemma secp256k1_p_odd_prop : Z.Odd Secp256k1_FpInv_half.secp256k1_p.
Proof.
  exists ((Secp256k1_FpInv_half.secp256k1_p - 1) / 2).
  unfold Secp256k1_FpInv_half.secp256k1_p. vm_compute. reflexivity.
Qed.

Lemma secp256k1_p_bound_self : (Secp256k1_FpInv_half.secp256k1_p <= Secp256k1_FpInv_half.secp256k1_p)%Z.
Proof. lia. Qed.

(** Discharges Secp256k1_FpInv_half's convergence axiom for any input
    [x ∈ (0, secp256k1_p)] with [gcd(x, secp256k1_p) = 1]. *)
Theorem secp256k1_by_convergence_dfg_half_proved : forall x,
  0 < x < Secp256k1_FpInv_half.secp256k1_p ->
  Z.gcd x Secp256k1_FpInv_half.secp256k1_p = 1 ->
  let '(_, f_N, g_N) :=
    Fe25519_FpInv.iter_divstep_dfg_half
      (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half) (-1)
      Secp256k1_FpInv_half.secp256k1_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  rewrite <- secp256k1_iter_divstep_dfg_half_eq.
  assert (HN : (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half
                = N.to_nat 590)%nat).
  { unfold Secp256k1_FpInv_half.secp256k1_divstep_iters_half. vm_compute. reflexivity. }
  rewrite HN.
  apply convergence_monotone_half with (N0 := 590%N) (M := Secp256k1_FpInv_half.secp256k1_p).
  - exact secp256k1_p_odd_prop.
  - exact secp256k1_p_bound_self.
  - lia.
  - apply Zgcd_1_rel_prime.
    rewrite Z.gcd_comm.
    exact Hgcd.
  - exact divsteps_secp256k1_half.secp256k1_half_certificate.
  - lia.
Qed.

(** [Print Assumptions secp256k1_by_convergence_dfg_half_proved]: should
    report exactly one axiom, [secp256k1_half_certificate]. *)

(** End-to-end inversion correctness, with the per-file convergence
    axiom DISCHARGED via [secp256k1_by_convergence_dfg_half_proved].
    The proof body mirrors Secp256k1_FpInv_half.secp256k1_fp_inv_correct_ax_half
    but substitutes the proved convergence theorem for the axiom.

    [Print Assumptions secp256k1_fp_inv_correct_half_proved]: exactly one
    axiom, [secp256k1_half_certificate] (= same trust footing as the
    safegcd convex-hull cert). *)
Theorem secp256k1_fp_inv_correct_half_proved : forall x,
  0 < x < Secp256k1_FpInv_half.secp256k1_p ->
  Z.gcd x Secp256k1_FpInv_half.secp256k1_p = 1 ->
  (Secp256k1_FpInv_half.secp256k1_fp_inv_spec_half x * x)
    mod Secp256k1_FpInv_half.secp256k1_p = 1.
Proof.
  intros x Hx Hgcd.
  unfold Secp256k1_FpInv_half.secp256k1_fp_inv_spec_half.
  pose proof (secp256k1_by_convergence_dfg_half_proved x Hx Hgcd) as Hconv.
  destruct (Fe25519_FpInv.iter_divstep_spec_half
              Secp256k1_FpInv_half.secp256k1_p
              (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)
              (-1) Secp256k1_FpInv_half.secp256k1_p x 0 1)
    as [[[[d_N f_N] g_N] v_N] r_N] eqn:Hiter.
  set (p := Secp256k1_FpInv_half.secp256k1_p) in *.
  pose proof (Fe25519_FpInv.iter_invariant_half p
                (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)
                (-1) p x 0 1 x
                Secp256k1_FpInv_half.secp256k1_p_pos
                Secp256k1_FpInv_half.secp256k1_p_odd) as Hinv.
  assert (H0 : (0 * x - p) mod p = 0)
    by (replace (0 * x - p) with ((-1) * p) by ring; rewrite Z_mod_mult; reflexivity).
  assert (H1 : (1 * x - x) mod p = 0)
    by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv H0 H1). rewrite Hiter in Hinv.
  destruct Hinv as [Hv_inv Hr_inv].
  pose proof (Fe25519_FpInv.iter_dfg_agree_half
                (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)
                p (-1) p x 0 1) as Hagree.
  rewrite Hiter in Hagree.
  destruct (Fe25519_FpInv.iter_divstep_dfg_half
              (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)
              (-1) p x)
    as [[d2 f2] g2] eqn:Hdfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]].
  subst f_N g_N. destruct Hconv as [Hg0 Hf_cases]. subst g2.
  clear Hr_inv H0 H1 Hiter Hdfg d_N d2 r_N.
  destruct Hf_cases as [Hf1 | Hfm1]; subst f2.
  - replace (1 <? 0) with false by reflexivity.
    rewrite Z.mul_1_r in Hv_inv.
    rewrite Zmult_mod_idemp_l.
    replace (v_N mod p * Secp256k1_FpInv_half.secp256k1_precomp_val_half * x)
      with (v_N mod p * (Secp256k1_FpInv_half.secp256k1_precomp_val_half * x)) by ring.
    rewrite Zmult_mod_idemp_l.
    replace (v_N * (Secp256k1_FpInv_half.secp256k1_precomp_val_half * x))
      with (Secp256k1_FpInv_half.secp256k1_precomp_val_half * (v_N * x)) by ring.
    assert (Hmod : (v_N * x) mod p =
                   (2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)) mod p). {
      assert (Hp : p <> 0) by (pose proof Secp256k1_FpInv_half.secp256k1_p_pos; lia).
      apply Z.mod_divide in Hv_inv; [|exact Hp].
      destruct Hv_inv as [k Hk].
      assert (v_N * x = 2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half) + k * p) by lia.
      rewrite H.
      rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
      reflexivity.
    }
    rewrite <- Zmult_mod_idemp_r, Hmod, Zmult_mod_idemp_r.
    rewrite Z2Nat.id by (unfold Secp256k1_FpInv_half.secp256k1_divstep_iters_half; vm_compute; discriminate).
    exact Secp256k1_FpInv_half.secp256k1_precomp_times_pow2_half.
  - replace (-1 <? 0) with true by reflexivity.
    replace (2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half) * -1)
      with (- (2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half))) in Hv_inv by ring.
    replace (v_N * x - - 2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half))
      with (v_N * x + 2 ^ Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)) in Hv_inv by ring.
    set (iters := Z.of_nat (Z.to_nat Secp256k1_FpInv_half.secp256k1_divstep_iters_half)) in *.
    assert (HpN : p <> 0) by (pose proof Secp256k1_FpInv_half.secp256k1_p_pos; lia).
    assert (Hmod_neg : ((p - v_N) * x) mod p = (2 ^ iters) mod p). {
      replace ((p - v_N) * x) with (x * p + (-(v_N * x + 2 ^ iters) + 2 ^ iters)) by ring.
      rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod by lia.
      rewrite Zplus_mod, (Z.mod_opp_l_z _ _ HpN Hv_inv).
      simpl. rewrite Z.mod_mod by lia. reflexivity.
    }
    rewrite Zmult_mod_idemp_l.
    replace ((p - v_N) mod p * Secp256k1_FpInv_half.secp256k1_precomp_val_half * x)
      with ((p - v_N) mod p * (Secp256k1_FpInv_half.secp256k1_precomp_val_half * x)) by ring.
    rewrite Zmult_mod_idemp_l.
    replace ((p - v_N) * (Secp256k1_FpInv_half.secp256k1_precomp_val_half * x))
      with (Secp256k1_FpInv_half.secp256k1_precomp_val_half * ((p - v_N) * x)) by ring.
    rewrite <- Zmult_mod_idemp_r, Hmod_neg, Zmult_mod_idemp_r.
    subst iters.
    rewrite Z2Nat.id by (unfold Secp256k1_FpInv_half.secp256k1_divstep_iters_half; vm_compute; discriminate).
    exact Secp256k1_FpInv_half.secp256k1_precomp_times_pow2_half.
Qed.
