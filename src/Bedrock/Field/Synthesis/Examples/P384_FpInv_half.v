(** * P384 Fp inversion via δ₀ = 1/2 Bernstein–Yang divsteps.

    Mirrors [Fe25519_FpInv.v] for the P384 base-field prime.
    Iteration count [N = 885] (paper §3.4 / Theorem 1 lower bound; this
    value matches the Rust runtime at
    [curve25519-jasmin-rs/src/safegcd_p384.rs]).

    The algorithm and proof structure are identical to [Fe25519_FpInv.v];
    only the prime, iteration count, and precomp value change. *)

From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Znumtheory.
(** Reuse all parametric divstep machinery from Fe25519_FpInv (iter,
    invariants, dfg agreement, etc — all take the modulus as a parameter). *)
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.

Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* P384 prime and machine parameters                              *)
(* ================================================================== *)

Definition p384_p : Z := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff.

(** Number of divsteps for [p384_p] using δ₀ = 1/2.  Matches the
    iteration count used at runtime in the Rust safegcd port. *)
Definition p384_divstep_iters_half : Z := 885.

(* ================================================================== *)
(* Full Fp inversion specification                                     *)
(* ================================================================== *)

Section FpInv_p384.
  Let p := p384_p.

  (** [precomp = ((p+1)/2)^N mod p].  As [(p+1)/2 = 2^{-1} mod p] (since
      [p] is odd), this equals [2^{-N} mod p] and cancels the [2^N]
      factor from the Bernstein–Yang loop invariant. *)
  Definition p384_precomp_val_half : Z :=
    Eval vm_compute in
      (let half := (p384_p + 1) / 2 in
       Fe25519_FpInv.pow_mod_pos half (Z.to_pos p384_divstep_iters_half) p384_p).

  (** The full inversion. *)
  Definition p384_fp_inv_spec_half (x : Z) : Z :=
    let '(d, f, g, v, r) :=
      Fe25519_FpInv.iter_divstep_spec_half p (Z.to_nat p384_divstep_iters_half) (-1) p x 0 1 in
    let v_corrected := if (f <? 0) then (p - v) mod p else v mod p in
    (v_corrected * p384_precomp_val_half) mod p.

  (* ================================================================ *)
  (* Convergence axiom (δ₀ = 1/2; EUROCRYPT 2026, Theorem 1)            *)
  (* Discharged in [P384_FpInv_half_proved.v] via the safegcd       *)
  (* convex-hull cert + bridge.                                         *)
  (* ================================================================ *)

  Axiom p384_by_convergence_dfg_half : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    let '(_, f_N, g_N) :=
      Fe25519_FpInv.iter_divstep_dfg_half (Z.to_nat p384_divstep_iters_half) (-1) p x in
    g_N = 0 /\ (f_N = 1 \/ f_N = -1).

  (* ================================================================ *)
  (* Auxiliary computational lemmas                                    *)
  (* ================================================================ *)

  Lemma p384_p_pos : 0 < p.
  Proof. subst p. unfold p384_p. vm_compute. reflexivity. Qed.

  Lemma p384_p_odd : Z.odd p = true.
  Proof. subst p. unfold p384_p. vm_compute. reflexivity. Qed.

  (** [precomp * 2^N ≡ 1 (mod p)]. *)
  Lemma p384_precomp_times_pow2_half :
    (p384_precomp_val_half * 2 ^ p384_divstep_iters_half) mod p = 1.
  Proof.
    subst p. unfold p384_precomp_val_half, p384_divstep_iters_half, p384_p.
    vm_compute. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Main correctness theorem                                          *)
  (* ================================================================ *)

  Lemma p384_fp_inv_correct_ax_half : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (p384_fp_inv_spec_half x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd.
    unfold p384_fp_inv_spec_half.
    destruct (Fe25519_FpInv.iter_divstep_spec_half p (Z.to_nat p384_divstep_iters_half) (-1) p x 0 1)
      as [[[[d_N f_N] g_N] v_N] r_N] eqn:Hiter.
    (* (A) Loop invariant *)
    pose proof (Fe25519_FpInv.iter_invariant_half p (Z.to_nat p384_divstep_iters_half) (-1) p x 0 1 x
                  p384_p_pos p384_p_odd) as Hinv.
    assert (H0 : (0 * x - p) mod p = 0)
      by (replace (0 * x - p) with ((-1) * p) by ring; rewrite Z_mod_mult; reflexivity).
    assert (H1 : (1 * x - x) mod p = 0)
      by (replace (1 * x - x) with 0 by ring; reflexivity).
    specialize (Hinv H0 H1). rewrite Hiter in Hinv.
    destruct Hinv as [Hv_inv Hr_inv].
    (* (B) Convergence *)
    pose proof (p384_by_convergence_dfg_half x Hx Hgcd) as Hconv.
    pose proof (Fe25519_FpInv.iter_dfg_agree_half (Z.to_nat p384_divstep_iters_half) p (-1) p x 0 1) as Hagree.
    rewrite Hiter in Hagree.
    destruct (Fe25519_FpInv.iter_divstep_dfg_half (Z.to_nat p384_divstep_iters_half) (-1) p x)
      as [[d2 f2] g2] eqn:Hdfg.
    destruct Hagree as [_ [Hf_eq Hg_eq]].
    subst f_N g_N. destruct Hconv as [Hg0 Hf_cases]. subst g2.
    clear Hr_inv H0 H1 Hiter Hdfg d_N d2 r_N.
    destruct Hf_cases as [Hf1 | Hfm1]; subst f2.
    - replace (1 <? 0) with false by reflexivity.
      rewrite Z.mul_1_r in Hv_inv.
      rewrite Zmult_mod_idemp_l.
      replace (v_N mod p * p384_precomp_val_half * x)
        with (v_N mod p * (p384_precomp_val_half * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace (v_N * (p384_precomp_val_half * x))
        with (p384_precomp_val_half * (v_N * x)) by ring.
      assert (Hmod : (v_N * x) mod p = (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half)) mod p). {
        assert (Hp : p <> 0) by (pose proof p384_p_pos; lia).
        apply Z.mod_divide in Hv_inv; [|exact Hp].
        destruct Hv_inv as [k Hk].
        assert (v_N * x = 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half) + k * p) by lia.
        rewrite H.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        reflexivity.
      }
      rewrite <- Zmult_mod_idemp_r, Hmod, Zmult_mod_idemp_r.
      rewrite Z2Nat.id by (unfold p384_divstep_iters_half; vm_compute; discriminate).
      exact p384_precomp_times_pow2_half.
    - replace (-1 <? 0) with true by reflexivity.
      replace (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half) * -1)
        with (- (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half))) in Hv_inv by ring.
      replace (v_N * x - - 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half))
        with (v_N * x + 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters_half)) in Hv_inv by ring.
      set (iters := Z.of_nat (Z.to_nat p384_divstep_iters_half)) in *.
      assert (HpN : p <> 0) by (pose proof p384_p_pos; lia).
      assert (Hmod_neg : ((p - v_N) * x) mod p = (2 ^ iters) mod p). {
        replace ((p - v_N) * x) with (x * p + (-(v_N * x + 2 ^ iters) + 2 ^ iters)) by ring.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod by lia.
        rewrite Zplus_mod, (Z.mod_opp_l_z _ _ HpN Hv_inv).
        simpl. rewrite Z.mod_mod by lia. reflexivity.
      }
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) mod p * p384_precomp_val_half * x)
        with ((p - v_N) mod p * (p384_precomp_val_half * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) * (p384_precomp_val_half * x))
        with (p384_precomp_val_half * ((p - v_N) * x)) by ring.
      rewrite <- Zmult_mod_idemp_r, Hmod_neg, Zmult_mod_idemp_r.
      subst iters.
      rewrite Z2Nat.id by (unfold p384_divstep_iters_half; vm_compute; discriminate).
      exact p384_precomp_times_pow2_half.
  Qed.

  Theorem p384_invert_correct_half : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (p384_fp_inv_spec_half x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd. apply p384_fp_inv_correct_ax_half; auto.
  Qed.

End FpInv_p384.
