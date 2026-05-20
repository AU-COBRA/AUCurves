(** * P-384 (secp384r1) Fp inversion via Bernstein-Yang divstep algorithm.

    Mirrors [P256_FpInv.v] for the NIST P-384 base field.

    P-384 base prime:
      p = 2^384 - 2^128 - 2^96 + 2^32 - 1
      Z.log2 p + 1 = 384
      iterations = (49 * 384 + 57) / 17 = 18873 / 17 = 1110

    Word-by-word Montgomery layout: 6 limbs of 64 bits (saturated: 7 limbs).
*)

From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Znumtheory.
Require Import Crypto.Arithmetic.BYInv.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Bedrock.Field.Synthesis.Examples.p384_prime.

Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* P-384 prime and its parameters                                      *)
(* ================================================================== *)

Definition p384_p : Z :=
  Eval vm_compute in p384_modulus.

Definition machine_wordsize : Z := 64.

(** Number of 64-bit limbs for Montgomery representation (6 limbs = 384 bits). *)
Definition n : nat := 6.

(** Saturated representation uses n+1 = 7 limbs. *)
Definition sat_limbs : nat := 7.

Definition p384_mbits : Z := Z.log2 p384_p + 1.

Lemma p384_mbits_val : p384_mbits = 384.
Proof. vm_compute. reflexivity. Qed.

Lemma p384_mbits_ge_46 : 46 <= p384_mbits.
Proof. vm_compute. discriminate. Qed.

(* ================================================================== *)
(* Bernstein-Yang iteration count                                      *)
(* ================================================================== *)

Definition p384_divstep_iters : Z :=
  Eval vm_compute in ((49 * p384_mbits + 57) / 17).

Lemma p384_divstep_iters_val : p384_divstep_iters = 1110.
Proof. vm_compute. reflexivity. Qed.

Lemma p384_divstep_iters_eq_precomp_exp :
  p384_divstep_iters =
  (if Decidable.dec (p384_mbits < 46) then (49 * p384_mbits + 80) / 17
   else (49 * p384_mbits + 57) / 17).
Proof.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Iterated divstep specification                                      *)
(* ================================================================== *)

Fixpoint iter_divstep_spec (m : Z) (nsteps : nat)
    (d : Z) (f g v r : Z) : Z * Z * Z * Z * Z :=
  match nsteps with
  | O => (d, f, g, v, r)
  | S k =>
    let '(d', f', g', v', r') := divstep_spec_full m d f g v r in
    iter_divstep_spec m k d' f' g' v' r'
  end.

Fixpoint iter_divstep_dfg (nsteps : nat) (d f g : Z) : Z * Z * Z :=
  match nsteps with
  | O => (d, f, g)
  | S k =>
    let '(d', f', g') := divstep_spec d f g in
    iter_divstep_dfg k d' f' g'
  end.

(* ================================================================== *)
(* General divstep lemmas                                              *)
(* ================================================================== *)

Lemma iter_dfg_agree : forall nsteps m d f g v r,
  let '(d1, f1, g1, _, _) := iter_divstep_spec m nsteps d f g v r in
  let '(d2, f2, g2) := iter_divstep_dfg nsteps d f g in
  d1 = d2 /\ f1 = f2 /\ g1 = g2.
Proof.
  induction nsteps as [|k IH]; intros; simpl.
  - auto.
  - unfold divstep_spec_full, divstep_spec.
    destruct ((0 <? d) && Z.odd g) eqn:E;
    [ specialize (IH m (1 - d) g ((g - f) / 2) (2 * r mod m) ((r - v) mod m))
    | specialize (IH m (1 + d) f ((g + g mod 2 * f) / 2) (2 * v mod m) ((r + g mod 2 * v) mod m)) ];
    destruct (iter_divstep_spec m k _ _ _ _ _) as [[[[? ?] ?] ?] ?];
    destruct (iter_divstep_dfg k _ _ _) as [[? ?] ?];
    exact IH.
Qed.

Lemma divstep_spec_f_odd : forall d f g,
  Z.odd f = true ->
  let '(d', f', _) := divstep_spec d f g in
  Z.odd f' = true.
Proof.
  intros d f g Hf. unfold divstep_spec.
  destruct ((0 <? d) && Z.odd g) eqn:E.
  - apply andb_prop in E. tauto.
  - exact Hf.
Qed.

Lemma iter_divstep_dfg_f_odd : forall k d f g,
  Z.odd f = true ->
  let '(_, f', _) := iter_divstep_dfg k d f g in
  Z.odd f' = true.
Proof.
  induction k as [|k IH]; intros d f g Hf; simpl.
  - exact Hf.
  - pose proof (divstep_spec_f_odd d f g Hf) as Hstep.
    destruct (divstep_spec d f g) as [[d' f'] g'].
    exact (IH d' f' g' Hstep).
Qed.

Lemma divstep_step_invariant : forall m d f g v r x A,
  0 < m ->
  Z.odd f = true ->
  (v * x - A * f) mod m = 0 ->
  (r * x - A * g) mod m = 0 ->
  let '(_, f', g', v', r') := divstep_spec_full m d f g v r in
  (v' * x - (2 * A) * f') mod m = 0 /\
  (r' * x - (2 * A) * g') mod m = 0.
Proof.
  intros m d f g v r x A Hm Hfodd Hv Hr.
  unfold divstep_spec_full.
  destruct ((0 <? d) && Z.odd g) eqn:E.
  - apply andb_prop in E. destruct E as [Hd Hgodd].
    split.
    + rewrite Zminus_mod, (Zmult_mod_idemp_l (2 * r) x m), <- Zminus_mod.
      replace ((2 * r) * x - 2 * A * g) with (2 * (r * x - A * g)) by ring.
      rewrite <- (Zmult_mod_idemp_r (r * x - A * g) 2 m), Hr. reflexivity.
    + assert (Heven : (g - f) mod 2 = 0).
      { rewrite Zminus_mod, (Zmod_odd g), Hgodd, (Zmod_odd f), Hfodd. reflexivity. }
      rewrite Zminus_mod, (Zmult_mod_idemp_l (r - v) x m), <- Zminus_mod.
      replace ((r - v) * x - 2 * A * ((g - f) / 2))
        with ((r * x - A * g) - (v * x - A * f)).
      2:{ assert (2 * ((g - f) / 2) = g - f) by
            (rewrite (Z.div_mod (g - f) 2) at 2 by lia; lia). nia. }
      rewrite Zminus_mod, Hr, Hv. reflexivity.
  - split.
    + rewrite Zminus_mod, (Zmult_mod_idemp_l (2 * v) x m), <- Zminus_mod.
      replace ((2 * v) * x - 2 * A * f) with (2 * (v * x - A * f)) by ring.
      rewrite <- (Zmult_mod_idemp_r (v * x - A * f) 2 m), Hv. reflexivity.
    + assert (Heven : (g + g mod 2 * f) mod 2 = 0).
      { assert (g mod 2 = 0 \/ g mod 2 = 1) as [Hg | Hg]
          by (pose proof (Z.mod_pos_bound g 2 ltac:(lia)); lia).
        - rewrite Hg, Z.mul_0_l, Z.add_0_r. exact Hg.
        - rewrite Hg, Z.mul_1_l.
          rewrite Zplus_mod, Hg, (Zmod_odd f), Hfodd. reflexivity. }
      rewrite Zminus_mod, (Zmult_mod_idemp_l (r + g mod 2 * v) x m), <- Zminus_mod.
      replace ((r + g mod 2 * v) * x - 2 * A * ((g + g mod 2 * f) / 2))
        with ((r * x - A * g) + g mod 2 * (v * x - A * f)).
      2:{ assert (2 * ((g + g mod 2 * f) / 2) = g + g mod 2 * f) by
            (rewrite (Z.div_mod (g + g mod 2 * f) 2) at 2 by lia; lia). nia. }
      rewrite Zplus_mod.
      rewrite <- (Zmult_mod_idemp_r (v * x - A * f) (g mod 2) m), Hv.
      rewrite Z.mul_0_r, Z.add_0_r.
      rewrite Z.mod_mod by lia.
      exact Hr.
Qed.

Lemma iter_invariant_gen : forall m k d f g v r x A,
  0 < m ->
  Z.odd f = true ->
  (v * x - A * f) mod m = 0 ->
  (r * x - A * g) mod m = 0 ->
  let '(d', f', g', v', r') := iter_divstep_spec m k d f g v r in
  (v' * x - (2 ^ Z.of_nat k * A) * f') mod m = 0 /\
  (r' * x - (2 ^ Z.of_nat k * A) * g') mod m = 0.
Proof.
  intros m.
  induction k as [|k IH]; intros d f g v r x A Hm Hfodd Hv Hr;
    simpl iter_divstep_spec.
  - rewrite Z.pow_0_r, Z.mul_1_l. auto.
  - pose proof (divstep_step_invariant m d f g v r x A Hm Hfodd Hv Hr) as Hstep.
    unfold divstep_spec_full in Hstep |- *.
    destruct ((0 <? d) && Z.odd g) eqn:E.
    + destruct Hstep as [Hv' Hr'].
      assert (Hfodd' : Z.odd g = true).
      { apply andb_prop in E. tauto. }
      specialize (IH (1 - d) g ((g - f) / 2) (2 * r mod m) ((r - v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd' Hv' Hr').
      destruct (iter_divstep_spec m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
    + destruct Hstep as [Hv' Hr'].
      specialize (IH (1 + d) f ((g + g mod 2 * f) / 2) (2 * v mod m) ((r + g mod 2 * v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd Hv' Hr').
      destruct (iter_divstep_spec m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma iter_invariant : forall m k d f g v r x,
  0 < m ->
  Z.odd f = true ->
  (v * x - f) mod m = 0 ->
  (r * x - g) mod m = 0 ->
  let '(_, f', g', v', r') := iter_divstep_spec m k d f g v r in
  (v' * x - 2 ^ Z.of_nat k * f') mod m = 0 /\
  (r' * x - 2 ^ Z.of_nat k * g') mod m = 0.
Proof.
  intros m k d f g v r x Hm Hfodd Hv Hr.
  pose proof (iter_invariant_gen m k d f g v r x 1 Hm Hfodd) as H.
  rewrite !Z.mul_1_l in H.
  specialize (H Hv Hr).
  destruct (iter_divstep_spec m k d f g v r) as [[[[d' f'] g'] v'] r'].
  rewrite !Z.mul_1_r in H.
  exact H.
Qed.

(* ================================================================== *)
(* Full Fp inversion specification                                     *)
(* ================================================================== *)

Section FpInv.
  Let p := p384_p.

  (** Precomputation: ((p+1)/2)^N mod p with N = 1110.
      Computed externally via:
        python3 -c "p=2**384-2**128-2**96+2**32-1; print(hex(pow((p+1)//2, 1110, p)))"
  *)
  Definition precomp_val : Z :=
    0xfe32d7fffe7f43ffff3edbfffff1780000573c00006bdc00004cc400001e03ff01c647ff0335dc00022a0400fef413ff.

  Definition fp_inv_spec (x : Z) : Z :=
    let '(d, f, g, v, r) :=
      iter_divstep_spec p (Z.to_nat p384_divstep_iters) 1 p x 0 1 in
    let v_corrected := if (f <? 0) then (p - v) mod p else v mod p in
    (v_corrected * precomp_val) mod p.

  Axiom by_convergence_dfg_p384 : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    let '(_, f_N, g_N) :=
      iter_divstep_dfg (Z.to_nat p384_divstep_iters) 1 p x in
    g_N = 0 /\ (f_N = 1 \/ f_N = -1).

  Lemma p_pos : 0 < p.
  Proof. subst p. vm_compute. reflexivity. Qed.

  Lemma p_odd : Z.odd p = true.
  Proof. subst p. vm_compute. reflexivity. Qed.

  Lemma precomp_times_pow2 :
    (precomp_val * 2 ^ p384_divstep_iters) mod p = 1.
  Proof.
    subst p. unfold precomp_val, p384_divstep_iters, p384_p.
    vm_compute. reflexivity.
  Qed.

  Lemma p384_coprime : forall x, 0 < x < p -> Z.gcd x p = 1.
  Proof.
    intros x Hx.
    apply Zgcd_1_rel_prime.
    apply rel_prime_sym.
    apply prime_rel_prime.
    - subst p. unfold p384_p. exact prime_p384.
    - intros [k Hk]. subst x.
      pose proof p_pos as Hp.
      destruct Hx as [Hx1 Hx2].
      assert (k <> 0) by (intro; subst; lia).
      assert (1 <= Z.abs k) by lia.
      assert (Z.abs (k * p) >= p) by (rewrite Z.abs_mul; nia).
      lia.
  Qed.

  Lemma fp_inv_correct_ax : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd.
    unfold fp_inv_spec.
    destruct (iter_divstep_spec p (Z.to_nat p384_divstep_iters) 1 p x 0 1)
      as [[[[d_N f_N] g_N] v_N] r_N] eqn:Hiter.
    pose proof (iter_invariant p (Z.to_nat p384_divstep_iters) 1 p x 0 1 x
                  p_pos p_odd) as Hinv.
    assert (H0 : (0 * x - p) mod p = 0)
      by (replace (0 * x - p) with ((-1) * p) by ring; rewrite Z_mod_mult; reflexivity).
    assert (H1 : (1 * x - x) mod p = 0)
      by (replace (1 * x - x) with 0 by ring; reflexivity).
    specialize (Hinv H0 H1). rewrite Hiter in Hinv.
    destruct Hinv as [Hv_inv Hr_inv].
    pose proof (by_convergence_dfg_p384 x Hx Hgcd) as Hconv.
    pose proof (iter_dfg_agree (Z.to_nat p384_divstep_iters) p 1 p x 0 1) as Hagree.
    rewrite Hiter in Hagree.
    destruct (iter_divstep_dfg (Z.to_nat p384_divstep_iters) 1 p x)
      as [[d2 f2] g2] eqn:Hdfg.
    destruct Hagree as [_ [Hf_eq Hg_eq]].
    subst f_N g_N. destruct Hconv as [Hg0 Hf_cases]. subst g2.
    clear Hr_inv H0 H1 Hiter Hdfg d_N d2 r_N.
    destruct Hf_cases as [Hf1 | Hfm1]; subst f2.
    - replace (1 <? 0) with false by reflexivity.
      rewrite Z.mul_1_r in Hv_inv.
      rewrite Zmult_mod_idemp_l.
      replace (v_N mod p * precomp_val * x)
        with (v_N mod p * (precomp_val * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace (v_N * (precomp_val * x))
        with (precomp_val * (v_N * x)) by ring.
      assert (Hmod : (v_N * x) mod p = (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters)) mod p). {
        assert (Hp : p <> 0) by (pose proof p_pos; lia).
        apply Z.mod_divide in Hv_inv; [|exact Hp].
        destruct Hv_inv as [k Hk].
        assert (v_N * x = 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters) + k * p) by lia.
        rewrite H.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        reflexivity.
      }
      rewrite <- Zmult_mod_idemp_r, Hmod, Zmult_mod_idemp_r.
      rewrite Z2Nat.id by (unfold p384_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
    - replace (-1 <? 0) with true by reflexivity.
      replace (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters) * -1)
        with (- (2 ^ Z.of_nat (Z.to_nat p384_divstep_iters))) in Hv_inv by ring.
      replace (v_N * x - - 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters))
        with (v_N * x + 2 ^ Z.of_nat (Z.to_nat p384_divstep_iters)) in Hv_inv by ring.
      set (iters := Z.of_nat (Z.to_nat p384_divstep_iters)) in *.
      assert (HpN : p <> 0) by (pose proof p_pos; lia).
      assert (Hmod_neg : ((p - v_N) * x) mod p = (2 ^ iters) mod p). {
        replace ((p - v_N) * x) with (x * p + (-(v_N * x + 2 ^ iters) + 2 ^ iters)) by ring.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod by lia.
        rewrite Zplus_mod, (Z.mod_opp_l_z _ _ HpN Hv_inv).
        simpl. rewrite Z.mod_mod by lia. reflexivity.
      }
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) mod p * precomp_val * x)
        with ((p - v_N) mod p * (precomp_val * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) * (precomp_val * x))
        with (precomp_val * ((p - v_N) * x)) by ring.
      rewrite <- Zmult_mod_idemp_r, Hmod_neg, Zmult_mod_idemp_r.
      subst iters.
      rewrite Z2Nat.id by (unfold p384_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
  Qed.

  Theorem fp_inv_correct : forall x,
    0 < x < p ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx. apply fp_inv_correct_ax; auto. apply p384_coprime; auto.
  Qed.

End FpInv.

(* ================================================================== *)
(* Concrete parameters for P-384 divstep                               *)
(* ================================================================== *)

Definition p384_r' : Z :=
  Eval vm_compute in
    (let r := 2^machine_wordsize in
     let p := p384_p in
     (fst (Z.ggcd r p))).

Definition p384_m' : Z :=
  Eval vm_compute in
    (let r := 2^machine_wordsize in
     let p := p384_p in
     ((-1 / p) mod r + r) mod r).

Lemma p384_p_pos : 1 < p384_p.
Proof. vm_compute. reflexivity. Qed.

Lemma p384_p_fits : p384_p < (2^machine_wordsize) ^ Z.of_nat n.
Proof. vm_compute. reflexivity. Qed.

Lemma p384_p_odd : Z.odd p384_p = true.
Proof. vm_compute. reflexivity. Qed.
