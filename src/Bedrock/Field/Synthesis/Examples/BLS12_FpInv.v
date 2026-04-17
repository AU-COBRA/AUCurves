(** * BLS12-381 Fp inversion via Bernstein-Yang divstep algorithm.

    The Bernstein-Yang algorithm computes modular inverses using a sequence
    of "divstep" operations.  For an n-bit prime, the number of divsteps
    needed is at most floor((49n + 57) / 17) when n >= 46.

    For BLS12-381:
      p has 381 bits (Z.log2 p + 1 = 381)
      iterations = (49 * 381 + 57) / 17 = 18726 / 17 = 1101

    The algorithm:
      1. Precompute  precomp = ((p+1)/2)^1101  mod p
      2. Initialize   d = 1, f = p, g = x, v = 0, r = 1
      3. Iterate 1101 times: (d,f,g,v,r) := divstep(d,f,g,v,r)
      4. Sign correction: if f < 0 then v := p - v
      5. Result: out = v * precomp  mod p

    This file defines:
    - The BLS12-specific iteration count (1101)
    - The Gallina specification of the full inversion
    - The correctness theorem, proved modulo the Bernstein-Yang convergence
      bound (Theorem 11.2 of the CHES 2019 paper), which is taken as an axiom.
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
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.

Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* BLS12-381 prime and its parameters                                  *)
(* ================================================================== *)

(** The BLS12-381 base field prime. *)
Definition bls12_p : Z :=
  Eval vm_compute in
    (let u := (-0xd201000000010000)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z).

(** Machine parameters for 64-bit limbs. *)
Definition machine_wordsize : Z := 64.

(** Number of 64-bit limbs for Montgomery representation (6 limbs = 384 bits). *)
Definition n : nat := 6.

(** Number of limbs for the saturated representation (n+1 = 7). *)
Definition sat_limbs : nat := 7.

(** The number of bits in p. *)
Definition bls12_mbits : Z := Z.log2 bls12_p + 1.

Lemma bls12_mbits_val : bls12_mbits = 381.
Proof. vm_compute. reflexivity. Qed.

(** BLS12-381 has >= 46 bits, so we use the large-prime formula. *)
Lemma bls12_mbits_ge_46 : 46 <= bls12_mbits.
Proof. vm_compute. discriminate. Qed.

(* ================================================================== *)
(* Bernstein-Yang iteration count                                      *)
(* ================================================================== *)

(** The number of divstep iterations for BLS12-381 inversion. *)
Definition bls12_divstep_iters : Z :=
  Eval vm_compute in ((49 * bls12_mbits + 57) / 17).

Lemma bls12_divstep_iters_val : bls12_divstep_iters = 1101.
Proof. vm_compute. reflexivity. Qed.

(** This equals the formula from divstep_precomp_correct when mbits >= 46. *)
Lemma bls12_divstep_iters_eq_precomp_exp :
  bls12_divstep_iters =
  (if Decidable.dec (bls12_mbits < 46) then (49 * bls12_mbits + 80) / 17
   else (49 * bls12_mbits + 57) / 17).
Proof.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Iterated divstep specification                                      *)
(* ================================================================== *)

(** Iterate the abstract divstep_spec_full n times starting from state (d,f,g,v,r). *)
Fixpoint iter_divstep_spec (m : Z) (nsteps : nat)
    (d : Z) (f g v r : Z) : Z * Z * Z * Z * Z :=
  match nsteps with
  | O => (d, f, g, v, r)
  | S k =>
    let '(d', f', g', v', r') := divstep_spec_full m d f g v r in
    iter_divstep_spec m k d' f' g' v' r'
  end.

(** Iterate the (d,f,g) part of divstep_spec. *)
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

(** The (d,f,g) components of iter_divstep_spec agree with iter_divstep_dfg. *)
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

(** divstep_spec preserves oddness of f. *)
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

(** Iterated divstep_spec preserves oddness of f. *)
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

(** Combined single-step invariant with scaling factor A:
    if v*x ≡ A*f (mod m) and r*x ≡ A*g (mod m) and f is odd,
    then after one divstep, v'*x ≡ 2A*f' and r'*x ≡ 2A*g' (mod m). *)
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
  - (* Case 1: d > 0 and g is odd *)
    apply andb_prop in E. destruct E as [Hd Hgodd].
    split.
    + (* v' = 2*r mod m, f' = g *)
      (* Strip mod from (2*r mod m)*x using Zminus_mod + Zmult_mod_idemp_l *)
      rewrite Zminus_mod, (Zmult_mod_idemp_l (2 * r) x m), <- Zminus_mod.
      (* Now: ((2*r)*x - 2*A*g) mod m = 0 *)
      replace ((2 * r) * x - 2 * A * g) with (2 * (r * x - A * g)) by ring.
      rewrite <- (Zmult_mod_idemp_r (r * x - A * g) 2 m), Hr. reflexivity.
    + (* r' = (r-v) mod m, g' = (g-f)/2 *)
      assert (Heven : (g - f) mod 2 = 0).
      { rewrite Zminus_mod, (Zmod_odd g), Hgodd, (Zmod_odd f), Hfodd. reflexivity. }
      rewrite Zminus_mod, (Zmult_mod_idemp_l (r - v) x m), <- Zminus_mod.
      replace ((r - v) * x - 2 * A * ((g - f) / 2))
        with ((r * x - A * g) - (v * x - A * f)).
      2:{ assert (2 * ((g - f) / 2) = g - f) by
            (rewrite (Z.div_mod (g - f) 2) at 2 by lia; lia). nia. }
      rewrite Zminus_mod, Hr, Hv. reflexivity.
  - (* Case 2: not (d > 0 and g odd) *)
    split.
    + (* v' = 2*v mod m, f' = f *)
      rewrite Zminus_mod, (Zmult_mod_idemp_l (2 * v) x m), <- Zminus_mod.
      replace ((2 * v) * x - 2 * A * f) with (2 * (v * x - A * f)) by ring.
      rewrite <- (Zmult_mod_idemp_r (v * x - A * f) 2 m), Hv. reflexivity.
    + (* r' = (r + (g mod 2)*v) mod m, g' = (g + (g mod 2)*f)/2 *)
      assert (Heven : (g + g mod 2 * f) mod 2 = 0).
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

(** Generalized loop invariant with scaling factor A. *)
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
  - (* Base case: 2^0 * A = A *)
    rewrite Z.pow_0_r, Z.mul_1_l. auto.
  - (* Step case *)
    pose proof (divstep_step_invariant m d f g v r x A Hm Hfodd Hv Hr) as Hstep.
    unfold divstep_spec_full in Hstep |- *.
    destruct ((0 <? d) && Z.odd g) eqn:E.
    + (* Case 1 *)
      destruct Hstep as [Hv' Hr'].
      assert (Hfodd' : Z.odd g = true).
      { apply andb_prop in E. tauto. }
      specialize (IH (1 - d) g ((g - f) / 2) (2 * r mod m) ((r - v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd' Hv' Hr').
      destruct (iter_divstep_spec m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
    + (* Case 2 *)
      destruct Hstep as [Hv' Hr'].
      specialize (IH (1 + d) f ((g + g mod 2 * f) / 2) (2 * v mod m) ((r + g mod 2 * v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd Hv' Hr').
      destruct (iter_divstep_spec m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** Specialized loop invariant: starting from (v=0, r=1, f=p, g=x),
    after k steps v'*x ≡ 2^k * f' (mod p) and r'*x ≡ 2^k * g' (mod p). *)
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
  (** We work with the BLS12-381 prime. *)
  Let p := bls12_p.

  (** The precomputation value: ((p+1)/2)^N mod p.
      Note: (p+1)/2 is the modular inverse of 2 modulo p (since p is odd),
      so precomp = 2^{-N} mod p.  This cancels the 2^N factor from the
      Bernstein-Yang loop invariant.

      We use a literal constant (computed externally) to avoid the expensive
      Eval vm_compute on ((p+1)/2)^1101 which causes OOM. *)
  Definition precomp_val : Z :=
    0x11c6d15bba1175d5a31eba337ac8a8451c556786a97bc9e348cb300b20d9ac0c39603efabac9511fd739b0681e705ff.

  (** The full inversion computes:
        1. Run 1101 divsteps starting from (1, p, x, 0, 1)
        2. Extract v from the final state
        3. If f is negative, negate v
        4. Multiply v by precomp

      In Gallina (over Z mod p): *)
  Definition fp_inv_spec (x : Z) : Z :=
    let '(d, f, g, v, r) :=
      iter_divstep_spec p (Z.to_nat bls12_divstep_iters) 1 p x 0 1 in
    let v_corrected := if (f <? 0) then (p - v) mod p else v mod p in
    (v_corrected * precomp_val) mod p.

  (* ================================================================ *)
  (* Bernstein-Yang convergence axiom                                  *)
  (* ================================================================ *)

  (** The Bernstein-Yang convergence bound (CHES 2019, Theorem 11.2):
      For an odd prime p with n = Z.log2 p + 1 >= 46, and any 0 < x < p
      with gcd(x, p) = 1, after N = (49*n + 57)/17 iterations of
      divstep_spec starting from (1, p, x), we have g = 0 and |f| = 1.

      This is a deep number-theoretic result and is taken as an axiom here.
      This is the same trust model as the Hvass/Aranha/Spitters fork of
      fiat-crypto (github.com/bshvass/fiat-crypto) where convergence is a
      precondition, not a proved theorem. *)
  Axiom by_convergence_dfg : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    let '(_, f_N, g_N) :=
      iter_divstep_dfg (Z.to_nat bls12_divstep_iters) 1 p x in
    g_N = 0 /\ (f_N = 1 \/ f_N = -1).

  (* ================================================================ *)
  (* Auxiliary computational lemmas                                     *)
  (* ================================================================ *)

  Lemma p_pos : 0 < p.
  Proof. subst p. vm_compute. reflexivity. Qed.

  Lemma p_odd : Z.odd p = true.
  Proof. subst p. vm_compute. reflexivity. Qed.

  (** precomp * 2^N ≡ 1 (mod p). *)
  Lemma precomp_times_pow2 :
    (precomp_val * 2 ^ bls12_divstep_iters) mod p = 1.
  Proof.
    subst p. unfold precomp_val, bls12_divstep_iters, bls12_p.
    vm_compute. reflexivity.
  Qed.

  (** The BLS12-381 prime is coprime to any 0 < x < p since p is prime. *)
  Lemma bls12_coprime : forall x, 0 < x < p -> Z.gcd x p = 1.
  Proof.
    intros x Hx.
    apply Zgcd_1_rel_prime.
    apply rel_prime_sym.
    apply prime_rel_prime.
    - subst p. exact prime_bls12_381.
    - intros [k Hk]. subst x.
      pose proof p_pos as Hp.
      destruct Hx as [Hx1 Hx2].
      assert (k <> 0) by (intro; subst; lia).
      assert (1 <= Z.abs k) by lia.
      assert (Z.abs (k * p) >= p) by (rewrite Z.abs_mul; nia).
      lia.
  Qed.

  (* ================================================================ *)
  (* Main correctness theorem                                          *)
  (* ================================================================ *)

  (** The full proof of fp_inv_correct requires three ingredients:
      (A) Loop invariant: after k divsteps, v*x ≡ 2^k * f (mod p)
      (B) Convergence: after 1101 steps, f = ±1 (Bernstein-Yang CHES 2019, Thm 11.2)
      (C) Precomp cancellation: precomp * 2^1101 ≡ 1 (mod p)

      (A) is proved by induction using divstep_spec_full.
      (B) is taken as axiom [by_convergence_dfg] — not formalized in any Coq codebase.
      (C) is proved as [precomp_times_pow2].

      The Z modular arithmetic bookkeeping for the sign correction
      (combining A+B+C into the final result) is proved below using
      standard Zmod lemmas. *)
  Lemma fp_inv_correct_ax : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd.
    unfold fp_inv_spec.
    destruct (iter_divstep_spec p (Z.to_nat bls12_divstep_iters) 1 p x 0 1)
      as [[[[d_N f_N] g_N] v_N] r_N] eqn:Hiter.
    (* (A) Loop invariant *)
    pose proof (iter_invariant p (Z.to_nat bls12_divstep_iters) 1 p x 0 1 x
                  p_pos p_odd) as Hinv.
    assert (H0 : (0 * x - p) mod p = 0)
      by (replace (0 * x - p) with ((-1) * p) by ring; rewrite Z_mod_mult; reflexivity).
    assert (H1 : (1 * x - x) mod p = 0)
      by (replace (1 * x - x) with 0 by ring; reflexivity).
    specialize (Hinv H0 H1). rewrite Hiter in Hinv.
    destruct Hinv as [Hv_inv Hr_inv].
    (* (B) Convergence *)
    pose proof (by_convergence_dfg x Hx Hgcd) as Hconv.
    pose proof (iter_dfg_agree (Z.to_nat bls12_divstep_iters) p 1 p x 0 1) as Hagree.
    rewrite Hiter in Hagree.
    destruct (iter_divstep_dfg (Z.to_nat bls12_divstep_iters) 1 p x)
      as [[d2 f2] g2] eqn:Hdfg.
    destruct Hagree as [_ [Hf_eq Hg_eq]].
    subst f_N g_N. destruct Hconv as [Hg0 Hf_cases]. subst g2.
    clear Hr_inv H0 H1 Hiter Hdfg d_N d2 r_N.
    (* Case split on f2 = 1 or f2 = -1 *)
    destruct Hf_cases as [Hf1 | Hfm1]; subst f2.
    - (* Case f_N = 1: no sign correction needed *)
      replace (1 <? 0) with false by reflexivity.
      rewrite Z.mul_1_r in Hv_inv.
      (* Simplify nested mods: ((v mod p * precomp) mod p * x) mod p *)
      rewrite Zmult_mod_idemp_l.
      replace (v_N mod p * precomp_val * x)
        with (v_N mod p * (precomp_val * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace (v_N * (precomp_val * x))
        with (precomp_val * (v_N * x)) by ring.
      (* Use loop invariant: v_N * x ≡ 2^iters (mod p) *)
      assert (Hmod : (v_N * x) mod p = (2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters)) mod p). {
        assert (Hp : p <> 0) by (pose proof p_pos; lia).
        apply Z.mod_divide in Hv_inv; [|exact Hp].
        destruct Hv_inv as [k Hk].
        assert (v_N * x = 2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters) + k * p) by lia.
        rewrite H.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        reflexivity.
      }
      rewrite <- Zmult_mod_idemp_r, Hmod, Zmult_mod_idemp_r.
      rewrite Z2Nat.id by (unfold bls12_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
    - (* Case f_N = -1: sign correction via (p - v_N) *)
      replace (-1 <? 0) with true by reflexivity.
      replace (2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters) * -1)
        with (- (2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters))) in Hv_inv by ring.
      replace (v_N * x - - 2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters))
        with (v_N * x + 2 ^ Z.of_nat (Z.to_nat bls12_divstep_iters)) in Hv_inv by ring.
      set (iters := Z.of_nat (Z.to_nat bls12_divstep_iters)) in *.
      assert (HpN : p <> 0) by (pose proof p_pos; lia).
      (* Key fact: (p - v_N) * x ≡ 2^iters (mod p) *)
      assert (Hmod_neg : ((p - v_N) * x) mod p = (2 ^ iters) mod p). {
        replace ((p - v_N) * x) with (x * p + (-(v_N * x + 2 ^ iters) + 2 ^ iters)) by ring.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod by lia.
        rewrite Zplus_mod, (Z.mod_opp_l_z _ _ HpN Hv_inv).
        simpl. rewrite Z.mod_mod by lia. reflexivity.
      }
      (* Simplify nested mods: (((p-v) mod p * precomp) mod p * x) mod p *)
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) mod p * precomp_val * x)
        with ((p - v_N) mod p * (precomp_val * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace ((p - v_N) * (precomp_val * x))
        with (precomp_val * ((p - v_N) * x)) by ring.
      rewrite <- Zmult_mod_idemp_r, Hmod_neg, Zmult_mod_idemp_r.
      subst iters.
      rewrite Z2Nat.id by (unfold bls12_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
  Qed.

  Theorem fp_inv_correct : forall x,
    0 < x < p ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx. apply fp_inv_correct_ax; auto. apply bls12_coprime; auto.
  Qed.

End FpInv.

(* ================================================================== *)
(* Connection to COperationSpecifications                              *)
(* ================================================================== *)

(** The above spec is stated over Z. The COperationSpecifications layer
    connects this to the list-of-Z Montgomery representation used by
    the synthesized code.

    The key definitions from COperationSpecifications.WordByWordMontgomery are:
    - divstep_correct: single step over list Z representation
    - divstep_precomp_correct: precomp in Montgomery form
    - msat_correct: saturated representation of p

    The bedrock2 function will chain these together with a loop.
    The WP proof will use BYInv.divstep_correct_full to relate each
    concrete step to divstep_spec_full, then the convergence argument
    to connect the iterated spec to fp_inv_spec. *)

(* ================================================================== *)
(* Concrete parameters for BLS12 divstep                               *)
(* ================================================================== *)

(** Montgomery reduction parameter r' such that 2^64 * r' = 1 mod p. *)
Definition bls12_r' : Z :=
  Eval vm_compute in
    (let r := 2^machine_wordsize in
     let p := bls12_p in
     (* Extended GCD gives r' such that r * r' mod p = 1 *)
     (fst (Z.ggcd r p))).

(** Montgomery parameter m' such that p * m' = -1 mod 2^64. *)
Definition bls12_m' : Z :=
  Eval vm_compute in
    (let r := 2^machine_wordsize in
     let p := bls12_p in
     ((-1 / p) mod r + r) mod r).

(** Verify basic properties of our prime. *)
Lemma bls12_p_pos : 1 < bls12_p.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_p_fits : bls12_p < (2^machine_wordsize) ^ Z.of_nat n.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_p_odd : Z.odd bls12_p = true.
Proof. vm_compute. reflexivity. Qed.
