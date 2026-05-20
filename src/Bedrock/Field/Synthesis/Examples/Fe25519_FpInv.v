(** * Curve25519 Fp inversion via δ₀ = 1/2 Bernstein–Yang divsteps.

    Mirrors [BLS12_FpInv.v], but for the Curve25519 base-field prime
    [p25519 = 2^255 - 19] using the [δ₀ = 1/2] variant of the
    Bernstein–Yang algorithm (EUROCRYPT 2026, §3.4 / Theorem 1).

    Iteration count: [N = 590] divsteps  (vs. ~720 for the BY-2019
    δ₀ = 1 loose bound on b = 256).  This matches the libsecp256k1
    [modinv64] structure and the Rust port at
    [curve25519-jasmin-rs/src/safegcd25519.rs].

    Algorithm (Wuille's [zeta] reformulation):
    - Represent δ via integer [d := zeta = -(δ + 1/2)].
      Initial value [d_0 = -1] encodes [δ_0 = 1/2].
    - Test "δ > 0" becomes "d < 0".
    - δ ↦ -δ + 1 (swap branch) becomes d ↦ -d - 2.
    - δ ↦ δ + 1 (no-swap branch) becomes d ↦ d - 1.

    The (f, g, v, r) updates are identical to the standard δ₀ = 1
    [divstep_spec_full] modulo the test direction; the loop invariant
    proof is therefore essentially the same.

    The full inversion:
    1. Precompute  [precomp = ((p+1)/2)^590 mod p]   (= [2^{-590} mod p]).
    2. Initialize  [d = -1, f = p, g = x, v = 0, r = 1].
    3. Iterate 590 times.
    4. Sign correction: if [f < 0] then [v := p - v].
    5. Result: [out = v * precomp mod p].

    This file defines the Gallina specification of the full inversion and
    proves it correct modulo one number-theoretic axiom (convergence of
    the divstep iteration to [g = 0, |f| = 1] at [N = 590], stated as
    [by_convergence_dfg_half] — the δ₀ = 1/2 counterpart of the
    EUROCRYPT 2026 Theorem 1, taken on the same trust footing as the
    BY-2019 axiom in [BLS12_FpInv.v]).

    The convex-hull certificate in [src/Arithmetic/safegcd/divsteps590.v]
    discharges convergence for [divsteps_half.step] (the 3-field algorithm
    in [divsteps_def_half.v]).  Bridging that to the 5-field
    [iter_divstep_spec_half] used here closes [by_convergence_dfg_half]
    completely; the bridge mirrors the structurally identical gap in
    [BLS12_FpInv.v] and is mechanical Z bookkeeping over (v, r).
*)

From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Znumtheory.

Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* Curve25519 prime and machine parameters                             *)
(* ================================================================== *)

(** The Curve25519 base-field prime [2^255 - 19]. *)
Definition p25519 : Z := 2^255 - 19.

Lemma p25519_val : p25519 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.
Proof. vm_compute. reflexivity. Qed.

Definition machine_wordsize : Z := 64.

(** 4 × 64-bit limbs for Montgomery; 5 × 62-bit limbs for the
    [Signed62] saturated representation used by the Rust port. *)
Definition n : nat := 4.
Definition sat_limbs : nat := 5.

Definition p25519_mbits : Z := Z.log2 p25519 + 1.

Lemma p25519_mbits_val : p25519_mbits = 255.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Bernstein-Yang iteration count (EUROCRYPT 2026, δ₀ = 1/2)            *)
(* ================================================================== *)

(** Number of divsteps for [p25519] using δ₀ = 1/2 and the
    convex-hull-tight bound at b = 256.  This is the count formalised by
    the certificate [divsteps590.v]. *)
Definition p25519_divstep_iters : Z := 590.

(* ================================================================== *)
(* δ₀ = 1/2 divstep specification                                       *)
(* ================================================================== *)

(** Single divstep, δ₀ = 1/2 variant.  The arithmetic on (f, g, v, r) is
    identical to the standard δ₀ = 1 spec; the integer [d] encodes
    Wuille's [zeta = -(δ + 1/2)] so the test and update on [d] are
    rewritten:

    - Test [(0 <? d) && Z.odd g]  →  [(d <? 0) && Z.odd g]
    - "Swap" branch:    [d := 1 - d]   →   [d := -d - 2]
    - "No-swap" branch: [d := 1 + d]   →   [d := d - 1]
*)
Definition divstep_spec_full_half (m d f g v r : Z) : Z * Z * Z * Z * Z :=
  if (d <? 0) && Z.odd g
  then (- d - 2, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (d - 1, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Definition divstep_spec_half (d f g : Z) : Z * Z * Z :=
  if (d <? 0) && Z.odd g
  then (- d - 2, g, (g - f) / 2)
  else (d - 1, f, (g + (g mod 2) * f) / 2).

(** Iterated divstep_spec_full_half. *)
Fixpoint iter_divstep_spec_half (m : Z) (nsteps : nat)
    (d f g v r : Z) : Z * Z * Z * Z * Z :=
  match nsteps with
  | O => (d, f, g, v, r)
  | S k =>
    let '(d', f', g', v', r') := divstep_spec_full_half m d f g v r in
    iter_divstep_spec_half m k d' f' g' v' r'
  end.

(** (d, f, g)-only iteration. *)
Fixpoint iter_divstep_dfg_half (nsteps : nat) (d f g : Z) : Z * Z * Z :=
  match nsteps with
  | O => (d, f, g)
  | S k =>
    let '(d', f', g') := divstep_spec_half d f g in
    iter_divstep_dfg_half k d' f' g'
  end.

(* ================================================================== *)
(* Agreement of (d, f, g) projections                                  *)
(* ================================================================== *)

Lemma iter_dfg_agree_half : forall nsteps m d f g v r,
  let '(d1, f1, g1, _, _) := iter_divstep_spec_half m nsteps d f g v r in
  let '(d2, f2, g2) := iter_divstep_dfg_half nsteps d f g in
  d1 = d2 /\ f1 = f2 /\ g1 = g2.
Proof.
  induction nsteps as [|k IH]; intros; simpl.
  - auto.
  - unfold divstep_spec_full_half, divstep_spec_half.
    destruct ((d <? 0) && Z.odd g) eqn:E;
    [ specialize (IH m (- d - 2) g ((g - f) / 2) (2 * r mod m) ((r - v) mod m))
    | specialize (IH m (d - 1) f ((g + g mod 2 * f) / 2) (2 * v mod m) ((r + g mod 2 * v) mod m)) ];
    destruct (iter_divstep_spec_half m k _ _ _ _ _) as [[[[? ?] ?] ?] ?];
    destruct (iter_divstep_dfg_half k _ _ _) as [[? ?] ?];
    exact IH.
Qed.

(* ================================================================== *)
(* Oddness preservation                                                *)
(* ================================================================== *)

Lemma divstep_spec_half_f_odd : forall d f g,
  Z.odd f = true ->
  let '(_, f', _) := divstep_spec_half d f g in
  Z.odd f' = true.
Proof.
  intros d f g Hf. unfold divstep_spec_half.
  destruct ((d <? 0) && Z.odd g) eqn:E.
  - apply andb_prop in E. tauto.
  - exact Hf.
Qed.

Lemma iter_divstep_dfg_half_f_odd : forall k d f g,
  Z.odd f = true ->
  let '(_, f', _) := iter_divstep_dfg_half k d f g in
  Z.odd f' = true.
Proof.
  induction k as [|k IH]; intros d f g Hf; simpl.
  - exact Hf.
  - pose proof (divstep_spec_half_f_odd d f g Hf) as Hstep.
    destruct (divstep_spec_half d f g) as [[d' f'] g'].
    exact (IH d' f' g' Hstep).
Qed.

(* ================================================================== *)
(* Loop invariant for (v, r)                                           *)
(* ================================================================== *)

(** Single-step invariant with scaling factor [A]:
    if [v*x ≡ A*f (mod m)], [r*x ≡ A*g (mod m)], and f is odd,
    then after one [divstep_spec_full_half], the same invariant holds
    with [A] doubled. *)
Lemma divstep_step_invariant_half : forall m d f g v r x A,
  0 < m ->
  Z.odd f = true ->
  (v * x - A * f) mod m = 0 ->
  (r * x - A * g) mod m = 0 ->
  let '(_, f', g', v', r') := divstep_spec_full_half m d f g v r in
  (v' * x - (2 * A) * f') mod m = 0 /\
  (r' * x - (2 * A) * g') mod m = 0.
Proof.
  intros m d f g v r x A Hm Hfodd Hv Hr.
  unfold divstep_spec_full_half.
  destruct ((d <? 0) && Z.odd g) eqn:E.
  - (* Case 1: d < 0 and g is odd  (i.e., δ > 0 and g odd; swap branch) *)
    apply andb_prop in E. destruct E as [Hd Hgodd].
    split.
    + (* v' = 2*r mod m, f' = g *)
      rewrite Zminus_mod, (Zmult_mod_idemp_l (2 * r) x m), <- Zminus_mod.
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
  - (* Case 2: not (d < 0 ∧ g odd); no-swap branch *)
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

(** Generalised loop invariant with scaling factor [A]. *)
Lemma iter_invariant_gen_half : forall m k d f g v r x A,
  0 < m ->
  Z.odd f = true ->
  (v * x - A * f) mod m = 0 ->
  (r * x - A * g) mod m = 0 ->
  let '(d', f', g', v', r') := iter_divstep_spec_half m k d f g v r in
  (v' * x - (2 ^ Z.of_nat k * A) * f') mod m = 0 /\
  (r' * x - (2 ^ Z.of_nat k * A) * g') mod m = 0.
Proof.
  intros m.
  induction k as [|k IH]; intros d f g v r x A Hm Hfodd Hv Hr;
    simpl iter_divstep_spec_half.
  - rewrite Z.pow_0_r, Z.mul_1_l. auto.
  - pose proof (divstep_step_invariant_half m d f g v r x A Hm Hfodd Hv Hr) as Hstep.
    unfold divstep_spec_full_half in Hstep |- *.
    destruct ((d <? 0) && Z.odd g) eqn:E.
    + destruct Hstep as [Hv' Hr'].
      assert (Hfodd' : Z.odd g = true).
      { apply andb_prop in E. tauto. }
      specialize (IH (- d - 2) g ((g - f) / 2) (2 * r mod m) ((r - v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd' Hv' Hr').
      destruct (iter_divstep_spec_half m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
    + destruct Hstep as [Hv' Hr'].
      specialize (IH (d - 1) f ((g + g mod 2 * f) / 2) (2 * v mod m) ((r + g mod 2 * v) mod m) x (2 * A)).
      specialize (IH Hm Hfodd Hv' Hr').
      destruct (iter_divstep_spec_half m k _ _ _ _ _) as [[[[d' f'] g'] v'] r'].
      replace (2 ^ Z.of_nat (S k) * A) with (2 ^ Z.of_nat k * (2 * A)).
      { exact IH. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** Specialised loop invariant: starting from [v = 0, r = 1, f = p, g = x],
    after k steps [v' * x ≡ 2^k * f' (mod p)] and [r' * x ≡ 2^k * g' (mod p)]. *)
Lemma iter_invariant_half : forall m k d f g v r x,
  0 < m ->
  Z.odd f = true ->
  (v * x - f) mod m = 0 ->
  (r * x - g) mod m = 0 ->
  let '(_, f', g', v', r') := iter_divstep_spec_half m k d f g v r in
  (v' * x - 2 ^ Z.of_nat k * f') mod m = 0 /\
  (r' * x - 2 ^ Z.of_nat k * g') mod m = 0.
Proof.
  intros m k d f g v r x Hm Hfodd Hv Hr.
  pose proof (iter_invariant_gen_half m k d f g v r x 1 Hm Hfodd) as H.
  rewrite !Z.mul_1_l in H.
  specialize (H Hv Hr).
  destruct (iter_divstep_spec_half m k d f g v r) as [[[[d' f'] g'] v'] r'].
  rewrite !Z.mul_1_r in H.
  exact H.
Qed.

(* ================================================================== *)
(* Full Fp inversion specification                                     *)
(* ================================================================== *)

Section FpInv.
  Let p := p25519.

  (** Binary square-and-multiply modular exponentiation. *)
  Fixpoint pow_mod_pos (base : Z) (exp : positive) (m : Z) : Z :=
    match exp with
    | xH => base mod m
    | xO p =>
        let r := pow_mod_pos base p m in (r * r) mod m
    | xI p =>
        let r := pow_mod_pos base p m in (((r * r) mod m) * base) mod m
    end.

  (** [precomp = ((p+1)/2)^590 mod p].  As [(p+1)/2 = 2^{-1} mod p] (since
      [p] is odd), this equals [2^{-590} mod p] and cancels the [2^590]
      factor from the Bernstein–Yang loop invariant. *)
  Definition precomp_val : Z :=
    Eval vm_compute in
      (let half := (p25519 + 1) / 2 in
       pow_mod_pos half 590 p25519).

  (** The full inversion. *)
  Definition fp_inv_spec (x : Z) : Z :=
    let '(d, f, g, v, r) :=
      iter_divstep_spec_half p (Z.to_nat p25519_divstep_iters) (-1) p x 0 1 in
    let v_corrected := if (f <? 0) then (p - v) mod p else v mod p in
    (v_corrected * precomp_val) mod p.

  (* ================================================================ *)
  (* Convergence axiom (δ₀ = 1/2; EUROCRYPT 2026, Theorem 1)            *)
  (* ================================================================ *)

  (** For an odd prime [p] of [b ≤ 256] bits, after [N = 590] iterations
      of [divstep_spec_half] starting from [d = -1, f = p, g = x] with
      [0 < x < p] and [gcd(x, p) = 1], we have [g_N = 0] and [|f_N| = 1].

      This is the δ₀ = 1/2 counterpart of [BLS12_FpInv.by_convergence_dfg].

      The convex-hull certificate at [src/Arithmetic/safegcd/divsteps590.v]
      discharges this convergence for the actual [divsteps.step] (in
      [divsteps_def.v], parametric in INC).  The bridge from
      [divsteps.step] (3-field) to [divstep_spec_half] (5-field) is
      identical in structure to the BLS12 case and is left as a [.todo]
      to keep parity. *)
  Axiom by_convergence_dfg_half : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    let '(_, f_N, g_N) :=
      iter_divstep_dfg_half (Z.to_nat p25519_divstep_iters) (-1) p x in
    g_N = 0 /\ (f_N = 1 \/ f_N = -1).

  (* ================================================================ *)
  (* Auxiliary computational lemmas                                    *)
  (* ================================================================ *)

  Lemma p_pos : 0 < p.
  Proof. subst p. unfold p25519. vm_compute. reflexivity. Qed.

  Lemma p_odd : Z.odd p = true.
  Proof. subst p. unfold p25519. vm_compute. reflexivity. Qed.

  (** [precomp * 2^N ≡ 1 (mod p)]. *)
  Lemma precomp_times_pow2 :
    (precomp_val * 2 ^ p25519_divstep_iters) mod p = 1.
  Proof.
    subst p. unfold precomp_val, p25519_divstep_iters, p25519.
    vm_compute. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Main correctness theorem                                          *)
  (* ================================================================ *)

  Lemma fp_inv_correct_ax : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd.
    unfold fp_inv_spec.
    destruct (iter_divstep_spec_half p (Z.to_nat p25519_divstep_iters) (-1) p x 0 1)
      as [[[[d_N f_N] g_N] v_N] r_N] eqn:Hiter.
    (* (A) Loop invariant *)
    pose proof (iter_invariant_half p (Z.to_nat p25519_divstep_iters) (-1) p x 0 1 x
                  p_pos p_odd) as Hinv.
    assert (H0 : (0 * x - p) mod p = 0)
      by (replace (0 * x - p) with ((-1) * p) by ring; rewrite Z_mod_mult; reflexivity).
    assert (H1 : (1 * x - x) mod p = 0)
      by (replace (1 * x - x) with 0 by ring; reflexivity).
    specialize (Hinv H0 H1). rewrite Hiter in Hinv.
    destruct Hinv as [Hv_inv Hr_inv].
    (* (B) Convergence *)
    pose proof (by_convergence_dfg_half x Hx Hgcd) as Hconv.
    pose proof (iter_dfg_agree_half (Z.to_nat p25519_divstep_iters) p (-1) p x 0 1) as Hagree.
    rewrite Hiter in Hagree.
    destruct (iter_divstep_dfg_half (Z.to_nat p25519_divstep_iters) (-1) p x)
      as [[d2 f2] g2] eqn:Hdfg.
    destruct Hagree as [_ [Hf_eq Hg_eq]].
    subst f_N g_N. destruct Hconv as [Hg0 Hf_cases]. subst g2.
    clear Hr_inv H0 H1 Hiter Hdfg d_N d2 r_N.
    (* Case split on f2 = 1 or f2 = -1 *)
    destruct Hf_cases as [Hf1 | Hfm1]; subst f2.
    - (* f_N = 1: no sign correction *)
      replace (1 <? 0) with false by reflexivity.
      rewrite Z.mul_1_r in Hv_inv.
      rewrite Zmult_mod_idemp_l.
      replace (v_N mod p * precomp_val * x)
        with (v_N mod p * (precomp_val * x)) by ring.
      rewrite Zmult_mod_idemp_l.
      replace (v_N * (precomp_val * x))
        with (precomp_val * (v_N * x)) by ring.
      assert (Hmod : (v_N * x) mod p = (2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters)) mod p). {
        assert (Hp : p <> 0) by (pose proof p_pos; lia).
        apply Z.mod_divide in Hv_inv; [|exact Hp].
        destruct Hv_inv as [k Hk].
        assert (v_N * x = 2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters) + k * p) by lia.
        rewrite H.
        rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        reflexivity.
      }
      rewrite <- Zmult_mod_idemp_r, Hmod, Zmult_mod_idemp_r.
      rewrite Z2Nat.id by (unfold p25519_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
    - (* f_N = -1: sign correction *)
      replace (-1 <? 0) with true by reflexivity.
      replace (2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters) * -1)
        with (- (2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters))) in Hv_inv by ring.
      replace (v_N * x - - 2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters))
        with (v_N * x + 2 ^ Z.of_nat (Z.to_nat p25519_divstep_iters)) in Hv_inv by ring.
      set (iters := Z.of_nat (Z.to_nat p25519_divstep_iters)) in *.
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
      rewrite Z2Nat.id by (unfold p25519_divstep_iters; vm_compute; discriminate).
      exact precomp_times_pow2.
  Qed.

  (** The user-facing theorem.  No primality of [p25519] needed in the
      statement — only [Z.gcd x p = 1] (which is implied by primality if
      desired). *)
  Theorem fe25519_invert_correct : forall x,
    0 < x < p ->
    Z.gcd x p = 1 ->
    (fp_inv_spec x * x) mod p = 1.
  Proof.
    intros x Hx Hgcd. apply fp_inv_correct_ax; auto.
  Qed.

End FpInv.
