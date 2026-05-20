(** * Closes [BLS12_FpInv.by_convergence_dfg] axiom via the existing bridge.

    Composes [divsteps_bridge.by_convergence_dfg_proved] (which uses
    [divsteps_bridge]'s own [iter_divstep_dfg] definition) with
    [BLS12_FpInv]'s [iter_divstep_dfg] (identical body, different
    file) via a trivial equality lemma.  Result:
    [by_convergence_dfg_closed] has the exact statement of
    [BLS12_FpInv.by_convergence_dfg], discharging the axiom.

    Net axiom in the chain: just [bls12_certificate] (the cert is
    axiomatized in [divsteps_bls12.v] per the file's own header
    comment, with independent OCaml + vm_compute verification).
*)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_bridge.
Require Import Crypto.Arithmetic.BYInv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpInv.

Local Open Scope Z_scope.

(** The two [iter_divstep_dfg] definitions (one in [divsteps_bridge.v],
    one in [BLS12_FpInv.v]) have identical bodies; they coincide. *)
Lemma iter_divstep_dfg_eq : forall n d f g,
  divsteps_bridge.iter_divstep_dfg n d f g =
  BLS12_FpInv.iter_divstep_dfg n d f g.
Proof.
  induction n as [|k IH]; intros d f g; simpl; [reflexivity|].
  destruct (divstep_spec d f g) as [[d' f'] g'].
  apply IH.
Qed.

(** Discharges [BLS12_FpInv.by_convergence_dfg]: the convergence
    statement with the exact shape of the axiom. *)
Theorem by_convergence_dfg_closed : forall x,
  0 < x < BLS12_FpInv.bls12_p ->
  Z.gcd x BLS12_FpInv.bls12_p = 1 ->
  let '(_, f_N, g_N) :=
    BLS12_FpInv.iter_divstep_dfg
      (Z.to_nat BLS12_FpInv.bls12_divstep_iters) 1 BLS12_FpInv.bls12_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  rewrite <- iter_divstep_dfg_eq.
  apply divsteps_bridge.by_convergence_dfg_proved; auto.
Qed.

(* ================================================================ *)
(* Helper lemmas (mirrored from BLS12_FpInv_proof.v).                *)
(* ================================================================ *)

Local Notation p := BLS12_FpInv.bls12_p.

Lemma Zmod_sub_zero : forall a b m,
  m <> 0 -> (a - b) mod m = 0 -> a mod m = b mod m.
Proof.
  intros a b m Hm H.
  apply Zmod_divides in H; [| exact Hm].
  destruct H as [k Hk].
  assert (a = b + k * m) by lia.
  subst a. rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Zmod_mod. reflexivity.
Qed.

Lemma Zmul_mod_compat : forall a b c m,
  a mod m = b mod m -> (a * c) mod m = (b * c) mod m.
Proof.
  intros a b c m H.
  destruct (Z.eq_dec m 0) as [->|Hm].
  { rewrite !Zmod_0_r in *. subst. reflexivity. }
  assert (Hdiff : (a - b) mod m = 0).
  { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; [reflexivity | exact Hm]. }
  apply Zmod_divides in Hdiff; [| exact Hm].
  destruct Hdiff as [k Hk].
  replace a with (b + m * k) by lia.
  replace ((b + m * k) * c) with (b * c + k * c * m) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma mod_mul_rearrange : forall v c x m,
  ((v mod m * c) mod m * x) mod m = (v * x * c) mod m.
Proof.
  intros.
  rewrite Zmult_mod_idemp_l with (a := v mod m * c) (b := x).
  replace (v mod m * c * x) with (v mod m * (c * x)) by ring.
  rewrite Zmult_mod_idemp_l with (a := v) (b := c * x).
  f_equal. ring.
Qed.

(* ================================================================ *)
(* The headline: fp_inv_correct without the by_convergence_dfg       *)
(* axiom — goes through by_convergence_dfg_closed instead.           *)
(* ================================================================ *)

(** Mirror of [BLS12_FpInv_proof.fp_inv_correct_proved] with the
    single line [by_convergence_dfg] replaced by [by_convergence_dfg_closed]. *)
Theorem fp_inv_correct_closed : forall x,
  0 < x < p ->
  Z.gcd x p = 1 ->
  (BLS12_FpInv.fp_inv_spec x * x) mod p = 1.
Proof.
  intros x Hx Hgcd.
  unfold BLS12_FpInv.fp_inv_spec.
  set (N := Z.to_nat BLS12_FpInv.bls12_divstep_iters).
  destruct (BLS12_FpInv.iter_divstep_spec p N 1 p x 0 1)
    as [[[[d_N f_N] g_N] v_N] r_N] eqn:Espec.
  pose proof (BLS12_FpInv.iter_invariant p N 1 p x 0 1 x
                BLS12_FpInv.p_pos BLS12_FpInv.p_odd) as Hinv.
  assert (Hv0 : (0 * x - p) mod p = 0).
  { replace (0 * x - p) with ((-1) * p) by ring.
    rewrite Z_mod_mult. reflexivity. }
  assert (Hr0 : (1 * x - x) mod p = 0)
    by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv Hv0 Hr0). rewrite Espec in Hinv.
  destruct Hinv as [Hinv_v _].
  pose proof (BLS12_FpInv.iter_dfg_agree N p 1 p x 0 1) as Hagree.
  rewrite Espec in Hagree.
  destruct (BLS12_FpInv.iter_divstep_dfg N 1 p x) as [[d2 f2] g2] eqn:Edfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]]. subst f2 g2.
  pose proof (by_convergence_dfg_closed x Hx Hgcd) as Hconv.
  unfold N in Edfg. rewrite Edfg in Hconv.
  destruct Hconv as [Hg0 Hf_pm1]. subst g_N.
  assert (Hp : p <> 0) by (pose proof BLS12_FpInv.p_pos; lia).
  Opaque BLS12_FpInv.bls12_p.
  destruct Hf_pm1 as [Hf1 | Hf_neg1].
  - subst f_N. rewrite Z.mul_1_r in Hinv_v.
    change (1 <? 0) with false. simpl (if false then _ else _).
    assert (Hvx : (v_N * x) mod p = (2 ^ Z.of_nat N) mod p)
      by (apply Zmod_sub_zero; auto).
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * BLS12_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BLS12_FpInv.bls12_divstep_iters; vm_compute; discriminate).
    exact BLS12_FpInv.precomp_times_pow2.
  - subst f_N.
    change (-1 <? 0) with true. simpl (if true then _ else _).
    replace (2 ^ Z.of_nat N * -1) with (-(2 ^ Z.of_nat N)) in Hinv_v by ring.
    assert (Hpvx : ((p - v_N) * x) mod p = (2 ^ Z.of_nat N) mod p).
    { assert (Hvx_neg : (v_N * x) mod p = (-(2 ^ Z.of_nat N)) mod p)
        by (apply Zmod_sub_zero; auto).
      replace ((p - v_N) * x) with (-(v_N * x) + x * p) by ring.
      rewrite Z_mod_plus_full.
      rewrite Z.opp_eq_mul_m1.
      apply Zmul_mod_compat with (c := -1) in Hvx_neg.
      replace (v_N * x * -1) with ((v_N * x) * -1) by ring.
      rewrite Hvx_neg.
      replace (-(2 ^ Z.of_nat N) * -1) with (2 ^ Z.of_nat N) by ring.
      reflexivity. }
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * BLS12_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hpvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BLS12_FpInv.bls12_divstep_iters; vm_compute; discriminate).
    exact BLS12_FpInv.precomp_times_pow2.
Qed.

(** [Print Assumptions fp_inv_correct_closed]: should report only
    [bls12_certificate] (the convex-hull cert from [divsteps_bls12.v],
    independently verified by OCaml extraction per that file's header).
    No [by_convergence_dfg] axiom — the chain goes through
    [by_convergence_dfg_closed] which goes through the convex-hull
    bridge and the cert directly. *)
