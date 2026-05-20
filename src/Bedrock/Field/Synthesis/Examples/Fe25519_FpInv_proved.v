(** * Discharge of [Fe25519_FpInv.by_convergence_dfg_half] axiom.

    Composes:
    - [divsteps_p25519_half.p25519_half_certificate] — the convex-hull
      cert at N=590, axiomatized for parity with the BLS12-381 cert in
      [divsteps_bls12.v]. OCaml-extraction-verified at runtime (~100s,
      see that file's header comment).
    - [divsteps_bridge_half.convergence_monotone_half] — the O'Connor →
      BYInv convergence bridge for δ₀=1/2.
    - A trivial definitional-equality lemma between the bridge's
      [iter_divstep_dfg_half] and [Fe25519_FpInv]'s copy (identical bodies).

    Result: [by_convergence_dfg_half_proved] has the EXACT statement of
    [Fe25519_FpInv.by_convergence_dfg_half]; [Print Assumptions] of it
    reports a single axiom, [p25519_half_certificate] — same trust
    footing as BLS12-381's [bls12_certificate]. *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def_half.
Require Import divsteps_base_half.
Require Import divsteps_theory_half.
Require Import divsteps_bridge_half.
(** The cert at N=590 for p25519 (axiomatized; OCaml-verified). *)
Require Import divsteps_p25519_half.
(** The Fe25519 Gallina spec (defines [iter_divstep_dfg_half],
    [p25519], [p25519_divstep_iters = 590]). *)
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.

Local Open Scope Z_scope.

(** The bridge's [divstep_spec_half] and [Fe25519_FpInv]'s are defined
    with identical bodies in different files; show they coincide. *)
Lemma divstep_spec_half_eq : forall d f g,
  divsteps_bridge_half.divstep_spec_half d f g =
  Fe25519_FpInv.divstep_spec_half d f g.
Proof. reflexivity. Qed.

(** Likewise for the (d, f, g) iteration. *)
Lemma iter_divstep_dfg_half_eq : forall n d f g,
  divsteps_bridge_half.iter_divstep_dfg_half n d f g =
  Fe25519_FpInv.iter_divstep_dfg_half n d f g.
Proof.
  (* Both definitions reduce to the same term; reflexivity at any n. *)
  reflexivity.
Qed.

(** p25519 is odd. *)
Lemma p25519_odd : Z.Odd Fe25519_FpInv.p25519.
Proof.
  exists ((Fe25519_FpInv.p25519 - 1) / 2).
  unfold Fe25519_FpInv.p25519. vm_compute. reflexivity.
Qed.

(** p25519 fits the bound (it is its own modulus). *)
Lemma p25519_bound : (Fe25519_FpInv.p25519 <= Fe25519_FpInv.p25519)%Z.
Proof. lia. Qed.

(** Main theorem: discharges Fe25519_FpInv's convergence axiom for
    any input [x ∈ (0, p25519)] with [gcd(x, p25519) = 1]. *)
Theorem by_convergence_dfg_half_proved : forall x,
  0 < x < Fe25519_FpInv.p25519 ->
  Z.gcd x Fe25519_FpInv.p25519 = 1 ->
  let '(_, f_N, g_N) :=
    Fe25519_FpInv.iter_divstep_dfg_half
      (Z.to_nat Fe25519_FpInv.p25519_divstep_iters) (-1)
      Fe25519_FpInv.p25519 x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  (* Substitute Fe25519_FpInv.iter_… with divsteps_bridge_half.iter_… *)
  rewrite <- iter_divstep_dfg_half_eq.
  (* Iteration count: p25519_divstep_iters = 590 (concrete). *)
  assert (HN : (Z.to_nat Fe25519_FpInv.p25519_divstep_iters
                = N.to_nat 590)%nat).
  { unfold Fe25519_FpInv.p25519_divstep_iters. vm_compute. reflexivity. }
  rewrite HN.
  (* The bridge's [convergence_monotone_half] applies. *)
  apply convergence_monotone_half with (N0 := 590%N) (M := Fe25519_FpInv.p25519).
  - exact p25519_odd.
  - exact p25519_bound.
  - lia.
  - apply Zgcd_1_rel_prime.
    rewrite Z.gcd_comm.
    exact Hgcd.
  - exact p25519_half_certificate.
  - lia.
Qed.

(** [Print Assumptions by_convergence_dfg_half_proved]: should be
    [Closed under the global context]. *)
