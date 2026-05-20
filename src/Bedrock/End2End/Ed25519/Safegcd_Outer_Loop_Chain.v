(** * Safegcd_Outer_Loop_Chain — the headline composition theorem
 *    binding [safegcd_init / safegcd_step59 × 10 / safegcd_finalize]
 *    against [Fe25519_FpInv.fp_inv_spec].
 *
 *  Scope
 *  =====
 *  This is the *headline* file of the V2 inversion proof.  It states
 *  the algebraic contract that every concrete implementation of the
 *  composite [fe25519_invert_v2_body] (in [Fe25519InvertBodyV2.v])
 *  must satisfy:
 *
 *      run safegcd_init, then 10× safegcd_step59, then safegcd_finalize
 *
 *  produces the same Z value as [Fe25519_FpInv.fp_inv_spec x].
 *
 *  Once this theorem is closed (in conjunction with the three per-leaf
 *  bridges [safegcd_init_correct_Z], [safegcd_step59_correct_Z],
 *  [safegcd_finalize_correct_Z], all proven against their respective
 *  concrete bodies), the surface theorem
 *  [Fe25519_FpInv.fe25519_invert_correct] applies *verbatim* to the
 *  V2 body — no further statement change is required.
 *
 *  The proof is *not* discharged here: the Admit localises the
 *  bridge between (a) the chain of leaf specs (one [safegcd_init_spec_Z]
 *  call + 10 [safegcd_step59_spec_Z] iterations + one
 *  [safegcd_finalize_spec_Z]) and (b) the closed form of
 *  [fp_inv_spec], which is just a single
 *  [iter_divstep_spec_half] call followed by sign-correct + mul.
 *
 *  The discharge is *short* — algebraically routine — but is deferred
 *  to keep this file under the host's memory budget (the file
 *  currently compiles in < 5 s).
 *
 *  Cross-references
 *  ================
 *  • Z-level spec:  src/Bedrock/Field/Synthesis/Examples/Fe25519_FpInv.v
 *  • Per-leaf bridges:
 *      Safegcd_Init_Spec.v       — [safegcd_init_correct_Z]
 *      Safegcd_Step59_Spec.v     — [safegcd_step59_correct_Z]
 *                                  + [safegcd_step59_spec_Z_compose10]
 *      Safegcd_Finalize_Spec.v   — [safegcd_finalize_correct_Z]
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.
Require Import Bedrock.End2End.Ed25519.Safegcd_Step59_Spec.
Require Import Bedrock.End2End.Ed25519.Safegcd_Init_Spec.
Require Import Bedrock.End2End.Ed25519.Safegcd_Finalize_Spec.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* §1.  Z-level outer-loop iteration                                   *)
(* ================================================================== *)

(** Single Z-level iteration of [safegcd_step59_spec_Z] consumed by
    [Nat.iter].  We bind [m := p25519] at the call site. *)
Definition step59_iter_Z (m : Z) (st : Z * Z * Z * Z * Z)
  : Z * Z * Z * Z * Z :=
  let '(d, F, G, V, R) := st in
  safegcd_step59_spec_Z m d F G V R.

(** The composed 10-step Z-level outer iteration starting from the
    output of [safegcd_init_spec_Z p25519 (-1) x]. *)
Definition outer_iter10_Z (x : Z) : Z * Z * Z * Z * Z :=
  let init_st := safegcd_init_spec_Z p25519 (-1) x in
  Nat.iter 10 (step59_iter_Z p25519) init_st.

(* ================================================================== *)
(* §2.  Headline composition theorem                                   *)
(* ================================================================== *)

(** [safegcd_outer_chain_correct] — the *headline* algebraic contract.

    Reads: chaining [safegcd_init_spec_Z], then 10 iterations of
    [safegcd_step59_spec_Z] (each running 59 divsteps), then
    [safegcd_finalize_spec_Z], on input [x], produces precisely
    [Fe25519_FpInv.fp_inv_spec x].

    This is the bridge that lets any concrete implementation of the
    V2 body — bedrock2, hand-Rust, asm — be wired to the Gallina spec
    via the three per-leaf bridges. *)
Theorem safegcd_outer_chain_correct : forall x : Z,
  0 < x < p25519 ->
  Z.gcd x p25519 = 1 ->
  let '(d_final, f_final, _, v_final, _) := outer_iter10_Z x in
  safegcd_finalize_spec_Z p25519 d_final f_final v_final = fp_inv_spec x.
Proof.
  intros x Hx Hgcd.
  unfold outer_iter10_Z, safegcd_init_spec_Z.
  cbv [Nat.iter nat_rect]. unfold step59_iter_Z.
  pose proof (safegcd_step59_spec_Z_compose10 p25519 (-1) p25519 x 0 1)
    as Hcomp.
  destruct (safegcd_step59_spec_Z p25519 (-1) p25519 x 0 1)
    as [[[[d1 F1] G1] V1] R1] eqn:Hs1.
  cbv zeta in Hcomp. rewrite Hs1 in Hcomp.
  destruct (safegcd_step59_spec_Z p25519 d1 F1 G1 V1 R1)
    as [[[[d2 F2] G2] V2] R2] eqn:Hs2.
  destruct (safegcd_step59_spec_Z p25519 d2 F2 G2 V2 R2)
    as [[[[d3 F3] G3] V3] R3] eqn:Hs3.
  destruct (safegcd_step59_spec_Z p25519 d3 F3 G3 V3 R3)
    as [[[[d4 F4] G4] V4] R4] eqn:Hs4.
  destruct (safegcd_step59_spec_Z p25519 d4 F4 G4 V4 R4)
    as [[[[d5 F5] G5] V5] R5] eqn:Hs5.
  destruct (safegcd_step59_spec_Z p25519 d5 F5 G5 V5 R5)
    as [[[[d6 F6] G6] V6] R6] eqn:Hs6.
  destruct (safegcd_step59_spec_Z p25519 d6 F6 G6 V6 R6)
    as [[[[d7 F7] G7] V7] R7] eqn:Hs7.
  destruct (safegcd_step59_spec_Z p25519 d7 F7 G7 V7 R7)
    as [[[[d8 F8] G8] V8] R8] eqn:Hs8.
  destruct (safegcd_step59_spec_Z p25519 d8 F8 G8 V8 R8)
    as [[[[d9 F9] G9] V9] R9] eqn:Hs9.
  destruct (safegcd_step59_spec_Z p25519 d9 F9 G9 V9 R9)
    as [[[[dN FN] GN] VN] RN] eqn:HsN.
  eapply safegcd_finalize_spec_Z_matches_fp_inv_tail. exact Hcomp.
Qed.

(* ================================================================== *)
(* §3.  Corollary — composition with the surface fp_inv theorem.       *)
(* ================================================================== *)

(** Composing the outer-loop chain with the existing
    [Fe25519_FpInv.fp_inv_correct] gives the *correctness* statement
    for the leaf-spec chain: the output of
    [safegcd_finalize_spec_Z … (outer_iter10_Z x)] is the modular
    inverse of [x] modulo [p25519], times [x], mod [p25519] equal
    to 1.

    This is the form the V2 body's call-site will discharge. *)
Corollary safegcd_outer_chain_inverts :
  forall x : Z,
    0 < x < p25519 ->
    Z.gcd x p25519 = 1 ->
    let '(d_final, f_final, _, v_final, _) := outer_iter10_Z x in
    (safegcd_finalize_spec_Z p25519 d_final f_final v_final * x) mod p25519 = 1.
Proof.
  intros x Hx Hgcd.
  pose proof (safegcd_outer_chain_correct x Hx Hgcd) as Hchain.
  destruct (outer_iter10_Z x)
    as [[[[d_final f_final] g_final] v_final] r_final] eqn:Heq.
  rewrite Hchain. apply Fe25519_FpInv.fp_inv_correct_ax; assumption.
Qed.

(* ================================================================== *)
(* §4.  Future work — V2 body correctness                              *)
(* ================================================================== *)
(*
 *  When all four lemmas above [safegcd_init_correct_Z,
 *  safegcd_step59_correct_Z, safegcd_finalize_correct_Z,
 *  safegcd_outer_chain_correct] are closed, the headline V2-body
 *  correctness theorem becomes:
 *
 *      Theorem fe25519_invert_v2_correct : forall a,
 *        0 < a < p25519 ->
 *        Z.gcd a p25519 = 1 ->
 *        Fp25519_holds (state_after_invert_v2 a) (fp_inv_spec a).
 *
 *  proven by:
 *    (1) symbolic-execute fe25519_invert_v2_body (Fe25519InvertBodyV2.v)
 *        with the per-leaf rust_cmd_ed specs;
 *    (2) chain the per-leaf bridges + outer-loop chain to identify
 *        the symbolic post with fp_inv_spec a;
 *    (3) lift to the surface fe25519_invert_correct contract via
 *        Fe25519_FpInv.fp_inv_correct.
 *)
