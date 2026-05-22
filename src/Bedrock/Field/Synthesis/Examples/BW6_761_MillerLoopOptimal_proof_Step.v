(** * BW6-761 Optimal-Ate Miller Loop — Step sub-lemma.

    Per-iteration invariant preservation: for each
    [v ∈ {1,...,187}] the unrolled body fragment
    [miller_iter_body (bw6_alphabet v)] takes the invariant from
    measure [v] to measure [v - 1].

    Closing this requires walking the per-iteration WP through:
      - 1 × fp6_sqr (f := f²)
      - 1 × g2_double_step (T := 2T, line coeffs r0d/r1d/r2d)
      - 1 × sparse_line_eval (line_d := sparse(r0d, r1d, r2d, P))
      - 1 × fp6_mul (f := f × line_d)
    and, when [bw6_alphabet v ≠ 0] (a non-zero NAF digit), also:
      - 1 × g2_add_step against the appropriate (q0/q0Neg/q1/q1Neg)
      - 1 × sparse_line_eval (line_a)
      - 1 × fp6_mul (f := f × line_a)
    and then deriving the Gallina-level invariant transition from
    [multibase_state_at k …] to [multibase_state_at (k+1) …] via
    [multibase_iter_step_j0] / [_j1] / [_jm1] / [_j3] / [_jm3] as
    applicable.

    Currently [Admitted] (Phase 2 Step 5).  Sister agent
    (a1444e31d54a30e0c) is fixing the Rust extraction path that
    feeds the per-call WP bridging lemmas — once that lands, the
    per-call WP discharges should be drop-in.

    Split out of [BW6_761_MillerLoopOptimal_proof.v] for build-time
    budget (see [_proof_Common.v] header). *)

Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal_proof_Common.

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BW6_761_MillerLoopOptimal_Step.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp_names
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok bw6_Fp3_names
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok bw6_Fp6_names.

  Local Notation Fp  := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Local Notation Fp_felem  := (@AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_felem := (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_felem := (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Lemma miller_loop_body_step_opt :
    forall functions
      (HFp3mul  : spec_of (AbstractField.mul (F:=Fp3)) functions)
      (HFp3add  : spec_of (AbstractField.add (F:=Fp3)) functions)
      (HFp3sub  : spec_of (AbstractField.sub (F:=Fp3)) functions)
      (HFp3sqr  : spec_of (AbstractField.square (F:=Fp3)) functions)
      (HFp3opp  : spec_of (AbstractField.opp (F:=Fp3)) functions)
      (HFp3copy : spec_of (AbstractField.felem_copy (F:=Fp3)) functions)
      (HFp6mul  : spec_of (AbstractField.mul (F:=Fp6)) functions)
      (HFp6sqr  : spec_of (AbstractField.square (F:=Fp6)) functions),
    forall a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
           a_line_d a_line_a
           pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
           (old_out : Fp6_felem) (p_x p_y : Fp_felem)
           (q0x q0y q1x q1y q0ny q1ny : Fp3_felem) (half : Fp_felem)
           (Rr : mem -> Prop) (tr : Semantics.trace)
           (vi : nat) (ti : Semantics.trace) (mi : mem) (li : locals),
      miller_loop_inv_opt
        a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
        a_line_d a_line_a
        pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
        old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr
        vi ti mi li ->
      (0 < vi <= 187)%nat ->
      WeakestPrecondition.cmd (BasicC64Semantics.call functions)
        (miller_iter_body (bw6_alphabet vi)) ti mi li
        (fun t' m' l' =>
          miller_loop_inv_opt
            a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
            a_line_d a_line_a
            pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
            old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr
            (vi - 1)%nat t' m' l').
  Proof.
    (* TODO Phase 2 Step 5.  Walk the per-iteration WP through the
       dbl_step + sparse_line + fp6_mul (+ optional add_step branch)
       and use multibase_iter_step_jX consistency lemmas from
       AffineMultibase to bump the Gallina counter. *)
  Admitted.

End BW6_761_MillerLoopOptimal_Step.
