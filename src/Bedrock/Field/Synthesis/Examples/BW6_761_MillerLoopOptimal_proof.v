(** * BW6-761 Optimal-Ate Miller Loop — WP correctness top-level.

    Step 3 of Phase 2 of the BW6-761 optimal-ate pairing proof.
    Defines and (eventually) proves the strengthened specification
    of [bw6_761_miller_loop_optimal] (from
    [BW6_761_MillerLoopOptimal.v]) that ties the bedrock2 body's
    output [Fp6_felem] to the Gallina reference model
    [affine_miller_optimal_ate] from
    [PairingTheory/AffineMultibase.v].

    File-split layout (for build-time budget per CLAUDE.md 5-min
    threshold):

      - [BW6_761_MillerLoopOptimal_proof_Common.v]
          imports + Strategy 0 directive + [Existing Instances] +
          Local Notations + alphabet ([bw6_alphabet],
          [bw6_j_seq_length]) + FieldOps instance
          ([bw6_761_field_ops]) + strengthened spec
          ([spec_of_bw6_761_miller_loop_optimal_strengthened]) +
          loop invariant ([multibase_state_at],
          [miller_loop_inv_opt]) + [multibase_state_at_zero] Qed +
          [miller_loop_inv_opt_init] Qed +
          [miller_loop_inv_opt_exit] Qed.

      - [BW6_761_MillerLoopOptimal_proof_Step.v]
          [miller_loop_body_step_opt] Admitted (Phase 2 Step 5).

      - this file
          main theorem [bw6_761_miller_loop_optimal_ok] Admitted
          (depends on the Step lemma; gap documented).

    Initially we tried a 5-file split (Common + Init + Step + Exit
    + main).  Per-file Rupicola+bedrock2 imports turned out to
    dominate compile time (>10 min for each of Init/Exit despite
    trivial proof bodies), so Init/Exit were folded back into
    Common.  Step remains a separate file because its [Admitted]
    body lets that file compile fast despite the same import
    chain.

    The bedrock2 body is FULLY UNROLLED (189 iterations spelled out
    by [emit_iters bw6_main_loop_js]), so the WP proof does NOT use
    a single [Loops.while_localsmap].  Instead, the structural
    skeleton is:

      - Init   : after the seeding block
                 (q := q1, qz := 1, [miller_iter_init] at i=188)
                 the running [(f, T)] equals
                 [affine_miller_5symbol_aux bw6_alphabet 188 …
                    (fp12_one ops) Qx Qy] — i.e. one iteration of
                 the multibase auxiliary has been performed.
      - Step   : each subsequent unrolled iteration body
                 [miller_iter_body j] advances the running [(f, T)]
                 by one [multibase_iter_step].  Closing this is
                 Phase 2 Step 5 (sister-agent territory); LEFT
                 [Admitted] there with a documented TODO.
      - Exit   : after the final [miller_iter_final] at i=0, the
                 emitted result equals
                 [affine_miller_5symbol_final_adjustment …]
                 composed with the post-loop main-loop result.

    Note on tower naming: in [AffineMultibase] the abstract types
    are written [Fp / Fp2 / Fp12].  BW6-761 instantiates them as
    [Fp / Fp3 / Fp6] respectively (i.e. the "Fp2" slot of FieldOps
    holds an Fp3 in our concrete tower, and the "Fp12" slot holds
    an Fp6).  The Gallina model is polymorphic in those three type
    arguments, so the instantiation is straightforward.

    STATUS (this file, Step 3): scaffolding only.
      - [bw6_761_field_ops]:                Definition  (Common).
      - [bw6_alphabet]:                     Definition  (Common).
      - [spec_of_bw6_761_miller_loop_optimal_strengthened]:
                                            Definition  (Common).
      - [miller_loop_inv_opt]:              Definition  (Common).
      - [multibase_state_at_zero]:          Qed         (Common).
      - [miller_loop_inv_opt_init]:         Qed         (Common).
      - [miller_loop_body_step_opt]:        Admitted    (Step,
                                            Phase 2 Step 5).
      - [miller_loop_inv_opt_exit]:         Qed         (Common).
      - [bw6_761_miller_loop_optimal_ok]:   Admitted
                                            (depends on the Step
                                            lemma; gap documented).
*)

Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal_proof_Common.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal_proof_Step.

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
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

Section BW6_761_MillerLoopOptimal_Top.

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

  (* ================================================================ *)
  (* Main theorem.                                                     *)
  (*                                                                  *)
  (* Currently [Admitted] because closing it requires:                 *)
  (*   - the per-iteration Step lemma [miller_loop_body_step_opt]     *)
  (*     (LEFT Admitted in the _Step.v sub-file, Phase 2 Step 5),     *)
  (*     and                                                           *)
  (*   - the per-call WP bridging lemmas for g2_double_step,           *)
  (*     g2_add_step, g2_line_compute, sparse_line_eval (Phase 2 Step *)
  (*     4, currently in flight on the sister-agent branch).           *)
  (*                                                                  *)
  (* The skeleton: function entry + stackallocs + master-sep build +  *)
  (* body execution via Init + (187 × Step) + Exit + post-loop          *)
  (* dealloc.                                                           *)
  (* ================================================================ *)

  Theorem bw6_761_miller_loop_optimal_ok :
    forall functions
      (EnvContains : map.get functions "bw6_761_miller_loop_optimal" =
        Some (snd bw6_761_miller_loop_optimal))
      (HFp3mul  : spec_of (AbstractField.mul (F:=Fp3)) functions)
      (HFp3add  : spec_of (AbstractField.add (F:=Fp3)) functions)
      (HFp3sub  : spec_of (AbstractField.sub (F:=Fp3)) functions)
      (HFp3sqr  : spec_of (AbstractField.square (F:=Fp3)) functions)
      (HFp3opp  : spec_of (AbstractField.opp (F:=Fp3)) functions)
      (HFp3copy : spec_of (AbstractField.felem_copy (F:=Fp3)) functions)
      (HFp6mul  : spec_of (AbstractField.mul (F:=Fp6)) functions)
      (HFp6sqr  : spec_of (AbstractField.square (F:=Fp6)) functions)
      (HFp6copy : spec_of (AbstractField.felem_copy (F:=Fp6)) functions)
      (HFpcopy  : spec_of (AbstractField.felem_copy (F:=Fp)) functions)
      (HFromword : spec_of PrimeField.from_word functions)
      (HG2dbl  : spec_of "bw6_761_g2_double_step" functions)
      (HG2add  : spec_of "bw6_761_g2_add_step" functions)
      (HG2line : spec_of "bw6_761_g2_line_compute" functions)
      (HSparse : spec_of "bw6_761_sparse_line_eval" functions),
    spec_of_bw6_761_miller_loop_optimal_strengthened functions.
  Proof.
    (* Skeleton.

       Phase A: function entry + 12 stackallocs (anybytes → FElem
       conversions), master-sep build.

       Phase B: seeding fragment
         fp3_copy qx q1x; fp3_copy qy q1y; from_word qz := (1,0,0)
         followed by [miller_iter_init] (i = 188, no square).
         By [miller_loop_inv_opt_init] (in _Common.v) + the
         per-call WP, the invariant holds at v = 188 immediately
         after the init fragment.

       Phase C: 187 iterations of [miller_loop_body_step_opt] (in
         _Step.v, currently Admitted, Phase 2 Step 5).  After 187
         step applications, invariant holds at v = 1.  (The
         unrolled body's last "main loop" iteration is
         [bw6_alphabet 1].)

       Phase D: [miller_iter_final] (i = 0).  By the per-call WP
         plus [miller_loop_inv_opt_exit] (in _Common.v), the
         running f equals
         [affine_miller_optimal_ate ops 188 bw6_alphabet …].

       Phase E: [fp6_copy out f] + 12-level stack dealloc, output
         postcondition.

       Currently Admitted because Phase C depends on the Step lemma
       (Admitted) and Phases B+D depend on per-call WP bridging
       lemmas that are sister-agent territory. *)
  Admitted.

End BW6_761_MillerLoopOptimal_Top.
