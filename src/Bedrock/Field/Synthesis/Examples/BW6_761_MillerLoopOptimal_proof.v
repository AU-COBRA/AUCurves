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
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Keep the 189-element digit list and the projective model functions opaque
   to reduction: they sit in the postcondition that [straightline] carries
   through all 12 stackallocs, and (once [GenericSplitJoin] is imported)
   straightline otherwise normalizes them at every step, blowing up. *)
Local Opaque bw6_main_loop_js_loc.
Local Opaque BW6_761_ProjOps.bw6_proj_whole_body.

(* KNOWN [Qed]-PERFORMANCE ISSUE (not a math gap).  The proof body elaborates in
   ~0.1s (verified with [rocq compile -time]: every tactic times at 0s), but the
   monolithic [Qed] kernel-check does not terminate in 30 min.
     DIAGNOSIS (what has been ruled out, all build-verified):
   - It is NOT the dealloc certificates: rewriting the 12-cert dealloc to a single
     cancellation + 12 cert-free peels did not help.
   - It is NOT the dealloc nest itself: that nest, factored into the generic
     [bw6_dealloc12] lemma below and applied opaquely ([eapply], 0.005s), has its
     own [Qed] check in 0.075s — yet WITH that factoring the main [Qed] still
     stalls >300s.
   - [Local Opaque AbstractField.FElem] is valid hygiene but insufficient ([Opaque]
     only makes the kernel *reluctant* to unfold; it still unfolds when a
     conversion requires it).
     LOCALIZATION RESULT: the dominant cost is the UPSTREAM WP term — the
   [emit_iters_ok]/[final_ok] applications over the 189-iteration projective model,
   the 12 stackalloc post-nest types, and the [change]/[feval] reasoning.  Closing
   it requires factoring/optimizing the upstream (a separate, larger effort), not
   the dealloc (already factored). *)
Local Opaque AbstractField.FElem.

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

  (* Instance-containment: keep the tower [field_parameters] builders opaque
     to typeclass resolution (mirrors [BW6_761_MillerLoopOptimal.v]).  Without
     this, importing [GenericSplitJoin] exposes the generic extension
     [field_parameters] instances, which compete during [FElem] resolution and
     blow up [straightline]'s unification across the 12 stackallocs. *)
  Local Typeclasses Opaque bw6_Fp3_params.
  Local Typeclasses Opaque bw6_Fp6_params.

  (* Generic 12-level stack-dealloc helper, [Qed]-sealed so its kernel-check runs
     ONCE here (over abstract addresses/values => small term), decoupled from the
     main theorem's [Qed].  Peels 12 [FElem]s (reverse stackalloc order) back to
     [anybytes], leaving residual [Rtail]; any post [P] that follows from [Rtail]
     on the final kept mem is then discharged.  This is the factoring that the
     inline 12-deep dealloc (whose monolithic [Qed] was intractable) is replaced by. *)
  Lemma bw6_dealloc12
    (P Rtail : mem -> Prop) (mC : mem)
    (a_la a_ld a_r2a a_r1a a_r0a a_r2d a_r1d a_r0d a_qz a_qy a_qx a_f : word)
    (v_la v_ld v_f v_r2a v_r1a v_r0a v_r2d v_r1d v_r0d v_qz v_qy v_qx : list word) :
    (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr a_la v_la
     * (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr a_ld v_ld
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r2a v_r2a
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r1a v_r1a
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r0a v_r0a
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r2d v_r2d
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r1d v_r1d
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_r0d v_r0d
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_qz v_qz
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_qy v_qy
     * (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_qx v_qx
     * (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr a_f v_f
     * Rtail))))))))))))%sep mC ->
    (forall mk, Rtail mk -> P mk) ->
    exists m1 mS1, Memory.anybytes a_la (@AbstractField.felem_size_in_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr) mS1 /\ map.split mC m1 mS1 /\
    (exists m2 mS2, Memory.anybytes a_ld (@AbstractField.felem_size_in_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr) mS2 /\ map.split m1 m2 mS2 /\
    (exists m3 mS3, Memory.anybytes a_r2a (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS3 /\ map.split m2 m3 mS3 /\
    (exists m4 mS4, Memory.anybytes a_r1a (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS4 /\ map.split m3 m4 mS4 /\
    (exists m5 mS5, Memory.anybytes a_r0a (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS5 /\ map.split m4 m5 mS5 /\
    (exists m6 mS6, Memory.anybytes a_r2d (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS6 /\ map.split m5 m6 mS6 /\
    (exists m7 mS7, Memory.anybytes a_r1d (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS7 /\ map.split m6 m7 mS7 /\
    (exists m8 mS8, Memory.anybytes a_r0d (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS8 /\ map.split m7 m8 mS8 /\
    (exists m9 mS9, Memory.anybytes a_qz (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS9 /\ map.split m8 m9 mS9 /\
    (exists m10 mS10, Memory.anybytes a_qy (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS10 /\ map.split m9 m10 mS10 /\
    (exists m11 mS11, Memory.anybytes a_qx (@AbstractField.felem_size_in_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) mS11 /\ map.split m10 m11 mS11 /\
    (exists m12 mS12, Memory.anybytes a_f (@AbstractField.felem_size_in_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr) mS12 /\ map.split m11 m12 mS12 /\
     P m12))))))))))).
  Proof.
    intros Hsep HP.
    destruct Hsep as (A1 & B1 & HPa1 & HF1 & HR1). exists B1, A1. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp6_params bw6_Fp6_repr a_la v_la) A1 HF1). } split. { apply map.split_comm; exact HPa1. }
    destruct HR1 as (A2 & B2 & HPa2 & HF2 & HR2). exists B2, A2. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp6_params bw6_Fp6_repr a_ld v_ld) A2 HF2). } split. { apply map.split_comm; exact HPa2. }
    destruct HR2 as (A3 & B3 & HPa3 & HF3 & HR3). exists B3, A3. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r2a v_r2a) A3 HF3). } split. { apply map.split_comm; exact HPa3. }
    destruct HR3 as (A4 & B4 & HPa4 & HF4 & HR4). exists B4, A4. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r1a v_r1a) A4 HF4). } split. { apply map.split_comm; exact HPa4. }
    destruct HR4 as (A5 & B5 & HPa5 & HF5 & HR5). exists B5, A5. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r0a v_r0a) A5 HF5). } split. { apply map.split_comm; exact HPa5. }
    destruct HR5 as (A6 & B6 & HPa6 & HF6 & HR6). exists B6, A6. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r2d v_r2d) A6 HF6). } split. { apply map.split_comm; exact HPa6. }
    destruct HR6 as (A7 & B7 & HPa7 & HF7 & HR7). exists B7, A7. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r1d v_r1d) A7 HF7). } split. { apply map.split_comm; exact HPa7. }
    destruct HR7 as (A8 & B8 & HPa8 & HF8 & HR8). exists B8, A8. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_r0d v_r0d) A8 HF8). } split. { apply map.split_comm; exact HPa8. }
    destruct HR8 as (A9 & B9 & HPa9 & HF9 & HR9). exists B9, A9. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_qz v_qz) A9 HF9). } split. { apply map.split_comm; exact HPa9. }
    destruct HR9 as (A10 & B10 & HPa10 & HF10 & HR10). exists B10, A10. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_qy v_qy) A10 HF10). } split. { apply map.split_comm; exact HPa10. }
    destruct HR10 as (A11 & B11 & HPa11 & HF11 & HR11). exists B11, A11. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr a_qx v_qx) A11 HF11). } split. { apply map.split_comm; exact HPa11. }
    destruct HR11 as (A12 & B12 & HPa12 & HF12 & HR12). exists B12, A12. split. { exact ((@AbstractField.FElem_to_bytes _ _ _ _ _ _ _ bw6_Fp6_params bw6_Fp6_repr a_f v_f) A12 HF12). } split. { apply map.split_comm; exact HPa12. }
    apply HP; exact HR12.
  Qed.

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
      (HFp3copy : AbstractField.spec_of_felem_copy (field_representation:=bw6_Fp3_repr) functions)
      (HFp6copy : AbstractField.spec_of_felem_copy (field_representation:=bw6_Fp6_repr) functions)
      (HFromword : PrimeField.spec_of_from_word (field_representation:=bw6_Fp_repr) functions)
      (HFp6mul  : AbstractField.spec_of_BinOp AbstractField.bin_mul (field_representation:=bw6_Fp6_repr) functions)
      (HFp6sqr  : AbstractField.spec_of_UnOp AbstractField.un_square (field_representation:=bw6_Fp6_repr) functions)
      (HG2dbl  : spec_of_bw6_761_g2_double_step functions)
      (HG2add  : spec_of_bw6_761_g2_add_step functions)
      (HG2line : spec_of_bw6_761_g2_line_compute functions)
      (HSparse : spec_of_bw6_761_sparse_line_eval functions),
    spec_of_bw6_761_miller_loop_optimal_strengthened functions.
  Proof.
    (* ===== Phase 0: entry + 12 stackallocs + master-sep build ===== *)
    intros functions EnvContains HFp3copy HFp6copy HFromword HFp6mul HFp6sqr HG2dbl HG2add HG2line HSparse.
    unfold spec_of_bw6_761_miller_loop_optimal_strengthened.
    intros pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr mem0 Hpre.
    destruct Hpre as (Hbpx & Hbpy & Hbq0x & Hbq0y & Hbq1x & Hbq1y & Hbq0ny & Hbq1ny & Hbhalf & Hsep).
    eapply WeakestPreconditionProperties.start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func]. unfold bw6_761_miller_loop_optimal. simpl snd. simpl fst. cbv match beta.
    eexists. split. { exact eq_refl. } repeat straightline.
    (* Hide the inputs sep behind a [unit ->] wrapper so [straightline]'s
       array threading does not grow it (the fast solver cliffs ~7 atoms). *)
    rename Hsep into Hin. pose proof (fun (_:unit) => Hin) as HinF. clear Hin.
    split. { apply Z_mod_mult. } intros a_f mStack_f mComb_f HanyF HsplitF. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_qx mStack_qx mComb_qx HanyQx HsplitQx. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_qy mStack_qy mComb_qy HanyQy HsplitQy. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_qz mStack_qz mComb_qz HanyQz HsplitQz. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r0d mStack_r0d mComb_r0d HanyR0d HsplitR0d. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r1d mStack_r1d mComb_r1d HanyR1d HsplitR1d. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r2d mStack_r2d mComb_r2d HanyR2d HsplitR2d. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r0a mStack_r0a mComb_r0a HanyR0a HsplitR0a. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r1a mStack_r1a mComb_r1a HanyR1a HsplitR1a. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_r2a mStack_r2a mComb_r2a HanyR2a HsplitR2a. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_line_d mStack_line_d mComb_line_d HanyLd HsplitLd. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    split. { apply Z_mod_mult. } intros a_line_a mStack_line_a mComb_line_a HanyLa HsplitLa. repeat match goal with Hs : sep _ _ _ |- _ => clear Hs end. repeat straightline.
    pose proof (HinF tt) as Hin. clear HinF.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr _ _ a_f) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_f) HanyF) as [fv0 Hfe_f]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_qx) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_qx) HanyQx) as [qxv Hfe_qx]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_qy) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_qy) HanyQy) as [qyv Hfe_qy]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_qz) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_qz) HanyQz) as [qzv Hfe_qz]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r0d) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r0d) HanyR0d) as [r0dv Hfe_r0d]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r1d) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r1d) HanyR1d) as [r1dv Hfe_r1d]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r2d) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r2d) HanyR2d) as [r2dv Hfe_r2d]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r0a) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r0a) HanyR0a) as [r0av Hfe_r0a]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r1a) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r1a) HanyR1a) as [r1av Hfe_r1a]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr _ _ a_r2a) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_r2a) HanyR2a) as [r2av Hfe_r2a]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr _ _ a_line_d) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_line_d) HanyLd) as [ldv Hfe_ld]. clear Hfb.
    pose proof (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr _ _ a_line_a) as Hfb. unfold AbstractField.Placeholder in Hfb. pose proof (proj1 (Hfb mStack_line_a) HanyLa) as [lav Hfe_la]. clear Hfb.
    assert (sfs : forall (A B : mem -> Prop) (m mOld mNew : mem), map.split m mOld mNew -> A mOld -> B mNew -> (A * B)%sep m).
    { clear. intros A B m mOld mNew [Heq Hd] HA HB. subst m. exists mOld, mNew. split. { split; [reflexivity| exact Hd]. } split; assumption. }
    pose proof (sfs _ _ _ _ _ HsplitF Hin Hfe_f) as Hm0.
    pose proof (sfs _ _ _ _ _ HsplitQx Hm0 Hfe_qx) as Hm1.
    pose proof (sfs _ _ _ _ _ HsplitQy Hm1 Hfe_qy) as Hm2.
    pose proof (sfs _ _ _ _ _ HsplitQz Hm2 Hfe_qz) as Hm3.
    pose proof (sfs _ _ _ _ _ HsplitR0d Hm3 Hfe_r0d) as Hm4.
    pose proof (sfs _ _ _ _ _ HsplitR1d Hm4 Hfe_r1d) as Hm5.
    pose proof (sfs _ _ _ _ _ HsplitR2d Hm5 Hfe_r2d) as Hm6.
    pose proof (sfs _ _ _ _ _ HsplitR0a Hm6 Hfe_r0a) as Hm7.
    pose proof (sfs _ _ _ _ _ HsplitR1a Hm7 Hfe_r1a) as Hm8.
    pose proof (sfs _ _ _ _ _ HsplitR2a Hm8 Hfe_r2a) as Hm9.
    pose proof (sfs _ _ _ _ _ HsplitLd Hm9 Hfe_ld) as Hm10.
    pose proof (sfs _ _ _ _ _ HsplitLa Hm10 Hfe_la) as Hmaster.
    clear Hm0 Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 Hm7 Hm8 Hm9 Hm10 Hin Hfe_f Hfe_qx Hfe_qy Hfe_qz Hfe_r0d Hfe_r1d Hfe_r2d Hfe_r0a Hfe_r1a Hfe_r2a Hfe_ld Hfe_la HanyF HanyQx HanyQy HanyQz HanyR0d HanyR1d HanyR2d HanyR0a HanyR1a HanyR2a HanyLd HanyLa HsplitF HsplitQx HsplitQy HsplitQz HsplitR0d HsplitR1d HsplitR2d HsplitR0a HsplitR1a HsplitR2a HsplitLd HsplitLa.
    (* ===== Phase A: seed q := q1, qz := (1,0,0) ===== *)
    eapply Semantics.weaken_call.
    { eapply HFp3copy. split. { SeparationLogic.ecancel_assumption_impl. } { SeparationLogic.ecancel_assumption_impl. } }
    cbv beta. intros t1 m1 rets1 (-> & -> & Hs1).
    eexists. split. 1: reflexivity. repeat straightline.
    eapply Semantics.weaken_call.
    { eapply HFp3copy. split. { SeparationLogic.ecancel_assumption_impl. } { SeparationLogic.ecancel_assumption_impl. } }
    cbv beta. intros t2 m2 rets2 (-> & -> & Hs2). clear Hs1 Hmaster.
    eexists. split. 1: reflexivity. repeat straightline.
    (* qz: split FElem_Fp3 into 3 Fp slots, from_word each, rejoin *)
    eassert (Hqz : (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr a_qz qzv * _)%sep m2). { SeparationLogic.ecancel_assumption_impl. }
    apply (ce_raw_FElem_split_in_sep BW6_761_Instances.bw6_Fp_mul_by_nr_model "bw6_761_Fp3_" BW6_761_Instances.Fp_eq_dec) in Hqz.
    eapply Semantics.weaken_call.
    { eapply HFromword. SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tc0 mc0 retsc0 (-> & -> & Xc0 & Hfc0 & Hbc0 & Hsc0).
    eexists. split. 1: reflexivity. repeat straightline.
    eapply Semantics.weaken_call.
    { eapply HFromword. SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tc1 mc1 retsc1 (-> & -> & Xc1 & Hfc1 & Hbc1 & Hsc1). clear Hsc0.
    eexists. split. 1: reflexivity. repeat straightline.
    eapply Semantics.weaken_call.
    { eapply HFromword. SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tc2 mc2 retsc2 (-> & -> & Xc2 & Hfc2 & Hbc2 & Hsc2). clear Hsc1.
    eexists. split. 1: reflexivity. repeat straightline.
    assert (Hl0 : Datatypes.length Xc0 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr).
    { pose proof Hbc0 as Hs. cbv [AbstractField.bounded_by AbstractField.tight_bounds bw6_Fp_repr BW6_761_Instances.bw6_frep Signature.field_representation Representation.frep Field.bounded_by Field.tight_bounds] in Hs. cbn in Hs. destruct Hs as [Hsm _]. apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hsm. rewrite map_length in Hsm. exact Hsm. }
    assert (Hl1 : Datatypes.length Xc1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr).
    { pose proof Hbc1 as Hs. cbv [AbstractField.bounded_by AbstractField.tight_bounds bw6_Fp_repr BW6_761_Instances.bw6_frep Signature.field_representation Representation.frep Field.bounded_by Field.tight_bounds] in Hs. cbn in Hs. destruct Hs as [Hsm _]. apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hsm. rewrite map_length in Hsm. exact Hsm. }
    assert (Hl2 : Datatypes.length Xc2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr).
    { pose proof Hbc2 as Hs. cbv [AbstractField.bounded_by AbstractField.tight_bounds bw6_Fp_repr BW6_761_Instances.bw6_frep Signature.field_representation Representation.frep Field.bounded_by Field.tight_bounds] in Hs. cbn in Hs. destruct Hs as [Hsm _]. apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hsm. rewrite map_length in Hsm. exact Hsm. }
    eassert (Hjoin_in : (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr a_qz Xc0 * (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr (word.add a_qz (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))) Xc1 * (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr (word.add a_qz (word.of_Z (2 * (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr))))) Xc2 * _)))%sep mc2).
    { SeparationLogic.ecancel_assumption_impl. }
    pose proof (ce_raw_FElem_join_in_sep BW6_761_Instances.bw6_Fp_mul_by_nr_model "bw6_761_Fp3_" BW6_761_Instances.Fp_eq_dec a_qz Xc0 Xc1 Xc2 _ mc2 Hl0 Hl1 Hl2 Hjoin_in) as Hqzj.
    clear Hjoin_in.
    (* EVOLVE-BLOCK-START *)
    (* === Steps b–h: init double+sparse, main loop (emit_iters_ok),
       final adjustment (final_ok), output copy, 12-level stack dealloc,
       and the projective whole-body value match. === *)
    (* (a) Bounds for the i=188 init g2_double_step: relax q1x/q1y to loose
       and assemble Fp3_loose on the rejoined qz = Xc0++Xc1++Xc2. *)
    pose proof (@AbstractField.relax_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr bw6_Fp3_repr_ok _ Hbq1x) as Hbq1x_l.
    pose proof (@AbstractField.relax_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr bw6_Fp3_repr_ok _ Hbq1y) as Hbq1y_l.
    assert (Ec0 : @GenericCubicSpecs.ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc0) by (unfold GenericCubicSpecs.ce_c0_felem; apply firstn_app_le; exact Hl0).
    assert (Ec1 : @GenericCubicSpecs.ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc1) by (unfold GenericCubicSpecs.ce_c1_felem; rewrite (skipn_app_le Xc0 (Xc1 ++ Xc2) _ Hl0); apply firstn_app_le; exact Hl1).
    assert (Ec2 : @GenericCubicSpecs.ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc2) by (unfold GenericCubicSpecs.ce_c2_felem; rewrite List.app_assoc; apply skipn_app_le; rewrite List.app_length, Hl0, Hl1; lia).
    assert (Hbqz_l : @AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr) (Xc0 ++ Xc1 ++ Xc2)) by (apply (@AbstractField.relax_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr bw6_Fp3_repr_ok); split; [|split]; [rewrite Ec0; exact Hbc0 | rewrite Ec1; exact Hbc1 | rewrite Ec2; exact Hbc2]).
    (* (b) g2_double_step (i=188 init) *)
    eapply Semantics.weaken_call.
    { eapply HG2dbl. split;[exact Hbq1x_l|]. split;[exact Hbq1y_l|]. split;[exact Hbqz_l|]. split;[exact Hbhalf|]. SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tD mD retsD HpostD.
    destruct HpostD as (-> & <- & x1v & y1v & z1v & r0v & r1v & r2v & Hbx1 & Hby1 & Hbz1 & Hbr0 & Hbr1 & Hbr2 & HsD & HvalD).
    eexists. split. 1: reflexivity. repeat straightline.
    (* (c) sparse_line_eval (i=188 init) -> f *)
    eapply Semantics.weaken_call.
    { eapply HSparse. split;[exact Hbr0|]. split;[exact Hbr1|]. split;[exact Hbr2|]. split;[exact Hbpx|]. split;[exact Hbpy|]. SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tS mS retsS HpostS.
    destruct HpostS as (-> & <- & fSv & HbfS & HsS & HvalfS).
    clear Hs2 Hqz Hsc2 Hqzj HsD Hbq1x_l Hbq1y_l Hbqz_l Ec0 Ec1 Ec2.
    eexists. split. 1: reflexivity.
    (* (d) Assemble the running [proj_running] after the init step. *)
    assert (Hrun : proj_running a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a a_line_d a_line_a pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tc2 (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr fSv) (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr x1v) (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr y1v) (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr z1v) tc2 mS l10) by (unfold proj_running; split; [reflexivity|]; split; [exact Hbpx|]; split; [exact Hbpy|]; split; [exact Hbhalf|]; split; [exact Hbq0x|]; split; [exact Hbq0y|]; split; [exact Hbq1x|]; split; [exact Hbq1y|]; split; [exact Hbq0ny|]; split; [exact Hbq1ny|]; exists fSv, x1v, y1v, z1v, r0v, r1v, r2v, r0av, r1av, r2av, ldv, lav; split; [exact HbfS|]; split; [exact Hbx1|]; split; [exact Hby1|]; split; [exact Hbz1|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; SeparationLogic.ecancel_assumption_impl).
    (* (e) Main loop: emit_iters_ok advances proj_running over bw6_main_loop_js. *)
    cbv [cmd_seq_list BW6_761_MillerLoop.cmd_seq_list].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply (emit_iters_ok functions HG2dbl HG2add HSparse HFp6mul HFp6sqr bw6_main_loop_js bw6_main_loop_js_alphabet).
         - cbv [step_locals]. repeat split; reflexivity.
         - exact Hrun. }
    intros tM mM lM HpostM.
    destruct HpostM as [-> HrunM].
    destruct (BW6_761_ProjOps.bw6_proj_main_loop bw6_main_loop_js (feval q0x) (feval q0y) (feval q0ny) (feval q1x) (feval q1y) (feval q1ny) (feval p_x) (feval p_y) (feval half) (feval fSv) (feval x1v) (feval y1v) (feval z1v)) as [fv2 [[Tx2 Ty2] Tz2]] eqn:HML.
    (* (f) Final adjustment (i=0): final_ok. *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply (final_ok functions HG2dbl HG2line HSparse HFp6mul HFp6sqr).
         - cbv [step_locals]. repeat split; reflexivity.
         - exact HrunM. }
    intros tF mF lF HpostF.
    destruct HpostF as [-> HrunF].
    destruct (BW6_761_ProjOps.bw6_proj_double_step Tx2 Ty2 Tz2 (feval half)) as [[[x1f y1f] z1f] rd] eqn:HDF.
    clear Hrun HrunM HsS.
    unfold proj_running in HrunF.
    destruct HrunF as (HtrF & Hbpx2 & Hbpy2 & Hbhalf2 & Hbq0x2 & Hbq0y2 & Hbq1x2 & Hbq1y2 & Hbq0ny2 & Hbq1ny2 & ffin & qxf & qyf & qzf & r0df & r1df & r2df & r0af & r1af & r2af & ldf & laf & Hbffin & Hbqxf & Hbqyf & Hbqzf & Heffin & Heqxf & Heqyf & Heqzf & HsF).
    (* (g) fp6_copy out <- f *)
    repeat straightline.
    eapply Semantics.weaken_call.
    { eapply HFp6copy. split. { SeparationLogic.ecancel_assumption_impl. } { SeparationLogic.ecancel_assumption_impl. } }
    cbv beta. intros tC mC retsC HpostC.
    destruct HpostC as (-> & -> & Hcopy).
    eexists. split. 1: reflexivity.
    (* Fp3_feval (Xc0++Xc1++Xc2) = bw6_fp3_one (the projective Z=1 seed). *)
    assert (Hone : @AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr (Xc0 ++ Xc1 ++ Xc2) = BW6_761_ProjOps.bw6_fp3_one).
    unfold BW6_761_ProjOps.bw6_fp3_one.
    cbn [AbstractField.feval bw6_Fp3_repr GenericCubicSpecs.CE_field_representation].
    unfold GenericCubicSpecs.CE_feval.
    assert (Ec0 : @GenericCubicSpecs.ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc0) by (unfold GenericCubicSpecs.ce_c0_felem; apply firstn_app_le; exact Hl0).
    assert (Ec1 : @GenericCubicSpecs.ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc1) by (unfold GenericCubicSpecs.ce_c1_felem; rewrite (skipn_app_le Xc0 (Xc1 ++ Xc2) _ Hl0); apply firstn_app_le; exact Hl1).
    assert (Ec2 : @GenericCubicSpecs.ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (Xc0 ++ Xc1 ++ Xc2) = Xc2) by (unfold GenericCubicSpecs.ce_c2_felem; rewrite List.app_assoc; apply skipn_app_le; rewrite List.app_length, Hl0, Hl1; lia).
    rewrite Ec0, Ec1, Ec2, Hfc0, Hfc1, Hfc2.
    unfold AbstractField.Fone, bw6_Fp3_params, GenericCubicSpecs.CE_field_parameters.
    unfold CubicExtensionsAbstract.ce_build; rewrite word.unsigned_of_Z_1, word.unsigned_of_Z_0; reflexivity.
    (* The init-step Gallina value equals the bedrock-produced (f, T). *)
    assert (Hinit : BW6_761_ProjOps.bw6_proj_init_step (feval p_x) (feval p_y) (feval half) (feval q1x) (feval q1y) BW6_761_ProjOps.bw6_fp3_one = (feval fSv, (feval x1v, feval y1v, feval z1v))).
    unfold BW6_761_ProjOps.bw6_proj_init_step, ProjectiveMultibase.proj_init_step.
    rewrite <- Hone.
    destruct (BW6_761_ProjOps.bw6_proj_double_step (feval q1x) (feval q1y) (feval (Xc0 ++ Xc1 ++ Xc2)) (feval half)) as [[[nx ny] nz] [[c0 c1] c2]] eqn:HDD.
    unfold BW6_761_ProjOps.bw6_proj_double_step in HDD.
    rewrite HDD.
    destruct HvalD as (Ex & Ey & Ez & E0 & E1 & E2).
    rewrite Ex, Ey, Ez, HvalfS, E0, E1, E2.
    reflexivity.
    assert (Hjs : bw6_main_loop_js = bw6_main_loop_js_loc) by reflexivity.
    (* (h) 12-level stack dealloc, FACTORED into the generic [bw6_dealloc12] lemma
       (Qed-sealed above; its own Qed is 0.075s).  [eapply] (0.005s) peels all 12
       FElems opaquely, leaving (1) the single residual-sep obligation on [mC]
       (closed by ecancel, which also resolves the 12 FElem values), and (2) the
       kept-mem post [P mk] (the [list_map] postcondition below, discharged with
       [Hmk]).  This is a sound, reusable factoring — BUT it does NOT fix the main
       [Qed]-time issue (verified: with this factoring the main [Qed] still stalls
       >300s).  LOCALIZATION RESULT: the dominant [Qed] cost is therefore NOT the
       dealloc nest (which checks in 0.075s once factored) but the UPSTREAM WP term
       — the [emit_iters_ok]/[final_ok] applications over the 189-iteration model,
       the stackalloc post-nest types, and the [change]/[feval] reasoning.  Fixing
       that requires factoring/optimizing the upstream (a separate, larger effort);
       see the KNOWN-ISSUE note at the top of the file. *)
    eapply bw6_dealloc12.
    { SeparationLogic.ecancel_assumption_impl. }
    intros mk Hmk.
    (* Final spec postcondition: output = projective whole-body value. *)
    cbv [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].
    split. 1: reflexivity.
    split. 1: reflexivity.
    exists ffin.
    split. 1: exact Hbffin.
    split. 1: SeparationLogic.ecancel_assumption_impl.
    rewrite Heffin.
    change (BW6_761_ProjOps.bw6_proj_whole_body bw6_main_loop_js_loc (feval p_x) (feval p_y) (feval q0x) (feval q0y) (feval q1x) (feval q1y) (feval q0ny) (feval q1ny) (feval half)) with (let '(f1, (x1, y1, z1)) := BW6_761_ProjOps.bw6_proj_init_step (feval p_x) (feval p_y) (feval half) (feval q1x) (feval q1y) BW6_761_ProjOps.bw6_fp3_one in let '(f2, (x2, y2, z2)) := BW6_761_ProjOps.bw6_proj_main_loop bw6_main_loop_js_loc (feval q0x) (feval q0y) (feval q0ny) (feval q1x) (feval q1y) (feval q1ny) (feval p_x) (feval p_y) (feval half) f1 x1 y1 z1 in BW6_761_ProjOps.bw6_proj_final_adjustment f2 x2 y2 z2 (feval q1x) (feval q1ny) (feval p_x) (feval p_y) (feval half)).
    rewrite Hinit. rewrite <- Hjs. rewrite HML. reflexivity.
  Qed.
  (* EVOLVE-BLOCK-END *)

End BW6_761_MillerLoopOptimal_Top.
