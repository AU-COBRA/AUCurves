(** * BW6-761 Optimal-Ate Miller Loop — WP correctness scaffold.

    Step 3 of Phase 2 of the BW6-761 optimal-ate pairing proof.
    Defines the strengthened specification of
    [bw6_761_miller_loop_optimal] (from
    [BW6_761_MillerLoopOptimal.v]) that ties the bedrock2 body's
    output [Fp6_felem] to the Gallina reference model
    [affine_miller_optimal_ate] from
    [PairingTheory/AffineMultibase.v].

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
                 [Admitted] here with a documented TODO.
      - Exit   : after the final [miller_iter_final] at i=0, the
                 emitted result equals
                 [affine_miller_5symbol_final_adjustment …]
                 composed with the post-loop main-loop result.

    For the strengthened postcondition we package these into a
    single equality
        [Fp6_feval out = affine_miller_optimal_ate ops bw6_alphabet …]
    where [ops] is the canonical bedrock2-Fp/Fp3/Fp6 [FieldOps]
    instance computed from the synthesis-pipeline [feval] functions
    (NOT a fresh axiom; built directly out of [bw6_Fp_repr],
    [bw6_Fp3_repr], [bw6_Fp6_repr]).

    Note on tower naming: in [AffineMultibase] the abstract types
    are written [Fp / Fp2 / Fp12].  BW6-761 instantiates them as
    [Fp / Fp3 / Fp6] respectively (i.e. the "Fp2" slot of FieldOps
    holds an Fp3 in our concrete tower, and the "Fp12" slot holds
    an Fp6).  The Gallina model is polymorphic in those three type
    arguments, so the instantiation is straightforward.

    STATUS (this file, Step 3): scaffolding only.
      - [bw6_761_field_ops]:                Definition.
      - [bw6_alphabet]:                     Definition.
      - [spec_of_bw6_761_miller_loop_optimal_strengthened]:
                                            Definition.
      - [miller_loop_inv_opt]:              Definition.
      - [miller_loop_inv_opt_init]:         Qed.
      - [miller_loop_body_step_opt]:        Admitted (Phase 2 Step 5).
      - [miller_loop_inv_opt_exit]:         Qed.
      - [bw6_761_miller_loop_optimal_ok]:   Admitted
                                            (depends on the Step
                                            lemma; gap documented).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoop.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal.
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.AffineMultibase.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BW6 5-symbol alphabet — indexable Z function over [bw6_j_seq].   *)
(*                                                                  *)
(* The bedrock2 body's [emit_iters bw6_main_loop_js] processes      *)
(* indices 187 down to 1 (with i = 188 by [miller_iter_init] and    *)
(* i = 0 by [miller_iter_final]).  Our alphabet picks j[i] from     *)
(* [bw6_j_seq] (a 189-element list of symbols ∈ {-3,-1,0,1,3}).     *)
(*                                                                  *)
(* Defined at TOP LEVEL (outside Section) to avoid heavy section-   *)
(* variable accumulation when later referenced from the strengthened*)
(* spec.                                                             *)
(* ================================================================ *)

(** Lookup with default 0 (covers out-of-range indices, which are
    unreachable in the BW6 loop). *)
Definition bw6_alphabet (i : nat) : Z :=
  nth i BW6_761_MillerLoopOptimal.bw6_j_seq 0%Z.

(** Sanity: list length 189 — accepts all main-loop indices. *)
Lemma bw6_j_seq_length :
  length BW6_761_MillerLoopOptimal.bw6_j_seq = 189%nat.
Proof. reflexivity. Qed.


(** Slow-Qed mitigation per reference_qed_kernel_check_blowup_dealloc.md:
    prevent the kernel from re-unfolding the heavy 188-iteration
    Gallina model at Qed time.  [Strategy 0] tells the conversion
    test to leave these names opaque unless explicitly unfolded. *)
Strategy 0
  [affine_miller_5symbol_aux
   affine_miller_5symbol
   affine_miller_optimal_ate
   affine_miller_5symbol_final_adjustment
   multibase_iter_step
   bw6_alphabet].

Section BW6_761_MillerLoopOptimal_Proof.

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

  Local Notation FElem_Fp  := (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation FElem_Fp3 := (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_bounded  := (@AbstractField.bounded_by _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_bounded := (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_tight  := (@AbstractField.tight_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp_loose  := (@AbstractField.loose_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_tight := (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_loose := (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_tight := (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_loose := (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_felem  := (@AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_felem := (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_felem := (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_feval  := (@AbstractField.feval _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_feval := (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_feval := (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation function_t :=
    (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

  (* ================================================================ *)
  (* FieldOps instance for the Gallina reference model.               *)
  (*                                                                  *)
  (* The Affine / AffineMultibase model is polymorphic in three       *)
  (* abstract types (Fp, Fp2, Fp12).  For BW6-761 we slot in          *)
  (*   "Fp2" := Fp3 and  "Fp12" := Fp6.                                *)
  (*                                                                  *)
  (* The actual arithmetic comes from the [F PrimeField.M_pos] /      *)
  (* product-type Gallina operations: [F.add / F.mul / F.sub / F.opp  *)
  (* / F.inv] on Fp, and the corresponding [AbstractField.Fadd /      *)
  (* Fmul / Fsub / Fopp / Finv] on Fp3 and Fp6 (which the generic CE *)
  (* / QE extensions provide).                                         *)
  (*                                                                  *)
  (* [make_line] is left as an OPAQUE parameter here — the BW6        *)
  (* line-evaluation is realised by the [sparse_line_eval] bedrock2   *)
  (* helper inside the body, not at the Gallina level.  Future        *)
  (* refinements may instantiate it concretely.                       *)
  (* ================================================================ *)

  (** [fp3_mul_fp]: scalar-multiply an Fp3 by an Fp element. *)
  Definition bw6_fp3_mul_fp (x : Fp3) (s : Fp) : Fp3 :=
    let '(a, b, c) := x in
    (F.mul a s, F.mul b s, F.mul c s).

  (** Abstract make_line: free parameter of the reference model.  We
      pass an arbitrary witness here (returns [Fone]).  Phase 2
      Step 5+ will refine this with the actual sparse-line
      constructor used by [bw6_761_sparse_line_eval]. *)
  Definition bw6_make_line_abstract (lam Tx Ty : Fp3) (Px Py : Fp) : Fp6 :=
    @AbstractField.Fone _ bw6_Fp6_params.

  (** Canonical [FieldOps] instance for BW6's tower.  Slot mapping:
        Fp_*    -> Fp
        Fp2_*   -> Fp3
        Fp12_*  -> Fp6
      Built from the generic [AbstractField] interface; no axioms.  *)
  Definition bw6_761_field_ops : FieldOps Fp Fp3 Fp6 :=
    {| fp_zero    := @F.zero PrimeField.M_pos;
       fp_one     := @F.one PrimeField.M_pos;
       fp2_zero   := @AbstractField.Fzero _ bw6_Fp3_params;
       fp2_one    := @AbstractField.Fone _ bw6_Fp3_params;
       fp2_add    := @AbstractField.Fadd _ bw6_Fp3_params;
       fp2_sub    := @AbstractField.Fsub _ bw6_Fp3_params;
       fp2_neg    := @AbstractField.Fopp _ bw6_Fp3_params;
       fp2_mul    := @AbstractField.Fmul _ bw6_Fp3_params;
       fp2_sqr    := fun x => @AbstractField.Fmul _ bw6_Fp3_params x x;
       fp2_inv    := @AbstractField.Finv _ bw6_Fp3_params;
       fp2_mul_fp := bw6_fp3_mul_fp;
       fp12_one   := @AbstractField.Fone _ bw6_Fp6_params;
       fp12_mul   := @AbstractField.Fmul _ bw6_Fp6_params;
       fp12_sqr   := fun x => @AbstractField.Fmul _ bw6_Fp6_params x x;
       make_line  := bw6_make_line_abstract |}.

  (* ================================================================ *)
  (* Strengthened spec.                                                *)
  (*                                                                  *)
  (* Strengthening vs. the current memory-safety-only spec (see       *)
  (* [BW6_761_MillerLoopOptimal.spec_of_bw6_761_miller_loop_optimal]) *)
  (* adds a single [Fp6_feval out = …] equation tying the bedrock2    *)
  (* output buffer to the Gallina [affine_miller_optimal_ate].        *)
  (* ================================================================ *)

  Instance spec_of_bw6_761_miller_loop_optimal_strengthened :
      spec_of "bw6_761_miller_loop_optimal" :=
    fnspec! "bw6_761_miller_loop_optimal"
      (pout p_px p_py p_q0x p_q0y p_q1x p_q1y
       p_q0ny p_q1ny p_half : word)
      / (old_out : Fp6_felem)
        (p_x p_y : Fp_felem)
        (q0x q0y q1x q1y q0ny q1ny : Fp3_felem)
        (half : Fp_felem) Rr,
    { requires tr mem :=
        Fp_bounded Fp_loose p_x /\
        Fp_bounded Fp_loose p_y /\
        Fp3_bounded Fp3_tight q0x /\
        Fp3_bounded Fp3_tight q0y /\
        Fp3_bounded Fp3_tight q1x /\
        Fp3_bounded Fp3_tight q1y /\
        Fp3_bounded Fp3_tight q0ny /\
        Fp3_bounded Fp3_tight q1ny /\
        Fp_bounded Fp_tight half /\
        (FElem_Fp6 pout old_out *
         (FElem_Fp p_px p_x *
          (FElem_Fp p_py p_y *
           (FElem_Fp3 p_q0x q0x *
            (FElem_Fp3 p_q0y q0y *
             (FElem_Fp3 p_q1x q1x *
              (FElem_Fp3 p_q1y q1y *
               (FElem_Fp3 p_q0ny q0ny *
                (FElem_Fp3 p_q1ny q1ny *
                 (FElem_Fp p_half half * Rr))))))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_bounded Fp6_loose out /\
          (FElem_Fp6 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp3 p_q0x q0x *
              (FElem_Fp3 p_q0y q0y *
               (FElem_Fp3 p_q1x q1x *
                (FElem_Fp3 p_q1y q1y *
                 (FElem_Fp3 p_q0ny q0ny *
                  (FElem_Fp3 p_q1ny q1ny *
                   (FElem_Fp p_half half * Rr))))))))))%sep mem' /\
          (* The output Fp6 value equals the Gallina reference model. *)
          Fp6_feval out =
            affine_miller_optimal_ate bw6_761_field_ops
              188%nat bw6_alphabet
              (Fp_feval p_x) (Fp_feval p_y)
              (Fp3_feval q0x) (Fp3_feval q0y)
              (Fp3_feval q0x) (Fp3_feval q0ny)
              (Fp3_feval q1x) (Fp3_feval q1y)
              (Fp3_feval q1x) (Fp3_feval q1ny) }.

  (* ================================================================ *)
  (* Loop invariant.                                                   *)
  (*                                                                  *)
  (* Indexed by a measure [v : nat] counting DOWN from 188 to 0.      *)
  (*   v = 188  →  fresh entry (running f = 1, T = q1)                *)
  (*   v ≤ 187  →  inside the main unrolled chain; (f, T) equals      *)
  (*                affine_miller_5symbol_aux bw6_alphabet (188-v)    *)
  (*                applied to the initial seed.                       *)
  (*   v = 0    →  pre-final-adjustment state.                         *)
  (*                                                                  *)
  (* For Step 3 we state the invariant; Step 5 mechanises it.         *)
  (* ================================================================ *)

  (** Gallina-level invariant tying [(f, T)] to the multibase aux.

      Indexed by the *number of iterations completed*, [k = 188 - v].
      At [k = 0] we have the freshly initialised (1, Q); at
      [k = 188] we have the post-main-loop state which is then fed
      into the final-adjustment step. *)
  Definition multibase_state_at
    (k : nat)
    (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp3)
    (f : Fp6) (Tx Ty : Fp3) : Prop :=
    let result :=
      affine_miller_5symbol_aux bw6_761_field_ops
        bw6_alphabet k Px Py
        Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
        (fp12_one bw6_761_field_ops) Qx Qy
    in
    fst (fst result) = f /\ snd (fst result) = Tx /\ snd result = Ty.

  (** Full loop invariant.  Memory layout + Gallina state. *)
  Definition miller_loop_inv_opt
    (a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
     a_line_d a_line_a : word)
    (pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half : word)
    (old_out : Fp6_felem)
    (p_x p_y : Fp_felem)
    (q0x q0y q1x q1y q0ny q1ny : Fp3_felem) (half : Fp_felem)
    (Rr : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\
    (v <= 188)%nat /\
    exists (f_val : Fp6_felem)
           (qx_val qy_val qz_val
            r0d_val r1d_val r2d_val
            r0a_val r1a_val r2a_val : Fp3_felem)
           (line_d_val line_a_val : Fp6_felem),
      Fp6_bounded Fp6_tight f_val /\
      Fp3_bounded Fp3_tight qx_val /\
      Fp3_bounded Fp3_tight qy_val /\
      Fp3_bounded Fp3_tight qz_val /\
      (FElem_Fp6 a_f f_val *
       (FElem_Fp3 a_qx qx_val *
        (FElem_Fp3 a_qy qy_val *
         (FElem_Fp3 a_qz qz_val *
          (FElem_Fp3 a_r0d r0d_val *
           (FElem_Fp3 a_r1d r1d_val *
            (FElem_Fp3 a_r2d r2d_val *
             (FElem_Fp3 a_r0a r0a_val *
              (FElem_Fp3 a_r1a r1a_val *
               (FElem_Fp3 a_r2a r2a_val *
                (FElem_Fp6 a_line_d line_d_val *
                 (FElem_Fp6 a_line_a line_a_val *
                  (FElem_Fp6 pout old_out *
                   (FElem_Fp p_px p_x *
                    (FElem_Fp p_py p_y *
                     (FElem_Fp3 p_q0x q0x *
                      (FElem_Fp3 p_q0y q0y *
                       (FElem_Fp3 p_q1x q1x *
                        (FElem_Fp3 p_q1y q1y *
                         (FElem_Fp3 p_q0ny q0ny *
                          (FElem_Fp3 p_q1ny q1ny *
                           (FElem_Fp p_half half * Rr))))))))))))))))))))))%sep m /\
      multibase_state_at (188 - v)%nat
        (Fp_feval p_x) (Fp_feval p_y)
        (Fp3_feval q0x) (Fp3_feval q0y)
        (Fp3_feval q0x) (Fp3_feval q0ny)
        (Fp3_feval q1x) (Fp3_feval q1y)
        (Fp3_feval q1x) (Fp3_feval q1ny)
        (Fp6_feval f_val) (Fp3_feval qx_val) (Fp3_feval qy_val).

  (* ================================================================ *)
  (* Sub-lemma 1 (Init): the invariant holds at [v = 188] under the   *)
  (* initial seeding (running f := 1, T := q1).                        *)
  (* ================================================================ *)

  Lemma multibase_state_at_zero :
    forall Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
           f Tx Ty,
      f = fp12_one bw6_761_field_ops ->
      Tx = Qx -> Ty = Qy ->
      multibase_state_at 0%nat
        Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
        f Tx Ty.
  Proof.
    intros Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg f Tx Ty Hf HTx HTy.
    unfold multibase_state_at; cbn [affine_miller_5symbol_aux fst snd].
    subst f Tx Ty.
    repeat split.
  Qed.

  (** Init lemma: from a fresh stack layout with [f := 1, T := Q],
      the invariant at [v = 188] is satisfied.  Corresponds to the
      post-seeding state of the bedrock2 body (after [fp3_copy qx
      q1x; fp3_copy qy q1y; from_word qz := (1,0,0)] but BEFORE the
      first [miller_iter_init] doubling step). *)
  Lemma miller_loop_inv_opt_init :
    forall a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
           a_line_d a_line_a
           pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
           (old_out : Fp6_felem) (p_x p_y : Fp_felem)
           (q0x q0y q1x q1y q0ny q1ny : Fp3_felem) (half : Fp_felem)
           (f_val : Fp6_felem)
           (qx_val qy_val qz_val
            r0d r1d r2d r0a r1a r2a : Fp3_felem)
           (line_d line_a : Fp6_felem)
           (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
      Fp6_bounded Fp6_tight f_val ->
      Fp3_bounded Fp3_tight qx_val ->
      Fp3_bounded Fp3_tight qy_val ->
      Fp3_bounded Fp3_tight qz_val ->
      (FElem_Fp6 a_f f_val *
       (FElem_Fp3 a_qx qx_val *
        (FElem_Fp3 a_qy qy_val *
         (FElem_Fp3 a_qz qz_val *
          (FElem_Fp3 a_r0d r0d *
           (FElem_Fp3 a_r1d r1d *
            (FElem_Fp3 a_r2d r2d *
             (FElem_Fp3 a_r0a r0a *
              (FElem_Fp3 a_r1a r1a *
               (FElem_Fp3 a_r2a r2a *
                (FElem_Fp6 a_line_d line_d *
                 (FElem_Fp6 a_line_a line_a *
                  (FElem_Fp6 pout old_out *
                   (FElem_Fp p_px p_x *
                    (FElem_Fp p_py p_y *
                     (FElem_Fp3 p_q0x q0x *
                      (FElem_Fp3 p_q0y q0y *
                       (FElem_Fp3 p_q1x q1x *
                        (FElem_Fp3 p_q1y q1y *
                         (FElem_Fp3 p_q0ny q0ny *
                          (FElem_Fp3 p_q1ny q1ny *
                           (FElem_Fp p_half half * Rr))))))))))))))))))))))%sep m ->
      Fp6_feval f_val = fp12_one bw6_761_field_ops ->
      Fp3_feval qx_val = Fp3_feval q1x ->
      Fp3_feval qy_val = Fp3_feval q1y ->
      miller_loop_inv_opt
        a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
        a_line_d a_line_a
        pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
        old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr
        188%nat tr m l.
  Proof.
    intros until l.
    intros Hbf Hbqx Hbqy Hbqz Hsep Hf_one Hqx_eq Hqy_eq.
    unfold miller_loop_inv_opt.
    split; [reflexivity |].
    split; [lia |].
    exists f_val, qx_val, qy_val, qz_val,
           r0d, r1d, r2d, r0a, r1a, r2a,
           line_d, line_a.
    split; [exact Hbf |].
    split; [exact Hbqx |].
    split; [exact Hbqy |].
    split; [exact Hbqz |].
    split; [exact Hsep |].
    replace (188 - 188)%nat with 0%nat by lia.
    apply multibase_state_at_zero; assumption.
  Qed.

  (* ================================================================ *)
  (* Sub-lemma 2 (Step): per-iteration invariant preservation.         *)
  (*                                                                  *)
  (* TODO Phase 2 Step 5 (sister agent): for each [v ∈ {1,...,187}]   *)
  (* the unrolled body fragment [miller_iter_body (bw6_alphabet v)]   *)
  (* takes the invariant from measure [v] to measure [v - 1].         *)
  (*                                                                  *)
  (* Closing this requires walking the per-iteration WP through:      *)
  (*   - 1 × fp6_sqr (f := f²)                                        *)
  (*   - 1 × g2_double_step (T := 2T, line coeffs r0d/r1d/r2d)         *)
  (*   - 1 × sparse_line_eval (line_d := sparse(r0d, r1d, r2d, P))     *)
  (*   - 1 × fp6_mul (f := f × line_d)                                 *)
  (* and, when [bw6_alphabet v ≠ 0] (a non-zero NAF digit), also:     *)
  (*   - 1 × g2_add_step against the appropriate (q0/q0Neg/q1/q1Neg)  *)
  (*   - 1 × sparse_line_eval (line_a)                                 *)
  (*   - 1 × fp6_mul (f := f × line_a)                                 *)
  (* and then deriving the Gallina-level invariant transition from    *)
  (* [multibase_state_at k …] to [multibase_state_at (k+1) …] via     *)
  (* [multibase_iter_step_j0] / [_j1] / [_jm1] / [_j3] / [_jm3] as    *)
  (* applicable.                                                       *)
  (*                                                                  *)
  (* Sister agent (a1444e31d54a30e0c) is fixing the Rust extraction   *)
  (* path that feeds the per-call WP bridging lemmas — once that      *)
  (* lands, the per-call WP discharges should be drop-in.             *)
  (* ================================================================ *)

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

  (* ================================================================ *)
  (* Sub-lemma 3 (Exit): the final-adjustment fragment converts the    *)
  (* post-main-loop state into the full optimal-ate output.             *)
  (* ================================================================ *)

  Lemma miller_loop_inv_opt_exit :
    forall (Px Py : Fp)
           (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp3)
           (f : Fp6) (Tx Ty : Fp3),
      multibase_state_at 188%nat
        Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
        f Tx Ty ->
      let f_final :=
        affine_miller_5symbol_final_adjustment bw6_761_field_ops
          f Tx Ty Px Py
          Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      in
      f_final =
        affine_miller_optimal_ate bw6_761_field_ops
          188%nat bw6_alphabet Px Py
          Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg.
  Proof.
    intros Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
           f Tx Ty Hinv f_final.
    unfold multibase_state_at in Hinv.
    unfold f_final.
    (* Use [remember] (vs original [destruct ... eqn:]) + [Strategy 0]
       at the top of the file: keeps the 188-step fixpoint opaque
       during kernel conversion (per
       reference_qed_kernel_check_blowup_dealloc.md). *)
    cbv beta delta [affine_miller_optimal_ate affine_miller_5symbol].
    remember (affine_miller_5symbol_aux bw6_761_field_ops bw6_alphabet
                188 Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
                (fp12_one bw6_761_field_ops) Qx Qy)
      as triple eqn:Heq.
    destruct triple as [[f' Tx'] Ty'].
    cbn [fst snd] in Hinv.
    destruct Hinv as [Hf [HTx HTy]]; subst.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* Main theorem.                                                     *)
  (*                                                                  *)
  (* Currently [Admitted] because closing it requires:                 *)
  (*   - the per-iteration Step lemma [miller_loop_body_step_opt]     *)
  (*     (LEFT Admitted above, Phase 2 Step 5), and                    *)
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
         By [miller_loop_inv_opt_init] + the per-call WP, the
         invariant holds at v = 188 immediately after the init
         fragment.

       Phase C: 187 iterations of [miller_loop_body_step_opt]
         (currently Admitted, Phase 2 Step 5).  After 187 step
         applications, invariant holds at v = 1.  (The unrolled
         body's last "main loop" iteration is [bw6_alphabet 1].)

       Phase D: [miller_iter_final] (i = 0).  By the per-call WP
         plus [miller_loop_inv_opt_exit], the running f equals
         [affine_miller_optimal_ate ops 188 bw6_alphabet …].

       Phase E: [fp6_copy out f] + 12-level stack dealloc, output
         postcondition.

       Currently Admitted because Phase C depends on the Step lemma
       (Admitted) and Phases B+D depend on per-call WP bridging
       lemmas that are sister-agent territory. *)
  Admitted.

End BW6_761_MillerLoopOptimal_Proof.
