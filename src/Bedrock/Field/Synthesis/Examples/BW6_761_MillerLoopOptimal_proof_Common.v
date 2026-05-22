(** * BW6-761 Optimal-Ate Miller Loop — Common scaffold.

    Shared header for the [BW6_761_MillerLoopOptimal_proof_*]
    family: imports, Strategy directives, [Existing Instances],
    Local Notations, FieldOps instance, alphabet, strengthened
    spec, loop invariant, and the [multibase_state_at_zero] base
    case.

    Split out of the monolithic [BW6_761_MillerLoopOptimal_proof.v]
    so that each individual sub-file fits under the 5-minute build
    budget specified in [CLAUDE.md].  The full file's import load
    (Rupicola + 882-LoC [BW6_761_MillerLoopOptimal] + 384-LoC
    [AffineMultibase]) exceeded 8 minutes; this Common header takes
    the same import hit ONCE and downstream Init/Step/Exit/main
    files only need to load Common.

    Build-time finding (2026-05-22): empirical cold-build wall
    time of this file is 704 s, with every per-sentence tactic
    measuring 0.0 s under `-time`.  The entire wall budget is
    spent loading [Rupicola.Lib.Api] + bedrock2 + the
    [PrimeFieldTheorems] ring machinery.  Removing the
    [AffineMultibase] import alone (the planned Module-Type
    refactor) would NOT bring this under the 5-min CLAUDE.md
    budget — [AffineMultibase] is only 384 LoC of Gallina, and
    none of the heavy load is attributable to it.  The Common
    header therefore stays as-is; downstream Step/main files
    remain build-excluded.

    STATUS: scaffolding only — see the [_proof.v] file for the main
    theorem statement and Phase-2 Step-5 TODO documentation. *)

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
(** Intentionally NOT importing [BW6_761_MillerLoopOptimal] here:
    its .vo load (882 LoC of fully-unrolled bedrock2 commands)
    dominates this file's compile time (per the
    [reference_mcp_timeout_heavy_imports.md] pattern).  We re-tabulate
    [bw6_j_seq] locally as [bw6_j_seq_loc] — the two are
    definitionally equal but distinct names, so downstream users
    that need the bridge can prove [bw6_j_seq_loc =
    BW6_761_MillerLoopOptimal.bw6_j_seq] by [reflexivity] in their
    own file. *)
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.AffineMultibase.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BW6 5-symbol alphabet.                                            *)
(*                                                                  *)
(* Defined at TOP LEVEL (outside Section) so it can be referenced   *)
(* from the strengthened spec and the loop invariant without        *)
(* dragging in section variables.                                   *)
(* ================================================================ *)

(** Local copy of [BW6_761_MillerLoopOptimal.bw6_j_seq] — a
    pre-tabulation of j[i] = LoopCounter1[i]*3 + LoopCounter[i] ∈
    {-3, -1, 0, 1, 3} for i = 0..188 (189 entries, BW6-761 seed).
    Inlined here to avoid importing the 882-LoC unrolled
    [BW6_761_MillerLoopOptimal] body at this scaffold layer. *)
Definition bw6_j_seq_loc : list Z := [
  -3;  1;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0; -1;  0;  1;  0;
   0;  1;  0;  0;  0;  0;  1;  0;  1;  0;
   0;  0;  0;  1;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
   0;  0;  0;  3;  0;  0;  3;  0;  0; -3;
   0;  3;  0; -3;  0;  0;  0;  0; -3;  0;
   3;  0;  0;  0;  3;  0;  0;  0;  3;  0;
   0;  3;  0;  3;  0;  0;  0;  3;  0;  0;
   0;  0;  0;  0;  0;  0;  0;  0; -3;  0;
  -3;  0;  0;  0;  0; -3;  0;  0;  3;  0;
   0;  0; -3;  0;  0; -3;  0;  3;  0; -3;
   0;  0;  0;  3;  0;  0;  3;  0; -3;  0;
   3;  0;  3;  0;  0;  0;  3;  0; -3;  0;
  -3;  0;  0;  0;  0;  0;  3;  0;  0
].

(** Lookup with default 0 (covers out-of-range indices, which are
    unreachable in the BW6 loop). *)
Definition bw6_alphabet (i : nat) : Z :=
  nth i bw6_j_seq_loc 0%Z.

(** Sanity: list length 189 — accepts all main-loop indices. *)
Lemma bw6_j_seq_length : length bw6_j_seq_loc = 189%nat.
Proof. reflexivity. Qed.

Section BW6_761_MillerLoopOptimal_Common.

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
  (* ================================================================ *)

  (** [fp3_mul_fp]: scalar-multiply an Fp3 by an Fp element. *)
  Definition bw6_fp3_mul_fp (x : Fp3) (s : Fp) : Fp3 :=
    let '(a, b, c) := x in
    (F.mul a s, F.mul b s, F.mul c s).

  (** Abstract make_line: free parameter of the reference model. *)
  Definition bw6_make_line_abstract (lam Tx Ty : Fp3) (Px Py : Fp) : Fp6 :=
    @AbstractField.Fone _ bw6_Fp6_params.

  (** Canonical [FieldOps] instance for BW6's tower.  Slot mapping:
        Fp_*    -> Fp
        Fp2_*   -> Fp3
        Fp12_*  -> Fp6 *)
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
  (* ================================================================ *)

  (** Gallina-level invariant tying [(f, T)] to the multibase aux.
      Match-on-[k] so the [k = 0] base case reduces directly to
      a simple conjunction without forcing the kernel to walk
      [affine_miller_5symbol_aux ... 0 ...]'s let-binding. *)
  Definition multibase_state_at
    (k : nat)
    (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp3)
    (f : Fp6) (Tx Ty : Fp3) : Prop :=
    match k with
    | O => f = fp12_one bw6_761_field_ops /\ Tx = Qx /\ Ty = Qy
    | S _ =>
        let result :=
          affine_miller_5symbol_aux bw6_761_field_ops
            bw6_alphabet k Px Py
            Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
            (fp12_one bw6_761_field_ops) Qx Qy
        in
        fst (fst result) = f /\ snd (fst result) = Tx /\ snd result = Ty
    end.

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
  (* Base-case: invariant at k = 0.                                   *)
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
    (* With [multibase_state_at] now match-on-k, the iter-0 case
       unfolds directly to [f = fp12_one ... /\ Tx = Qx /\ Ty = Qy]. *)
    simpl. auto.
  Qed.

  (* ================================================================ *)
  (* Sub-lemma 1 (Init): the invariant holds at [v = 188] under the   *)
  (* initial seeding (running f := 1, T := q1).                        *)
  (*                                                                  *)
  (* Folded into Common (rather than its own file) because per-file   *)
  (* re-imports of the heavy Rupicola + bedrock2 chain dominate       *)
  (* compile time; bundling here keeps total split-build wall-clock   *)
  (* under the 5-min budget. *)
  (* ================================================================ *)

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
      Fp3_feval qx_val = Fp3_feval q0x ->
      Fp3_feval qy_val = Fp3_feval q0y ->
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
    change (188 - 188)%nat with 0%nat.
    (* [cbn in <hyp>] aligns [Fp6_feval] / [Fp3_feval] (BW6 notations)
       with [QE_feval] / [CE_feval] (the generic names in the goal
       after [simpl]).  Without this, [exact] / [apply] forces
       conversion through typeclass projections — minutes-long hang. *)
    simpl.
    cbn in Hf_one, Hqx_eq, Hqy_eq.
    split; [exact Hf_one |].
    split; [exact Hqx_eq | exact Hqy_eq].
  Qed.

  (* ================================================================ *)
  (* Sub-lemma 3 (Exit): the final-adjustment fragment converts the   *)
  (* post-main-loop state into the full optimal-ate output.            *)
  (* ================================================================ *)

  (** Exit lemma: the final-adjustment fragment converts the post-
      main-loop state into the full optimal-ate output. *)
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
    (* Use [remember] + [Strategy 0] at the top of this file to keep
       the 188-step fixpoint opaque during kernel conversion (per
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

End BW6_761_MillerLoopOptimal_Common.
