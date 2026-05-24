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

    Build note: this file's cold-build time (~11 min) is spent
    almost entirely loading [Rupicola.Lib.Api] + bedrock2 + the
    [PrimeFieldTheorems] ring machinery; the per-sentence tactic
    cost is negligible.  Removing the [AffineMultibase] import
    alone (the planned Module-Type refactor) would NOT bring this
    under the 5-min CLAUDE.md budget — [AffineMultibase] is only
    384 LoC of Gallina, and none of the heavy load is attributable
    to it.  The Common header therefore stays as-is; downstream
    Step/main files remain build-excluded.

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
Require Import Bedrock.Field.PairingTheory.ProjectiveMultibase.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_ProjOps.

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
  (* Main-loop digit list (the bedrock emit_iters argument).          *)
  (* ================================================================ *)

  (** The 187 main-loop digits j[187],...,j[1] processed by emit_iters
      between the i=188 init and the i=0 final adjustment.  Equal to the
      bedrock [bw6_main_loop_js] (= rev (tl (removelast bw6_j_seq))),
      stated here over the local copy [bw6_j_seq_loc].  The projective
      FieldOps + per-step models live in [BW6_761_ProjOps]. *)
  Definition bw6_main_loop_js_loc : list Z :=
    List.rev (List.tl (List.removelast bw6_j_seq_loc)).

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
          (* The output Fp6 value equals the projective whole-body model
             (faithful to [miller_loop_optimal_body]: seed q1 -> i=188
             init -> main loop over [bw6_main_loop_js_loc] -> i=0 final
             adjustment). *)
          Fp6_feval out =
            bw6_proj_whole_body bw6_main_loop_js_loc
              (Fp_feval p_x) (Fp_feval p_y)
              (Fp3_feval q0x) (Fp3_feval q0y)
              (Fp3_feval q1x) (Fp3_feval q1y)
              (Fp3_feval q0ny) (Fp3_feval q1ny)
              (Fp_feval half) }.

  (* ================================================================ *)
  (* Loop running-state relation (projective model).                  *)
  (* ================================================================ *)

  (** [proj_running ... fv Tx Ty Tz t m l]: the stack buffers hold a
      well-bounded Fp6/Fp3 layout whose fevals are exactly the Gallina
      state (running f = [fv], projective point T = (Tx,Ty,Tz)).  The
      main loop ([emit_iters]) is proved by induction on the digit list,
      advancing this by one [bw6_proj_multibase_iter] per
      [miller_iter_body]; init / final-adjustment bracket it.  The
      Gallina state is carried as explicit parameters (no [v <= 188]
      bound, no [multibase_state_at]). *)
  Definition proj_running
    (a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
     a_line_d a_line_a : word)
    (pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half : word)
    (old_out : Fp6_felem)
    (p_x p_y : Fp_felem)
    (q0x q0y q1x q1y q0ny q1ny : Fp3_felem) (half : Fp_felem)
    (Rr : mem -> Prop) (tr : Semantics.trace)
    (fv : Fp6) (Tx Ty Tz : Fp3)
    (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\
    (* Input-buffer bounds the callees require; invariant (never
       mutated): p_x/p_y for sparse_line, half for double_step, the
       affine targets q0x..q1ny for add_step. *)
    Fp_bounded Fp_loose p_x /\
    Fp_bounded Fp_loose p_y /\
    Fp_bounded Fp_tight half /\
    Fp3_bounded Fp3_tight q0x /\
    Fp3_bounded Fp3_tight q0y /\
    Fp3_bounded Fp3_tight q1x /\
    Fp3_bounded Fp3_tight q1y /\
    Fp3_bounded Fp3_tight q0ny /\
    Fp3_bounded Fp3_tight q1ny /\
    exists (f_val : Fp6_felem)
           (qx_val qy_val qz_val
            r0d_val r1d_val r2d_val
            r0a_val r1a_val r2a_val : Fp3_felem)
           (line_d_val line_a_val : Fp6_felem),
      Fp6_bounded Fp6_loose f_val /\
      Fp3_bounded Fp3_loose qx_val /\
      Fp3_bounded Fp3_loose qy_val /\
      Fp3_bounded Fp3_loose qz_val /\
      Fp6_feval f_val = fv /\
      Fp3_feval qx_val = Tx /\
      Fp3_feval qy_val = Ty /\
      Fp3_feval qz_val = Tz /\
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
                           (FElem_Fp p_half half * Rr))))))))))))))))))))))%sep m.

End BW6_761_MillerLoopOptimal_Common.
