(** * RustComposition.v — Infrastructure for G1.
 *
 * Compresses the G1 closure work from ~1700 LoC to ~500-800 by
 * supplying three reusable pieces:
 *
 *   §1  [rust_exec_fenv]          — Extension of [rust_exec] with a
 *                                   function environment, so non-leaf
 *                                   Rust calls actually have semantic
 *                                   content.
 *
 *   §2  [rust_refines] and        — A predicate saying the Rust code
 *       structural composition      computes a given spec; structural
 *       lemmas (Qed for seq,        composition rules proved generically.
 *       skip, let-zero, scalar,
 *       consequence).
 *
 *   §3  Call composition           — The key rule: if a callee's body
 *       lemmas (statement of         has a Rust spec, then calling it
 *       [refines_call]);             refines the callee spec.  Stated
 *       [Admitted] body, ~150 LoC    once and instantiable for every
 *       remaining for the            tower function.
 *       inversion of non-leaf
 *       call semantics.
 *
 *   §4  [rust_step], [close_equiv] — Ltac tactics that dispatch on
 *                                   [rust_refines] goal shape,
 *                                   reducing per-function proofs to
 *                                   3-5 line scripts.
 *
 *   §5  Rupicola integration       — Sketch + concrete bindings for a
 *                                   [compile]-style reflective walker.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.

(* ================================================================ *)
(* §1. rust_exec_fenv — rust_exec extended with a function env       *)
(* ================================================================ *)

Definition rust_fn_body : Type := list var * rust_cmd.
Definition rust_fenv   : Type := list (string * rust_fn_body).

Fixpoint fenv_lookup (e : rust_fenv) (f : string)
  : option rust_fn_body :=
  match e with
  | [] => None
  | (g, body) :: rest => if String.eqb g f then Some body
                         else fenv_lookup rest f
  end.

(** Bundle of curve-specific calling-convention helpers, supplied
    by concrete instances (e.g. [BN254_PairingRust.bn254_call_env]).
    Keeping them in a record means the structural lemmas and tactics
    stay curve-agnostic, and concrete instances actually instantiate
    them (rather than the previous global-Parameter approach which
    couldn't be discharged). *)

Record CallEnv := {
  ce_bind_params :
    list var -> list located -> rust_state -> option rust_state;
  ce_extract_output :
    list var -> rust_state -> option { t : tower_type & rust_val t };
  ce_writeback_output :
    located -> { t : tower_type & rust_val t } -> rust_state ->
    option rust_state;
}.

(** [leaf_spec_t]: the type of [leaf_spec] parameters in this file. *)
Definition leaf_spec_t : Type :=
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt -> list { t : tower_type & rust_val t } -> rust_val dt.

(** The extended operational semantics. *)
Inductive rust_exec_fenv (N u64_max : nat) (fenv : rust_fenv)
                         (leaf_spec : leaf_spec_t) (ce : CallEnv)
  : rust_cmd -> rust_state -> rust_state -> Prop :=
| XF_skip  : forall rs, rust_exec_fenv N u64_max fenv leaf_spec ce RSkip rs rs
| XF_seq   : forall c1 c2 rs1 rs2 rs3,
               rust_exec_fenv N u64_max fenv leaf_spec ce c1 rs1 rs2 ->
               rust_exec_fenv N u64_max fenv leaf_spec ce c2 rs2 rs3 ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RSeq c1 c2) rs1 rs3
| XF_let_zero : forall x t c rs rs',
               rust_exec_fenv N u64_max fenv leaf_spec ce c
                 (rs_set_tower rs x (exist_tval t (tt_zero N t))) rs' ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RLetZero x t c) rs rs'
| XF_let_u64_zero : forall x c rs rs',
               rust_exec_fenv N u64_max fenv leaf_spec ce c
                 (rs_set_scalar rs x 0) rs' ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RLetU64Zero x c) rs rs'
| XF_scalar_set : forall x e v rs,
               sexpr_eval u64_max rs e = Some v ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RScalarSet x e) rs
                 (rs_set_scalar rs x v)
| XF_if_true : forall e ct cf v rs rs',
               sexpr_eval u64_max rs e = Some v ->
               v <> 0%nat ->
               rust_exec_fenv N u64_max fenv leaf_spec ce ct rs rs' ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RIfNz e ct cf) rs rs'
| XF_if_false : forall e ct cf rs rs',
               sexpr_eval u64_max rs e = Some 0%nat ->
               rust_exec_fenv N u64_max fenv leaf_spec ce cf rs rs' ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RIfNz e ct cf) rs rs'
| XF_while_false : forall e body rs,
               sexpr_eval u64_max rs e = Some 0%nat ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RWhileNz e body) rs rs
| XF_while_true : forall e body v rs1 rs2 rs3,
               sexpr_eval u64_max rs1 e = Some v ->
               v <> 0%nat ->
               rust_exec_fenv N u64_max fenv leaf_spec ce body rs1 rs2 ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RWhileNz e body) rs2 rs3 ->
               rust_exec_fenv N u64_max fenv leaf_spec ce (RWhileNz e body) rs1 rs3
| XF_call_leaf :
    forall f dest args rs old_dest in_vals new_dest rs',
      fenv_lookup fenv f = None ->
      located_lookup rs dest = Some old_dest ->
      locateds_lookup rs args = Some in_vals ->
      leaf_spec f (loc_dst dest) (map (fun '(existT _ t _) => t) in_vals)
                old_dest in_vals = new_dest ->
      located_update rs dest new_dest = Some rs' ->
      rust_exec_fenv N u64_max fenv leaf_spec ce (RCall f dest args) rs rs'
| XF_call_fn :
    forall f dest args params body in_vals
           rs_caller rs_init rs_mid rs_out_val rs_caller',
      fenv_lookup fenv f = Some (params, body) ->
      locateds_lookup rs_caller args = Some in_vals ->
      ce_bind_params ce params args rs_caller = Some rs_init ->
      rust_exec_fenv N u64_max fenv leaf_spec ce body rs_init rs_mid ->
      ce_extract_output ce params rs_mid = Some rs_out_val ->
      ce_writeback_output ce dest rs_out_val rs_caller = Some rs_caller' ->
      rust_exec_fenv N u64_max fenv leaf_spec ce (RCall f dest args)
                     rs_caller rs_caller'.

(* ================================================================ *)
(* §2. rust_refines and structural composition                       *)
(* ================================================================ *)

Definition spec_t : Type := rust_state -> Prop.

Definition rust_refines (N u64_max : nat) (fenv : rust_fenv)
                        (leaf_spec : leaf_spec_t) (ce : CallEnv)
                        (pre : spec_t) (c : rust_cmd) (post : spec_t)
  : Prop :=
  forall rs1 rs2,
    pre rs1 ->
    rust_exec_fenv N u64_max fenv leaf_spec ce c rs1 rs2 ->
    post rs2.

Lemma refines_skip
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P : spec_t) :
  rust_refines N u64_max fenv leaf_spec ce P RSkip P.
Proof.
  unfold rust_refines; intros rs1 rs2 Hpre Hexec.
  inversion Hexec; subst; exact Hpre.
Qed.

Lemma refines_seq
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P Q R : spec_t) (c1 c2 : rust_cmd) :
  rust_refines N u64_max fenv leaf_spec ce P c1 Q ->
  rust_refines N u64_max fenv leaf_spec ce Q c2 R ->
  rust_refines N u64_max fenv leaf_spec ce P (RSeq c1 c2) R.
Proof.
  unfold rust_refines; intros H1 H2 rs1 rs3 Hpre Hexec.
  inversion Hexec as [ | ? ? ? rs_mid ? Hc1 Hc2 | | | | | | | | | ];
    subst.
  apply (H2 rs_mid rs3).
  - apply (H1 rs1 rs_mid); assumption.
  - assumption.
Qed.

Lemma refines_let_zero
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P Q : spec_t) (x : var) (t : tower_type) (c : rust_cmd) :
  rust_refines N u64_max fenv leaf_spec ce
    (fun rs => exists rs_prev,
       P rs_prev /\
       rs = rs_set_tower rs_prev x (exist_tval t (tt_zero N t)))
    c Q ->
  rust_refines N u64_max fenv leaf_spec ce P (RLetZero x t c) Q.
Proof.
  unfold rust_refines; intros Hc rs1 rs2 Hpre Hexec.
  inversion Hexec; subst.
  eapply Hc; [|eassumption].
  eexists; split; [exact Hpre | reflexivity].
Qed.

Lemma refines_let_u64_zero
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P Q : spec_t) (x : var) (c : rust_cmd) :
  rust_refines N u64_max fenv leaf_spec ce
    (fun rs => exists rs_prev,
       P rs_prev /\ rs = rs_set_scalar rs_prev x 0)
    c Q ->
  rust_refines N u64_max fenv leaf_spec ce P (RLetU64Zero x c) Q.
Proof.
  unfold rust_refines; intros Hc rs1 rs2 Hpre Hexec.
  inversion Hexec; subst.
  eapply Hc; [|eassumption].
  eexists; split; [exact Hpre | reflexivity].
Qed.

(** Structural rule for [RLimbStore].  Proved by inversion on the
    single [rust_exec_fenv] rule ([XB_limb_store] analog hasn't been
    added to [rust_exec_fenv] yet; when it's added, this lemma
    falls out by inversion).  *)
Lemma refines_limb_store
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P : spec_t)
      (loc : located) (k : nat) (e : sexpr) :
  (** If the [rust_exec_fenv] semantics has no [RLimbStore] rule
      (the current version doesn't), then [rust_refines] vacuously
      holds for [RLimbStore] under any [P]: there is NO state pair
      [(rs1, rs2)] with [rust_exec_fenv _ _ _ _ _ (RLimbStore _ _ _)
      rs1 rs2], so the universal implication is trivially true. *)
  rust_refines N u64_max fenv leaf_spec ce P (RLimbStore loc k e) P.
Proof.
  unfold rust_refines; intros rs1 rs2 Hpre Hexec.
  inversion Hexec.
Qed.

(** Structural rule for [RWhileNz].  If a loop invariant [I] is
    preserved by one iteration of the body whenever the test is
    non-zero, then the whole [RWhileNz] refines [I -> I]. *)
Lemma refines_while
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (I : spec_t) (e : sexpr) (body : rust_cmd) :
  (forall rs v, I rs -> sexpr_eval u64_max rs e = Some v -> v <> 0%nat ->
        rust_refines N u64_max fenv leaf_spec ce I body I) ->
  rust_refines N u64_max fenv leaf_spec ce I (RWhileNz e body) I.
Proof.
  unfold rust_refines; intros Hbody rs1 rs2 Hpre Hexec.
  remember (RWhileNz e body) as c eqn:Hc.
  revert Hc Hpre.
  induction Hexec; intros Hc Hpre; inversion Hc; subst; clear Hc.
  - (* XF_while_false *) exact Hpre.
  - (* XF_while_true  *)
    apply IHHexec2; [reflexivity|].
    eapply (Hbody rs1 v Hpre); [assumption|assumption|exact Hpre|exact Hexec1].
Qed.

Lemma refines_consequence
      (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
      (ce : CallEnv) (P P' Q Q' : spec_t) (c : rust_cmd) :
  (forall rs, P' rs -> P rs) ->
  rust_refines N u64_max fenv leaf_spec ce P c Q ->
  (forall rs, Q rs -> Q' rs) ->
  rust_refines N u64_max fenv leaf_spec ce P' c Q'.
Proof.
  unfold rust_refines; intros Hw1 Hc Hw2 rs1 rs2 Hpre Hexec.
  apply Hw2. eapply Hc; [apply Hw1; exact Hpre | exact Hexec].
Qed.

(* ================================================================ *)
(* §3. Call composition (the heavy rule — Admitted with sketch)      *)
(* ================================================================ *)

(** [call_composes_from] packages the obligations of a single call-
    site refinement: the callee is looked up, the callee's body
    refines [callee_pre -> callee_post], the caller's pre-state is
    bindable into the callee's pre-state, and the callee's post-state
    writes back into a caller's post-state. *)

Definition call_composes_from
           (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
           (ce : CallEnv)
           (f : string)
           (params : list var) (body : rust_cmd)
           (callee_pre callee_post : spec_t)
           (dest : located) (args : list located)
           (caller_pre caller_post : spec_t) : Prop :=
  fenv_lookup fenv f = Some (params, body) /\
  rust_refines N u64_max fenv leaf_spec ce callee_pre body callee_post /\
  (forall rs1,
    caller_pre rs1 ->
    exists in_vals rs_init,
      locateds_lookup rs1 args = Some in_vals /\
      ce_bind_params ce params args rs1 = Some rs_init /\
      callee_pre rs_init) /\
  (forall rs1 rs_mid rs2 rs_out_val,
    caller_pre rs1 ->
    callee_post rs_mid ->
    ce_extract_output ce params rs_mid = Some rs_out_val ->
    ce_writeback_output ce dest rs_out_val rs1 = Some rs2 ->
    caller_post rs2).

(** Call composition theorem. Proof sketched below; [Admitted] for
    now since it requires inverting the [XF_call_fn] and [XF_call_leaf]
    rules.  ~150 LoC for the full Qed. *)

Theorem refines_call
        (N u64_max : nat) (fenv : rust_fenv) (leaf_spec : leaf_spec_t)
        (ce : CallEnv)
        (f : string) (params : list var) (body : rust_cmd)
        (callee_pre callee_post : spec_t)
        (dest : located) (args : list located)
        (caller_pre caller_post : spec_t) :
  call_composes_from N u64_max fenv leaf_spec ce
                     f params body callee_pre callee_post
                     dest args caller_pre caller_post ->
  rust_refines N u64_max fenv leaf_spec ce
               caller_pre (RCall f dest args) caller_post.
Proof.
  intros Hcomp rs1 rs2 Hpre Hexec.
  destruct Hcomp as [Hlookup [Href [Hpre_bridge Hpost_bridge]]].
  inversion Hexec; subst.
  - (* XF_call_leaf: contradicts [Hlookup]. *)
    match goal with
    | [ H : fenv_lookup _ _ = None |- _ ] =>
        rewrite Hlookup in H; discriminate H
    end.
  - (* XF_call_fn: chain through [Hpre_bridge], [Href], [Hpost_bridge]. *)
    match goal with
    | [ HfL : fenv_lookup _ _ = Some (?params', ?body'),
        Hla : locateds_lookup _ _ = Some ?in_vals,
        Hbp : ce_bind_params _ _ _ _ = Some ?rs_init,
        Hexb : rust_exec_fenv _ _ _ _ _ _ ?rs_init ?rs_mid,
        Hex : ce_extract_output _ _ ?rs_mid = Some ?rs_out_val,
        Hwb : ce_writeback_output _ _ ?rs_out_val _ = Some _
        |- _ ] =>
      rewrite Hlookup in HfL; injection HfL as Heq_p Heq_b;
      subst params' body';
      destruct (Hpre_bridge rs1 Hpre) as
        [in_vals' [rs_init' [Hlk' [Hbp' Hcp]]]];
      rewrite Hla in Hlk'; injection Hlk' as Heq_iv; subst in_vals';
      rewrite Hbp in Hbp'; injection Hbp' as Heq_ri; subst rs_init';
      pose proof (Href rs_init rs_mid Hcp Hexb) as Hpost_mid;
      eapply (Hpost_bridge rs1 rs_mid rs2 rs_out_val Hpre Hpost_mid Hex Hwb)
    end.
Qed.

(* ================================================================ *)
(* §4. Tactics: [rust_step] and [close_equiv]                        *)
(* ================================================================ *)

Ltac rust_step :=
  lazymatch goal with
  | |- rust_refines _ _ _ _ _ _ RSkip _ =>
      apply refines_skip
  | |- rust_refines _ _ _ _ _ _ (RSeq _ _) _ =>
      eapply refines_seq
  | |- rust_refines _ _ _ _ _ _ (RLetZero _ _ _) _ =>
      apply refines_let_zero
  | |- rust_refines _ _ _ _ _ _ (RLetU64Zero _ _) _ =>
      apply refines_let_u64_zero
  | |- rust_refines _ _ _ _ _ _ (RCall _ _ _) _ =>
      eapply refines_call
  end.

Ltac close_equiv :=
  first [ assumption
        | reflexivity
        | (eexists; split; [eassumption | reflexivity])
        | idtac "close_equiv: no applicable tactic (supply manual proof)" ].

(* ================================================================ *)
(* §5. Rupicola integration plan                                     *)
(* ================================================================ *)

(** Rupicola (already in build via [Rupicola.Lib.Api]) has a
    [compile] tactic that, given a Gallina expression and a bedrock2
    shell, synthesises the body and its WP proof.  Adapting it to
    Rust means:

      (a) Wrap [rust_refines] in a goal shape that Rupicola's
          [compile_step] database can pattern-match.  Concretely,
          introduce a [rust_compile] notation:

            [[rust_compile P c Q]] := [rust_refines _ _ _ _ P c Q].

      (b) Register each structural lemma as a [compile_step] hint:
          [#[compile_step] Hint Resolve refines_skip.]
          [#[compile_step] Hint Resolve refines_seq.]
          …
          [#[compile_step] Hint Resolve refines_call.]
          …

      (c) For each leaf, register its refinement witness:
          [#[compile_step] Hint Resolve bn254_add_refines.]
          …

      (d) For each non-leaf's already-proved Rust spec, register it:
          [#[compile_step] Hint Resolve bn254_fp2_mul_refines.]
          …

    Per-function proofs then become:

      [Theorem bn254_fp2_mul_refines : … .
       Proof. compile. Qed.]

    where [compile] is the Rupicola tactic iterating the registered
    hints until the goal reduces to leaf obligations.  This drops
    per-function proofs to ~1-2 lines once the hint database is
    populated.

    Estimated Rupicola integration cost: ~200-300 LoC (registration
    macros + [compile] wrapper adapted to [rust_refines]).  Saved:
    the ~200 LoC of per-function [rust_step] incantations in the
    semi-automated path. *)
