(** * InlineCallFn: Body-inlining pass for [REdCallFn] sites
 *
 * Companion to [SafeRustEd25519Sim.v].  Defines a structural transformation
 * over [rust_cmd_ed] that replaces every [REdCallFn fname dst args] callsite
 * with [body dst args] looked up in a [function_table_ed].
 *
 * Purpose: per the whole-protocol Jasmin emission plan
 * (docs/whole-protocol-jasmin-plan.md, Blocker 2), the [REdCallFn] sites in
 * Ed25519 protocol bodies currently become Jasmin [call] instructions when
 * extracted via [RustCmdEdToRealJasmin].  Each [call] introduces a calling-
 * convention boundary that defeats Jasmin's register allocator across the
 * full sign / verify body.  Inlining the bodies BEFORE extraction yields a
 * single straight-line Jasmin program that jasminc can register-allocate
 * end-to-end.
 *
 * Design (one-shot inlining):
 *   - [inline_callfn_one] replaces TOP-LEVEL [REdCallFn] sites with their
 *     bodies once.  Calls nested inside the inlined body itself remain as
 *     [REdCallFn] (so they will be inlined on the next pass).
 *   - [inline_callfn_n] iterates [inline_callfn_one] a fixed number of times.
 *     For a callgraph of depth d, applying [inline_callfn_n d] eliminates
 *     all [REdCallFn] sites.  In Ed25519 sign / verify the depth is at most
 *     3 (sign → ed25519_scalarmult_base → fe25519_mul → leaf-ops), so
 *     [inline_callfn_n 4] suffices.
 *   - No fuel-as-fixpoint-counter is needed because the [function_table_ed]
 *     callgraph is assumed acyclic at every callsite we extract — leaf ops
 *     are FFI [REdCall], not [REdCallFn].
 *
 * Status (2026-05-13):
 *   - [inline_callfn_one] : DEFINED, well-typed, structural recursion.
 *   - [inline_callfn_n]   : DEFINED.
 *   - Forward soundness [inline_callfn_one_preserves_semantics_fwd] : Qed
 *     by induction on the [rust_exec_ed] derivation (4 tactics including
 *     [econstructor; eauto] for the structural cases and [rewrite; exact]
 *     for [rexec_callfn]).
 *   - Iterated forward soundness [inline_callfn_n_preserves_semantics_fwd]
 *     : Qed.  This is the direction the Jasmin extraction pipeline needs
 *     (lifts a spec [R c rs1 rs2] to [R (inline_n n ftab c) rs1 rs2]
 *     before extracting the inlined [c] to Jasmin).
 *   - Backward soundness [inline_callfn_one_preserves_semantics_bwd] :
 *     Qed, by induction on the derivation with [c] generalised.  The
 *     non-injectivity of inlining (a [c0] of the form [REdCallFn] with a
 *     Seq-producing body inlines to the same shape as a structural
 *     [REdSeq]) turns out not to obstruct it: in the call case the
 *     derivation in hand IS a derivation of [body dst args], so
 *     [rexec_callfn] closes the goal with no induction hypothesis.  What
 *     does obstruct a structural induction on [c] is [REdWhileNz] /
 *     [REdFor]; inducting on the derivation avoids that.
 *   - Consequently [inline_callfn_one_preserves_semantics] (iff) and
 *     [inline_callfn_n_preserves_semantics] are Qed with no admits.
 *   - 0 new global Rocq axioms, and no [Admitted] remains in this file.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.

Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. One-pass inlining                                             *)
(* ================================================================ *)

(** Replace each top-level [REdCallFn fname dst args] with
    [body dst args] when [fname] is bound in [ftab]; leave it
    untouched (it stays an [REdCallFn]) when the name is missing.
    Recurses through compound constructors so that ALL [REdCallFn]
    sites at any nesting depth are replaced.

    Note: the body returned by [function_body_ed] is itself a
    [rust_cmd_ed] which may contain further [REdCallFn] sites.
    [inline_callfn_one] does NOT recurse into the body it splices in
    — that's the job of a SECOND call (see [inline_callfn_n]).
    This keeps the recursion structural over the input [c]. *)
Fixpoint inline_callfn_one
  (ftab : function_table_ed) (c : rust_cmd_ed) : rust_cmd_ed :=
  match c with
  | REdSkip => REdSkip
  | REdSeq c1 c2 =>
      REdSeq (inline_callfn_one ftab c1) (inline_callfn_one ftab c2)
  | REdLetZero x t c' =>
      REdLetZero x t (inline_callfn_one ftab c')
  | REdLetU64 x e c' =>
      REdLetU64 x e (inline_callfn_one ftab c')
  | REdScalarSet x e => REdScalarSet x e
  | REdCall fname dst args => REdCall fname dst args
  | REdIfNz e c1 c2 =>
      REdIfNz e (inline_callfn_one ftab c1) (inline_callfn_one ftab c2)
  | REdWhileNz e c' => REdWhileNz e (inline_callfn_one ftab c')
  | REdByteStore loc i v => REdByteStore loc i v
  | REdByteLoad x loc i => REdByteLoad x loc i
  | REdFor x n body => REdFor x n (inline_callfn_one ftab body)
  | REdSelect c if_t if_f dst => REdSelect c if_t if_f dst
  | REdCallN fname dsts args => REdCallN fname dsts args
  | REdCallFn fname dst args =>
      match List.find (fun p => String.eqb (fst p) fname) ftab with
      | Some (_, body) => body dst args
      | None => REdCallFn fname dst args  (* leave unchanged *)
      end
  | REdBlock body => REdBlock (inline_callfn_one ftab body)
  | REdSetBytes loc bs => REdSetBytes loc bs
  | REdArrLoad dst src i => REdArrLoad dst src i
  | REdArrStore arr i src => REdArrStore arr i src
  | REdLimbStore loc i e => REdLimbStore loc i e
  end.

(** Iterate [inline_callfn_one] [n] times.  For a [function_table_ed]
    whose callgraph has depth at most [n] from any callsite to a leaf
    (FFI [REdCall] / inline-arith / etc.), [inline_callfn_n n ftab c]
    is [REdCallFn]-free.  We do NOT prove this here — it's a metaproperty
    of the specific [ftab] in use (Ed25519 sign / verify callgraph is
    depth <= 3 + 1 buffer = 4). *)
Fixpoint inline_callfn_n (n : nat) (ftab : function_table_ed) (c : rust_cmd_ed)
  : rust_cmd_ed :=
  match n with
  | O => c
  | S n' => inline_callfn_n n' ftab (inline_callfn_one ftab c)
  end.

(* ================================================================ *)
(* §2. Soundness                                                     *)
(* ================================================================ *)

Section Soundness.

(** Big-step soundness: the inlined command has the same execution
    behaviour as the original, w.r.t. [rust_exec_ed] under the SAME
    [function_table_ed].

    The proof goes by structural induction on [c] (or, equivalently,
    on the derivation of [rust_exec_ed _ _ _ c rs1 rs2]).  For the
    [REdCallFn] constructor:
      - If [find _ ftab = Some (_, body)], the inlined command is
        [body dst args].  In the original, [rexec_callfn] required
        [rust_exec_ed _ _ _ (body dst args) rs1 rs2] as a premise,
        which is exactly the inlined execution.  The reverse
        direction uses [rexec_callfn] directly.
      - If [find _ ftab = None], the original [rexec_callfn] rule is
        not applicable (there is no other rule for [REdCallFn]), so
        the execution relation is empty for that command.  The
        inlined command equals the original (we leave it as
        [REdCallFn]), so both relations are empty.

    Statement is two-directional but expressed as iff.  Downstream
    Jasmin extraction (which targets the inlined command's [rust_exec_ed]
    derivation) only needs the [<-] direction. *)
Variables (callee_post : String.string ->
                          list located_ed ->
                          located_ed ->
                          rust_state_ed ->
                          rust_state_ed ->
                          Prop)
          (callee_post_n : String.string ->
                            list located_ed ->
                            list located_ed ->
                            rust_state_ed ->
                            rust_state_ed ->
                            Prop)
          (ftab : function_table_ed).

Local Notation R := (rust_exec_ed callee_post callee_post_n ftab).

(** Soundness, one-pass.  Forward direction (original ⇒ inlined).

    Proof: by induction on the [R] derivation.
    - [rexec_skip], [rexec_call], [rexec_scalar_set], [rexec_byte_*],
      [rexec_select], [rexec_calln], [rexec_setbytes], [rexec_arr_*]:
      the inlining is the identity (after [simpl]), so [econstructor;
      eauto] re-applies the same rule.
    - [rexec_seq], [rexec_let_*], [rexec_if_*], [rexec_while_*],
      [rexec_for_*], [rexec_block]: apply the IH to subderivations and
      re-construct the rule via [econstructor; eauto].
    - [rexec_callfn]: the inlined form is [match find ftab fname with
      | Some (_, body) => body dst args | None => REdCallFn ...].
      The rule premise gives [find ftab fname = Some (fname, body)],
      so the match reduces to [body dst args].  The other rule premise
      [R (body dst args) rs1 rs2] is exactly the resulting goal. *)
Theorem inline_callfn_one_preserves_semantics_fwd :
  forall c rs1 rs2,
    R c rs1 rs2 ->
    R (inline_callfn_one ftab c) rs1 rs2.
Proof.
  intros c rs1 rs2 H. induction H; simpl; try (econstructor; eauto; fail).
  (* Only [rexec_callfn] left. *)
  rewrite H. exact H0.
Qed.

(** Soundness, one-pass.  Reverse direction (inlined ⇒ original).

    NOTE (2026-05-13): The BWD direction is NOT required for the
    extraction-pipeline use of [inline_callfn_one].  The pipeline is:

      [R c rs1 rs2]                                  -- user-supplied spec
        ⇒ [R (inline_callfn_one ftab c) rs1 rs2]    -- by FWD (Qed below)
        ⇒ Jasmin asm satisfies [R (inline ...)]     -- by Jasmin compiler

    The asm therefore satisfies the (inlined) spec.  Code that wants to
    re-express the asm-level spec in terms of the ORIGINAL [c] needs BWD,
    but typical clients prove their goal in the inlined form directly.

    The general BWD direction is also subtler than FWD: a [c0] with
    [c0 = REdCallFn fname dst args] whose [body dst args = REdSeq c1 c2]
    inlines to [REdSeq c1 c2], so a derivation of the inlined form does
    not pin down [c0]'s structure (it could be [REdSeq c1 c2] OR
    [REdCallFn] of a Seq-producing body).  A specialised BWD for a
    concrete [ftab] (e.g. [ed25519_function_table]) avoids this by
    case-analysis on the table's entries; we defer that to a per-table
    lemma where it's actually needed. *)
(** The [REdCallFn] case of BWD.  Non-injectivity of inlining is not an
    obstacle here: when [c0] is a call, the derivation in hand IS a
    derivation of [body dst args], so [rexec_callfn] applies directly and
    no induction hypothesis is needed. *)
Lemma inline_callfn_bwd_callfn :
  forall fname dst args rs1 rs2,
    R (inline_callfn_one ftab (REdCallFn fname dst args)) rs1 rs2 ->
    R (REdCallFn fname dst args) rs1 rs2.
Proof.
  intros fname dst args rs1 rs2 H. simpl in H.
  destruct (List.find (fun p => String.eqb (fst p) fname) ftab) as [[nm body]|] eqn:Hf.
  - assert (Hnm : nm = fname).
    { apply List.find_some in Hf. destruct Hf as [_ Heq]. simpl in Heq.
      apply String.eqb_eq in Heq. exact Heq. }
    subst nm. eapply rexec_callfn; [ exact Hf | exact H ].
  - exact H.
Qed.

(** Soundness, backward.  Structural induction on [c] fails for
    [REdWhileNz] / [REdFor]; inducting on the derivation with [c]
    generalised is what makes it go through. *)
Theorem inline_callfn_one_preserves_semantics_bwd :
  forall c rs1 rs2,
    R (inline_callfn_one ftab c) rs1 rs2 ->
    R c rs1 rs2.
Proof.
  intros c rs1 rs2 H.
  remember (inline_callfn_one ftab c) as cin eqn:Hc.
  revert c Hc.
  induction H; intros c0 Hc0; destruct c0; simpl in Hc0; try discriminate.
  (* [solve] is load-bearing: [eauto] does not fail on an unsolved goal,
     so without it [econstructor] picks the wrong
     [REdIfNz]/[REdWhileNz]/[REdFor] rule and leaves residue. *)
  all: try (apply inline_callfn_bwd_callfn; simpl; rewrite <- Hc0;
            solve [ econstructor; eauto ]).
  all: try (inversion Hc0; subst; solve [ econstructor; eauto ]).
Qed.

(** Soundness, iff.  Forward direction is the load-bearing one for
    extraction; the backward direction is proved above. *)
Theorem inline_callfn_one_preserves_semantics :
  forall c rs1 rs2,
    R c rs1 rs2 <-> R (inline_callfn_one ftab c) rs1 rs2.
Proof.
  intros; split;
    [ apply inline_callfn_one_preserves_semantics_fwd
    | apply inline_callfn_one_preserves_semantics_bwd ].
Qed.

(** Iterated soundness, forward direction.  Iterating FWD over a callgraph
    of depth [n] eliminates all [REdCallFn] sites and preserves the
    original spec's holding (the direction needed by the Jasmin extraction
    pipeline). *)
Theorem inline_callfn_n_preserves_semantics_fwd :
  forall n c rs1 rs2,
    R c rs1 rs2 -> R (inline_callfn_n n ftab c) rs1 rs2.
Proof.
  induction n; intros c rs1 rs2 H; simpl.
  - exact H.
  - apply IHn. apply inline_callfn_one_preserves_semantics_fwd. exact H.
Qed.

(** Iterated soundness, iff form (depends on BWD; provided for
    completeness but [Admitted] until BWD is closed). *)
Theorem inline_callfn_n_preserves_semantics :
  forall n c rs1 rs2,
    R c rs1 rs2 <-> R (inline_callfn_n n ftab c) rs1 rs2.
Proof.
  induction n; intros c rs1 rs2; simpl.
  - reflexivity.
  - rewrite (inline_callfn_one_preserves_semantics c rs1 rs2).
    apply IHn.
Qed.

End Soundness.

(* ================================================================ *)
(* §3. Sanity checks                                                 *)
(* ================================================================ *)

(** [inline_callfn_one] on a [REdCallFn]-free command is the identity. *)
Section NoCallFn.

(** A command is [callfn_free] if it contains no [REdCallFn] constructor. *)
Fixpoint callfn_free (c : rust_cmd_ed) : bool :=
  match c with
  | REdSkip => true
  | REdSeq c1 c2 => andb (callfn_free c1) (callfn_free c2)
  | REdLetZero _ _ c' => callfn_free c'
  | REdLetU64 _ _ c' => callfn_free c'
  | REdScalarSet _ _ => true
  | REdCall _ _ _ => true
  | REdIfNz _ c1 c2 => andb (callfn_free c1) (callfn_free c2)
  | REdWhileNz _ c' => callfn_free c'
  | REdByteStore _ _ _ => true
  | REdByteLoad _ _ _ => true
  | REdFor _ _ body => callfn_free body
  | REdSelect _ _ _ _ => true
  | REdCallN _ _ _ => true
  | REdCallFn _ _ _ => false
  | REdBlock body => callfn_free body
  | REdSetBytes _ _ => true
  | REdArrLoad _ _ _ => true
  | REdArrStore _ _ _ => true
  | REdLimbStore _ _ _ => true
  end.

Lemma callfn_free_inline_one_id : forall ftab c,
  callfn_free c = true ->
  inline_callfn_one ftab c = c.
Proof.
  intros ftab.
  induction c; simpl; intros Hfree; try reflexivity.
  - (* REdSeq *)
    apply Bool.andb_true_iff in Hfree as [H1 H2].
    rewrite IHc1, IHc2 by assumption. reflexivity.
  - (* REdLetZero *)
    rewrite IHc by assumption. reflexivity.
  - (* REdLetU64 *)
    rewrite IHc by assumption. reflexivity.
  - (* REdIfNz *)
    apply Bool.andb_true_iff in Hfree as [H1 H2].
    rewrite IHc1, IHc2 by assumption. reflexivity.
  - (* REdWhileNz *)
    rewrite IHc by assumption. reflexivity.
  - (* REdFor *)
    rewrite IHc by assumption. reflexivity.
  - (* REdCallFn — Hfree : false = true is impossible *)
    inversion Hfree.
  - (* REdBlock *)
    rewrite IHc by assumption. reflexivity.
Qed.

End NoCallFn.
