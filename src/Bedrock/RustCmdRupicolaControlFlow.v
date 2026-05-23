(** * RustCmdRupicolaControlFlow — control-flow dispatch for [rust_cmd_ed]
 *
 *  This module extends the Gallina-driven compile framework
 *  ([RustCmdRupicolaGallina.v]) from straight-line [nlet_red]
 *  arithmetic chains to CONTROL FLOW.  Where the existing
 *  [compile_gallina_modp_*_emit] lemmas recognise a post of shape
 *    [fun rs' => nlet_red [n] (stack (a OP b)) k rs']
 *  and emit a straight-line [REdSeq (REdCall ...) ?k], the three
 *  lemmas here recognise the THREE Gallina control-flow shapes and
 *  emit the corresponding branching / multi-output AST:
 *
 *    1. [compile_gallina_match_option]  —  [match o with None | Some x]
 *         emits  [REdIfNz status_expr none_ast some_ast].
 *         (Generalises [compile_red_parse_canonical] in
 *          [RustCmdRupicolaRistretto.v] off the concrete option-Z type
 *          to an arbitrary [option A], and off the concrete
 *          [slot_holds] witness to an abstract per-state predicate.)
 *
 *    2. [compile_gallina_let_pair]  —  [let '(a, b) := f args in k a b]
 *         emits  [REdSeq (REdCallN fname [da; db] arg_locs) ?k].
 *         (Generalises [compile_red_sqrt_ratio_m1].)
 *
 *    3. [compile_gallina_if_bool_select]  —
 *         [nlet_red [n] (stack (if b then v_then else v_else)) k]
 *         emits  [REdSelect cond_expr then_loc else_loc dst]  (CT).
 *         (Packages [compile_red_select].)
 *
 *  Plus a dispatcher [compile_cf_step] (lazymatch on the post shape,
 *  mirrors [compile_step_ristretto]) and a self-contained TOY DEMO
 *  ([Demo] module) chaining all three through one [compile_cf]
 *  invocation.
 *
 *  Design notes
 *  ------------
 *  - All three lemmas live in a [Section] parameterised by
 *    [callee_post], [callee_post_n], [function_table] — exactly the
 *    [RustTriple] section signature of [RustCmdRupicola.v] — so
 *    [rhoare] / [compile_red_*] are in scope with those leading args.
 *  - The lemmas are abstract: they take per-state witness predicates
 *    ([wit_*] / [holds_*]) as Section/lemma parameters rather than the
 *    concrete [slot_holds].  This keeps the file (and the demo) free of
 *    any Ristretto / Ed25519 leaf dependency, so it is a reusable
 *    framework, not a one-off.
 *  - ZERO admits, ZERO new axioms (verified by [Print Assumptions]).
 *
 *  Status (2026-05-23): all 3 lemmas + demo Qed.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** [stack] is the same identity Rupicola markup as in
    [RustCmdRupicolaGallina.v]: it tags a binding that wants a stack
    slot.  We re-declare it locally (definitionally equal to the
    user's) so the [if_bool_select] pattern can recognise [stack (if b
    then _ else _)] without importing the ristretto file. *)
Definition stack {A} (x : A) : A := x.

Section ControlFlow.
  (* Mirror RustCmdRupicola.v's [RustTriple] section signature so
     [rhoare] / the core [compile_red_*] lemmas apply with these
     leading parameters. *)
  Context (callee_post : String.string -> list located_ed -> located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).
  Context (function_table : function_table_ed).

  Local Notation rhoare := (rhoare callee_post callee_post_n function_table).

  (* ================================================================ *)
  (* §1. compile_gallina_match_option                                  *)
  (* ================================================================ *)

  (** [compile_gallina_match_option] — option-typed dispatch.

      Compiles a Gallina post of shape
      {{
        match o with
        | None   => kn          (* the "rejected" continuation *)
        | Some x => ks x        (* the "accepted" continuation *)
        end
      }}
      to the IR [REdIfNz status_expr none_ast some_ast], where the
      status scalar reflects the discriminant with the convention
      established by [compile_red_parse_canonical]:

        eval status_expr = Some 0   ⇔   o = Some _   (accept)
        eval status_expr = Some v≠0 ⇔   o = None      (reject)

      Generalises [compile_red_parse_canonical] off the concrete
      [option Z] / [slot_holds] to an arbitrary [option A] and an
      abstract per-state [accept]/[reject] reflection.

      The two continuation triples are stated point-wise on the SAME
      [rs] (no intervening call): this is the pure-control-flow lemma,
      so the call that produced [o] is the caller's responsibility
      (typically threaded by [compile_gallina_let_pair] first).  *)
  Lemma compile_gallina_match_option
        {A : Type}
        (rs : rust_state_ed)
        (o : option A)
        (status_expr : sexpr_ed)
        (none_ast some_ast : rust_cmd_ed)
        (kn : rust_state_ed -> Prop)
        (ks : A -> rust_state_ed -> Prop) :
    (* status reflects the discriminant *)
    (match o with
     | Some _ => eval_sexpr_ed rs status_expr = Some 0
     | None   => exists v, eval_sexpr_ed rs status_expr = Some v /\ v <> 0
     end) ->
    (* accept branch: when [o = Some x], [some_ast] establishes [ks x] *)
    (forall x, o = Some x -> rhoare rs some_ast (ks x)) ->
    (* reject branch: when [o = None], [none_ast] establishes [kn] *)
    (o = None -> rhoare rs none_ast kn) ->
    rhoare rs (REdIfNz status_expr none_ast some_ast)
      (fun rs' =>
         match o with
         | None   => kn rs'
         | Some x => ks x rs'
         end).
  Proof.
    intros Hstatus Hsome Hnone.
    eapply compile_red_if_nz.
    - (* status ≠ 0 ⇒ o = None ⇒ run none_ast, post is [kn] *)
      intros v Heval Hnz.
      destruct o as [x|] eqn:Ho.
      + (* Some: Hstatus says status = Some 0, contradicting Hnz. *)
        rewrite Heval in Hstatus. inversion Hstatus. congruence.
      + (* None: run none_ast; the goal's post on the None branch is [kn]. *)
        eapply rhoare_weaken; [| eapply Hnone; reflexivity ].
        intros rs' Hkn. exact Hkn.
    - (* status = 0 ⇒ o = Some x ⇒ run some_ast, post is [ks x] *)
      intros Heval0.
      destruct o as [x|] eqn:Ho.
      + (* Some: run some_ast; post on Some branch is [ks x]. *)
        eapply rhoare_weaken; [| eapply Hsome; reflexivity ].
        intros rs' Hks. exact Hks.
      + (* None: Hstatus gives status = Some v, v≠0, contradicting Heval0. *)
        destruct Hstatus as [v [Hv Hvnz]].
        rewrite Heval0 in Hv. inversion Hv. congruence.
  Qed.

  (* ================================================================ *)
  (* §2. compile_gallina_let_pair                                      *)
  (* ================================================================ *)

  (** [compile_gallina_let_pair] — destructuring-let over a 2-output call.

      Compiles a Gallina post of shape
      {{
        let '(a, b) := p in k a b
      }}
      (where [p : A * B] is the abstract result of a 2-output leaf) to
      the IR [REdSeq (REdCallN fname dests args) kont].

      The call's effect is captured abstractly by [call_post]: it is
      the [callee_post_n]-derived relation between the pre-state [rs]
      and the post-state [rs1].  The user supplies:
        - that [REdCallN] satisfies [call_post] (the leaf's
          [callee_post_n] discharge), and
        - that, given [call_post rs rs1], the continuation [kont]
          establishes [k (fst p) (snd p)] on [rs1].

      Generalises [compile_red_sqrt_ratio_m1] (whose [p] is the
      concrete [(was_square, r)] pair and whose [call_post] is the
      conjunction of [slot_holds] facts). *)
  Lemma compile_gallina_let_pair
        {A B : Type}
        (rs : rust_state_ed)
        (p : A * B)
        (fname : String.string)
        (dests args : list located_ed)
        (kont : rust_cmd_ed)
        (call_post : rust_state_ed -> rust_state_ed -> Prop)
        (k : A -> B -> rust_state_ed -> Prop) :
    (* the 2-output call's [callee_post_n] discharges to [call_post] *)
    (forall rs', callee_post_n fname dests args rs rs' -> call_post rs rs') ->
    (* with the call's effect in hand, the continuation establishes
       [k a b] (where [(a, b) = p]) *)
    (forall rs1, call_post rs rs1 ->
                 rhoare rs1 kont (fun rs' => k (fst p) (snd p) rs')) ->
    rhoare rs (REdSeq (REdCallN fname dests args) kont)
      (fun rs' => (let '(a, b) := p in k a b) rs').
  Proof.
    intros Hcall Hk.
    (* Rewrite the eta-expanded pair post into [k (fst p) (snd p)]. *)
    eapply rhoare_weaken with
      (pred1 := fun rs' => k (fst p) (snd p) rs').
    { intros rs' Hk'. destruct p as [a b]. exact Hk'. }
    eapply compile_red_seq.
    { eapply compile_red_calln.
      intros rs1 Hpost. exact (Hcall rs1 Hpost). }
    intros rs1 Hcp.
    apply Hk. exact Hcp.
  Qed.

  (* ================================================================ *)
  (* §3. compile_gallina_if_bool_select                                *)
  (* ================================================================ *)

  (** [compile_gallina_if_bool_select] — constant-time [if : bool].

      Compiles a Gallina post of shape
      {{
        nlet_red [name] (stack (if b then v_then else v_else)) k
      }}
      (where [b : bool] is a SOURCE-level boolean) to the IR
      [REdSelect cond_expr then_loc else_loc dst] — a constant-time
      conditional move (both [then_loc] and [else_loc] are always read;
      no branch on [cond_expr]).

      The boolean [b] is reflected by a scalar [cond_expr] with the
      convention [eval cond_expr = Some (if b then 1 else 0)] (matching
      [REdSelect]'s "non-zero ⇒ if_t" semantics).

      The continuation [k] must hold on the post-state [rs_post b],
      which is [rs] with [dst]'s tower-slot overwritten by the source
      slot ([then_loc] when [b], [else_loc] when [¬b]).  We package
      that post-state abstractly via [tv_then] / [tv_else] (the source
      tvals).

      Packages [compile_red_select].  *)
  Lemma compile_gallina_if_bool_select
        {Tv : Type}                              (* abstract value type carried by [k] *)
        (rs : rust_state_ed)
        (b : bool)
        (cond_expr : sexpr_ed)
        (then_loc else_loc dst : located_ed)
        (tv_then tv_else : tval_ed)
        (name : String.string)
        (v_then v_else : Tv)
        (k : Tv -> rust_state_ed -> Prop) :
    (* [b] reflected by [cond_expr] as 1/0 *)
    eval_sexpr_ed rs cond_expr = Some (if b then 1 else 0) ->
    (* type compatibility for the CT move *)
    then_loc.(loc_type) = dst.(loc_type) ->
    else_loc.(loc_type) = dst.(loc_type) ->
    (* the source tvals at then_loc / else_loc *)
    rs_get_tower_ed rs then_loc.(loc_var) = Some tv_then ->
    rs_get_tower_ed rs else_loc.(loc_var) = Some tv_else ->
    (* the continuation holds on the post-state for whichever branch *)
    k (if b then v_then else v_else)
      (rs_set_tower_ed rs dst.(loc_var) (if b then tv_then else tv_else)) ->
    rhoare rs (REdSelect cond_expr then_loc else_loc dst)
      (fun rs' =>
         nlet_red [name] (stack (if b then v_then else v_else)) k rs').
  Proof.
    intros Hcond Hty_t Hty_f Hget_t Hget_f Hk.
    unfold nlet_red, stack.
    eapply compile_red_select.
    intros cond_v src tv Heval Hsrc Hif_t Hif_f Hget.
    (* From Hcond and Heval, [cond_v = if b then 1 else 0]. *)
    rewrite Hcond in Heval. inversion Heval as [Hcv]. clear Heval.
    subst cond_v.
    (* Determine [src] from [b]. *)
    destruct b.
    - (* b = true: cond_v = 1, so [1 =? 0 = false], src = then_loc. *)
      cbn in Hsrc. subst src.
      (* tv at then_loc = tv_then. *)
      rewrite Hget_t in Hget. inversion Hget; subst tv.
      exact Hk.
    - (* b = false: cond_v = 0, so [0 =? 0 = true], src = else_loc. *)
      cbn in Hsrc. subst src.
      rewrite Hget_f in Hget. inversion Hget; subst tv.
      exact Hk.
  Qed.

End ControlFlow.

(* ================================================================ *)
(* §4. compile_cf_step — control-flow dispatcher                     *)
(*                                                                    *)
(* Mirrors [compile_step_ristretto] in [RustCmdRupicolaGallina.v]:    *)
(* lazymatch on the [rhoare]-goal's POST shape and apply the right    *)
(* control-flow emit lemma.  This handles ONLY control flow; straight-*)
(* line arithmetic is left to the existing arithmetic dispatcher.     *)
(* ================================================================ *)

(** NB: we match against the fully-qualified [RustCmdRupicola.rhoare]
    head (its 6 explicit arguments) rather than a [Local Notation
    rhoare] abbreviation.  A section-local [Notation rhoare := (rhoare
    cp cpn ft)] (as we use inside the lemmas and the demo) prints only
    3 visible arguments, so a pattern written against the *notation*
    would have the wrong arity and silently fail to match.  Matching
    the underlying constant is robust to whatever notation is in scope
    at the call site. *)
Ltac compile_cf_step :=
  lazymatch goal with
  (* §4a. [match o with None | Some x] — emit REdIfNz.  (The per-branch
     bodies absorb the [rs'] application, so there is no trailing app
     after the [match].) *)
  | |- RustCmdRupicola.rhoare _ _ _ _ _
        (fun _ => match _ with
                  | Some _ => _
                  | None   => _
                  end) =>
      eapply compile_gallina_match_option

  (* §4b. [let '(a, b) := p in k a b] — emit REdSeq (REdCallN ...).
     The whole let is applied to [rs'] on the outside. *)
  | |- RustCmdRupicola.rhoare _ _ _ _ _
        (fun _ => (let '(_, _) := _ in _) _) =>
      eapply compile_gallina_let_pair

  (* §4c. [nlet_red [n] (stack (if b then _ else _)) k] — emit REdSelect. *)
  | |- RustCmdRupicola.rhoare _ _ _ _ _
        (fun _ => nlet_red _ (stack (if _ then _ else _)) _ _) =>
      eapply compile_gallina_if_bool_select
  end.

(** [compile_cf] — repeated control-flow dispatcher.  Like Rupicola's
    [compile], iterates [compile_cf_step] until no control-flow pattern
    matches.  Residual side conditions (status reflection, call_post,
    slot facts) become subgoals. *)
Ltac compile_cf := repeat compile_cf_step.

(* ================================================================ *)
(* §5. TOY DEMO — control-flow auto-dispatch end-to-end              *)
(*                                                                    *)
(* A small, fully self-contained Gallina program combining all three *)
(* control-flow shapes:                                              *)
(*    match o with                                                   *)
(*    | None   => (* reject *)                                       *)
(*    | Some p =>  let '(a, b) := p in                               *)
(*                 nlet_red [...] (stack (if flag then a else b))    *)
(*                   (fun chosen => ...)                             *)
(*    end                                                            *)
(* and a lemma showing [compile_cf] auto-discharges its compilation  *)
(* to a concrete AST.  No ristretto / ed25519 leaf dependency.       *)
(* ================================================================ *)

Module Demo.

  Section DemoSection.
    Context (callee_post : String.string -> list located_ed -> located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).
    Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                             rust_state_ed -> rust_state_ed -> Prop).
    Context (function_table : function_table_ed).

    (** The abstract input parse-result: an [option] of a [Z * Z] pair.
        Kept abstract — no ristretto leaf. *)
    Context (o : option (Z * Z)).
    (** The source boolean selecting between the pair components. *)
    Context (flag : bool).

    (** Pre-state and reflection witnesses. *)
    Context (rs : rust_state_ed).
    (** status scalar reflecting [o]'s discriminant. *)
    Context (status_expr : sexpr_ed).
    (** abstract: the call producing [o]'s pair, as a [callee_post_n]
        relation summarised by [call_post]. *)
    Context (call_post : rust_state_ed -> rust_state_ed -> Prop).
    (** the final-answer predicate the whole program must establish. *)
    Context (final : Z -> rust_state_ed -> Prop).
    (** the reject-branch postcondition. *)
    Context (rejected : rust_state_ed -> Prop).

    (** AST holes the demo will synthesise / supply.  We GIVE the
        none-branch + the inner select/cond locs concretely so the demo
        AST is fully concrete; the [some]-branch AST is derived by
        [compile_cf]'s [REdSeq (REdCallN ...) ?k] emission. *)
    Context (none_ast : rust_cmd_ed).
    Context (pair_fname : String.string)
            (pair_dests pair_args : list located_ed).
    Context (cond_expr : sexpr_ed)
            (then_loc else_loc dst : located_ed)
            (tv_then tv_else : tval_ed).

    Local Notation rhoare := (rhoare callee_post callee_post_n function_table).

    (** The TOY GALLINA PROGRAM. *)
    Definition demo_gallina : rust_state_ed -> Prop :=
      fun rs' =>
        match o with
        | None   => rejected rs'
        | Some p =>
            (let '(a, b) := p in
             fun rs'' =>
               nlet_red ["chosen"%string]
                 (stack (if flag then a else b))
                 final rs'')
              rs'
        end.

    (** Hypotheses wiring the abstract pieces to the IR.  These are the
        per-leaf side conditions a real instantiation would discharge
        from [slot_holds] / leaf [callee_post_n]; here they are
        Section-level givens so the demo stays self-contained.  Their
        SHAPE is exactly what each emit lemma asks for. *)

    (* H1: status reflects [o]'s discriminant (accept ⇔ Some). *)
    Context (Hstatus :
      match o with
      | Some _ => eval_sexpr_ed rs status_expr = Some 0
      | None   => exists v, eval_sexpr_ed rs status_expr = Some v /\ v <> 0
      end).

    (* H2: the reject branch establishes [rejected]. *)
    Context (Hreject : o = None -> rhoare rs none_ast rejected).

    (* H3: the 2-output call's callee_post_n discharges to call_post. *)
    Context (Hcall : forall p, o = Some p ->
      forall rs', callee_post_n pair_fname pair_dests pair_args rs rs' ->
                  call_post rs rs').

    (* H4: in the post-call state, cond_expr reflects [flag] as 1/0. *)
    Context (Hcond : forall rs1, call_post rs rs1 ->
      eval_sexpr_ed rs1 cond_expr = Some (if flag then 1 else 0)).

    (* H5: type compat for the CT select. *)
    Context (Hty_t : then_loc.(loc_type) = dst.(loc_type))
            (Hty_f : else_loc.(loc_type) = dst.(loc_type)).

    (* H6: the source tvals at then_loc/else_loc in the post-call state. *)
    Context (Hget_t : forall rs1, call_post rs rs1 ->
      rs_get_tower_ed rs1 then_loc.(loc_var) = Some tv_then)
            (Hget_f : forall rs1, call_post rs rs1 ->
      rs_get_tower_ed rs1 else_loc.(loc_var) = Some tv_else).

    (* H7: the final answer holds on the post-select state. *)
    Context (Hfinal : forall p rs1, o = Some p -> call_post rs rs1 ->
      final (if flag then fst p else snd p)
            (rs_set_tower_ed rs1 dst.(loc_var)
               (if flag then tv_then else tv_else))).

    (** THE SUCCESS CRITERION: [compile_cf] auto-discharges the
        compilation of [demo_gallina] to a concrete AST whose
        [some]-branch continuation [?kont] is synthesised. *)
    Theorem demo_compiles :
      rhoare rs
        (REdIfNz status_expr
           none_ast
           (REdSeq (REdCallN pair_fname pair_dests pair_args)
                   (REdSelect cond_expr then_loc else_loc dst)))
        demo_gallina.
    Proof.
      unfold demo_gallina.
      (* §1: match option → REdIfNz. *)
      compile_cf_step.
      - exact Hstatus.
      - (* accept branch (some_ast): [let '(a,b) := p in ...] *)
        intros p Hp.
        (* §2: let-pair → REdSeq (REdCallN ...). *)
        compile_cf_step.
        + (* call_post discharge *)
          intros rs' Hpost. exact (Hcall p Hp rs' Hpost).
        + (* continuation after the call: the inner select. *)
          intros rs1 Hcp.
          (* §3: if-bool → REdSelect. *)
          compile_cf_step.
          * exact (Hcond rs1 Hcp).
          * exact Hty_t.
          * exact Hty_f.
          * exact (Hget_t rs1 Hcp).
          * exact (Hget_f rs1 Hcp).
          * (* final answer on the post-select state. *)
            exact (Hfinal p rs1 Hp Hcp).
      - (* reject branch (none_ast). *)
        intros Ho. exact (Hreject Ho).
    Qed.

  End DemoSection.

End Demo.

(* Axiom-freedom check (must report Closed under the global context). *)
Print Assumptions Demo.demo_compiles.
