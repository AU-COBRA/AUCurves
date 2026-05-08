(** * CmdAST — deep-AST mirror of [bedrock2.Syntax.cmd] for reflective WP.

    Phase 1 deliverable per [BEDROCK2_REFLECTIVE_PLAN.md].  Defines a
    1-to-1 deep mirror of [bedrock2.Syntax.cmd]'s 10 constructors and
    a [denote] function back to [cmd].

    No soundness theorem yet (phase 2).  No reify Ltac yet (phase 5).
    The point of this file is to lock in the AST shape and verify the
    universe / typeclass / opam-build interactions before we spend
    weeks on soundness.

    Why a separate Inductive when [cmd] is already an Inductive?  Two
    reasons:

      1. Allows [Strategy] / [Set Universe Polymorphism] / etc. tweaks
         that we may not want to apply to upstream [cmd].

      2. Future phases (3, 4) may extend the AST with semantic-level
         hints that don't have a [cmd] counterpart — e.g., a
         loop-invariant constructor that paniciffies the reify Ltac when
         a [Lemma] for the invariant isn't in scope.  Better to
         have a separate type so those extensions are obvious.

    For now [cmdAST] and [cmd] are isomorphic up to [denote].

    DESIGN NOTE.  Since this is phase 1 only, the deeper design
    choices (single AST vs per-shape; vm_compute strategy; reify path)
    are deferred to phase 2's soundness work.  Choices made here that
    are tentative:

      - [expr] is shared with [bedrock2.Syntax.expr] — we don't reify
        expressions because their evaluation is already tractable
        (they're not the bottleneck).  If phase 2 measures expr
        elaboration as a hot spot, revisit.
      - [access_size] is shared.  Same reasoning.
      - String identifiers (variable names, function names) are
        shared.  No reification needed; they're already first-class
        Coq values. *)

From Stdlib Require Import String List ZArith.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet.
Require Import bedrock2.Syntax bedrock2.Semantics bedrock2.WeakestPrecondition bedrock2.WeakestPreconditionProperties.
Import Coq.Init.Byte.

(** ** Mirror of [bedrock2.Syntax.cmd].

    Constructors are renamed [AST_*] to avoid shadowing.  Order and
    arity match [Syntax.cmd] exactly. *)
Inductive cmdAST : Set :=
| AST_skip
| AST_set        (lhs : String.string) (rhs : Syntax.expr)
| AST_unset      (lhs : String.string)
| AST_store      (sz : access_size) (address : Syntax.expr) (value : Syntax.expr)
| AST_stackalloc (lhs : String.string) (nbytes : Z) (body : cmdAST)
| AST_cond       (condition : Syntax.expr) (nonzero_branch zero_branch : cmdAST)
| AST_seq        (s1 s2 : cmdAST)
| AST_while      (test : Syntax.expr) (body : cmdAST)
| AST_call       (binds : list String.string) (function : String.string) (args : list Syntax.expr)
| AST_interact   (binds : list String.string) (action : String.string) (args : list Syntax.expr).

(** ** Denotation [cmdAST → cmd].

    Trivial structural recursion: each [AST_*] maps to [cmd.*].  A
    fixpoint, not a notation, so [vm_compute] can step through it. *)
Fixpoint denote (a : cmdAST) : Syntax.cmd :=
  match a with
  | AST_skip => cmd.skip
  | AST_set x e => cmd.set x e
  | AST_unset x => cmd.unset x
  | AST_store sz addr v => cmd.store sz addr v
  | AST_stackalloc x n body => cmd.stackalloc x n (denote body)
  | AST_cond c t f => cmd.cond c (denote t) (denote f)
  | AST_seq s1 s2 => cmd.seq (denote s1) (denote s2)
  | AST_while t body => cmd.while t (denote body)
  | AST_call binds f args => cmd.call binds f args
  | AST_interact binds a args => cmd.interact binds a args
  end.

(** ** Phase 2: reflective WP fixpoint [cmd_reflect].

    Mirrors [WeakestPrecondition.cmd_body]'s case-split, but as a
    direct [Fixpoint] on [cmdAST] (no Knaster-Tarski / [Fixpoint cmd c
    := cmd_body cmd c] indirection).

    Restricted in this phase to [AST_skip / AST_set / AST_unset /
    AST_store / AST_seq / AST_stackalloc / AST_cond].  [AST_while /
    AST_call / AST_interact] fall through to a sentinel [True] for now
    — their reflective-friendly forms are deferred to phases 3-4. *)
Section CmdReflect.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Init.Byte.byte}
          {locals : map.map String.string word}
          {ext_spec : ExtSpec}.
  Context (e : env).

  Local Notation post_ty := (trace -> mem -> locals -> Prop).

  Fixpoint cmd_reflect (a : cmdAST) (t : trace) (m : mem) (l : locals)
                       (post : post_ty) : Prop :=
    match a with
    | AST_skip => post t m l
    | AST_set x ev =>
        exists v, dexpr m l ev v /\
        dlet! l := map.put l x v in
        post t m l
    | AST_unset x =>
        dlet! l := map.remove l x in
        post t m l
    | AST_store sz ea ev =>
        exists a', dexpr m l ea a' /\
        exists v, dexpr m l ev v /\
        WeakestPrecondition.store sz m a' v (fun m =>
        post t m l)
    | AST_stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a' mStack mCombined,
          Memory.anybytes a' n mStack ->
          map.split mCombined m mStack ->
          dlet! l := map.put l x a' in
          cmd_reflect c t mCombined l (fun t' mCombined' l' =>
            exists m' mStack',
            Memory.anybytes a' n mStack' /\
            map.split mCombined' m' mStack' /\
            post t' m' l')
    | AST_cond br ct cf =>
        exists v, dexpr m l br v /\
        (word.unsigned v <> 0%Z -> cmd_reflect ct t m l post) /\
        (word.unsigned v = 0%Z -> cmd_reflect cf t m l post)
    | AST_seq s1 s2 =>
        cmd_reflect s1 t m l (fun t m l => cmd_reflect s2 t m l post)
    | AST_while _ _ => True   (* Phase 3 *)
    | AST_call _ _ _ => True   (* Phase 4 *)
    | AST_interact _ _ _ => True   (* Phase 4 *)
    end.

  (** ** Phase 2 soundness — equivalence with [WeakestPrecondition.cmd]
      for the supported subset.

      [a]-restricted: while / call / interact must not appear.  We
      encode this as a Boolean check [supported] and only prove the
      iff when [supported a = true]. *)
  Fixpoint supported (a : cmdAST) : bool :=
    match a with
    | AST_skip => true
    | AST_set _ _ => true
    | AST_unset _ => true
    | AST_store _ _ _ => true
    | AST_stackalloc _ _ b => supported b
    | AST_cond _ ct cf => andb (supported ct) (supported cf)
    | AST_seq s1 s2 => andb (supported s1) (supported s2)
    | AST_while _ _ => false
    | AST_call _ _ _ => false
    | AST_interact _ _ _ => false
    end.

  (** Phase 2 (this commit): leaf-only soundness — [AST_skip / AST_set
      / AST_unset / AST_store].  These reduce to identical normal
      forms under [cbv [WeakestPrecondition.cmd]] vs [cbn [cmd_reflect]],
      so the equivalence is [reflexivity].

      The recursive constructors ([AST_seq / AST_stackalloc / AST_cond])
      need an induction principle threading the post; their soundness
      proofs are non-trivial (need [Proper_cmd] for monotonicity) and
      are deferred to the next iteration of Phase 2. *)
  Definition supported_leaf (a : cmdAST) : bool :=
    match a with
    | AST_skip | AST_set _ _ | AST_unset _ | AST_store _ _ _ => true
    | _ => false
    end.

  Lemma cmd_reflect_correct_leaf (a : cmdAST) :
    supported_leaf a = true ->
    forall (t : trace) (m : mem) (l : locals) (post : post_ty),
      WeakestPrecondition.cmd e (denote a) t m l post <->
      cmd_reflect a t m l post.
  Proof.
    destruct a; intros Hsup t m l post; cbn [denote cmd_reflect] in *;
      try (cbv [WeakestPrecondition.cmd]; reflexivity);
      try discriminate.
  Qed.

  (** ** Phase 2.5 — [Proper_cmd_reflect] for recursive-case soundness.

      To prove [AST_seq] / [AST_stackalloc] / [AST_cond] soundness, we
      need [cmd_reflect] to respect post-condition weakening (a Proper
      instance).  This is structural induction on the AST.

      We prove it once here and use it for the recursive constructors
      below. *)
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}
          {ext_spec_ok : ext_spec.ok ext_spec}.

  Lemma Proper_cmd_reflect (a : cmdAST) :
    forall (t : trace) (m : mem) (l : locals) (post1 post2 : post_ty),
      (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
      cmd_reflect a t m l post1 -> cmd_reflect a t m l post2.
  Proof.
    induction a; intros t m l post1 post2 Himp H;
      cbn [cmd_reflect] in *.
    - apply Himp. exact H.
    - destruct H as (v & Hd & Hp). exists v. split; [exact Hd|]. cbv [dlet.dlet] in *. apply Himp. exact Hp.
    - cbv [dlet.dlet] in *. apply Himp. exact H.
    - destruct H as (a' & Hda & v & Hdv & m' & Hst & Hp). exists a'. split; [exact Hda|].
      exists v. split; [exact Hdv|]. exists m'. split; [exact Hst|]. apply Himp. exact Hp.
    - destruct H as [Hmod H]. split; [exact Hmod|].
      intros a' mStack mCombined Han Hsplit.
      specialize (H a' mStack mCombined Han Hsplit). cbv [dlet.dlet] in *.
      eapply IHa; [|exact H].
      intros t' m' l' (m'1 & mStack' & Han' & Hsplit' & Hp).
      exists m'1, mStack'. split; [exact Han'|]. split; [exact Hsplit'|]. apply Himp. exact Hp.
    - destruct H as (v & Hd & Hnz & Hz). exists v. split; [exact Hd|]. split.
      + intros Hne. eapply IHa1; [exact Himp|]. apply (Hnz Hne).
      + intros Heq. eapply IHa2; [exact Himp|]. apply (Hz Heq).
    - eapply IHa1; [|exact H]. intros t' m' l' Hp. eapply IHa2; [exact Himp|]. exact Hp.
    - exact I.
    - exact I.
    - exact I.
  Qed.

  (** ** Phase 2.5 — soundness for [AST_seq] (the critical inter-call
      glue case). *)
  Lemma cmd_reflect_correct_seq (a1 a2 : cmdAST)
        (IHa1 : forall t m l post,
                  WeakestPrecondition.cmd e (denote a1) t m l post <->
                  cmd_reflect a1 t m l post)
        (IHa2 : forall t m l post,
                  WeakestPrecondition.cmd e (denote a2) t m l post <->
                  cmd_reflect a2 t m l post) :
    forall t m l post,
      WeakestPrecondition.cmd e (denote (AST_seq a1 a2)) t m l post <->
      cmd_reflect (AST_seq a1 a2) t m l post.
  Proof.
    intros t m l post. cbn [denote cmd_reflect].
    cbv [WeakestPrecondition.cmd].
    cbn [WeakestPrecondition.cmd_body].
    fold (WeakestPrecondition.cmd e).
    split; intros H.
    - (* WP.cmd ... seq → cmd_reflect ... seq *)
      apply IHa1 in H.
      eapply Proper_cmd_reflect; [|exact H].
      intros t' m' l' Hp. apply IHa2. exact Hp.
    - (* cmd_reflect ... seq → WP.cmd ... seq *)
      eapply Proper_cmd_reflect with
        (post1 := (fun t' m' l' => cmd_reflect a2 t' m' l' post))
        in H;
        [| intros t' m' l' Hp; apply IHa2 in Hp; exact Hp].
      apply IHa1. exact H.
  Qed.

  (** ** Phase 2-rest — soundness for [AST_stackalloc].

      Pattern mirrors seq but the post threads through the
      [anybytes / map.split] wrapper. *)
  Lemma cmd_reflect_correct_stackalloc (x : String.string) (n : Z) (body : cmdAST)
        (IHbody : forall t m l post,
                    WeakestPrecondition.cmd e (denote body) t m l post <->
                    cmd_reflect body t m l post) :
    forall t m l post,
      WeakestPrecondition.cmd e (denote (AST_stackalloc x n body)) t m l post <->
      cmd_reflect (AST_stackalloc x n body) t m l post.
  Proof.
    intros t m l post. cbn [denote cmd_reflect].
    cbv [WeakestPrecondition.cmd]. cbn [WeakestPrecondition.cmd_body].
    fold (WeakestPrecondition.cmd e).
    split; intros [Hmod H]; split; [exact Hmod | | exact Hmod |];
      intros a' mStack mCombined Han Hsplit;
      specialize (H a' mStack mCombined Han Hsplit); cbv [dlet.dlet] in *.
    - apply IHbody. exact H.
    - apply IHbody. exact H.
  Qed.

  (** ** Phase 2-rest — soundness for [AST_cond]. *)
  Lemma cmd_reflect_correct_cond (br : Syntax.expr) (ct cf : cmdAST)
        (IHct : forall t m l post,
                  WeakestPrecondition.cmd e (denote ct) t m l post <->
                  cmd_reflect ct t m l post)
        (IHcf : forall t m l post,
                  WeakestPrecondition.cmd e (denote cf) t m l post <->
                  cmd_reflect cf t m l post) :
    forall t m l post,
      WeakestPrecondition.cmd e (denote (AST_cond br ct cf)) t m l post <->
      cmd_reflect (AST_cond br ct cf) t m l post.
  Proof.
    intros t m l post. cbn [denote cmd_reflect].
    cbv [WeakestPrecondition.cmd]. cbn [WeakestPrecondition.cmd_body].
    fold (WeakestPrecondition.cmd e).
    split.
    - intros (v & Hd & Hnz & Hz). exists v. split; [exact Hd|]. split.
      + intros Hne. apply IHct. apply (Hnz Hne).
      + intros Heq. apply IHcf. apply (Hz Heq).
    - intros (v & Hd & Hnz & Hz). exists v. split; [exact Hd|]. split.
      + intros Hne. apply IHct. apply (Hnz Hne).
      + intros Heq. apply IHcf. apply (Hz Heq).
  Qed.

  (** ** Phase 2-final — combined soundness for [supported] AST.

      Wraps the leaf + seq + stackalloc + cond cases into a single
      structural induction. *)
  Lemma cmd_reflect_correct (a : cmdAST) :
    supported a = true ->
    forall t m l post,
      WeakestPrecondition.cmd e (denote a) t m l post <->
      cmd_reflect a t m l post.
  Proof.
    induction a; intros Hsup t m l post; cbn [supported] in Hsup;
      try discriminate.
    - apply cmd_reflect_correct_leaf. reflexivity.
    - apply cmd_reflect_correct_leaf. reflexivity.
    - apply cmd_reflect_correct_leaf. reflexivity.
    - apply cmd_reflect_correct_leaf. reflexivity.
    - apply cmd_reflect_correct_stackalloc. apply IHa. exact Hsup.
    - apply Bool.andb_true_iff in Hsup as [Hsup1 Hsup2].
      apply cmd_reflect_correct_cond.
      + apply IHa1. exact Hsup1.
      + apply IHa2. exact Hsup2.
    - apply Bool.andb_true_iff in Hsup as [Hsup1 Hsup2].
      apply cmd_reflect_correct_seq.
      + apply IHa1. exact Hsup1.
      + apply IHa2. exact Hsup2.
  Qed.

End CmdReflect.

(** ** Smoke test: [denote] of a simple AST gives back the expected
    [cmd]. *)
Module SmokeTest.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Definition example_AST : cmdAST :=
    AST_seq
      (AST_set "x" (expr.literal 42))
      (AST_skip).

  (** [denote example_AST] should reduce to [cmd.seq (cmd.set "x" 42) cmd.skip]
      via [cbv [denote]] / [vm_compute]. *)
  Goal denote example_AST = cmd.seq (cmd.set "x" (expr.literal 42)) cmd.skip.
  Proof. cbv [denote example_AST]. reflexivity. Qed.

  (** Same goal via [vm_compute] — confirms the fixpoint reduces under
      the bytecode VM (no opacity / typeclass interference). *)
  Goal denote example_AST = cmd.seq (cmd.set "x" (expr.literal 42)) cmd.skip.
  Proof. vm_compute. reflexivity. Qed.

End SmokeTest.

(** ** Phase 1 result line.

    Build status: pending (this file is the deliverable).
    Soundness theorem: NOT proven (phase 2).
    Reify Ltac: NOT defined (phase 5).
    R10 wired: NO (phases 6+).

    Validation criterion (from plan): "File builds Qed-clean."
    The two [Goal]s in [SmokeTest] additionally verify that [denote]
    reduces under both [cbv] and [vm_compute] — early signal that
    phase 2's soundness theorem won't immediately hit a typeclass /
    opacity wall. *)
