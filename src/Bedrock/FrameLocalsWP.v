(** * FrameLocalsWP.v — frame-locals helper for bedrock2 WP composition.

    Motivation: composing sub-loop leaves (L1-L4 of MSM WP proof)
    requires each leaf's postcondition to preserve ALL outer-body
    locals (18 in the MSM case), even those it doesn't write.

    Each leaf's current spec only tracks its DIRECT locals.  Adding
    14+ `map.get l' "..." = Some ...` conjuncts to every leaf's post
    is invasive (re-proving Qed lemmas).

    Alternative: define [cmd_writes c] — the set of local variables
    potentially written by [c] — and prove once that unwritten
    locals are preserved through [WeakestPrecondition.cmd].  Then
    each leaf composition uses this helper.

    This file is STANDALONE: minimal imports (bedrock2 + coqutil)
    so it builds even when fiat-crypto .vo is invalidated.
*)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From coqutil Require Import Map.Interface Word.Interface.
From bedrock2 Require Import Syntax Semantics WeakestPrecondition
                              WeakestPreconditionProperties.

Local Open Scope string_scope.

Section FrameLocals.
  Context {width : Z} {BW : Bitwidth.Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (** [cmd_writes c] — conservative over-approximation of the set of
      local variables potentially written by [c].  Returns a [list
      string] (concrete, decidable membership).

      - [cmd.set x _] writes [x]
      - [cmd.unset x] writes [x]
      - [cmd.stackalloc x _ c] writes [x] and whatever [c] writes
      - [cmd.cond _ t f] writes the union of [t] and [f]
      - [cmd.seq c1 c2] writes the union
      - [cmd.while _ body] writes whatever [body] writes
      - [cmd.call binds _ _] writes each of [binds]
      - [cmd.interact binds _ _] writes each of [binds]
      - [cmd.skip] / [cmd.store _ _ _] write nothing to locals
  *)
  Fixpoint cmd_writes (c : cmd.cmd) : list String.string :=
    match c with
    | cmd.skip => []
    | cmd.set x _ => [x]
    | cmd.unset x => [x]
    | cmd.store _ _ _ => []
    | cmd.stackalloc x _ c' => x :: cmd_writes c'
    | cmd.cond _ ct cf => cmd_writes ct ++ cmd_writes cf
    | cmd.seq c1 c2 => cmd_writes c1 ++ cmd_writes c2
    | cmd.while _ body => cmd_writes body
    | cmd.call binds _ _ => binds
    | cmd.interact binds _ _ => binds
    end.

  (** Convenience: decidable membership in [cmd_writes c]. *)
  Definition in_writes (x : String.string) (c : cmd.cmd) : bool :=
    List.existsb (String.eqb x) (cmd_writes c).

  (** Helper lemmas (pure list/string facts). *)

  Lemma in_writes_spec x c :
    in_writes x c = true <-> In x (cmd_writes c).
  Proof.
    unfold in_writes. rewrite existsb_exists.
    split.
    - intros [y [Hin Heq]]. apply String.eqb_eq in Heq. subst. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply String.eqb_refl].
  Qed.

  Lemma not_in_writes_spec x c :
    in_writes x c = false <-> ~ In x (cmd_writes c).
  Proof.
    split.
    - intros H Hin. apply in_writes_spec in Hin. congruence.
    - intros H. destruct (in_writes x c) eqn:E; [|reflexivity].
      exfalso. apply H. apply in_writes_spec. exact E.
  Qed.

  (** * Main lemma.

      If [cmd c] doesn't write [x], and [l] has [x ↦ v] at entry,
      then we can conjoin [map.get l' x = Some v] to the post.
  *)

  Lemma frame_locals_wp :
    forall (fs : Semantics.env) (c : cmd.cmd)
           (x : String.string) (v : word)
           (t : Semantics.trace) (m : mem) (l : locals)
           (post : Semantics.trace -> mem -> locals -> Prop),
      ~ In x (cmd_writes c) ->
      map.get l x = Some v ->
      WeakestPrecondition.cmd fs c t m l post ->
      WeakestPrecondition.cmd fs c t m l
        (fun t' m' l' => map.get l' x = Some v /\ post t' m' l').
  (** Proof strategy (to be closed in a session with working MCP):
      induction on [c] with strong IH that doesn't fix the post.  Each
      constructor case:
      - [skip]: post preserved directly.
      - [set y e] / [unset y] (with y≠x): [map.get_put_diff] /
        [map.get_remove_diff] preserves x's mapping.
      - [store]: no local write; use [store_weaken] on memory predicate.
      - [stackalloc y n c']: y is fresh stack addr (y≠x); recurse on c'
        with the [map.put l y a] (a is the stack pointer).
      - [cond e ct cf]: split on value; apply IH on ct or cf.
      - [seq c1 c2]: apply IH on c1 to strengthen its post with
        [map.get l' x = Some v]; then [Proper_cmd] + IH on c2 inside
        the continuation using the strengthened post's conjunct as the
        new [Hget] for c2.
      - [while _ body]: fall back to [Semantics.exec.exec]; prove via
        induction on the exec trace.  Body doesn't write x ⇒ invariant
        preserved per iteration.
      - [call binds fname args]: if x ∉ binds, preserve; else contradicts
        [~ In x (cmd_writes c)].
      - [interact]: analogous to call. *)
  Admitted.

  (** Batched version: preserve a list of locals. *)

  Lemma frame_locals_wp_list :
    forall (fs : Semantics.env) (c : cmd.cmd)
           (xs : list String.string)
           (t : Semantics.trace) (m : mem) (l : locals)
           (post : Semantics.trace -> mem -> locals -> Prop),
      Forall (fun x => ~ In x (cmd_writes c)) xs ->
      Forall (fun x => exists v, map.get l x = Some v) xs ->
      WeakestPrecondition.cmd fs c t m l post ->
      WeakestPrecondition.cmd fs c t m l
        (fun t' m' l' =>
           Forall (fun x => map.get l x = map.get l' x) xs /\ post t' m' l').
  Proof.
  Admitted.

End FrameLocals.
