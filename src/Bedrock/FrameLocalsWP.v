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
From coqutil Require Import Map.Interface Map.Properties Word.Interface.
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

  (** Helper: frame-over-exec (needed for the cmd.while case below,
      since WeakestPrecondition.cmd drops to Semantics.exec for while). *)

  Lemma frame_locals_exec :
    forall (fs : Semantics.env) (c : cmd.cmd)
           (t : Semantics.trace) (m : mem) (l : locals)
           (post : Semantics.trace -> mem -> locals -> Prop),
      Semantics.exec fs c t m l post ->
      forall (x : String.string) (v : word),
        ~ In x (cmd_writes c) ->
        map.get l x = Some v ->
        Semantics.exec fs c t m l
          (fun t' m' l' => map.get l' x = Some v /\ post t' m' l').
  Proof.
    intros fs c t m l post Hexec.
    induction Hexec; intros x0 v0 Hnotin Hget.
    - (* skip *)
      apply Semantics.exec.skip. split; [exact Hget | exact H].
    - (* set x e *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.set; [exact H|].
      split; [|exact H0].
      rewrite map.get_put_diff; [exact Hget|].
      intros ->. apply Hnotin. left. reflexivity.
    - (* unset x *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.unset.
      split; [|exact H].
      rewrite map.get_remove_diff; [exact Hget|].
      intros ->. apply Hnotin. left. reflexivity.
    - (* store *)
      eapply Semantics.exec.store; try eassumption.
      split; [exact Hget | exact H2].
    - (* stackalloc x n body *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.stackalloc; [exact H|].
      intros a mStack mCombined Hany Hsplit.
      specialize (H1 a mStack mCombined Hany Hsplit x0 v0).
      eapply Semantics.exec.weaken.
      + apply H1.
        * intros Hin. apply Hnotin. right. exact Hin.
        * rewrite map.get_put_diff; [exact Hget|].
          intros ->. apply Hnotin. left. reflexivity.
      + intros t' mC' l' [Hget' [mS' [mT' [Hany' [Hspl' Hp]]]]].
        exists mS', mT'. split; [exact Hany'|]. split; [exact Hspl'|].
        split; [exact Hget' | exact Hp].
    - (* if_true *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.if_true; try eassumption.
      apply IHHexec; [|exact Hget].
      intros Hin. apply Hnotin. apply in_or_app. left. exact Hin.
    - (* if_false *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.if_false; try eassumption.
      apply IHHexec; [|exact Hget].
      intros Hin. apply Hnotin. apply in_or_app. right. exact Hin.
    - (* seq *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.seq.
      + apply IHHexec; [|exact Hget].
        intros Hin. apply Hnotin. apply in_or_app. left. exact Hin.
      + intros t' m' l' [Hget' Hmid].
        apply H0; [exact Hmid| |exact Hget'].
        intros Hin. apply Hnotin. apply in_or_app. right. exact Hin.
    - (* while_false *)
      eapply Semantics.exec.while_false; try eassumption.
      split; [exact Hget | exact H1].
    - (* while_true *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.while_true.
      + exact H.
      + exact H0.
      + apply IHHexec; [exact Hnotin | exact Hget].
      + intros t' m' l' [Hget' Hmid].
        apply (H2 t' m' l' Hmid x0 v0 Hnotin Hget').
    - (* call *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.call; try eassumption.
      intros t' m' st1 Hmid.
      specialize (H2 t' m' st1 Hmid).
      destruct H2 as [retvs [Hretvs [l' [Hputmany Hpost]]]].
      exists retvs. split; [exact Hretvs|].
      exists l'. split; [exact Hputmany|].
      split; [|exact Hpost].
      eapply map.putmany_of_list_zip_get_oldval; eauto.
    - (* interact *)
      cbn [cmd_writes] in Hnotin.
      eapply Semantics.exec.interact; try eassumption.
      intros mReceive resvals Hmid.
      specialize (H2 mReceive resvals Hmid).
      destruct H2 as [l' [Hputmany Hcont]].
      exists l'. split; [exact Hputmany|].
      intros m' Hsplit'.
      split; [|apply Hcont; exact Hsplit'].
      eapply map.putmany_of_list_zip_get_oldval; eauto.
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
  Proof.
    intros fs c.
    induction c; intros x v t m l post Hnotin Hget Hwp.
    - (* cmd.skip *)
      cbn in Hwp |- *. split; [exact Hget | exact Hwp].
    - (* cmd.set y e — y ≠ x *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [val [Hdexpr Hpost]].
      exists val. split; [exact Hdexpr|].
      cbv [dlet.dlet] in *.
      rewrite map.get_put_diff.
      { split; [exact Hget | exact Hpost]. }
      intros Hxx. apply Hnotin. subst. left. reflexivity.
    - (* cmd.unset y *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      cbv [dlet.dlet] in *.
      rewrite map.get_remove_diff.
      { split; [exact Hget | exact Hwp]. }
      intros Hxx. apply Hnotin. subst. left. reflexivity.
    - (* cmd.store sz e1 e2 — no local write *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [addr [Haddr [val [Hval Hstore]]]].
      exists addr. split; [exact Haddr|].
      exists val. split; [exact Hval|].
      (* WP.store is: exists m', Memory.store sz m a v = Some m' /\ post m'.
         We weaken [post] in place. *)
      unfold WeakestPrecondition.store in *.
      destruct Hstore as [m' [Hstore Hpost]].
      exists m'. split; [exact Hstore|].
      split; [exact Hget | exact Hpost].
    - (* cmd.stackalloc y n c' — y fresh, recurse *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [Hmod Hcont].
      split; [exact Hmod|].
      intros a mStack mCombined Hany Hsplit.
      specialize (Hcont a mStack mCombined Hany Hsplit).
      cbv [dlet.dlet] in *.
      (* Apply IHc to strengthen Hcont's post with [map.get l' x = Some v],
         then use Proper_cmd to move the conjunct into the exists. *)
      apply IHc with (x := x) (v := v) in Hcont.
      2: { intros H. apply Hnotin. right. exact H. }
      2: { rewrite map.get_put_diff; [exact Hget|].
           intros Hxx. apply Hnotin. subst. left. reflexivity. }
      eapply WeakestPreconditionProperties.Proper_cmd; [ | exact Hcont ].
      intros t' mC' l' [Hget' [m' [mStack' [Hany' [Hsplit' Hpost]]]]].
      exists m', mStack'. split; [exact Hany'|]. split; [exact Hsplit'|].
      split; [exact Hget' | exact Hpost].
    - (* cmd.cond e ct cf *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [val [Hdexpr [Ht Hf]]].
      exists val. split; [exact Hdexpr|].
      split.
      + intros Hne. apply IHc1;
          [intros H; apply Hnotin; apply in_or_app; left; exact H
          | exact Hget | exact (Ht Hne)].
      + intros Heq. apply IHc2;
          [intros H; apply Hnotin; apply in_or_app; right; exact H
          | exact Hget | exact (Hf Heq)].
    - (* cmd.seq c1 c2 — the hard case: thread invariant through continuation *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      fold WeakestPrecondition.cmd in *.
      (* Hwp : cmd fs c1 t m l (fun t' m' l' => cmd fs c2 t' m' l' post).
         Goal: cmd fs c1 t m l
                 (fun t' m' l' => cmd fs c2 t' m' l'
                    (fun t'' m'' l'' => map.get l'' x = Some v /\ post t'' m'' l'')).
         Apply IHc1 to weaken Hwp's post to
           (fun t' m' l' => map.get l' x = Some v /\ cmd fs c2 t' m' l' post).
         Then weaken further using Proper_cmd + IHc2 inside. *)
      apply IHc1 with (x := x) (v := v) in Hwp;
        [ | intros H; apply Hnotin; apply in_or_app; left; exact H
          | exact Hget ].
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ | exact Hwp].
      intros tr' mem' l' [Hget' Hc2].
      apply IHc2; [intros H; apply Hnotin; apply in_or_app; right; exact H
                  | exact Hget' | exact Hc2].
    - (* cmd.while e body — WP drops to Semantics.exec; use frame_locals_exec. *)
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      apply frame_locals_exec with (x := x) (v := v) in Hwp; assumption.
    - (* cmd.call binds fname args *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [vargs [Hargs Hcall]].
      exists vargs. split; [exact Hargs|].
      eapply Semantics.weaken_call; [exact Hcall|].
      intros t' m' rets [l' [Hputmany Hpost]].
      exists l'. split; [exact Hputmany|].
      split; [|exact Hpost].
      eapply map.putmany_of_list_zip_get_oldval; eauto.
    - (* cmd.interact binds action args *)
      cbn [cmd_writes] in Hnotin.
      cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body] in Hwp |- *.
      destruct Hwp as [vargs [Hargs [mKeep [mGive [Hsplit Hext]]]]].
      exists vargs. split; [exact Hargs|].
      exists mKeep, mGive. split; [exact Hsplit|].
      eapply Semantics.ext_spec.weaken; [|exact Hext].
      intros mReceive rets [l' [Hputmany Hcont]].
      exists l'. split; [exact Hputmany|].
      intros m' Hsplit'.
      split; [|apply Hcont; exact Hsplit'].
      eapply map.putmany_of_list_zip_get_oldval; eauto.
  Qed.

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
    intros fs c xs. induction xs as [|x xs' IH]; intros t m l post Hnot Hget Hwp.
    - (* xs = [] *)
      eapply WeakestPreconditionProperties.Proper_cmd; [|exact Hwp].
      intros t' m' l' Hpost. split; [constructor|exact Hpost].
    - (* xs = x :: xs' *)
      inversion Hnot as [|? ? Hnx Hnxs]; subst; clear Hnot.
      inversion Hget as [|? ? Hgx Hgxs]; subst; clear Hget.
      destruct Hgx as [v Hgetv].
      apply frame_locals_wp with (x := x) (v := v) in Hwp;
        [|exact Hnx|exact Hgetv].
      apply IH in Hwp; [|exact Hnxs|exact Hgxs].
      eapply WeakestPreconditionProperties.Proper_cmd; [|exact Hwp].
      intros t' m' l' [Hforall [Hgetx Hpost]].
      split; [|exact Hpost].
      constructor; [|exact Hforall].
      rewrite Hgetv, Hgetx. reflexivity.
  Qed.

End FrameLocals.
