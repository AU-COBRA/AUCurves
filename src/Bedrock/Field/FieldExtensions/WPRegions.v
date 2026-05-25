(** * Generic WP-region lemmas (representation-agnostic).

    A central, reusable library for the bedrock2 WP "stack-buffer" pattern that
    shows up in every pairing / MSM proof: allocate N scratch buffers, run a body,
    deallocate them.  Proving each region by an UNROLLED [repeat straightline] makes
    the [Qed] kernel-check super-linear in N (measured ~N^2; see
    docs/bw6-761-optimal-ate-qed-performance.md).  Proving it ONCE here by induction
    over the buffer list, then APPLYING it, makes the per-use [Qed] cost O(1).

    The lemmas are agnostic to the field representation: a buffer is just an address
    + size + a predicate that entails [anybytes] (e.g. [FElem]/[Placeholder]).  So
    BW6 (Fp3/Fp6), BN254 (Fp2), MSM, etc. all reuse them. *)
From Stdlib Require Import Lists.List ZArith Strings.String. Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.dlet.
Require Import bedrock2.Memory.
Require Import bedrock2.Syntax bedrock2.Semantics bedrock2.WeakestPrecondition.

Section WPRegions.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Init.Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  (* Right-nested separating conjunction of a list of predicates, with a frame [R]. *)
  Fixpoint sep_list (Ps : list (mem -> Prop)) (R : mem -> Prop) : mem -> Prop :=
    match Ps with
    | [] => R
    | P :: rest => sep P (sep_list rest R)
    end.

  (* A scratch buffer: the predicate currently holding it, its address+size, and the
     fact that the predicate entails [anybytes] (i.e. it is deallocatable). *)
  Record Buffer := {
    b_pred : mem -> Prop;
    b_addr : word;
    b_sz   : Z;
    b_ent  : forall mm, b_pred mm -> Memory.anybytes b_addr b_sz mm
  }.

  (* The nested [stackalloc] dealloc obligation for a list of buffers, innermost-first. *)
  Fixpoint dealloc_post (bufs : list Buffer) (P : mem -> Prop) (mFull : mem) : Prop :=
    match bufs with
    | [] => P mFull
    | b :: rest => exists mSmall mStack,
        Memory.anybytes (b_addr b) (b_sz b) mStack
        /\ map.split mFull mSmall mStack
        /\ dealloc_post rest P mSmall
    end.

  (* DEALLOC: peel all [bufs] back to [anybytes] in one O(1) lemma application.
     Proved once by induction over the buffer list. *)
  Lemma dealloc_buffers :
    forall (bufs : list Buffer) (R P : mem -> Prop) (mFull : mem),
      sep_list (List.map b_pred bufs) R mFull ->
      (forall mk, R mk -> P mk) ->
      dealloc_post bufs P mFull.
  Proof.
    induction bufs as [|b rest IH]; intros R P mFull Hsep HP;
      cbn [sep_list List.map dealloc_post] in *.
    - apply HP. exact Hsep.
    - destruct Hsep as (mp & mq & Hsplit & Hb & Hrest).
      exists mq, mp.
      split. { apply (b_ent b). exact Hb. }
      split. { apply map.split_comm. exact Hsplit. }
      eapply IH. { exact Hrest. } { exact HP. }
  Qed.

End WPRegions.

Section AllocRegions.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Init.Byte.byte}
          {locals: map.map String.string word}
          {ext_spec: Semantics.ExtSpec}.

  (* ALLOC: one [cmd.stackalloc], factored as an O(1) lemma.  bedrock2's stackalloc WP
     (WeakestPrecondition.v) COUPLES the alloc with its dealloc obligation: the body
     gets a fresh [anybytes] buffer [a] (size [n]) split into memory and [x ↦ a] in
     locals, and must establish [post] wrapped with the matching re-[anybytes] split.
     Sealing this once and APPLYING it (vs `straightline`'s inline term, which the top
     [Qed] re-checks) keeps each stackalloc's [Qed] cost O(1).  Apply it once per
     stackalloc: N applications ⟹ top [Qed] linear in N, not super-linear (see
     docs/bw6-761-optimal-ate-qed-performance.md).  The residual N-deep dealloc nest in
     the body's post is then peeled by [dealloc_buffers] above (also O(1)). *)
  Lemma alloc_one (e: Semantics.env) (x: String.string) (n: Z) (c: Syntax.cmd)
        (t: Semantics.trace) (m: mem) (l: locals)
        (post: Semantics.trace -> mem -> locals -> Prop) :
    Z.modulo n (Memory.bytes_per_word width) = 0 ->
    (forall a mStack mCombined,
        Memory.anybytes a n mStack -> map.split mCombined m mStack ->
        WeakestPrecondition.cmd e c t mCombined (map.put l x a)
          (fun t' mC' l' => exists m' mS',
             Memory.anybytes a n mS' /\ map.split mC' m' mS' /\ post t' m' l')) ->
    WeakestPrecondition.cmd e (cmd.stackalloc x n c) t m l post.
  Proof.
    intros Hmod Hbody.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    split; [ exact Hmod | ].
    intros a mStack mCombined Hany Hsplit. cbv [dlet].
    exact (Hbody a mStack mCombined Hany Hsplit).
  Qed.

End AllocRegions.

(** A monolithic "N-stackallocs at once" wrapper over [alloc_one] is possible (induct on
    a [list (string * Z)]), but the stackalloc semantics deallocate in REVERSE order, so
    its statement carries a [rev] in the dealloc nest.  In practice the pairing/MSM proofs
    interleave per-buffer work between allocs, so applying [alloc_one] once per stackalloc
    (then [dealloc_buffers] for the whole nest) is both simpler and a better fit. *)
