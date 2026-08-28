(** * BignumStoreFold — shared store/fold machinery for Bignum-style
      bedrock2 WP proofs over word-by-word Montgomery field elements.

    UNCOMPILED DRAFT (2026-08-28).  This file consolidates the proof
    machinery developed during the P-256 G1-add first-execution debug
    campaign (see [scripts/logs/p256_g1_add_debug_notes.md] and the
    working copy of [src/Bedrock/Curve/P256_G1_Add_Spec.v]); it has not
    yet been compiled — a memory-critical build occupies the tree.  The
    lemmas [many_Scalars_fold_Bignum] / [fold4_scalars_Bignum] follow
    proof scripts that executed during that campaign;
    [fold6_scalars_Bignum] is a mechanical 6-limb extension and is
    untested.

    Contents:
    - [many_Scalars_fold_Bignum]: generic n-limb fold of a
      [many_Scalars] chain into a [Bignum], from [Bignum_n_Scalar].
    - [fold4_scalars_Bignum] / [fold6_scalars_Bignum]: the same fold
      stated over the LITERAL nested scalar subtree that the store
      phase leaves in the sep chain (4 resp. 6 limbs).  The literal
      statement is what makes [seprewrite_in] match syntactically; the
      generic lemma cannot be used for that purpose because the
      hypothesis never mentions [many_Scalars].
    - The stackalloc-intro conversion pass
      ([stackalloc_anybytes_to_arrays]): this bedrock2 release's
      [straightline] consumes the stackalloc intros itself, leaving raw
      [anybytes]/[map.split] pairs; the pass converts each to a byte
      array merged into the ambient sep chain (debug-note defect
      class 2).
    - The byte-array → [Bignum] conversion pass
      ([byte_arrays_to_Bignums]).
    - The decomposed store-step template ([store_step_sep_solve],
      [wp_store_scalar], [next_store_prelude]) and the literal-dexpr
      bridges ([dexpr_literal_bridge], [dexpr_var_offset_bridge])
      (debug-note defect classes 1 and 5: committed single store
      steps instead of one packed [repeat (...)]).
    - Store-target destructuring helpers
      ([destruct_store_target_bignum], [unfold_bignum_to_scalars]) and
      [clear_stale_seps].

    Conventions and caveats:
    - The fold lemmas are stated in the generic
      width/word/mem section context of [Bedrock.Util.Bignum].
    - The Ltac blocks are transcriptions of the P-256 working copy and
      hard-code the [BasicC64Semantics] 64-bit instance where the
      original did (explicit [@word.of_Z 64 BasicC64Semantics.word]).
      All current users (P-224/P-256/P-384 and the a=0 curves) are
      BasicC64.
    - Debug-note defect class 4: [Local Open Scope Z_scope] makes a
      bare [4] in an Ltac pattern parse as [4%Z] against [4%nat]
      terms, so every limb count below is written [..%nat] or passed
      as an explicit argument by the caller.
    - [store_step_sep_solve] ends in [ecancel_assumption]; files that
      rebind it ([Local Ltac ecancel_assumption ::= ...], e.g. to the
      O(n) fast variant) get the rebound tactic, since Ltac [::=]
      redefinition is dynamic.  The P-256 campaign ran the store
      ecancels through the [ecancel_assumption_fast] override.
    - Escalation if a store-step ecancel stalls: the reflective
      [flatten_seps] + [cancel_seps_at_indices] recipe
      (memory: reference_slow_proofs_fiat, H3 worked example). *)

Require Import Coq.Init.Byte.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Array.
Require Import bedrock2.Memory.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.BasicC64Semantics.
Require bedrock2.Scalars.
Require bedrock2.ArrayCasts.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Properties.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Bedrock.Util.Word.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Import ListNotations.

(* ================================================================ *)
(* §1. Fold lemmas: nested scalar subtree ↔ Bignum                   *)
(* ================================================================ *)

Section folds.
  Context
    {width : Z} {BW : Bitwidth.Bitwidth width} {word : word.word width}
    {word_ok : word.ok word}
    {mem : Interface.map.map word Byte.byte} {mem_ok : Interface.map.ok mem}.

  Local Notation word_size_in_bytes := (Memory.bytes_per_word width).
  Local Notation Bignum := (@Bignum width word mem) (only parsing).

  Local Infix "*" := sep : sep_scope.
  Delimit Scope sep_scope with sep.

  (** Generic form.  Useful for stating facts; NOT the seprewrite
      workhorse (the hypothesis after a store phase contains the
      literal nested subtree, not [many_Scalars]). *)
  Lemma many_Scalars_fold_Bignum (k : nat) (a : word) (lv : list word) :
    length lv = k ->
    Lift1Prop.iff1 (many_Scalars k a lv) (Bignum k a lv).
  Proof.
    intros Hlen.
    etransitivity.
    2: { symmetry. apply Bignum_n_Scalar. }
    intros mm; split; intro Hm.
    - apply sep_emp_l. auto.
    - apply sep_emp_l in Hm. apply Hm.
  Qed.

  (** Deterministic 4-scalar → Bignum fold: the exact nested subtree
      the store phase leaves in the sep chain.  [seprewrite_in] with
      this iff1 replaces the searching ecancel-based reassembly.
      Statement and proof are the P-256 campaign's
      [fold4_scalars_Bignum] (a Local Lemma near the theorem there),
      lifted to the generic section context. *)
  Lemma fold4_scalars_Bignum aa v0 v1 v2 v3 :
    Lift1Prop.iff1
      (Scalars.scalar aa v0 *
       (Scalars.scalar (word.add (word.of_Z word_size_in_bytes) aa) v1 *
        (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                           (word.add (word.of_Z word_size_in_bytes) aa)) v2 *
         (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                            (word.add (word.of_Z word_size_in_bytes)
                               (word.add (word.of_Z word_size_in_bytes) aa))) v3 *
          emp True))))%sep
      (Bignum 4%nat aa [v0; v1; v2; v3]).
  Proof.
    etransitivity.
    2: { symmetry. apply Bignum_n_Scalar. }
    cbn [many_Scalars hd tl].
    intro mm; split; intro Hm'.
    - apply sep_emp_l. split; [reflexivity| exact Hm'].
    - apply sep_emp_l in Hm'. apply Hm'.
  Qed.

  (** 6-limb variant (P-384).  Mechanical extension of
      [fold4_scalars_Bignum]; untested. *)
  Lemma fold6_scalars_Bignum aa v0 v1 v2 v3 v4 v5 :
    Lift1Prop.iff1
      (Scalars.scalar aa v0 *
       (Scalars.scalar (word.add (word.of_Z word_size_in_bytes) aa) v1 *
        (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                           (word.add (word.of_Z word_size_in_bytes) aa)) v2 *
         (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                            (word.add (word.of_Z word_size_in_bytes)
                               (word.add (word.of_Z word_size_in_bytes) aa))) v3 *
          (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                             (word.add (word.of_Z word_size_in_bytes)
                                (word.add (word.of_Z word_size_in_bytes)
                                   (word.add (word.of_Z word_size_in_bytes) aa)))) v4 *
           (Scalars.scalar (word.add (word.of_Z word_size_in_bytes)
                              (word.add (word.of_Z word_size_in_bytes)
                                 (word.add (word.of_Z word_size_in_bytes)
                                    (word.add (word.of_Z word_size_in_bytes)
                                       (word.add (word.of_Z word_size_in_bytes) aa))))) v5 *
            emp True))))))%sep
      (Bignum 6%nat aa [v0; v1; v2; v3; v4; v5]).
  Proof.
    etransitivity.
    2: { symmetry. apply Bignum_n_Scalar. }
    cbn [many_Scalars hd tl].
    intro mm; split; intro Hm'.
    - apply sep_emp_l. split; [reflexivity| exact Hm'].
    - apply sep_emp_l in Hm'. apply Hm'.
  Qed.

End folds.

(* ================================================================ *)
(* §2. Stackalloc-intro conversion pass (debug-note defect class 2)  *)
(* ================================================================ *)

(** This bedrock2 release's [straightline] consumes the stackalloc
    intros itself, so a destruct-based [straightline'] branch never
    fires; raw [anybytes]/[map.split] pairs must be converted by an
    explicit post-pass.  One step converts one pair to a byte ARRAY
    (keeping the [length bs = Z.to_nat num_bytes] fact the store
    script keys on) and merges it into the ambient sep chain via
    [alloc_seps_alt]/[empty_frame] (Bedrock.Util.Util).
    Transcribed from the debugged P-256 working copy. *)
Ltac stackalloc_anybytes_to_array_step :=
  lazymatch goal with
  | Hany : anybytes ?aa _ ?mS,
    Hsplit : Interface.map.split ?mnew ?minit ?mS,
    Hminit : ?mcond ?minit |- _ =>
    let bs := fresh "bs" in
    let Harr := fresh "Harr" in
    let Hlen := fresh "Hlen" in
    let R := fresh "R" in
    let Hmnew := fresh "Hmnew" in
    apply anybytes_to_array_1 in Hany;
    destruct Hany as [bs [Harr Hlen]];
    destruct (alloc_seps_alt mnew minit mS mcond
               (array ptsto (@word.of_Z 64 BasicC64Semantics.word 1) aa bs)
               Hsplit
               (empty_frame mcond minit Hminit)
               (empty_frame (array ptsto (@word.of_Z 64 BasicC64Semantics.word 1) aa bs)
                  mS Harr))
      as [R Hmnew];
    clear Hsplit Harr
  end.

Ltac stackalloc_anybytes_to_arrays :=
  repeat stackalloc_anybytes_to_array_step.

(* ================================================================ *)
(* §3. Byte-array → Bignum conversion pass                           *)
(* ================================================================ *)

(** Convert one [array ptsto] byte block to a [Bignum nlimbs] via
    [Bignum_of_bytes].  [nlimbs] must be an explicit [_%nat] literal
    (defect class 4) and [nbytes] the corresponding [Z] byte count
    (32 for 4 limbs, 48 for 6). *)
Ltac byte_array_to_Bignum_step nlimbs nbytes :=
  lazymatch goal with
  | Hmem : context[array ptsto _ ?ptr ?bs] |- _ =>
    lazymatch goal with
    | _ : context[Bignum nlimbs ptr _] |- _ => fail
    | _ =>
      let Hiff := fresh "Hiff" in
      assert (Hiff : Lift1Prop.iff1
              (array ptsto (@word.of_Z 64 BasicC64Semantics.word 1) ptr bs)
              (Bignum nlimbs ptr
                 (ArrayCasts.bs2ws (Z.to_nat (Memory.bytes_per_word 64)) bs)))
      by (apply Bignum_of_bytes;
          match goal with
          | Hl : Datatypes.length bs = Z.to_nat nbytes |- _ =>
            rewrite Hl; reflexivity
          end);
      seprewrite_in Hiff Hmem; clear Hiff
    end
  end.

Ltac byte_arrays_to_Bignums nlimbs nbytes :=
  repeat (byte_array_to_Bignum_step nlimbs nbytes).

(** Clear separation facts about memories other than the one in the
    current [store]/[cmd] goal (keeps the store-step ecancel context
    small; cf. memory feedback_clear_intermediate_seps). *)
Ltac clear_stale_seps :=
  repeat match goal with
  | H : (_ * _)%sep ?mem |- _ =>
    lazymatch goal with
    | |- WeakestPrecondition.store _ ?m _ _ _ =>
      assert_fails unify m mem; clear H
    | |- WeakestPrecondition.cmd _ _ _ ?m _ _ =>
      assert_fails unify m mem; clear H
    | _ => fail
    end
  end.

(* ================================================================ *)
(* §4. Store-target destructuring                                    *)
(* ================================================================ *)

(** Destructure a list variable [wsl'] into its elements, given
    [len_lem : Datatypes.length wsl' = k] for a concrete [k]; each
    over-short case dies by [discriminate], the over-long case by the
    final destruct.  n-generic replacement for the P-256 campaign's
    fixed [destruct wsl' as [|r0 [|r1 [|r2 [|r3 [|]]]]]] (new tactic,
    not verbatim from the working copy). *)
Ltac destruct_wordlist_by_length wsl' len_lem :=
  repeat (let w := fresh "w" in
          destruct wsl' as [|w wsl'];
          [ simpl in len_lem; discriminate | ]);
  destruct wsl'; [ | simpl in len_lem; discriminate ].

(** Find the [Bignum nlimbs p ?wsl] covering the current store target
    [p], prove its length ([bs2ws_length] route from the conversion
    pass), and destructure it into concrete limb variables.
    [nlimbs] a [_%nat] literal, [nbytes] the matching [Z] byte count.
    Generalization of the P-256 working copy's two inline blocks. *)
Ltac destruct_store_target_bignum nlimbs nbytes :=
  lazymatch goal with
  | |- WeakestPrecondition.store _ _ ?p _ _ =>
    lazymatch goal with
    | Hmem : context[Bignum nlimbs p ?wsl] |- _ =>
      let len_lem := fresh "Hlen_bn" in
      assert (len_lem : Datatypes.length wsl = nlimbs)
        by (match goal with
            | Hbs : Datatypes.length ?bs = Z.to_nat nbytes |- _ =>
              lazymatch wsl with
              | ArrayCasts.bs2ws _ bs =>
                rewrite ArrayCasts.bs2ws_length;
                  [rewrite Hbs; cbv; reflexivity
                  |cbv; discriminate
                  |rewrite Hbs; cbv; reflexivity]
              end
            end);
      let wsl' := fresh "wsl'" in
      let wsl_eq := fresh "wsl_eq" in
      remember wsl as wsl' eqn:wsl_eq;
      destruct_wordlist_by_length wsl' len_lem;
      clear len_lem wsl_eq
    end
  end.

(** Unfold the store-target [Bignum] (now over a concrete cons-list)
    into the nested scalar chain via [Bignum_n_Scalar], in place. *)
Ltac unfold_bignum_to_scalars nlimbs :=
  lazymatch goal with
  | H : context[Bignum nlimbs ?p ?l] |- _ =>
    lazymatch l with
    | _ :: _ =>
      let Hiff := fresh "Hiff" in
      pose proof (Bignum_n_Scalar nlimbs p l) as Hiff;
      cbn [many_Scalars hd tl] in Hiff;
      seprewrite_in Hiff H; clear Hiff
    end
  end.

(* ================================================================ *)
(* §5. Decomposed store steps + literal-dexpr bridges                *)
(*     (debug-note defect classes 1 and 5)                           *)
(* ================================================================ *)

(** Solve the sep side condition of [Scalars.store_word_of_sep]:
    subst the let-bound target address, normalize offset addresses to
    the [N (word.add ... )] form via [next_word']/[word_add_0], then
    cancel against the ambient hypothesis.  [ecancel_assumption] here
    picks up any file-local [::=] rebinding (the campaign ran it
    through [ecancel_assumption_fast]). *)
Ltac store_step_sep_solve :=
  repeat match goal with
         | |- ((Scalars.scalar ?addr _) * _)%sep _ => subst addr
         | _ => idtac
         end;
  repeat (rewrite next_word'; try rewrite word_add_0);
  ecancel_assumption.

(** One committed store step (never pack these into a [repeat]: the
    packed form re-runs the 26-atom ecancel under in-sentence
    backtracking and diverges — defect classes 1 and 5). *)
Ltac wp_store_scalar :=
  eapply Scalars.store_word_of_sep;
  [ store_step_sep_solve | intros ? ? ].

(** Expose the next command after a store continuation. *)
Ltac open_cmd :=
  unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].

Ltac subst_word_lets :=
  repeat match goal with x := _ : word.rep |- _ => subst x end.

Ltac subst_all_lets :=
  repeat match reverse goal with x := _ |- _ => subst x end.

(** Literal-dexpr bridge: discharge the [dexpr] obligation for a
    literal store VALUE (or any bare-literal expression).  The cbv
    list must include [expr_body], [get], [literal], [interp_binop]
    (the released [straightline] does not reduce these here). *)
Ltac dexpr_literal_bridge :=
  eexists; split;
  [ cbv [dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.literal dlet.dlet]; reflexivity | ].

(** Literal-dexpr bridge for a [var + literal-offset] store ADDRESS. *)
Ltac dexpr_var_offset_bridge :=
  eexists; split;
  [ cbv [dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal
         Semantics.interp_binop dlet.dlet];
    eexists; split; [reflexivity|]; reflexivity | ].

(** Prelude for each store after the first of a block: open the next
    cmd, bridge the address and value dexprs, drop stale word lets.
    (The FIRST store of a block is prefaced only by
    [dexpr_literal_bridge] for its value — its address is a bare
    variable consumed by [store]'s own obligation.) *)
Ltac next_store_prelude :=
  open_cmd; dexpr_var_offset_bridge; dexpr_literal_bridge; subst_word_lets.

(* ================================================================ *)
(* §6. Fold-back after a store block                                 *)
(* ================================================================ *)

(** Rebuild the freshly stored constant's [Bignum] from the nested
    scalar chain.  Try the 6-limb fold FIRST: on a 6-limb chain the
    4-limb pattern can match an inner 4-scalar suffix (both end in
    [emp True]) and fold the wrong subtree. *)
Ltac fold_stored_scalars_Bignum :=
  match goal with
  | [ Hc : (_ * _)%sep _ |- _ ] =>
    first [ seprewrite_in fold6_scalars_Bignum Hc
          | seprewrite_in fold4_scalars_Bignum Hc ]
  end.
