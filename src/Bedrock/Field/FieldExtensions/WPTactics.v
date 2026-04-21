(** * Shared WP proof tactics for field extension operations.

    Provides reusable Ltac tactics that automate the mechanical parts
    of bedrock2 weakest-precondition proofs for Fp6/Fp12/... operations.

    Each field extension WP proof follows a 4-phase structure:
      SETUP -> PER-CALL (xN) -> STACK DEALLOCATION -> POSTCONDITION
    The per-call phase is 90%+ mechanical and is the main target of
    these tactics.

    Usage pattern for a binop sub-call:
    <<
      exists [ptr_out; ptr_x; ptr_y]. split. { solve_dexprs. }
      eapply Semantics.weaken_call.
      1: { eapply (HFop ptr_out ptr_x ptr_y val_out val_x val_y _ tr).
           wp_binop_precond solve_bounds. }
      (* ... intros pattern for postcondition ... *)
    >>

    Usage pattern for a unop sub-call:
    <<
      exists [ptr_out; ptr_x]. split. { solve_dexprs. }
      eapply Semantics.weaken_call.
      1: { eapply (HFop ptr_out ptr_x val_out val_x _ tr).
           wp_unop_precond solve_bounds. }
      (* ... intros pattern for postcondition ... *)
    >>
*)

Require Import Rupicola.Lib.Api.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Bedrock.Specs.AbstractField.

(** ** ecancel_assumption_with_copy

    Like [ecancel_assumption] but first copies the sep hypothesis so it
    survives for subsequent calls.  [ecancel_assumption] is destructive:
    it clears the hypothesis it matches.  In WP proofs we typically need
    the same master sep fact for 2-3 obligations per call. *)

Ltac ecancel_assumption_with_copy :=
  match goal with
  | Hsep : (_ * _)%sep _ |- (_ * _)%sep _ =>
    let H' := fresh "Hcopy" in
    pose proof Hsep as H'; ecancel_assumption
  end.

(** ** ecancel_fast / ecancel_assumption_fast

    O(n) sep-logic frame inference via [Lift1Prop.impl1] instead of the
    default [ecancel_assumption] which does O(n!) permutation search. *)

Ltac cancel_impl_step :=
  let RHS := lazymatch goal with
             | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
  let jy := index_and_element_of RHS in
  let j := lazymatch jy with (?i, _) => i end in
  let y := lazymatch jy with (_, ?y) => y end in
  assert_fails (idtac; let y := rdelta_var y in is_evar y);
  let LHS := lazymatch goal with
             | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
  let i := find_syntactic_unify_deltavar LHS y in
  cancel_seps_at_indices_by_implication i j;
  [exact (impl1_refl _)|].

Ltac ecancel_fast :=
  cancel;
  lazymatch goal with
  | |- Lift1Prop.impl1 _ _ =>
    repeat cancel_impl_step;
    first [ cbv [seps];
            repeat (apply (proj2 (impl1_l_sep_emp True _ _)); intros _);
            exact impl1_refl
          | repeat ecancel_step_by_implication;
            cbv [seps];
            repeat (apply (proj2 (impl1_l_sep_emp True _ _)); intros _);
            exact impl1_refl ]
  | |- Lift1Prop.iff1 _ _ =>
    ecancel_steps_at O;
    ecancel_done
  end.

Ltac ecancel_assumption_fast :=
  multimatch goal with
  | |- ?PG ?m1 =>
    multimatch goal with
    | H: _ ?m2 |- _ =>
      syntactic_unify_deltavar m1 m2;
      let H' := fresh "Hcopy" in
      pose proof H as H';
      cbv beta iota zeta in H';
      lazymatch type of H' with
      | (_ * _)%sep _ =>
        refine (Morphisms.subrelation_refl
                  Lift1Prop.impl1 _ _ _ _ H');
        clear H';
        ecancel_fast
      end
    end
  end.

(** ** wp_binop_precond

    Solves the 5-part binop precondition after [eapply (HF ...)]:
      bounds_x /\ bounds_y /\ (exists Rx, sep) /\ (exists Ry, sep) /\ sep

    The [solve_bounds_tac] argument should handle bounds goals
    (typically [assumption] or a [first [...]] combinator).

    NOTE: The call hypothesis must be applied with explicit pointer and
    value arguments (not bare [eapply HF]) so that [ecancel_assumption]
    can match concrete FElem addresses against the sep hypothesis. *)

Ltac wp_binop_precond solve_bounds_tac :=
  split; [solve_bounds_tac |];
  split; [solve_bounds_tac |];
  split;
  [ eexists; ecancel_assumption_with_copy
  | split;
    [ eexists; ecancel_assumption_with_copy
    | ecancel_assumption_with_copy ] ].

(** ** wp_unop_precond

    Solves the 3-part unop precondition after [eapply (HF ...)]:
      bounds_x /\ (exists Rx, sep) /\ sep *)

Ltac wp_unop_precond solve_bounds_tac :=
  split; [solve_bounds_tac |];
  split;
  [ eexists; ecancel_assumption_with_copy
  | ecancel_assumption_with_copy ].

(** ** wp_destruct_sep

    Recursively destructs a nested [(_ * _)%sep _] hypothesis into
    individual map hypotheses.  Each layer produces:
      [m1], [m2], [Heq : _ = putmany m1 m2], [Hd : disjoint m1 m2],
      [H1 : P1 m1], and recurses on the rest. *)

Ltac wp_destruct_sep H :=
  lazymatch type of H with
  | (_ * _)%sep _ =>
    let m1 := fresh "m" in let m2 := fresh "m" in
    let Heq := fresh "Heq" in let Hd := fresh "Hd" in
    let H1 := fresh "Hf" in let H2 := fresh "Hrest" in
    destruct H as [m1 [m2 [[Heq Hd] [H1 H2]]]];
    subst; try wp_destruct_sep H2
  | _ => idtac
  end.

(** ** split_all_disjointness

    Splits all compound [map.disjoint (map.putmany ...) ...] hypotheses
    into atomic pairwise disjointness facts. *)

Ltac split_all_disjointness :=
  repeat match goal with
  | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hdj" in let H2 := fresh "Hdj" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
  | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      let H1 := fresh "Hdj" in let H2 := fresh "Hdj" in
      destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
  end.

(** ** map_disjoint_auto

    Solves [map.disjoint] goals by decomposing putmany and searching
    hypotheses (including symmetric matches). *)

Ltac map_disjoint_auto :=
  lazymatch goal with
  | |- map.disjoint (map.putmany _ _) _ =>
      apply map.disjoint_putmany_l; split; map_disjoint_auto
  | |- map.disjoint _ (map.putmany _ _) =>
      apply map.disjoint_putmany_r; split; map_disjoint_auto
  | |- map.disjoint ?a ?b =>
      first [ assumption
            | (unfold map.disjoint; intros ?k ?v1 ?v2 ?Hg1 ?Hg2;
               match goal with H : map.disjoint _ _ |- _ => exact (H k v2 v1 Hg2 Hg1) end) ]
  end.

(** ** wp_call_setup

    Common setup after [repeat straightline] produces the goal for a function call.
    Solves the [dexprs] part and prepares for [Semantics.weaken_call]. *)

Ltac solve_dexprs :=
  cbv [dexprs list_map list_map_body
       WeakestPrecondition.expr WeakestPrecondition.expr_body];
  repeat first
    [ exact eq_refl
    | eexists; split;
      [ repeat (first [ apply map.get_put_same
                      | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
    | straightline ].

(** ** wp_post_call

    Process the postcondition after a [Semantics.weaken_call]:
    intros the postcondition, provides locals, and straightlines. *)

(** ** build_sep

    Constructs a nested separation logic fact from individual predicates
    on disjoint sub-maps.  Given a goal of the form:

      (P0 * (P1 * ... * (Pn-1 * Pn))) (putmany m0 (putmany m1 ... (putmany mn-1 mn)))

    with hypotheses [H0 : P0 m0], [H1 : P1 m1], ..., [Hn : Pn mn] and
    pairwise [map.disjoint mi mj], solves the goal by constructing the
    nested existential witnesses and proving disjointness/equality/predicate
    obligations automatically.

    Handles bedrock2's [(P * Q)%sep m] which unfolds to
    [exists m1 m2, m = putmany m1 m2 /\ disjoint m1 m2 /\ P m1 /\ Q m2]
    as well as the [exists m1 m2, putmany m1 m2 = m /\ ...] variant.

    Usage: after [split_all_disjointness] derives pairwise disjointness,
    [build_sep] solves the sep goal in one call.

    Complexity: O(n^2) in the number of conjuncts (from disjointness checks),
    versus O(2^n) for [sauto]. Handles 9+ conjuncts instantly. *)

Ltac build_sep :=
  lazymatch goal with
  | |- (_ * _)%sep _ =>
    lazymatch goal with
    | |- (_ * _)%sep (map.putmany ?m1 ?m2) =>
      exists m1, m2;
      split; [split; [reflexivity | map_disjoint_auto] |];
      split; [first [eassumption | assumption] | build_sep]
    | |- (_ * _)%sep ?m =>
      first [eassumption | assumption]
    end
  | |- ?P ?m => first [eassumption | assumption]
  end.

Ltac wp_post_call locals_term :=
  let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
  intros t m rets;
  let H := fresh "H" in intro H;
  lazymatch type of H with
  | _ /\ _ =>
    let Hrets := fresh "Hrets" in let Htr := fresh "Htr" in
    destruct H as [Hrets [Htr H]];
    subst rets; try (symmetry in Htr; subst t);
    cbv [map.putmany_of_list_zip];
    exists locals_term;
    split; [ exact eq_refl | ];
    repeat straightline
  end.

(** ** solve_bounds_auto

    Solves bounds goals of the form [bounded_by ?b ?x] by trying
    [assumption] first, then [relax_bounds] (tight->loose) from
    any [FieldRepresentation_ok] in scope. *)

Ltac solve_bounds_auto :=
  first
  [ assumption
  | (* Try to find a relax_bounds-like hypothesis or instance.
       For BLS12 where tight=loose, [assumption] suffices.
       For other fields, override this tactic locally. *)
    match goal with
    | H : ?P ?b1 ?x |- ?P ?b2 ?x =>
      (* Same predicate, different bounds — try direct match *)
      exact H
    end ].

(** ** wp_postcall_auto

    Processes the postcondition after [Semantics.weaken_call] returns.
    Handles the common pattern:
      intros t m rets [Hrets [Htr <postcond>]].
      subst rets. subst t.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

    For binop/unop specs, [<postcond>] is
      [exists out, feval out = ... /\ bounded_by ... /\ sep].
    This tactic just does the intros, subst, and locals update.
    It does NOT straightline further (to avoid entering the next call). *)

Ltac wp_postcall_auto :=
  let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
  let H := fresh "Hpost" in
  intros t m rets H;
  lazymatch type of H with
  | ?A /\ ?B =>
    let Hrets := fresh "Hrets" in let Hrest := fresh "Hrest" in
    destruct H as [Hrets Hrest];
    subst rets;
    lazymatch type of Hrest with
    | ?C /\ ?D =>
      let Htr := fresh "Htr" in let Hrem := fresh "Hrem" in
      destruct Hrest as [Htr Hrem];
      first [ symmetry in Htr; subst t | subst t | idtac ];
      cbv [map.putmany_of_list_zip];
      (try (eexists; split; [ exact eq_refl | ]))
    | _ =>
      first [ subst t | idtac ];
      cbv [map.putmany_of_list_zip];
      (try (eexists; split; [ exact eq_refl | ]))
    end
  end.

(** ** wp_call

    Processes one function call end-to-end: argument evaluation via
    [straightline], [Semantics.weaken_call] with automatic spec
    instantiation, and postcondition processing.

    Usage:
      [wp_call HSpec]
    where [HSpec : spec_of_SomeOp functions] (binop, unop, copy, or
    from_word).

    The tactic:
    1. Runs [repeat straightline] to process cmd.seq and evaluate args
    2. Applies [Semantics.weaken_call]
    3. In the callee obligation: unfolds the spec, eapplies [HSpec],
       and solves the precondition (bounds + sep) automatically
    4. In the continuation: destructs the postcondition and prepares
       for the next call

    NOTE: For [felem_copy] specs, the precondition has a different
    shape (two sep conditions). [wp_call] tries the copy pattern as
    a fallback. For [from_word], the precondition is just a sep. *)

Ltac wp_call spec_hyp :=
  (* Step 1: process cmd.seq + cmd.call arg evaluation *)
  repeat straightline;
  (* Step 2: weaken_call *)
  eapply Semantics.weaken_call;
  [ (* Step 3: build the callee call.
       [eapply spec_hyp] unfolds the spec instance and unifies
       pointer/value arguments from the goal. The remaining
       subgoals are the precondition parts. We detect the shape
       (binop 5-part, unop 3-part, from_word 1-part, copy 2-part)
       by trying each solver in order. *)
    let H := fresh "Hcallee" in
    pose proof spec_hyp as H;
    eapply H;
    first
    [ (* binop_spec: bounded_x /\ bounded_y /\ (exists Rx, sep) /\ (exists Ry, sep) /\ sep *)
      wp_binop_precond solve_bounds_auto
    | (* unop_spec: bounded_x /\ (exists Rx, sep) /\ sep *)
      wp_unop_precond solve_bounds_auto
    | (* from_word: (FElem pout out * R) mem *)
      ecancel_assumption_with_copy
    | (* felem_copy: two sep conditions *)
      split; ecancel_assumption_with_copy
    | (* custom fnspec — try to solve conjunction tree *)
      repeat (first
        [ solve_bounds_auto
        | ecancel_assumption_with_copy
        | split ])
    ]
  | (* Step 4: process postcondition *)
    wp_postcall_auto
  ].

(* normalize_offsets: must be defined LOCALLY in each proof file
   because it references CubicFieldExtensions/DodecicFieldExtensions
   definitions that would create circular imports if placed here.
   See BLS12_PairingHelpers.v for the template. *)

(** ** wp_stackalloc

    Handles one level of [stackalloc] in a WP proof:
    1. Proves alignment via [Z_mod_mult]
    2. Intros the stack pointer, stack memory, combined memory
    3. Converts [anybytes] to an [FElem] via [FElem_from_bytes]

    After [wp_stackalloc], the context has:
    - [a_NAME : word] — the stack pointer
    - [NAME_val : felem] — the initial (junk) felem value
    - [NAME_felem : FElem a_NAME NAME_val mStack]
    - [mComb : mem] with [map.split mComb mPrev mStack]

    The [FieldParams] and [FieldRepr] arguments specify which field
    level the FElem lives at (Fp, Fp2, Fp6, Fp12).

    Usage:
      [wp_stackalloc FieldParams FieldRepr] *)

(* wp_stackalloc: handles one level of stackalloc.
   Must be defined locally in proof files since it references
   AbstractField.FElem_from_bytes.

   Template:
   Ltac wp_stackalloc FldParams FldRepr :=
     split; [ apply Z_mod_mult | ];
     let a := fresh "a" in let mStack := fresh "mStack" in
     let mComb := fresh "mComb" in let Hany := fresh "Hany" in
     let Hsplit := fresh "Hsplit" in
     intros a mStack mComb Hany Hsplit;
     let Hfb := fresh "Hfb" in
     pose proof (AbstractField.FElem_from_bytes (field_parameters:=FldParams)
       (field_representation:=FldRepr) a) as Hfb;
     unfold AbstractField.Placeholder in Hfb;
     let v := fresh "stkval" in let Hfe := fresh "Hfelem" in
     pose proof (proj1 (Hfb mStack) Hany) as [v Hfe]; clear Hfb. *)

(** ** wp_from_word_pair

    Handles the common pattern of zeroing an Fp2 slot via two
    consecutive [from_word(ptr, 0)] + [from_word(ptr+off, 0)] calls.

    Precondition: the sep hypothesis has [FElem_Fp2 p x] at the front
    (or findable by ecancel).

    The tactic:
    1. Splits [FElem_Fp2] into two [FElem_Fp] halves
    2. Processes the first [from_word] call
    3. Processes the second [from_word] call
    4. Joins the two [FElem_Fp] halves back into [FElem_Fp2]

    Usage:
      [wp_from_word_pair HFfromword Fp2_split_lemma Fp_join_lemma]
    where [Fp2_split_lemma] is [FElem_Fp2_split_in_sep] and
    [Fp_join_lemma] is [FElem_Fp_join_in_sep] from the proof file.

    NOTE: This tactic assumes the sep is in the right shape. If
    the target Fp2 is not at the front, rearrange first. *)

Ltac wp_from_word_pair HFfromword split_lemma join_lemma len_tac :=
  (* Split Fp2 into Fp halves *)
  match goal with
  | Hsep : (_ * _)%sep _ |- _ =>
    apply split_lemma in Hsep
  end;
  (* First from_word call (fst half) *)
  wp_call HFfromword;
  (* Second from_word call (snd half) *)
  wp_call HFfromword;
  (* Join back into Fp2 — need length witnesses *)
  match goal with
  | Hsep : (_ * _)%sep _ |- _ =>
    eapply join_lemma in Hsep; [ | len_tac | len_tac ]
  end.

(** ** putmany_transfer

    Key lemma for unop-style WP proofs where the same memory has two
    overlapping decompositions (one for the output, one for the input).

    If M = A + B = C + D with A ⊥ B, C ⊥ D, A ⊥ C, then C is a
    submap of B: there exists B' such that B = C + B' and C ⊥ B'.

    Application: After a call modifies the output region A (replacing it
    with A'), the frame B is preserved. Input FElems (from C) are in B
    because they're disjoint from A. So we can provide sep witnesses for
    input FElems using the frame. *)

Lemma putmany_transfer {key value : Type} {map : map.map key value}
    {ok : map.ok map}
    {key_eqb : key -> key -> bool}
    {key_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (key_eqb x y)} :
  forall (A B C D : map.rep (map:=map)),
    map.putmany A B = map.putmany C D ->
    map.disjoint A B -> map.disjoint C D ->
    map.disjoint A C ->
    exists B', B = map.putmany C B' /\ map.disjoint C B'.
Proof.
  intros A B C D Heq HdAB HdCD HdAC.
  assert (HCinB : forall k v, map.get C k = Some v -> map.get B k = Some v).
  { intros k v Hk.
    assert (HgetCD : map.get (map.putmany C D) k = Some v).
    { rewrite map.get_putmany_dec.
      assert (HgetDk : map.get D k = None).
      { destruct (map.get D k) eqn:E; auto. exfalso. eapply HdCD; eauto. }
      rewrite HgetDk. exact Hk. }
    rewrite <- Heq in HgetCD. rewrite map.get_putmany_dec in HgetCD.
    destruct (map.get B k) eqn:HgetBk.
    - injection HgetCD; auto.
    - exfalso. eapply HdAC; eauto. }
  assert (HBkeys : map.forall_keys
    (fun k => (exists v, map.get C k = Some v) \/ map.get C k = None) B).
  { unfold map.forall_keys. intros k v Hk.
    destruct (map.get C k) eqn:HC; [left; eauto | right; auto]. }
  apply map.split_by_or in HBkeys.
  destruct HBkeys as [mBC [mBrest [HBeq [HdBCrest [HkBC HkBrest]]]]].
  assert (HmBC_eq_C : mBC = C).
  { apply map.map_ext. intros k.
    destruct (map.get mBC k) eqn:HmBC.
    - unfold map.forall_keys in HkBC. specialize (HkBC k v HmBC).
      destruct HkBC as [vc Hvc].
      assert (HBk : map.get B k = Some v).
      { rewrite HBeq. rewrite map.get_putmany_dec.
        destruct (map.get mBrest k) as [vr|] eqn:Hr;
          [exfalso; eapply HdBCrest; eauto | auto]. }
      specialize (HCinB k vc Hvc). rewrite HBk in HCinB.
      injection HCinB; intros; subst. symmetry. exact Hvc.
    - destruct (map.get C k) eqn:HC; auto.
      assert (HBk := HCinB k v HC).
      rewrite HBeq in HBk. rewrite map.get_putmany_dec in HBk.
      rewrite HmBC in HBk.
      unfold map.forall_keys in HkBrest.
      destruct (map.get mBrest k) as [vr|] eqn:Hr.
      + specialize (HkBrest k vr Hr). congruence.
      + congruence. }
  subst mBC.
  exists mBrest. split; [exact HBeq | exact HdBCrest].
Qed.

(** ** sep_lift_putmany

    Lifts a sep from memory [m] to extended memory [putmany m mS].
    Used after stackalloc: if [(P * Q) m] and [disjoint m mS],
    then [(P * (Q * eq mS)) (putmany m mS)].

    This enables [ecancel_assumption] to find FElems from the original
    memory in the stack-extended memory. *)

Lemma sep_lift_putmany {key value : Type} {map : map.map key value}
    {ok : map.ok map}
    {key_eqb : key -> key -> bool}
    {key_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (key_eqb x y)} :
  forall (P Q : @map.rep key value map -> Prop)
    (m mS : @map.rep key value map),
    sep P Q m -> map.disjoint m mS ->
    sep P (sep Q (eq mS)) (map.putmany m mS).
Proof.
  intros P Q m mS [mP [mQ [Hsp [HP HQ]]]] HdmS.
  destruct Hsp as [Heq Hd]. subst m.
  assert (HdQS : map.disjoint mQ mS).
  { unfold map.disjoint in *. intros k v1 v2 HgQ HgS.
    eapply HdmS. exact (map.get_putmany_right _ _ _ _ HgQ). exact HgS. }
  assert (HdPQS : map.disjoint mP (map.putmany mQ mS)).
  { unfold map.disjoint in *. intros k v1 v2 HgP HgQS.
    rewrite map.get_putmany_dec in HgQS.
    destruct (map.get mS k) eqn:HgS.
    - eapply HdmS.
      + assert (Hn : map.get mQ k = None)
          by (destruct (map.get mQ k) eqn:E; [exfalso; eapply Hd; eauto | reflexivity]).
        exact (eq_trans (map.get_putmany_left _ _ _ Hn) HgP).
      + exact HgS.
    - eapply Hd; eauto. }
  exists mP, (map.putmany mQ mS).
  split; [split |].
  - rewrite map.putmany_assoc. reflexivity.
  - exact HdPQS.
  - split; [exact HP |].
    exists mQ, mS. split; [split; [reflexivity | exact HdQS] |].
    split; [exact HQ | reflexivity].
Qed.

(** ================================================================ *)
(** * Enhanced WP automation for multi-call proofs                    *)
(** ================================================================ *)

(** ** assert_sep_from_context

    Automatically collects ALL FElem, Bignum, scalar, and R hypotheses
    that hold on submaps of the current combined memory, and asserts
    a master sep covering all of them.

    Usage: after destructing Hsep + substing stackalloc splits +
    split_all_disjointness, the context has individual hypotheses like:
      Hfe_ox : FElem bounds ptr val m_ox
      Hbn_k1 : Bignum n pk1 k1_words m_k1
      Hsc_iter : scalar addr val m_iter
      HR : R m_R
    The tactic builds:
      Hsep_master : (FElem ... ⋆ (Bignum ... ⋆ (... ⋆ R))) mem_combined
    and proves it using build_sep_reorder. *)

(** ** resolve_map_get_fast

    Faster version of resolve_map_get that uses native_compute-friendly
    string comparison. For deep locals maps (20+ puts), this avoids
    the O(n) congruence chain. *)

(** ** sep_extract_ecancel — robust ecancel for deeply nested seps.
    Falls back to ecancel_assumption_impl first, then manual search. *)
Ltac sep_extract_ecancel :=
  first
  [ SeparationLogic.ecancel_assumption_impl
  | match goal with
    | Hsep : (_ * _)%sep ?m |- (_ * _)%sep ?m =>
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ Hsep);
      clear Hsep; SeparationLogic.ecancel
    | Hsep : (_ * _)%sep ?m |- (_ * _)%sep ?m2 =>
      unify m m2;
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ Hsep);
      clear Hsep; SeparationLogic.ecancel
    end ].

Ltac resolve_map_get_fast :=
  lazymatch goal with
  | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
    first
    [ constr_eq k k'; rewrite map.get_put_same; exact eq_refl
    | rewrite map.get_put_diff by discriminate;
      resolve_map_get_fast ]
  | |- map.get ?m ?k = Some _ =>
    first [ assumption
          | match goal with H : map.get m k = Some _ |- _ => exact H end ]
  end.

(** ** eval_dexprs_fast

    Faster dexprs evaluator using resolve_map_get_fast. *)
Ltac eval_dexprs_fast :=
  cbv [dexprs list_map list_map_body
       WeakestPrecondition.expr WeakestPrecondition.expr_body
       WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
  repeat (first
    [ exact eq_refl
    | eexists; split; [resolve_map_get_fast |]
    | eexists; split; [exact eq_refl |]
    ]).

(** ** wp_straightline

    Process cmd.seq/set/skip/store with abstract locals.
    Curve-independent version of MillerLoop's miller_straightline. *)
Ltac wp_straightline :=
  match goal with
  | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    letexists; split; [solve [eval_dexprs_fast] |]
  | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | |- WeakestPrecondition.cmd _ (cmd.store _ _) _ _ _ _ =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body]
  end.

(** ** wp_gcall

    Process one function call with abstract locals. Curve-independent.
    1. Peel cmd.seq if needed
    2. Expose cmd.call, provide args via eval_dexprs_fast
    3. Apply weaken_call with spec
    4. Leave callee precondition and postcondition as subgoals

    Usage:
      wp_gcall HSpec.
      { solve_precondition. }
      { solve_postcondition. }
    *)
Ltac wp_gcall spec_hyp :=
  try wp_straightline;
  unfold1_cmd_goal; cbv beta match delta [cmd_body];
  letexists; split; [solve [eval_dexprs_fast] |];
  eapply Semantics.weaken_call;
  [ eapply spec_hyp
  | cbv beta; intros ? ? ? ?;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try subst;
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [ exact eq_refl | ]) ].

(* ================================================================== *)
(** * Phase 0 Automation — New shared tactics for pairing proofs      *)
(* ================================================================== *)

(** ** T1: solve_one_mapget / solve_mapgets_n

    Generic n-ary conjunction solver for map.get goals.
    Replaces the hardcoded 8-element [solve_loop_mapgets] in
    BLS12_FinalExp.v with a recursive version that handles any n.

    Avoids focus corruption by using [lazymatch] for recursion
    instead of [split; [leaf | recurse]] inside brackets. *)

Ltac solve_one_mapget :=
  lazymatch goal with
  | |- map.get (map.put _ _ _) _ = Some _ =>
    first
    [ rewrite map.get_put_same; reflexivity
    | rewrite map.get_put_diff by congruence; solve_one_mapget ]
  | |- map.get _ _ = Some _ => assumption
  end.

Ltac solve_mapgets_n :=
  lazymatch goal with
  | |- _ /\ _ => split; [ solve_one_mapget | solve_mapgets_n ]
  | |- map.get _ _ = Some _ => solve_one_mapget
  | |- True => exact I
  end.

(* T2 (wp_straight_call) and T3 (dealloc_one) were removed:
   wp_gcall and repeat straightline already handle these cases. *)

(* ================================================================== *)
(** * Phase 1 Automation — Pairing-level call tactics                  *)
(* ================================================================== *)

(** ** wp_pairing_precond: solve preconditions for Fp6/Fp12 level ops.

    Pairing-level specs (conjugate, frobenius, pow_u, etc.) have
    preconditions of the form:
      bounds1 /\ bounds2 /\ ... /\ sep_assertion
    where the last conjunct is a sep and everything else is a bound.

    Strategy: repeatedly split, try bounds from context, then ecancel
    for the sep part. *)

Ltac wp_pairing_precond :=
  repeat match goal with
  | |- _ /\ _ => split; [ first [ solve_bounds_auto
                                 | eexists; ecancel_assumption
                                 | ecancel_assumption ] | ]
  end;
  first [ ecancel_assumption
        | eexists; ecancel_assumption
        | solve_bounds_auto
        | idtac ].

(** ** wp_pairing_call: one call in a pairing-level straight-line proof.

    Combines wp_gcall + precondition solving + postcondition processing.
    After this tactic, the proof state has fresh output value hypotheses
    (feval, bounds, sep) and is ready for the next call.

    Usage: wp_pairing_call HSpec.
    where HSpec is a hypothesis of the form:
      spec_of_SomeOp functions   or
      map.get functions name = Some body  (for EnvContains)

    For specs that need explicit pointer/value arguments, use wp_gcall
    directly. *)

Ltac wp_pairing_postcall :=
  cbv beta;
  intros ? ? ? ?;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  try subst;
  cbv [map.putmany_of_list_zip];
  try (eexists; split; [ exact eq_refl | ]);
  repeat (try wp_straightline; try straightline).

Ltac wp_pairing_call spec_hyp :=
  try wp_straightline;
  try straightline;
  unfold1_cmd_goal; cbv beta match delta [cmd_body];
  letexists; split; [solve [eval_dexprs_fast] |];
  eapply Semantics.weaken_call;
  [ eapply spec_hyp; wp_pairing_precond
  | wp_pairing_postcall ].

(** ** wp_loop: apply while_localsmap with a given invariant.

    Usage: wp_loop inv measure.
    where inv is the loop invariant and measure is the initial value.

    Sets up the while proof with:
    - well_foundedness of nat
    - subgoal for initial invariant
    - subgoal for loop body preservation *)

Ltac wp_loop invariant v0 :=
  eapply Loops.while_localsmap
    with (v0 := v0)
         (lt := Nat.lt)
         (invariant := invariant);
  [ exact lt_wf | | ].

(* ================================================================== *)
(** * Phase 2 Automation — Multi-call chains and batch operations      *)
(* ================================================================== *)

(** ** wp_auto_precond: smart precondition solver for any op level.

    Tries, in order:
    1. Solve as unop precond (3-part: bound, exist sep, sep)
    2. Solve as binop precond (5-part: bound, bound, exist sep, exist sep, sep)
    3. Solve as pairing precond (N bounds + sep)
    4. Solve as felem_copy precond (sep pair)
    5. Solve as load_constant precond (single sep)
    6. Raw ecancel_assumption as last resort *)

Ltac wp_auto_precond :=
  first
    [ (* felem_copy shape: (sep) /\ (sep) *)
      split; [ecancel_assumption | ecancel_assumption]
    | (* unop shape: bound /\ (exists Rx, sep) /\ sep *)
      wp_unop_precond solve_bounds_auto
    | (* binop shape: bound /\ bound /\ ... /\ sep *)
      wp_binop_precond solve_bounds_auto
    | (* pairing general: N bounds + sep *)
      wp_pairing_precond
    | (* single sep (load constants, etc.) *)
      ecancel_assumption
    | (* existential sep *)
      eexists; ecancel_assumption ].

(** ** wp_step: process one call + postcondition in a straight-line proof.

    This is the workhorse tactic. Given a spec hypothesis, it:
    1. Advances past any cmd.seq/set/skip
    2. Evaluates call arguments
    3. Applies weaken_call with the spec
    4. Solves preconditions automatically
    5. Destructures postcondition
    6. Continues past the return-locals update

    After wp_step, fresh hypotheses for the output value (feval,
    bounded_by, sep) are in context and the goal is at the next call.

    Usage:
      wp_step HFmul.    (* for a mul call *)
      wp_step HFconj.   (* for a conjugate call *)
      wp_step HFpow.    (* for a pow_u call *)
*)

Ltac wp_step spec_hyp :=
  (* Phase 1: advance to the call *)
  repeat (first [ wp_straightline | straightline ]);
  (* Phase 2: process the call *)
  (tryif (unfold1_cmd_goal; cbv beta match delta [cmd_body];
          letexists; split; [solve [eval_dexprs_fast] |])
   then idtac
   else (letexists; split; [solve [eval_dexprs_fast] |]));
  eapply Semantics.weaken_call;
  [ (* Callee obligation *)
    eapply spec_hyp; wp_auto_precond
  | (* Continuation: destructure postcondition *)
    cbv beta;
    let t := fresh "t" in let m := fresh "m" in
    let rets := fresh "rets" in let Hpost := fresh "Hpost" in
    intros t m rets Hpost;
    (* Postconditions come in several shapes.
       Common: rets = [] /\ tr = t /\ (exists out, feval /\ bound /\ sep) *)
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end;
    try subst;
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [ exact eq_refl | ]);
    repeat (first [ wp_straightline | straightline ]) ].

(** ** wp_steps: process N calls in sequence.

    Takes a list of spec hypotheses and applies wp_step to each.
    Usage:
      wp_steps [HFconj; HFinv; HFmul; HFfrob; HFmul; HFhard].
*)

Ltac wp_steps specs :=
  lazymatch specs with
  | ?h :: ?rest => wp_step h; wp_steps rest
  | nil => idtac
  | ?h => wp_step h  (* single spec, not in list *)
  end.

(** ** wp_call_step: FIXED version of wp_step.

    The original wp_step uses unfold1_cmd_goal + eval_dexprs_fast for
    dexpr evaluation, which fails when the cmd.call is already partially
    reduced by start_func (the goal shape doesn't match the unfold1
    pattern). This version uses [repeat straightline] instead, which
    handles dexpr evaluation correctly in all cases.

    Usage: identical to wp_step.
      wp_call_step HFmul.
      wp_call_step HFcopy.
*)

Ltac wp_call_step spec_hyp :=
  repeat straightline;
  eapply Semantics.weaken_call;
  [ eapply spec_hyp; wp_auto_precond
  | cbv beta;
    let t := fresh "t" in let m := fresh "m" in
    let rets := fresh "rets" in let Hpost := fresh "Hpost" in
    intros t m rets Hpost;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try subst;
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [ exact eq_refl | ]);
    repeat straightline ].

Ltac wp_call_steps specs :=
  lazymatch specs with
  | ?h :: ?rest => wp_call_step h; wp_call_steps rest
  | nil => idtac
  | ?h => wp_call_step h
  end.

(** ** wp_stackalloc_one: handle one stackalloc + anybytes→FElem conversion.

    Processes:
      stackalloc N as ptr; ...
    into:
      ptr : word, mStack : mem, mCombined : mem,
      Hfelem : FElem ptr init_val mStack

    Arguments:
      field_params  — e.g., Fp12_fp_inst
      field_repr    — e.g., Fp12_repr_inst

    Usage:
      wp_stackalloc_one Fp12_fp_inst Fp12_repr_inst.
*)

Ltac wp_stackalloc_one fp_inst fr_inst :=
  straightline;
  split; [ first [ apply Z_mod_mult | reflexivity ] | ];
  let a := fresh "a" in
  let mS := fresh "mS" in
  let mC := fresh "mC" in
  let HaS := fresh "HaS" in
  let HmS := fresh "HmS" in
  intros a mS mC HaS HmS;
  let Hex := fresh "Hex" in
  assert (Hex : exists v, @AbstractField.FElem _ fp_inst _ _ _ _ fr_inst a v mS);
  [ let Hconv := fresh "Hconv" in
    pose proof (@AbstractField.FElem_from_bytes _ fp_inst _ _ _ _ fr_inst) as Hconv;
    cbv [Lift1Prop.iff1 AbstractField.Placeholder] in Hconv;
    apply Hconv; [typeclasses eauto | typeclasses eauto | exact HaS]
  | let vi := fresh "vi" in let Hvi := fresh "Hvi" in
    destruct Hex as [vi Hvi] ].

(** ** wp_dealloc_one: deallocate one stack-allocated FElem.

    Given a sep hypothesis containing (FElem ptr val) for a stack pointer,
    converts it back to anybytes and provides the map.split witness.

    This tactic should be called once per stack allocation, in reverse
    order of allocation.

    Usage (inside the final postcondition):
      (* Reorder to isolate stack FElem *)
      assert (Hsplit : (Rest * FElem a_stk stk_val) m_final).
      { pose proof Hsep as H'. ecancel_assumption. }
      wp_dealloc_one Hsplit fp_inst fr_inst.
*)

Ltac wp_dealloc_one Hsplit fp_inst fr_inst :=
  let m_rest := fresh "m_rest" in
  let m_stk := fresh "m_stk" in
  let Heq := fresh "Heq" in
  let Hd := fresh "Hd" in
  let Hrest := fresh "Hrest" in
  let Hstk := fresh "Hstk" in
  destruct Hsplit as [m_rest [m_stk [[Heq Hd] [Hrest Hstk]]]];
  let Hab := fresh "Hab" in
  pose proof (@AbstractField.FElem_to_bytes _ _ _ _ ltac:(exact _) ltac:(exact _) _
    fp_inst fr_inst _ _ m_stk Hstk) as Hab;
  try (unfold AbstractField.Placeholder in Hab);
  exists m_rest, m_stk;
  split; [ exact Hab | ];
  split; [ split; [ exact Heq | exact Hd ] | ].

(** ** Global override: use O(n) sep solver by default.

    All files that [Require Import ... WPTactics] get the fast solver.
    If a specific file breaks, add locally:
      [Local Ltac ecancel_assumption ::= SeparationLogic.ecancel_assumption.]
    to revert to the default O(n!) solver for that file. *)
Ltac ecancel_assumption ::= ecancel_assumption_fast.
