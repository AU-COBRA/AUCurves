(** * MulxSoundness — scaffolding for [lower_mulx_pairs] soundness.
 *
 * Status (2026-04-15): Phase 3 progress — semantic foundation fixed
 * in [ExprBridge.v] (word.mulhuu in eval_jexpr) and [PolishProofs.v]
 * (jeval_mulx rule uses word.mulhuu for hi).  This file provides
 * the well-formedness predicate [wf_mulx_*] and the foundational
 * [cmd_to_list_sound] chain for lifting [jeval] (JCseq) to
 * [jeval_list] (list jasmin_cmd).
 *
 * Remaining (Phase 3 plan):
 *   - [cmd_touches_preserves_var] : if [cmd_touches x c = false] and
 *     [jeval e c e'] then [e' x = e x].
 *   - [jeval_list_unaffected] : lift to lists.
 *   - [scan_mulx_pairs_valid] : every match satisfies operand
 *     equivalence under def_map.
 *   - [rewrite_mulx_one_match_sound] : rewriting one match preserves
 *     [jeval_list].
 *   - [lower_mulx_pairs_list_correct] : full theorem.
 *   - Replace identity-case Qed in [PolishProofs.v].
 *)

Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Properties.
From Stdlib Require Import ZArith String Bool List Lia.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.ExprBridge.

(* ================================================================ *)
(* Well-formedness predicates                                       *)
(* ================================================================ *)

Section Predicates.

  (** True if variable [x] appears as [JEvar x] in expression [e]. *)
  Fixpoint expr_reads (x : string) (e : jasmin_expr) : bool :=
    match e with
    | JEvar y => String.eqb x y
    | JElit _ => false
    | JEadd a b | JEsub a b | JEmul a b | JEmulhuu a b
    | JEand a b | JEor  a b | JExor a b
    | JEshr a b | JEshl a b | JEltu a b | JEeq a b =>
        expr_reads x a || expr_reads x b
    | JEload base _ => expr_reads x base
    end.

  (** True if command [c] reads or writes variable [x] anywhere.
      Recurs into JCseq/JCif/JCwhile/JCdecl. *)
  Fixpoint cmd_touches (x : string) (c : jasmin_cmd) : bool :=
    match c with
    | JCskip => false
    | JCseq c1 c2 => cmd_touches x c1 || cmd_touches x c2
    | JCset y e => String.eqb x y || expr_reads x e
    | JCstore base _ v => expr_reads x base || expr_reads x v
    | JCcall _ args => existsb (expr_reads x) args
    | JCif e ct cf => expr_reads x e || cmd_touches x ct || cmd_touches x cf
    | JCwhile e body => expr_reads x e || cmd_touches x body
    | JCdecl _ _ body => cmd_touches x body
    | JCadd_flags cf r a b =>
        String.eqb x cf || String.eqb x r
        || expr_reads x a || expr_reads x b
    | JCadcx co r a b ci =>
        String.eqb x co || String.eqb x r || String.eqb x ci
        || expr_reads x a || expr_reads x b
    | JCmulx h l a b =>
        String.eqb x h || String.eqb x l
        || expr_reads x a || expr_reads x b
    | JCsub_flags cf r a b =>
        String.eqb x cf || String.eqb x r
        || expr_reads x a || expr_reads x b
    | JCsbb co r a b ci =>
        String.eqb x co || String.eqb x r || String.eqb x ci
        || expr_reads x a || expr_reads x b
    end.

  (** No statement at positions strictly between [mul_idx] and
      [mulhuu_idx] touches [hi].  [n] is the running position. *)
  Fixpoint stmts_between_safe (hi : string)
      (mul_idx mulhuu_idx n : nat) (cs : list jasmin_cmd) : bool :=
    match cs with
    | nil => true
    | c :: rest =>
        let is_between := Nat.ltb mul_idx n && Nat.ltb n mulhuu_idx in
        (if is_between then negb (cmd_touches hi c) else true)
        && stmts_between_safe hi mul_idx mulhuu_idx (S n) rest
    end.

  (** Every pair returned by [scan_mulx_pairs] must satisfy the safety
      condition. *)
  Definition wf_mulx_list (cs : list jasmin_cmd) : bool :=
    forallb (fun m =>
               let '(mul_idx, mulhuu_idx, hi, _, _, _) := m in
               stmts_between_safe hi mul_idx mulhuu_idx 0 cs)
            (scan_mulx_pairs cs).

  Fixpoint wf_mulx_cmd (c : jasmin_cmd) : bool :=
    match c with
    | JCseq _ _ => wf_mulx_list (cmd_to_list c)
    | JCif _ ct cf => wf_mulx_cmd ct && wf_mulx_cmd cf
    | JCwhile _ body => wf_mulx_cmd body
    | JCdecl _ _ body => wf_mulx_cmd body
    | _ => true
    end.

End Predicates.

(* ================================================================ *)
(* List-level big-step semantics + cmd_to_list soundness            *)
(* ================================================================ *)

Section WithWordCmd.

  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {word_ok : word.ok word}.

  (** A variable environment.  Mirror of [PolishProofs.env]. *)
  Definition env := string -> word.

  Definition update (e : env) (x : string) (w : word) : env :=
    fun y => if String.eqb y x then w else e y.

  Lemma update_self : forall e x, update e x (e x) = e.
  Proof.
    intros. apply functional_extensionality. intros y.
    unfold update. destruct (String.eqb y x) eqn:H; [|reflexivity].
    apply String.eqb_eq in H. subst. reflexivity.
  Qed.

  (** Big-step relational semantics for [jasmin_cmd].  Mirror of
      [PolishProofs.jeval] so this file can prove its lemmas
      standalone; [PolishProofs.v] imports [MulxSoundness] and
      identifies the two (they are definitionally equal). *)
  Inductive jeval : env -> jasmin_cmd -> env -> Prop :=
  | jeval_skip : forall e, jeval e JCskip e
  | jeval_seq : forall e1 e2 e3 c1 c2,
      jeval e1 c1 e2 -> jeval e2 c2 e3 ->
      jeval e1 (JCseq c1 c2) e3
  | jeval_set : forall e x ex w,
      eval_jexpr e ex = Some w ->
      jeval e (JCset x ex) (update e x w)
  | jeval_decl : forall e x ty body e',
      jeval e body e' ->
      jeval e (JCdecl x ty body) e'
  | jeval_if_true : forall e econd ct cf w e',
      eval_jexpr e econd = Some w ->
      w <> word.of_Z 0 ->
      jeval e ct e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_if_false : forall e econd ct cf e',
      eval_jexpr e econd = Some (word.of_Z 0) ->
      jeval e cf e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_while_false : forall e econd body,
      eval_jexpr e econd = Some (word.of_Z 0) ->
      jeval e (JCwhile econd body) e
  | jeval_while_true : forall e e' e'' econd body w,
      eval_jexpr e econd = Some w ->
      w <> word.of_Z 0 ->
      jeval e body e' ->
      jeval e' (JCwhile econd body) e'' ->
      jeval e (JCwhile econd body) e''
  | jeval_store : forall e base off v vbase vv,
      eval_jexpr e base = Some vbase ->
      eval_jexpr e v = Some vv ->
      jeval e (JCstore base off v) e
  | jeval_call : forall e f args,
      jeval e (JCcall f args) e
  | jeval_add_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadd_flags cf r a b)
        (update (update e cf (word.of_Z 0)) r (word.add va vb))
  | jeval_adcx : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadcx co r a b ci)
        (update (update e co (word.of_Z 0)) r (word.add va vb))
  | jeval_mulx : forall e h l a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCmulx h l a b)
        (update (update e h (word.mulhuu va vb)) l (word.mul va vb))
  | jeval_sub_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsub_flags cf r a b)
        (update (update e cf (word.of_Z 0)) r (word.sub va vb))
  | jeval_sbb : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsbb co r a b ci)
        (update (update e co (word.of_Z 0)) r (word.sub va vb))
  .

  (** List-level big-step evaluation. *)
  Inductive jeval_list : env -> list jasmin_cmd -> env -> Prop :=
  | jeval_list_nil  : forall e, jeval_list e nil e
  | jeval_list_cons : forall e e1 e' c cs,
      jeval e c e1 -> jeval_list e1 cs e' ->
      jeval_list e (c :: cs) e'.

  (** Splitting [jeval_list] at an append boundary. *)
  Lemma jeval_list_app :
    forall cs1 cs2 e e',
      jeval_list e (cs1 ++ cs2) e' <->
      exists em, jeval_list e cs1 em /\ jeval_list em cs2 e'.
  Proof.
    induction cs1 as [|c cs1 IH]; intros cs2 e e'; simpl.
    - split.
      + intros H. exists e. split; [constructor | exact H].
      + intros [em [Hl Hr]]. inversion Hl; subst. exact Hr.
    - split.
      + intros H. inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        apply IH in Hcs as [em' [Hl Hr]].
        exists em'. split; [econstructor; eassumption | exact Hr].
      + intros [em [Hl Hr]].
        inversion Hl as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        econstructor; [eassumption | apply IH; eauto].
  Qed.

  (** Helper for singleton-list cases: [jeval env1 c env2] iff
      [jeval_list env1 [c] env2]. *)
  Lemma jeval_singleton_iff : forall c env1 env2,
      jeval env1 c env2 <-> jeval_list env1 (c :: nil) env2.
  Proof.
    intros c env1 env2. split.
    - intros H. econstructor; [exact H | constructor].
    - intros H. inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
      inversion Hcs; subst. exact Hc.
  Qed.

  (** Flattening a JCseq-chain into a list preserves [jeval].
      All jasmin_cmd cases covered. *)
  Theorem cmd_to_list_sound :
    forall c env1 env2,
      jeval env1 c env2 <-> jeval_list env1 (cmd_to_list c) env2.
  Proof.
    induction c; intros env1 env2; simpl;
      try apply jeval_singleton_iff.
    - (* JCskip *)
      split.
      + intros H. inversion H; subst. constructor.
      + intros H. inversion H; subst. constructor.
    - (* JCseq *)
      split.
      + intros H. inversion H as [|e1' e2' e3' c1'' c2'' H1 H2|
                                  | | | | | | | | | | | |]; subst.
        apply IHc1 in H1. apply IHc2 in H2.
        apply jeval_list_app. eauto.
      + intros H. apply jeval_list_app in H as [em [Hl Hr]].
        apply IHc1 in Hl. apply IHc2 in Hr.
        econstructor; eassumption.
  Qed.

  (** The inverse direction: wrapping a list with [fold_right JCseq JCskip]. *)
  Theorem list_to_cmd_sound :
    forall cs e e',
      jeval_list e cs e' <-> jeval e (list_to_cmd cs) e'.
  Proof.
    induction cs as [|c cs IH]; intros e e'; unfold list_to_cmd; simpl.
    - split.
      + intros H. inversion H; subst. constructor.
      + intros H. inversion H; subst. constructor.
    - split.
      + intros H.
        inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        econstructor; [eassumption|].
        apply IH in Hcs. fold (list_to_cmd cs) in Hcs. exact Hcs.
      + intros H.
        inversion H; subst.
        econstructor; [eassumption|].
        match goal with
        | H : jeval _ _ _ |- _ =>
            let Hj := fresh in
            apply IH in H as Hj; exact Hj
        end.
  Qed.

  (* ================================================================ *)
  (* Remaining Phase 3 proof obligations (stated, proofs deferred)    *)
  (* ================================================================ *)

  (** Helper: [update e x v y = e y] when [y ≠ x]. *)
  Lemma update_other : forall e x v y,
    String.eqb y x = false -> update e x v y = e y.
  Proof.
    intros e x v y H. unfold update. rewrite H. reflexivity.
  Qed.

  (** If a command doesn't touch [x], evaluating it preserves [x]'s
      value.  Proof: structural induction on [jeval], using [update_other]
      to see through writes to other variables. *)
  Theorem cmd_touches_preserves_var :
    forall c e e' x,
      cmd_touches x c = false ->
      jeval e c e' ->
      e' x = e x.
  Proof.
    intros c e e' x Hnt H. revert x Hnt.
    induction H; intros y Hnt; simpl in Hnt.
    - (* JCskip *) reflexivity.
    - (* JCseq *)
      apply orb_false_iff in Hnt as [A B].
      specialize (IHjeval1 _ A).
      specialize (IHjeval2 _ B).
      congruence.
    - (* JCset *)
      apply orb_false_iff in Hnt as [A _].
      apply update_other. exact A.
    - (* JCdecl *) apply IHjeval. exact Hnt.
    - (* JCif_true *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [_ A].
      apply IHjeval. exact A.
    - (* JCif_false *)
      apply orb_false_iff in Hnt as [_ B].
      apply IHjeval. exact B.
    - (* JCwhile_false *) reflexivity.
    - (* JCwhile_true *)
      assert (Hnt' := Hnt).
      apply orb_false_iff in Hnt as [_ B].
      specialize (IHjeval1 _ B).
      specialize (IHjeval2 _ Hnt').
      congruence.
    - (* JCstore *) reflexivity.
    - (* JCcall *) reflexivity.
    - (* JCadd_flags *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Acf Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Acf.
    - (* JCadcx *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Aco Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Aco.
    - (* JCmulx *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Ah Al].
      rewrite update_other by exact Al.
      apply update_other. exact Ah.
    - (* JCsub_flags *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Acf Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Acf.
    - (* JCsbb *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Aco Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Aco.
  Qed.

  (** All-statements version: if no statement in the list touches [x],
      then [x]'s value is preserved by [jeval_list]. *)
  Theorem jeval_list_unaffected :
    forall cs e e' x,
      forallb (fun c => negb (cmd_touches x c)) cs = true ->
      jeval_list e cs e' ->
      e' x = e x.
  Proof.
    induction cs as [|c cs IH]; intros e e' x Hall Hev.
    - inversion Hev; subst. reflexivity.
    - simpl in Hall. apply andb_prop in Hall as [Hc Hrest].
      apply Bool.negb_true_iff in Hc.
      inversion Hev as [| e0 e1 e'0 c0 cs0 Hec Hecs ]; subst.
      rewrite (IH _ _ x Hrest Hecs).
      apply cmd_touches_preserves_var with (c := c); assumption.
  Qed.

  (** Every tuple [(mul_idx, mulhuu_idx, hi, lo, a, b)] from
      [scan_mulx_pairs cs] satisfies the [mulx_rewrite] relation
      (defined below) between [cs] and the result of applying that
      single match.  The proof requires a strengthened invariant on
      [scan_mulx_pairs_aux] that tracks: running position, def_map,
      pending mul list, and accumulated matches.  At each step the
      invariant says: every entry in the accumulator corresponds to a
      valid [mulx_rewrite] of the original [cs] slice.  ~60 lines.

      Defined after [mulx_rewrite] to reference it — see end of file. *)

  (** Full soundness of [lower_mulx_pairs] on lists, proved by
      induction on [scan_mulx_pairs cs] via the length measure.

      When [scan_mulx_pairs cs = nil], [lower_mulx_pairs cs = cs]
      (by [lower_mulx_pairs_empty]), trivially preserving jeval.

      Otherwise, we unfold [lower_mulx_pairs] to show it is equivalent
      to a sequence of single-match rewrites using
      [rewrite_mulx_one_match_sound] — each application reduces the
      match count by one.

      This theorem is stated as a conjecture in the current session:
      the composition requires a strengthened scan invariant relating
      [scan_mulx_pairs cs] entries to [mulx_rewrite] applications,
      plus a [rewrite_mulx_aux_seq] lemma showing batch application
      equals iterative (~90 lines total, all mechanical given the
      already-Qed single-match theorem). *)
  (* The full theorem [lower_mulx_pairs_list_correct_final] is stated
     below at the end of this section, after [rewrite_mulx_aux_sound_single]
     and the scan invariant are introduced. *)

  (* ================================================================ *)
  (* Empty-match special case: fully Qed                               *)
  (* ================================================================ *)

  (** When [matches = nil], [rewrite_mulx_aux] is the identity. *)
  Lemma rewrite_mulx_aux_nil_id :
    forall n cs, rewrite_mulx_aux n nil cs = cs.
  Proof.
    intros n cs. revert n.
    induction cs as [|c cs IH]; intros n; simpl; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Step 1: Disjoint decomposition of rewrite_mulx_aux                *)
  (* ================================================================ *)

  (** Two matches are disjoint if their position ranges don't overlap. *)
  Definition match_disjoint (m1 m2 : mulx_match) : Prop :=
    let '(i1, j1, _, _, _, _) := m1 in
    let '(i2, j2, _, _, _, _) := m2 in
    i1 <> i2 /\ i1 <> j2 /\ j1 <> i2 /\ j1 <> j2.

  (** Helper: find_mul_match on singleton [m] at position n. *)
  Lemma find_mul_match_singleton :
    forall n m,
      let '(i, _, _, _, _, _) := m in
      find_mul_match n [m] =
        if Nat.eqb n i then Some m else None.
  Proof.
    intros n m. destruct m as [[[[[i j] hi] lo] a] b]. simpl.
    destruct (Nat.eqb n i); reflexivity.
  Qed.

  (** Helper: is_mulhuu_idx on singleton [m]. *)
  Lemma is_mulhuu_idx_singleton :
    forall n m,
      let '(_, j, _, _, _, _) := m in
      is_mulhuu_idx n [m] = Nat.eqb n j.
  Proof.
    intros n m. destruct m as [[[[[i j] hi] lo] a] b]. simpl.
    apply Bool.orb_false_r.
  Qed.

  (** Helper: find_mul_match on [m :: ms] — case split on match. *)
  Lemma find_mul_match_cons :
    forall n m ms,
      let '(i, _, _, _, _, _) := m in
      find_mul_match n (m :: ms) =
        if Nat.eqb n i then Some m else find_mul_match n ms.
  Proof.
    intros n m ms. destruct m as [[[[[i j] hi] lo] a] b]. simpl.
    destruct (Nat.eqb n i); reflexivity.
  Qed.

  (** Helper: is_mulhuu_idx on [m :: ms]. *)
  Lemma is_mulhuu_idx_cons :
    forall n m ms,
      let '(_, j, _, _, _, _) := m in
      is_mulhuu_idx n (m :: ms) = Nat.eqb n j || is_mulhuu_idx n ms.
  Proof.
    intros n m ms. destruct m as [[[[[i j] hi] lo] a] b]. reflexivity.
  Qed.

  (** Auxiliary: find_mul_match returns None on ms when n equals the
      mul_idx of a disjoint m. *)
  Lemma find_mul_match_disjoint_i :
    forall m ms,
      let '(i, _, _, _, _, _) := m in
      Forall (match_disjoint m) ms ->
      find_mul_match i ms = None.
  Proof.
    intros [[[[[i j] hi] lo] a] b] ms Hd.
    induction ms as [|[[[[[i' j'] hi'] lo'] a'] b'] ms' IH]; [reflexivity|].
    inversion Hd as [|x y Hhd Htl]; subst.
    unfold match_disjoint in Hhd.
    destruct Hhd as [Hii' _]. simpl.
    destruct (Nat.eqb i i') eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - apply IH. exact Htl.
  Qed.

  Lemma find_mul_match_disjoint_j :
    forall m ms,
      let '(_, j, _, _, _, _) := m in
      Forall (match_disjoint m) ms ->
      find_mul_match j ms = None.
  Proof.
    intros [[[[[i j] hi] lo] a] b] ms Hd.
    induction ms as [|[[[[[i' j'] hi'] lo'] a'] b'] ms' IH]; [reflexivity|].
    inversion Hd as [|x y Hhd Htl]; subst.
    unfold match_disjoint in Hhd.
    destruct Hhd as [_ [_ [Hji' _]]]. simpl.
    destruct (Nat.eqb j i') eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - apply IH. exact Htl.
  Qed.

  Lemma is_mulhuu_idx_disjoint_i :
    forall m ms,
      let '(i, _, _, _, _, _) := m in
      Forall (match_disjoint m) ms ->
      is_mulhuu_idx i ms = false.
  Proof.
    intros [[[[[i j] hi] lo] a] b] ms Hd.
    induction ms as [|[[[[[i' j'] hi'] lo'] a'] b'] ms' IH]; [reflexivity|].
    inversion Hd as [|x y Hhd Htl]; subst.
    unfold match_disjoint in Hhd.
    destruct Hhd as [_ [Hij' _]]. simpl.
    destruct (Nat.eqb i j') eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - apply IH. exact Htl.
  Qed.

  Lemma is_mulhuu_idx_disjoint_j :
    forall m ms,
      let '(_, j, _, _, _, _) := m in
      Forall (match_disjoint m) ms ->
      is_mulhuu_idx j ms = false.
  Proof.
    intros [[[[[i j] hi] lo] a] b] ms Hd.
    induction ms as [|[[[[[i' j'] hi'] lo'] a'] b'] ms' IH]; [reflexivity|].
    inversion Hd as [|x y Hhd Htl]; subst.
    unfold match_disjoint in Hhd.
    destruct Hhd as [_ [_ [_ Hjj']]]. simpl.
    destruct (Nat.eqb j j') eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - apply IH. exact Htl.
  Qed.

  (** Core Step 1 lemma: [rewrite_mulx_aux] on [m :: ms] equals
      sequential application of [m] and then [ms], provided [m]'s
      positions are disjoint from every match in [ms]. *)
  (** Step lemma: unfold rewrite_mulx_aux one step. *)
  Lemma rewrite_mulx_aux_step :
    forall n ms c cs,
      rewrite_mulx_aux n ms (c :: cs) =
      (match find_mul_match n ms with
       | Some (_, _, hi, lo, a, b) => JCmulx hi lo a b
       | None => if is_mulhuu_idx n ms then JCskip else c
       end) :: rewrite_mulx_aux (S n) ms cs.
  Proof. intros. reflexivity. Qed.

  (* ================================================================ *)
  (* Step 2: Single-match rewrite produces mulx_rewrite                *)
  (* ================================================================ *)

  (** A match [m] is valid at [cs] if the required syntactic structure
      is present and the safety conditions hold. *)
  Definition valid_match_at (cs : list jasmin_cmd) (m : mulx_match) : Prop :=
    let '(mul_idx, mulhuu_idx, hi, lo, a, b) := m in
    (mul_idx < mulhuu_idx)%nat
    /\ (exists a'' b'',
          nth_error cs mul_idx = Some (JCset lo (JEmul a b))
          /\ nth_error cs mulhuu_idx = Some (JCset hi (JEmulhuu a'' b''))
          /\ (forall ev : env, eval_jexpr ev a = eval_jexpr ev a'')
          /\ (forall ev : env, eval_jexpr ev b = eval_jexpr ev b''))
    /\ (forall c i, (mul_idx < i < mulhuu_idx)%nat ->
          nth_error cs i = Some c ->
          cmd_touches hi c = false
          /\ (forall x, expr_reads x a = true -> cmd_touches x c = false)
          /\ (forall x, expr_reads x b = true -> cmd_touches x c = false))
    /\ expr_reads lo a = false
    /\ expr_reads lo b = false
    /\ hi <> lo.

  (** Splitting a list at a position: if nth_error cs k = Some x, then
      cs = firstn k cs ++ x :: skipn (S k) cs. *)
  Lemma list_split_nth :
    forall (A : Type) (cs : list A) k x,
      nth_error cs k = Some x ->
      cs = firstn k cs ++ x :: skipn (S k) cs.
  Proof.
    induction cs as [|c cs IH]; intros [|k] x Hnth; simpl in *;
      try discriminate.
    - injection Hnth as <-. reflexivity.
    - f_equal. apply IH. exact Hnth.
  Qed.

  Lemma nth_error_Some_length :
    forall (A : Type) (cs : list A) k x,
      nth_error cs k = Some x ->
      (k < length cs)%nat.
  Proof.
    induction cs as [|c cs IH]; intros [|k] x Hnth; simpl in *;
      try discriminate; try lia.
    apply IH in Hnth. lia.
  Qed.

  (* rewrite_mulx_aux_single_is_rewrite defined below after mulx_rewrite *)

  Lemma rewrite_mulx_aux_cons :
    forall ms m n cs,
      Forall (match_disjoint m) ms ->
      rewrite_mulx_aux n (m :: ms) cs =
      rewrite_mulx_aux n ms (rewrite_mulx_aux n [m] cs).
  Proof.
    intros ms m n cs Hdisj. revert n.
    destruct m as [[[[[i j] hi] lo] a] b].
    induction cs as [|c cs IH]; intros n; [reflexivity|].
    (* Unfold LHS one step *)
    rewrite rewrite_mulx_aux_step at 1.
    (* Unfold inner [m] rewrite on RHS one step *)
    rewrite rewrite_mulx_aux_step with (ms := [(i,j,hi,lo,a,b)]) at 1.
    simpl find_mul_match. simpl is_mulhuu_idx.
    rewrite Bool.orb_false_r.
    destruct (Nat.eqb n i) eqn:Heq_i.
    - (* n = i *)
      apply Nat.eqb_eq in Heq_i. subst i.
      (* LHS: find_mul_match n (m :: ms) = Some m (since n =? n = true) *)
      (* After single-match rewrite at position n: JCmulx hi lo a b *)
      rewrite rewrite_mulx_aux_step.
      pose proof (find_mul_match_disjoint_i (n,j,hi,lo,a,b) ms Hdisj) as Hfm.
      pose proof (is_mulhuu_idx_disjoint_i (n,j,hi,lo,a,b) ms Hdisj) as Hhu.
      simpl in Hfm, Hhu.
      rewrite Hfm, Hhu.
      f_equal. apply IH.
    - destruct (Nat.eqb n j) eqn:Heq_j.
      + (* n = j *)
        apply Nat.eqb_eq in Heq_j. subst j.
        rewrite rewrite_mulx_aux_step.
        pose proof (find_mul_match_disjoint_j (i,n,hi,lo,a,b) ms Hdisj) as Hfm.
        pose proof (is_mulhuu_idx_disjoint_j (i,n,hi,lo,a,b) ms Hdisj) as Hhu.
        simpl in Hfm, Hhu.
        rewrite Hfm, Hhu.
        f_equal. apply IH.
      + (* n <> i and n <> j *)
        rewrite rewrite_mulx_aux_step.
        destruct (find_mul_match n ms) as [m'|] eqn:Hfm;
          [|destruct (is_mulhuu_idx n ms) eqn:Hhu].
        * f_equal. apply IH.
        * f_equal. apply IH.
        * f_equal. apply IH.
  Qed.

  (** If [scan_mulx_pairs cs = nil], then [lower_mulx_pairs cs = cs]. *)
  Lemma lower_mulx_pairs_empty :
    forall cs,
      scan_mulx_pairs cs = nil ->
      lower_mulx_pairs cs = cs.
  Proof.
    intros cs Hscan. unfold lower_mulx_pairs.
    rewrite Hscan. apply rewrite_mulx_aux_nil_id.
  Qed.

  (** Soundness in the empty-match case (no pairs found by scan). *)
  Theorem lower_mulx_pairs_list_correct_empty :
    forall cs e e',
      scan_mulx_pairs cs = nil ->
      jeval_list e cs e' ->
      jeval_list e (lower_mulx_pairs cs) e'.
  Proof.
    intros cs e e' Hscan H.
    rewrite (lower_mulx_pairs_empty _ Hscan). exact H.
  Qed.

  (* ================================================================ *)
  (* One-match rewrite soundness: relational formulation              *)
  (* ================================================================ *)

  (** Express the single-rewrite schema as a relation on lists.  This
      side-steps list indexing and lets us reason directly about the
      five-part decomposition. *)
  Inductive mulx_rewrite (hi lo : string) (a b : jasmin_expr)
    : list jasmin_cmd -> list jasmin_cmd -> Prop :=
  | mulx_rewrite_intro : forall (prefix middle suffix : list jasmin_cmd)
                                (a'' b'' : jasmin_expr),
      (* middle doesn't touch hi (soundness of moving hi-write earlier) *)
      (forall c, In c middle -> cmd_touches hi c = false) ->
      (* middle doesn't touch any var read by a (so a's eval stable) *)
      (forall c x, In c middle -> expr_reads x a = true -> cmd_touches x c = false) ->
      (* middle doesn't touch any var read by b *)
      (forall c x, In c middle -> expr_reads x b = true -> cmd_touches x c = false) ->
      (* a'' and a have same eval under any env — post-def_map resolution *)
      (forall (ev : env), eval_jexpr ev a = eval_jexpr ev a'') ->
      (forall (ev : env), eval_jexpr ev b = eval_jexpr ev b'') ->
      mulx_rewrite hi lo a b
        (prefix ++ JCset lo (JEmul a b) :: middle
                ++ JCset hi (JEmulhuu a'' b'') :: suffix)
        (prefix ++ JCmulx hi lo a b :: middle
                ++ JCskip :: suffix).

  (** Step 2: decomposed version.  When cs has the 5-part structure
      required by [mulx_rewrite], [rewrite_mulx_aux] with the singleton
      match at the corresponding positions produces exactly the
      rewritten form. *)

  (** Helper: rewrite_mulx_aux offset [m] traverses a list whose length
      is exactly the position of m's mul_idx, producing the same list. *)
  Lemma rewrite_mulx_aux_pre :
    forall mi mj hi lo a b cs n,
      (mi < mj)%nat ->
      (n + length cs <= mi)%nat ->
      rewrite_mulx_aux n [(mi, mj, hi, lo, a, b)] cs = cs.
  Proof.
    intros mi mj hi lo a b cs n Hmm Hlen. revert n Hlen.
    induction cs as [|c cs IH]; intros n Hlen; simpl.
    - reflexivity.
    - simpl length in Hlen.
      assert (Hni : n <> mi) by lia.
      assert (Hnj : n <> mj) by lia.
      apply Nat.eqb_neq in Hni. rewrite Hni.
      apply Nat.eqb_neq in Hnj. rewrite Hnj. simpl.
      f_equal. apply IH. lia.
  Qed.

  (** Helper: after the mul_idx, before the mulhuu_idx, in the middle
      range, no match applies. *)
  Lemma rewrite_mulx_aux_mid :
    forall mi mj hi lo a b cs n,
      (mi < n)%nat ->
      (n + length cs <= mj)%nat ->
      rewrite_mulx_aux n [(mi, mj, hi, lo, a, b)] cs = cs.
  Proof.
    intros mi mj hi lo a b cs n Hmi Hlen. revert n Hmi Hlen.
    induction cs as [|c cs IH]; intros n Hmi Hlen; simpl.
    - reflexivity.
    - simpl length in Hlen.
      assert (Hni : n <> mi) by lia.
      assert (Hnj : n <> mj) by lia.
      apply Nat.eqb_neq in Hni. rewrite Hni.
      apply Nat.eqb_neq in Hnj. rewrite Hnj. simpl.
      f_equal. apply IH; lia.
  Qed.

  (** Helper: after mulhuu_idx, no match applies. *)
  Lemma rewrite_mulx_aux_post :
    forall mi mj hi lo a b cs n,
      (mi < mj)%nat ->
      (mj < n)%nat ->
      rewrite_mulx_aux n [(mi, mj, hi, lo, a, b)] cs = cs.
  Proof.
    intros mi mj hi lo a b cs n Hmm Hmj. revert n Hmj.
    induction cs as [|c cs IH]; intros n Hmj; simpl.
    - reflexivity.
    - assert (Hni : n <> mi) by lia.
      assert (Hnj : n <> mj) by lia.
      apply Nat.eqb_neq in Hni. rewrite Hni.
      apply Nat.eqb_neq in Hnj. rewrite Hnj. simpl.
      f_equal. apply IH. lia.
  Qed.

  (** Generalized over offset [n]: [rewrite_mulx_aux n] on a
      decomposed cs produces the rewritten decomposition, when
      positions align. *)
  Lemma rewrite_mulx_aux_single_decomposed_offset :
    forall prefix middle suffix hi lo a b a'' b'' n,
      let mi := (n + length prefix)%nat in
      let mj := (mi + 1 + length middle)%nat in
      rewrite_mulx_aux n [(mi, mj, hi, lo, a, b)]
        (prefix ++ JCset lo (JEmul a b) :: middle
                ++ JCset hi (JEmulhuu a'' b'') :: suffix)
      = prefix ++ JCmulx hi lo a b :: middle
              ++ JCskip :: suffix.
  Proof.
    induction prefix as [|c prefix IH];
      intros middle suffix hi lo a b a'' b'' n;
      cbn [length].
    - (* prefix = nil: start at position n, n = mi *)
      cbn [app].
      rewrite Nat.add_0_r.
      rewrite rewrite_mulx_aux_step.
      cbn [find_mul_match is_mulhuu_idx].
      rewrite Nat.eqb_refl. cbn [orb].
      f_equal.
      (* rewrite_mulx_aux (S n) [(n, n+1+length middle, ...)]
           (middle ++ JCset hi ... :: suffix) *)
      (* Now traverse middle (S n .. mj-1), then JCset hi at mj,
         then suffix *)
      assert (Hmid :
        forall mid sfx k,
          (n < k)%nat ->
          (k + length mid = n + 1 + length middle)%nat ->
          rewrite_mulx_aux k [(n, (n + 1 + length middle)%nat, hi, lo, a, b)]
            (mid ++ JCset hi (JEmulhuu a'' b'') :: sfx)
          = mid ++ JCskip :: sfx).
      { induction mid as [|cm mid IHmid]; intros sfx k Hk Hlen;
        cbn [length] in Hlen; cbn [app].
        - (* mid = nil: k should equal mj *)
          assert (Hkmj : k = (n + 1 + length middle)%nat) by lia.
          subst k.
          rewrite rewrite_mulx_aux_step.
          cbn [find_mul_match is_mulhuu_idx].
          assert (Hkneq : ((n + 1 + length middle)%nat <> n)%nat) by lia.
          apply Nat.eqb_neq in Hkneq. rewrite Hkneq.
          rewrite Nat.eqb_refl. cbn [orb].
          f_equal.
          apply rewrite_mulx_aux_post; lia.
        - assert (Hkni : k <> n) by lia.
          assert (Hknj : k <> (n + 1 + length middle)%nat) by lia.
          rewrite rewrite_mulx_aux_step.
          cbn [find_mul_match is_mulhuu_idx].
          apply Nat.eqb_neq in Hkni. rewrite Hkni.
          apply Nat.eqb_neq in Hknj. rewrite Hknj. cbn [orb].
          f_equal. apply IHmid; lia. }
      specialize (Hmid middle suffix (S n)).
      apply Hmid; lia.
    - (* prefix = c :: prefix': advance offset *)
      simpl.
      set (mi' := (n + S (length prefix))%nat).
      set (mj' := (mi' + 1 + length middle)%nat).
      (* At position n: not a match because n < mi' = n + S (length prefix) *)
      assert (Hni : n <> mi') by (unfold mi'; lia).
      assert (Hnj : n <> mj') by (unfold mj', mi'; lia).
      apply Nat.eqb_neq in Hni. rewrite Hni.
      apply Nat.eqb_neq in Hnj. rewrite Hnj. simpl.
      f_equal.
      specialize (IH middle suffix hi lo a b a'' b'' (S n)).
      cbv zeta in IH.
      replace (S n + length prefix)%nat with (n + S (length prefix))%nat in IH by lia.
      replace (n + S (length prefix) + 1 + length middle)%nat
        with (mi' + 1 + length middle)%nat in IH by (unfold mi'; lia).
      exact IH.
  Qed.

  (** The decomposed form at offset 0. *)
  Lemma rewrite_mulx_aux_single_decomposed :
    forall prefix middle suffix hi lo a b a'' b'',
      let mi := length prefix in
      let mj := (mi + 1 + length middle)%nat in
      rewrite_mulx_aux 0 [(mi, mj, hi, lo, a, b)]
        (prefix ++ JCset lo (JEmul a b) :: middle
                ++ JCset hi (JEmulhuu a'' b'') :: suffix)
      = prefix ++ JCmulx hi lo a b :: middle
              ++ JCskip :: suffix.
  Proof.
    intros. pose proof
      (rewrite_mulx_aux_single_decomposed_offset
         prefix middle suffix hi lo a b a'' b'' 0) as H.
    cbv zeta in H. subst mi mj. exact H.
  Qed.

  (** A useful invariant: [jeval_list] on a middle range where no
      statement touches [hi] preserves [hi]. *)
  Lemma jeval_list_middle_preserves_hi :
    forall middle hi env env',
      (forall c, In c middle -> cmd_touches hi c = false) ->
      jeval_list env middle env' ->
      env' hi = env hi.
  Proof.
    induction middle as [|c cs IH]; intros hi env env' Hsafe Hev.
    - inversion Hev; subst. reflexivity.
    - inversion Hev as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
      assert (Hc_safe : cmd_touches hi c = false).
      { apply Hsafe. left. reflexivity. }
      rewrite (IH hi e1 env' (fun c' Hin => Hsafe c' (or_intror Hin)) Hcs).
      apply cmd_touches_preserves_var with (c := c); assumption.
  Qed.

  (** If a variable [x] doesn't appear in expression [e], the
      evaluation doesn't depend on [x]'s value in the environment. *)
  Lemma eval_jexpr_agnostic_to_var :
    forall e x env w,
      expr_reads x e = false ->
      eval_jexpr env e = eval_jexpr (update env x w) e.
  Proof.
    induction e; intros y env w Hnr; simpl in *; try reflexivity.
    - (* JEvar *) unfold update.
      destruct (String.eqb x y) eqn:Heq; [|reflexivity].
      apply String.eqb_eq in Heq. subst. rewrite String.eqb_refl in Hnr.
      discriminate.
    - (* JEadd *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEsub *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEmul *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEmulhuu *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEand *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEor *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JExor *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEshr *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEshl *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEltu *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    - (* JEeq *) apply orb_false_iff in Hnr as [H1 H2].
      rewrite <- (IHe1 y env w H1), <- (IHe2 y env w H2); reflexivity.
    (* JEload closed by [try reflexivity] (eval_jexpr returns None
       on both sides since JEload requires memory support). *)
  Qed.

  (** [update] at disjoint variables commutes. *)
  Lemma update_comm : forall (env : env) x1 x2 w1 w2,
      x1 <> x2 ->
      update (update env x1 w1) x2 w2 = update (update env x2 w2) x1 w1.
  Proof.
    intros env x1 x2 w1 w2 Hneq.
    apply functional_extensionality. intros y.
    unfold update.
    destruct (String.eqb y x2) eqn:H2;
      destruct (String.eqb y x1) eqn:H1; try reflexivity.
    apply String.eqb_eq in H1, H2. subst. contradiction.
  Qed.

  (** Helper: String.eqb sym. *)
  Lemma streqb_sym_neq : forall x y,
    String.eqb x y = false -> String.eqb y x = false.
  Proof.
    intros x y H. destruct (String.eqb y x) eqn:E; [|reflexivity].
    apply String.eqb_eq in E. subst. rewrite String.eqb_refl in H. discriminate.
  Qed.

  (** If a command [c] doesn't touch [x], then adding an [x]-update
      around the execution still works.  Structural induction on
      [jeval]; uses [eval_jexpr_agnostic_to_var] for expressions and
      [update_comm] to commute updates at disjoint vars. *)
  Lemma jeval_agnostic_to_var :
    forall env c env' x w,
      cmd_touches x c = false ->
      jeval env c env' ->
      jeval (update env x w) c (update env' x w).
  Proof.
    intros env c env' x w Hnt H. revert x w Hnt.
    induction H; intros y wy Hnt; simpl in Hnt.
    - (* JCskip *) constructor.
    - (* JCseq *)
      apply orb_false_iff in Hnt as [A B].
      econstructor; [apply IHjeval1; exact A | apply IHjeval2; exact B].
    - (* JCset *)
      apply orb_false_iff in Hnt as [A Bx].
      assert (Hxy : String.eqb x y = false).
      { apply streqb_sym_neq. exact A. }
      rewrite update_comm by (intro; subst; rewrite String.eqb_refl in A; discriminate).
      constructor. rewrite <- eval_jexpr_agnostic_to_var by exact Bx. exact H.
    - (* JCdecl *) apply jeval_decl. apply IHjeval. exact Hnt.
    - (* JCif_true *)
      apply orb_false_iff in Hnt as [P Hcf].
      apply orb_false_iff in P as [He Hct].
      eapply jeval_if_true; [|exact H0|apply IHjeval; exact Hct].
      rewrite <- eval_jexpr_agnostic_to_var by exact He. exact H.
    - (* JCif_false *)
      apply orb_false_iff in Hnt as [P Hcf].
      apply orb_false_iff in P as [He Hct].
      eapply jeval_if_false; [|apply IHjeval; exact Hcf].
      rewrite <- eval_jexpr_agnostic_to_var by exact He. exact H.
    - (* JCwhile_false *)
      apply orb_false_iff in Hnt as [He _].
      apply jeval_while_false.
      rewrite <- eval_jexpr_agnostic_to_var by exact He. exact H.
    - (* JCwhile_true *)
      assert (Hnt' := Hnt).
      apply orb_false_iff in Hnt as [He Hb].
      eapply jeval_while_true.
      + rewrite <- eval_jexpr_agnostic_to_var by exact He. exact H.
      + exact H0.
      + apply IHjeval1; exact Hb.
      + apply IHjeval2; exact Hnt'.
    - (* JCstore *)
      apply orb_false_iff in Hnt as [Hb Hv].
      eapply jeval_store.
      + rewrite <- eval_jexpr_agnostic_to_var by exact Hb. exact H.
      + rewrite <- eval_jexpr_agnostic_to_var by exact Hv. exact H0.
    - (* JCcall *) constructor.
    - (* JCadd_flags *)
      apply orb_false_iff in Hnt as [P Hb].
      apply orb_false_iff in P as [P Ha].
      apply orb_false_iff in P as [Hcf Hr].
      assert (Hry : r <> y) by (intros ->; rewrite String.eqb_refl in Hr; discriminate).
      assert (Hcfy : cf <> y) by (intros ->; rewrite String.eqb_refl in Hcf; discriminate).
      rewrite (update_comm _ r y _ _ Hry).
      rewrite (update_comm _ cf y _ _ Hcfy).
      apply jeval_add_flags; rewrite <- eval_jexpr_agnostic_to_var; eauto.
    - (* JCadcx *)
      apply orb_false_iff in Hnt as [P Hb].
      apply orb_false_iff in P as [P Ha].
      apply orb_false_iff in P as [P Hci].
      apply orb_false_iff in P as [Hco Hr].
      assert (Hry : r <> y) by (intros ->; rewrite String.eqb_refl in Hr; discriminate).
      assert (Hcoy : co <> y) by (intros ->; rewrite String.eqb_refl in Hco; discriminate).
      rewrite (update_comm _ r y _ _ Hry).
      rewrite (update_comm _ co y _ _ Hcoy).
      apply jeval_adcx; rewrite <- eval_jexpr_agnostic_to_var; eauto.
    - (* JCmulx *)
      apply orb_false_iff in Hnt as [P Hb].
      apply orb_false_iff in P as [P Ha].
      apply orb_false_iff in P as [Hh Hl].
      assert (Hly : l <> y) by (intros ->; rewrite String.eqb_refl in Hl; discriminate).
      assert (Hhy : h <> y) by (intros ->; rewrite String.eqb_refl in Hh; discriminate).
      rewrite (update_comm _ l y _ _ Hly).
      rewrite (update_comm _ h y _ _ Hhy).
      apply jeval_mulx; rewrite <- eval_jexpr_agnostic_to_var; eauto.
    - (* JCsub_flags *)
      apply orb_false_iff in Hnt as [P Hb].
      apply orb_false_iff in P as [P Ha].
      apply orb_false_iff in P as [Hcf Hr].
      assert (Hry : r <> y) by (intros ->; rewrite String.eqb_refl in Hr; discriminate).
      assert (Hcfy : cf <> y) by (intros ->; rewrite String.eqb_refl in Hcf; discriminate).
      rewrite (update_comm _ r y _ _ Hry).
      rewrite (update_comm _ cf y _ _ Hcfy).
      apply jeval_sub_flags; rewrite <- eval_jexpr_agnostic_to_var; eauto.
    - (* JCsbb *)
      apply orb_false_iff in Hnt as [P Hb].
      apply orb_false_iff in P as [P Ha].
      apply orb_false_iff in P as [P Hci].
      apply orb_false_iff in P as [Hco Hr].
      assert (Hry : r <> y) by (intros ->; rewrite String.eqb_refl in Hr; discriminate).
      assert (Hcoy : co <> y) by (intros ->; rewrite String.eqb_refl in Hco; discriminate).
      rewrite (update_comm _ r y _ _ Hry).
      rewrite (update_comm _ co y _ _ Hcoy).
      apply jeval_sbb; rewrite <- eval_jexpr_agnostic_to_var; eauto.
  Qed.

  (** Commute a [hi]-update past a middle range when middle doesn't
      touch [hi]: executing the middle from [update env hi w] yields
      the same values (for all non-hi vars) as executing from [env],
      and [hi] stays at [w]. *)
  Lemma jeval_list_hi_update_commutes :
    forall middle hi env w env',
      (forall c, In c middle -> cmd_touches hi c = false) ->
      jeval_list env middle env' ->
      jeval_list (update env hi w) middle (update env' hi w).
  Proof.
    induction middle as [|c cs IH]; intros hi env w env' Hsafe Hev.
    - inversion Hev; subst. constructor.
    - inversion Hev as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
      assert (Hc_safe : cmd_touches hi c = false).
      { apply Hsafe. left. reflexivity. }
      econstructor.
      + eapply jeval_agnostic_to_var; eassumption.
      + apply IH; [|exact Hcs].
        intros c' Hin. apply Hsafe. right. exact Hin.
  Qed.

  (** If an expression's read-set is untouched by the command, its
      evaluation is preserved. *)
  Lemma eval_preserved_through_cmd :
    forall c expr env env',
      (forall x, expr_reads x expr = true -> cmd_touches x c = false) ->
      jeval env c env' ->
      eval_jexpr env' expr = eval_jexpr env expr.
  Proof.
    intros c expr env env' Hsafe Hev.
    induction expr; simpl; try reflexivity.
    - (* JEvar *) simpl in Hsafe.
      specialize (Hsafe x).
      destruct (String.eqb x x) eqn:Heq; [|rewrite String.eqb_refl in Heq; discriminate].
      specialize (Hsafe eq_refl).
      apply (cmd_touches_preserves_var _ _ _ _ Hsafe) in Hev. congruence.
    - (* JEadd, JEsub, ..., JEmulhuu — all binary *)
      rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
    - rewrite IHexpr1, IHexpr2; try reflexivity;
        simpl in Hsafe; intros x Hr; apply Hsafe;
        apply orb_true_iff; [right; exact Hr | left; exact Hr].
  Qed.

  (** Lift to jeval_list. *)
  Lemma eval_preserved_through_list :
    forall cs expr env env',
      (forall c x, In c cs -> expr_reads x expr = true -> cmd_touches x c = false) ->
      jeval_list env cs env' ->
      eval_jexpr env' expr = eval_jexpr env expr.
  Proof.
    induction cs as [|c cs IH]; intros expr env env' Hsafe Hev.
    - inversion Hev; subst. reflexivity.
    - inversion Hev as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
      rewrite (IH expr e1 env'). 2:{
        intros c' x Hin Hr. apply Hsafe; [right; exact Hin | exact Hr].
      } 2: exact Hcs.
      apply eval_preserved_through_cmd with (c := c); [|exact Hc].
      intros x Hr. apply Hsafe; [left; reflexivity | exact Hr].
  Qed.

  (** Single-match rewrite preserves [jeval_list].
      Proof structure: inversion on mulx_rewrite, decompose cs into
      5 parts, reconstruct cs' execution.

      Required additional property (not in current [mulx_rewrite]
      relation): [expr_reads lo a = false] and [expr_reads lo b = false]
      — i.e., the [JCset lo (JEmul a b)] itself doesn't affect operand
      evaluation.  This is naturally satisfied by [scan_mulx_pairs]
      because the matched operands come from a [def_map] built BEFORE
      the JCset lo (so they can't reference lo).

      The proof outline (using already-Qed lemmas):
      1. jeval_list_app to split cs into prefix execution + rest.
      2. inversion on cons to extract JCset lo execution:
         va = eval env_after_prefix a, vb = eval env_after_prefix b,
         env_after_mul = update env_after_prefix lo (word.mul va vb).
      3. jeval_list_app on rest to split middle + JCset hi :: suffix.
      4. inversion on JCset hi:
         env_after_mulhuu = update env_after_middle hi
                                   (word.mulhuu va'' vb'')
         where va'' = eval env_after_middle a'', vb'' = eval env_after_middle b''.
         By Ha_eq + eval_preserved_through_list (using Hmid_a):
           va'' = eval env_after_middle a = eval env_after_mul a.
         With lo ∉ reads(a): = eval env_after_prefix a = va.
         Similarly vb'' = vb.
      5. Build rewritten execution:
         - prefix: same as original (Hev_pre).
         - JCmulx: produces env_after_mulx =
             update (update env_after_prefix hi (word.mulhuu va vb)) lo (word.mul va vb).
         - middle from env_after_mulx: by jeval_list_hi_update_commutes
           (applied with w = word.mulhuu va vb), produces
             update env_after_middle hi (word.mulhuu va vb)
             = update env_after_middle hi (word.mulhuu va'' vb'')
             = env_after_mulhuu.
         - JCskip: identity, env stays at env_after_mulhuu.
         - suffix: same as original. *)
  Theorem rewrite_mulx_one_match_sound :
    forall hi lo a b cs cs' ev ev',
      mulx_rewrite hi lo a b cs cs' ->
      hi <> lo ->
      expr_reads lo a = false ->
      expr_reads lo b = false ->
      jeval_list ev cs ev' ->
      jeval_list ev cs' ev'.
  Proof.
    intros hi lo a b cs cs' ev ev' Hrew Hhi_lo Ha_lo Hb_lo Hev.
    inversion Hrew as [prefix middle suffix a'' b''
                       Hmid_hi Hmid_a Hmid_b Ha_eq Hb_eq]; subst.
    (* Step 1: prefix then rest *)
    apply jeval_list_app in Hev as [e1 [Hev_pre Hev_rest]].
    (* Step 2: JCset lo :: middle ++ JCset hi :: suffix *)
    inversion Hev_rest; subst.
    match goal with H : jeval e1 (JCset lo (JEmul a b)) _ |- _ =>
      rename H into Hev_mul end.
    match goal with H : jeval_list _ (middle ++ _) ev' |- _ =>
      rename H into Hev_rest2 end.
    inversion Hev_mul; subst.
    match goal with H : eval_jexpr e1 (JEmul a b) = Some _ |- _ =>
      rename H into Heval_mul end.
    simpl in Heval_mul.
    destruct (eval_jexpr e1 a) as [va|] eqn:Hva_ev; [|discriminate].
    destruct (eval_jexpr e1 b) as [vb|] eqn:Hvb_ev; [|discriminate].
    injection Heval_mul; intros <-; clear Heval_mul.
    (* Step 3: middle then JCset hi :: suffix *)
    apply jeval_list_app in Hev_rest2 as [e2 [Hev_mid Hev_rest3]].
    inversion Hev_rest3; subst.
    match goal with H : jeval e2 (JCset hi (JEmulhuu a'' b'')) _ |- _ =>
      rename H into Hev_mulhuu end.
    match goal with H : jeval_list _ suffix ev' |- _ =>
      rename H into Hev_suf end.
    inversion Hev_mulhuu; subst.
    match goal with H : eval_jexpr e2 (JEmulhuu a'' b'') = Some _ |- _ =>
      rename H into Heval_mulhuu end.
    simpl in Heval_mulhuu.
    destruct (eval_jexpr e2 a'') as [va2|] eqn:Hva2_ev; [|discriminate].
    destruct (eval_jexpr e2 b'') as [vb2|] eqn:Hvb2_ev; [|discriminate].
    injection Heval_mulhuu; intros <-; clear Heval_mulhuu.
    (* Step 4: show va2 = va, vb2 = vb via Ha_eq + eval_preserved + lo-unread *)
    rewrite <- (Ha_eq e2) in Hva2_ev.
    rewrite (eval_preserved_through_list middle a _ _ Hmid_a Hev_mid)
      in Hva2_ev.
    rewrite <- (Hb_eq e2) in Hvb2_ev.
    rewrite (eval_preserved_through_list middle b _ _ Hmid_b Hev_mid)
      in Hvb2_ev.
    (* Now Hva2_ev: eval_jexpr (update e1 lo (word.mul va vb)) a = Some va2
       Use eval_jexpr_agnostic_to_var (with x = lo): since lo ∉ reads(a),
       the update doesn't change eval a. *)
    rewrite <- (eval_jexpr_agnostic_to_var a lo e1 (word.mul va vb) Ha_lo)
      in Hva2_ev.
    rewrite Hva_ev in Hva2_ev. injection Hva2_ev as Hva_eq2.
    rewrite <- (eval_jexpr_agnostic_to_var b lo e1 (word.mul va vb) Hb_lo)
      in Hvb2_ev.
    rewrite Hvb_ev in Hvb2_ev. injection Hvb2_ev as Hvb_eq2.
    subst va2 vb2.
    (* Step 5: build rewritten execution *)
    apply jeval_list_app. exists e1. split; [exact Hev_pre|].
    (* JCmulx hi lo a b :: middle ++ JCskip :: suffix *)
    eapply jeval_list_cons.
    { apply jeval_mulx with (va := va) (vb := vb); assumption. }
    (* After JCmulx: state is
         update (update e1 hi (word.mulhuu va vb)) lo (word.mul va vb) *)
    apply jeval_list_app.
    (* Apply jeval_list_hi_update_commutes to push the hi-update through
       middle.  middle runs from env_after_mul = update e1 lo (word.mul va vb)
       to e2.  Adding hi-update: runs from
         update (update e1 lo ...) hi (mulhuu va vb)
       to update e2 hi (mulhuu va vb).  But we need to start from
         update (update e1 hi (mulhuu va vb)) lo (word.mul va vb)
       — these are equal by update_comm (hi <> lo). *)
    exists (update e2 hi (word.mulhuu va vb)). split.
    { rewrite (update_comm e1 hi lo _ _ Hhi_lo).
      apply jeval_list_hi_update_commutes; [exact Hmid_hi | exact Hev_mid]. }
    (* Then JCskip :: suffix from update e2 hi (mulhuu va vb).
       After JCskip: same env.  Then suffix execution; we have
       Hev_suf: jeval_list (update e2 hi (mulhuu va vb)) suffix ev'
       because update e2 hi (mulhuu va vb) is exactly the post-mulhuu env
       in the original execution. *)
    eapply jeval_list_cons.
    { constructor. }
    exact Hev_suf.
  Qed.

  (* ================================================================ *)
  (* Transitive-closure composition: iterated single-match rewrites    *)
  (* ================================================================ *)

  (** [mulx_rewrite_star] is the reflexive-transitive closure of
      [mulx_rewrite], representing applying zero or more single-match
      rewrites in sequence. *)
  Inductive mulx_rewrite_star : list jasmin_cmd -> list jasmin_cmd -> Prop :=
  | mulx_rewrite_star_refl : forall cs, mulx_rewrite_star cs cs
  | mulx_rewrite_star_step : forall cs1 cs2 cs3 hi lo a b,
      mulx_rewrite hi lo a b cs1 cs2 ->
      hi <> lo ->
      expr_reads lo a = false ->
      expr_reads lo b = false ->
      mulx_rewrite_star cs2 cs3 ->
      mulx_rewrite_star cs1 cs3.

  (** Iterated soundness: if cs' is reachable from cs by
      [mulx_rewrite_star], then jeval_list is preserved. *)
  Theorem mulx_rewrite_star_sound :
    forall cs cs' e e',
      mulx_rewrite_star cs cs' ->
      jeval_list e cs e' ->
      jeval_list e cs' e'.
  Proof.
    intros cs cs' e e' Hstar. revert e e'.
    induction Hstar as [cs | cs1 cs2 cs3 hi lo a b Hone Hhi_lo Ha_lo Hb_lo Hrest IH];
      intros e e' Hev.
    - exact Hev.
    - apply IH.
      eapply rewrite_mulx_one_match_sound; eassumption.
  Qed.

  (** The final theorem at the paper-ready level: if cs can be
      transformed to cs' by any sequence of valid single-match
      rewrites, jeval_list is preserved.

      The bridge [lower_mulx_pairs_reduces_to_star] below closes the
      remaining gap for the trivial-scan case (and documents what's
      needed for the general case). *)

  (** When [scan_mulx_pairs cs = nil], [lower_mulx_pairs cs = cs], so
      the rewrite_star is reflexive.  Direct from [lower_mulx_pairs_empty]. *)
  Lemma lower_mulx_pairs_to_star_empty :
    forall cs,
      scan_mulx_pairs cs = nil ->
      mulx_rewrite_star cs (lower_mulx_pairs cs).
  Proof.
    intros cs Hscan.
    rewrite (lower_mulx_pairs_empty _ Hscan).
    constructor.
  Qed.

  (** Step 2 main theorem: applying rewrite_mulx_aux 0 [m] yields a
      [mulx_rewrite], given [valid_match_at cs m]. *)
  Lemma rewrite_mulx_aux_single_is_rewrite :
    forall cs m,
      valid_match_at cs m ->
      let '(_, _, hi, lo, a, b) := m in
      mulx_rewrite hi lo a b cs (rewrite_mulx_aux 0 [m] cs).
  Proof.
    intros cs [[[[[mi mj] hi] lo] a] b] Hv.
    destruct Hv as [Hij [[a'' [b'' [Hnth_mul [Hnth_mulhuu [Ha_eq Hb_eq]]]]]
                    [Hmid [Hla [Hlb Hhi_lo]]]]].
    (* Split cs at positions mi and mj *)
    set (prefix := firstn mi cs).
    set (middle := firstn (mj - S mi) (skipn (S mi) cs)).
    set (suffix := skipn (S mj) cs).
    (* Key structural decomposition of cs *)
    assert (Hcs_eq :
      cs = prefix ++ JCset lo (JEmul a b) :: middle
                ++ JCset hi (JEmulhuu a'' b'') :: suffix).
    { pose proof (list_split_nth _ cs mi _ Hnth_mul) as E1.
      rewrite E1 at 1. f_equal.
      (* need skipn (S mi) cs = middle ++ JCset hi (...) :: suffix *)
      assert (Hskip_mi :
        skipn (S mi) cs
        = middle ++ JCset hi (JEmulhuu a'' b'') :: suffix).
      { subst middle suffix.
        rewrite <- (firstn_skipn (mj - S mi) (skipn (S mi) cs)) at 1.
        f_equal.
        rewrite skipn_skipn.
        replace (mj - S mi + S mi)%nat with mj by lia.
        (* skipn mj cs = JCset hi :: skipn (S mj) cs *)
        assert (Hnth_skipn : nth_error (skipn mj cs) 0
                             = Some (JCset hi (JEmulhuu a'' b''))).
        { rewrite nth_error_skipn. rewrite Nat.add_0_r. exact Hnth_mulhuu. }
        destruct (skipn mj cs) as [|c' tail] eqn:Hsk.
        - simpl in Hnth_skipn. discriminate.
        - simpl in Hnth_skipn. injection Hnth_skipn as <-.
          f_equal.
          replace (S mj) with (1 + mj)%nat by lia.
          rewrite <- skipn_skipn. rewrite Hsk. reflexivity. }
      f_equal. exact Hskip_mi. }
    (* Apply the decomposed rewrite lemma *)
    assert (Hmi_len : length prefix = mi).
    { subst prefix. apply List.firstn_length_le.
      assert (Hmi_lt : (mi < length cs)%nat) by
        (eapply nth_error_Some_length; eassumption). lia. }
    assert (Hmid_len : (length prefix + 1 + length middle = mj)%nat).
    { subst middle. rewrite Hmi_len.
      rewrite List.firstn_length_le.
      - lia.
      - rewrite skipn_length.
        assert (Hmj_lt : (mj < length cs)%nat) by
          (eapply nth_error_Some_length; eassumption). lia. }
    rewrite Hcs_eq.
    rewrite <- Hmi_len. rewrite <- Hmid_len.
    rewrite rewrite_mulx_aux_single_decomposed.
    apply mulx_rewrite_intro; try assumption.
    (* middle safety: follows from Hmid applied per-element *)
    - intros c Hin.
      subst middle.
      apply In_nth_error in Hin as [k Hnth].
      assert (Hk_bound : (k < mj - S mi)%nat).
      { apply nth_error_Some_length in Hnth.
        rewrite firstn_length_le in Hnth; [exact Hnth|].
        rewrite skipn_length.
        assert (Hmj_lt : (mj < length cs)%nat) by
          (eapply nth_error_Some_length; eassumption). lia. }
      assert (HSmi_le : (S mi <= mj)%nat) by lia.
      assert (Horig : nth_error cs (S mi + k) = Some c).
      { rewrite <- nth_error_skipn.
        rewrite nth_error_firstn in Hnth.
        destruct (Nat.ltb k (mj - S mi)) eqn:Hlt; [exact Hnth|].
        apply Nat.ltb_ge in Hlt. lia. }
      assert (HiRange : (mi < S mi + k < mj)%nat) by lia.
      pose proof (Hmid c (S mi + k)%nat HiRange Horig) as [Hmid_hi [_ _]].
      exact Hmid_hi.
    - intros c x Hin Hrx.
      subst middle.
      apply In_nth_error in Hin as [k Hnth].
      assert (Hk_bound : (k < mj - S mi)%nat).
      { apply nth_error_Some_length in Hnth.
        rewrite firstn_length_le in Hnth; [exact Hnth|].
        rewrite skipn_length.
        assert (Hmj_lt : (mj < length cs)%nat) by
          (eapply nth_error_Some_length; eassumption). lia. }
      assert (HSmi_le : (S mi <= mj)%nat) by lia.
      assert (Horig : nth_error cs (S mi + k) = Some c).
      { rewrite <- nth_error_skipn.
        rewrite nth_error_firstn in Hnth.
        destruct (Nat.ltb k (mj - S mi)) eqn:Hlt; [exact Hnth|].
        apply Nat.ltb_ge in Hlt. lia. }
      assert (HiRange : (mi < S mi + k < mj)%nat) by lia.
      pose proof (Hmid c (S mi + k)%nat HiRange Horig) as [_ [Hmid_a _]].
      apply Hmid_a. exact Hrx.
    - intros c x Hin Hrx.
      subst middle.
      apply In_nth_error in Hin as [k Hnth].
      assert (Hk_bound : (k < mj - S mi)%nat).
      { apply nth_error_Some_length in Hnth.
        rewrite firstn_length_le in Hnth; [exact Hnth|].
        rewrite skipn_length.
        assert (Hmj_lt : (mj < length cs)%nat) by
          (eapply nth_error_Some_length; eassumption). lia. }
      assert (HSmi_le : (S mi <= mj)%nat) by lia.
      assert (Horig : nth_error cs (S mi + k) = Some c).
      { rewrite <- nth_error_skipn.
        rewrite nth_error_firstn in Hnth.
        destruct (Nat.ltb k (mj - S mi)) eqn:Hlt; [exact Hnth|].
        apply Nat.ltb_ge in Hlt. lia. }
      assert (HiRange : (mi < S mi + k < mj)%nat) by lia.
      pose proof (Hmid c (S mi + k)%nat HiRange Horig) as [_ [_ Hmid_b]].
      apply Hmid_b. exact Hrx.
  Qed.

  (** Pairwise disjointness of a match list. *)
  Definition matches_pairwise_disjoint (ms : list mulx_match) : Prop :=
    forall m1 m2, In m1 ms -> In m2 ms -> m1 <> m2 -> match_disjoint m1 m2.

  (** Remove one match from a list and check Forall-disjoint with the
      remaining. *)
  Lemma matches_pairwise_disjoint_tail :
    forall m ms,
      matches_pairwise_disjoint (m :: ms) ->
      matches_pairwise_disjoint ms.
  Proof.
    intros m ms H. unfold matches_pairwise_disjoint in *.
    intros m1 m2 Hin1 Hin2 Hneq.
    apply H; [right; exact Hin1 | right; exact Hin2 | exact Hneq].
  Qed.

  (** Variable-names-disjoint property between two matches m1 and m2.
      Strong form: applying m1 (JCmulx hi1 lo1 a1 b1 insertion +
      JCskip at mj1) must not touch m2's safety-protected variables
      (hi2 and the reads of a2/b2).

      [cmd_touches x (JCmulx hi lo a b) = false] requires:
        x ≠ hi, x ≠ lo, expr_reads x a = false, expr_reads x b = false.
      So match_names_disjoint m1 m2 needs:
      - hi2 ≠ hi1, hi2 ≠ lo1, hi2 ∉ reads(a1), hi2 ∉ reads(b1)
      - for every x ∈ reads(a2) ∪ reads(b2):
          x ≠ hi1, x ≠ lo1, x ∉ reads(a1), x ∉ reads(b1). *)
  Definition match_names_disjoint (m1 m2 : mulx_match) : Prop :=
    let '(_, _, hi1, lo1, a1, b1) := m1 in
    let '(_, _, hi2, _, a2, b2) := m2 in
    (* m1's inserted JCmulx does not touch hi2 *)
    hi2 <> hi1 /\ hi2 <> lo1
    /\ expr_reads hi2 a1 = false /\ expr_reads hi2 b1 = false
    /\ (* m1's inserted JCmulx does not touch any var read by a2 *)
       (forall x, expr_reads x a2 = true ->
          x <> hi1 /\ x <> lo1 /\ expr_reads x a1 = false /\ expr_reads x b1 = false)
    /\ (* ...or by b2 *)
       (forall x, expr_reads x b2 = true ->
          x <> hi1 /\ x <> lo1 /\ expr_reads x a1 = false /\ expr_reads x b1 = false).

  (** Strong pairwise-disjointness: position AND name. *)
  Definition matches_strong_disjoint (ms : list mulx_match) : Prop :=
    forall m1 m2, In m1 ms -> In m2 ms -> m1 <> m2 ->
      match_disjoint m1 m2 /\ match_names_disjoint m1 m2.

  (* ================================================================ *)
  (* Scan invariant: strengthened wf predicate + direct implication    *)
  (* ================================================================ *)

  (** Boolean check: does the scan-produced match m satisfy all
      valid_match_at conditions against cs?  This is a syntactic
      predicate we can check post-hoc, strictly stronger than
      [wf_mulx_list] (which only checks stmts_between_safe). *)
  Definition match_well_formed_at_b (cs : list jasmin_cmd) (m : mulx_match) : bool :=
    let '(mi, mj, hi, lo, a, b) := m in
    (* Position ordering *)
    Nat.ltb mi mj
    (* Positions have the right JCset shape *)
    && match nth_error cs mi with
       | Some (JCset lo_cs (JEmul a_cs b_cs)) =>
           String.eqb lo_cs lo && expr_eqb_full a_cs a && expr_eqb_full b_cs b
       | _ => false
       end
    && match nth_error cs mj with
       | Some (JCset hi_cs (JEmulhuu _ _)) => String.eqb hi_cs hi
       | _ => false
       end
    (* Operand-self and hi<>lo constraints *)
    && negb (expr_reads lo a)
    && negb (expr_reads lo b)
    && negb (String.eqb hi lo)
    (* Middle-safety for hi, a-reads, b-reads *)
    && stmts_between_safe hi mi mj 0 cs.
    (* Note: middle-safety for a-reads/b-reads not encoded here; covered
       by a generalized safe predicate below. *)

  (** Strong scan output validity: every match is [valid_match_at] AND
      the list is pairwise strong-disjoint AND NoDup.  This is what we
      need for [lower_mulx_pairs_list_correct_final].  It is a
      post-hoc check on [scan_mulx_pairs cs] that the user can
      [vm_compute] at call sites. *)
  Definition scan_output_valid_b (cs : list jasmin_cmd) : Prop :=
    Forall (valid_match_at cs) (scan_mulx_pairs cs)
    /\ matches_strong_disjoint (scan_mulx_pairs cs)
    /\ NoDup (scan_mulx_pairs cs).

  (** Closing the scan invariant: we prove the empty-scan case
      directly (Qed), and reduce the general case to a stronger
      syntactic check [scan_output_valid_bool cs = true] that a user
      can [vm_compute]. *)

  (** Boolean check on scan output.  Each match passes
      [match_well_formed_at_b] and the list is pairwise position-
      disjoint.  This is efficiently [vm_compute]-checkable. *)
  Definition matches_position_disjoint_b (m1 m2 : mulx_match) : bool :=
    let '(i1, j1, _, _, _, _) := m1 in
    let '(i2, j2, _, _, _, _) := m2 in
    negb (Nat.eqb i1 i2)
    && negb (Nat.eqb i1 j2)
    && negb (Nat.eqb j1 i2)
    && negb (Nat.eqb j1 j2).

  Fixpoint all_pairwise_disjoint_b (ms : list mulx_match) : bool :=
    match ms with
    | nil => true
    | m :: rest =>
        forallb (matches_position_disjoint_b m) rest
        && all_pairwise_disjoint_b rest
    end.

  (** Empty-scan case: trivially valid. *)
  Lemma scan_output_valid_b_empty :
    forall cs, scan_mulx_pairs cs = nil -> scan_output_valid_b cs.
  Proof.
    intros cs Hs. unfold scan_output_valid_b. rewrite Hs.
    split; [constructor|].
    split.
    - unfold matches_strong_disjoint. intros m1 m2 [] _ _.
    - constructor.
  Qed.

  (** Reduction: the general scan invariant.  Proof strategy: by
      strengthened induction on [scan_mulx_pairs_aux], with a 4-part
      invariant tracking def-map consistency, pending validity, acc
      validity, and acc disjointness.  ~100 lines to fully close;
      left as a conjecture here with detailed invariant documented. *)

  (** The scan invariant. *)
  Record scan_inv_pred (cs_all : list jasmin_cmd) (n : nat)
                       (m : def_map) (pending : list pending_mul)
                       (acc : list mulx_match) : Prop := {
    (* 1. acc entries are all valid at cs_all *)
    si_acc_valid : Forall (valid_match_at cs_all) acc;
    (* 2. acc is pairwise strong-disjoint *)
    si_acc_disjoint : matches_strong_disjoint acc;
    (* 3. acc has no duplicates *)
    si_acc_nodup : NoDup acc;
    (* 4. acc positions are all < n *)
    si_acc_behind : forall mm, In mm acc ->
      let '(mi, mj, _, _, _, _) := mm in (mj < n)%nat /\ (mi < mj)%nat;
    (* 5. pending entries correspond to JCset lo (JEmul a b) at idx < n *)
    si_pending_valid : forall p, In p pending ->
      let '(idx, lo_p, a_p, b_p) := p in
      (idx < n)%nat /\
      nth_error cs_all idx = Some (JCset lo_p (JEmul a_p b_p));
  }.

  (** Base case: the initial invariant holds vacuously. *)
  Lemma scan_inv_pred_init :
    forall cs, scan_inv_pred cs 0 nil nil nil.
  Proof.
    intros cs. constructor.
    - constructor.
    - unfold matches_strong_disjoint. intros m1 m2 [] _ _.
    - constructor.
    - intros mm [].
    - intros p [].
  Qed.

  (** Invariant preservation through non-JCset statements.  The aux
      function leaves m, pending, acc unchanged and increments n. *)
  Lemma scan_inv_pred_step_nonset :
    forall (cs_all : list jasmin_cmd) (n : nat) (m : def_map)
           (pending : list pending_mul) (acc : list mulx_match) (c : jasmin_cmd),
      scan_inv_pred cs_all n m pending acc ->
      (* c is not a JCset *)
      (match c with JCset _ _ => False | _ => True end) ->
      nth_error cs_all n = Some c ->
      scan_inv_pred cs_all (S n) m pending acc.
  Proof.
    intros cs_all n m pending acc c [Hval Hdisj Hnodup Hbehind Hpend]
           Hnonset Hnth.
    constructor; auto.
    - intros [[[[[mi mj] hi] lo] a] b] Hin.
      specialize (Hbehind (mi,mj,hi,lo,a,b) Hin). destruct Hbehind.
      split; lia.
    - intros [[[idx lo_p] a_p] b_p] Hin.
      specialize (Hpend (idx, lo_p, a_p, b_p) Hin). destruct Hpend.
      split; [lia|auto].
  Qed.

  (** Invariant preservation: JCset x e where e is NOT JEmul or JEmulhuu.
      The def_map is updated but pending and acc are unchanged. *)
  Lemma scan_inv_pred_step_JCset_other :
    forall (cs_all : list jasmin_cmd) (n : nat) (m : def_map)
           (pending : list pending_mul) (acc : list mulx_match)
           (x : string) (e : jasmin_expr),
      scan_inv_pred cs_all n m pending acc ->
      (match e with JEmul _ _ => False | JEmulhuu _ _ => False | _ => True end) ->
      nth_error cs_all n = Some (JCset x e) ->
      scan_inv_pred cs_all (S n) (defmap_update m x e) pending acc.
  Proof.
    intros cs_all n m pending acc x e
           [Hval Hdisj Hnodup Hbehind Hpend] Hnot_mulx Hnth.
    constructor; auto.
    - intros [[[[[mi mj] hi] lo] a] b] Hin.
      specialize (Hbehind (mi,mj,hi,lo,a,b) Hin). destruct Hbehind.
      split; lia.
    - intros [[[idx lo_p] a_p] b_p] Hin.
      specialize (Hpend (idx, lo_p, a_p, b_p) Hin). destruct Hpend.
      split; [lia|auto].
  Qed.

  (** Invariant preservation: JCset x (JEmul a b).  The new pending
      entry is valid (idx = n, JCset matches at position n). *)
  Lemma scan_inv_pred_step_JCset_mul :
    forall (cs_all : list jasmin_cmd) (n : nat) (m : def_map)
           (pending : list pending_mul) (acc : list mulx_match)
           (x : string) (a b : jasmin_expr),
      scan_inv_pred cs_all n m pending acc ->
      nth_error cs_all n = Some (JCset x (JEmul a b)) ->
      scan_inv_pred cs_all (S n) (defmap_update m x (JEmul a b))
                    ((n, x, a, b) :: pending) acc.
  Proof.
    intros cs_all n m pending acc x a b
           [Hval Hdisj Hnodup Hbehind Hpend] Hnth.
    constructor; auto.
    - intros [[[[[mi mj] hi] lo] a0] b0] Hin.
      specialize (Hbehind (mi,mj,hi,lo,a0,b0) Hin). destruct Hbehind.
      split; lia.
    - intros [[[idx lo_p] a_p] b_p] Hin. simpl in Hin.
      destruct Hin as [Heq | Hin'].
      + injection Heq as <- <- <- <-.
        split; [lia | exact Hnth].
      + specialize (Hpend (idx, lo_p, a_p, b_p) Hin'). destruct Hpend.
        split; [lia|auto].
  Qed.

  (** Invariant preservation: JCset hi (JEmulhuu a b) with NO pending
      match.  The def_map is updated; pending and acc unchanged. *)
  Lemma scan_inv_pred_step_JCset_mulhuu_nomatch :
    forall (cs_all : list jasmin_cmd) (n : nat) (m : def_map)
           (pending : list pending_mul) (acc : list mulx_match)
           (hi : string) (a b : jasmin_expr),
      scan_inv_pred cs_all n m pending acc ->
      find_matching_mul m a b pending = None ->
      nth_error cs_all n = Some (JCset hi (JEmulhuu a b)) ->
      scan_inv_pred cs_all (S n) (defmap_update m hi (JEmulhuu a b))
                    pending acc.
  Proof.
    intros cs_all n m pending acc hi a b
           [Hval Hdisj Hnodup Hbehind Hpend] _ Hnth.
    constructor; auto.
    - intros [[[[[mi mj] hi0] lo] a0] b0] Hin.
      specialize (Hbehind (mi,mj,hi0,lo,a0,b0) Hin). destruct Hbehind.
      split; lia.
    - intros [[[idx lo_p] a_p] b_p] Hin.
      specialize (Hpend (idx, lo_p, a_p, b_p) Hin). destruct Hpend.
      split; [lia|auto].
  Qed.

  (** Does command [c] touch any variable read by expression [op]? *)
  Fixpoint cmd_touches_any_read (c : jasmin_cmd) (op : jasmin_expr) : bool :=
    match op with
    | JEvar x => cmd_touches x c
    | JElit _ => false
    | JEadd a b | JEsub a b | JEmul a b | JEmulhuu a b
    | JEand a b | JEor a b | JExor a b
    | JEshr a b | JEshl a b | JEltu a b | JEeq a b =>
        cmd_touches_any_read c a || cmd_touches_any_read c b
    | JEload base _ => cmd_touches_any_read c base
    end.

  (** No statement between [mi, mj] touches any var read by [op]. *)
  Fixpoint stmts_between_operand_safe (op : jasmin_expr)
      (mi mj n : nat) (cs : list jasmin_cmd) : bool :=
    match cs with
    | nil => true
    | c :: rest =>
        let is_between := Nat.ltb mi n && Nat.ltb n mj in
        (if is_between then negb (cmd_touches_any_read c op) else true)
        && stmts_between_operand_safe op mi mj (S n) rest
    end.

  (** Strengthened post-hoc match check: includes every syntactic
      condition [valid_match_at] demands.  Adds to
      [match_well_formed_at_b] the verification that the JEmulhuu
      operands are [expr_eqb_full]-equal to the JEmul operands (making
      the [forall ev, eval_jexpr] clause follow by reflexivity) plus
      middle-safety on operand reads. *)
  Definition match_fully_valid_b (cs : list jasmin_cmd) (m : mulx_match) : bool :=
    let '(mi, mj, hi, lo, a, b) := m in
    Nat.ltb mi mj
    && (match nth_error cs mi with
        | Some (JCset lo' (JEmul a' b')) =>
            String.eqb lo lo' && expr_eqb_full a a' && expr_eqb_full b b'
        | _ => false
        end)
    && (match nth_error cs mj with
        | Some (JCset hi' (JEmulhuu a'' b'')) =>
            String.eqb hi hi' && expr_eqb_full a a'' && expr_eqb_full b b''
        | _ => false
        end)
    && negb (expr_reads lo a)
    && negb (expr_reads lo b)
    && negb (String.eqb hi lo)
    && stmts_between_safe hi mi mj 0 cs
    && stmts_between_operand_safe a mi mj 0 cs
    && stmts_between_operand_safe b mi mj 0 cs.

  (** For every variable read by [op], it's safe wrt {hi1, lo1, a1, b1}:
      - not equal to hi1 or lo1
      - not read by a1 or b1. *)
  Fixpoint expr_reads_all_safe (hi1 lo1 : string)
      (a1 b1 op : jasmin_expr) : bool :=
    match op with
    | JEvar x => negb (String.eqb x hi1) && negb (String.eqb x lo1)
              && negb (expr_reads x a1) && negb (expr_reads x b1)
    | JElit _ => true
    | JEadd u v | JEsub u v | JEmul u v | JEmulhuu u v
    | JEand u v | JEor u v | JExor u v
    | JEshr u v | JEshl u v | JEltu u v | JEeq u v =>
        expr_reads_all_safe hi1 lo1 a1 b1 u
        && expr_reads_all_safe hi1 lo1 a1 b1 v
    | JEload base _ => expr_reads_all_safe hi1 lo1 a1 b1 base
    end.

  (** Pairwise name-disjointness check (boolean).  Verifies
      [match_names_disjoint] structurally. *)
  Definition pair_names_disjoint_b (m1 m2 : mulx_match) : bool :=
    let '(_, _, hi1, lo1, a1, b1) := m1 in
    let '(_, _, hi2, _, a2, b2) := m2 in
    negb (String.eqb hi2 hi1)
    && negb (String.eqb hi2 lo1)
    && negb (expr_reads hi2 a1)
    && negb (expr_reads hi2 b1)
    && expr_reads_all_safe hi1 lo1 a1 b1 a2
    && expr_reads_all_safe hi1 lo1 a1 b1 b2.

  Fixpoint all_pair_names_disjoint_b (ms : list mulx_match) : bool :=
    match ms with
    | nil => true
    | m :: rest =>
        forallb (pair_names_disjoint_b m) rest
        && forallb (fun m' => pair_names_disjoint_b m' m) rest
        && all_pair_names_disjoint_b rest
    end.

  (** Strong wf predicate: checks every scan output is fully valid
      PLUS pairwise position-disjoint PLUS pairwise name-disjoint. *)
  Definition wf_mulx_list_strong_b (cs : list jasmin_cmd) : bool :=
    forallb (match_fully_valid_b cs) (scan_mulx_pairs cs)
    && all_pairwise_disjoint_b (scan_mulx_pairs cs)
    && all_pair_names_disjoint_b (scan_mulx_pairs cs).

  (** Helper: expr_eqb_full is sound. *)
  Lemma expr_eqb_full_sound :
    forall e1 e2, expr_eqb_full e1 e2 = true -> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros H; try discriminate;
      try (apply String.eqb_eq in H; subst; reflexivity);
      try (apply Z.eqb_eq in H; subst; reflexivity);
      try (apply andb_prop in H as [Ha Hb];
           apply IHe1_1 in Ha; apply IHe1_2 in Hb; subst; reflexivity).
    - apply andb_prop in H as [Ha Hb].
      apply IHe1 in Ha. apply Z.eqb_eq in Hb. subst. reflexivity.
  Qed.

  (** Helper: [stmts_between_safe] reflection. *)
  Lemma stmts_between_safe_nth :
    forall x mi mj n cs i c,
      stmts_between_safe x mi mj n cs = true ->
      (mi < n + i < mj)%nat ->
      nth_error cs i = Some c ->
      cmd_touches x c = false.
  Proof.
    intros x mi mj n cs. revert n.
    induction cs as [|c0 cs IH]; intros n i c Hsafe Hrange Hnth.
    - destruct i; discriminate Hnth.
    - destruct i as [|i']; simpl in Hnth.
      + injection Hnth as <-. simpl in Hsafe.
        rewrite Nat.add_0_r in Hrange.
        assert (Hrange' : (mi <? n)%nat && (n <? mj)%nat = true).
        { apply andb_true_iff. split; apply Nat.ltb_lt; lia. }
        rewrite Hrange' in Hsafe.
        apply andb_prop in Hsafe as [Hhd _].
        apply negb_true_iff in Hhd. exact Hhd.
      + simpl in Hsafe. apply andb_prop in Hsafe as [_ Hsafe_tl].
        apply (IH (S n) i' c); auto. lia.
  Qed.

  (** Helper: [cmd_touches_any_read] reflection. *)
  Lemma cmd_touches_any_read_sound :
    forall c op x,
      cmd_touches_any_read c op = false ->
      expr_reads x op = true ->
      cmd_touches x c = false.
  Proof.
    intros c op. induction op; intros y Hct Hre; simpl in *;
      try discriminate;
      try (apply Bool.orb_true_iff in Hre as [Ha|Hb];
           apply Bool.orb_false_iff in Hct as [Hca Hcb];
           [apply IHop1; auto | apply IHop2; auto]).
    - apply String.eqb_eq in Hre. subst. exact Hct.
    - apply IHop; auto.
  Qed.

  (** [stmts_between_operand_safe] reflection. *)
  Lemma stmts_between_operand_safe_nth :
    forall op mi mj n cs i c x,
      stmts_between_operand_safe op mi mj n cs = true ->
      (mi < n + i < mj)%nat ->
      nth_error cs i = Some c ->
      expr_reads x op = true ->
      cmd_touches x c = false.
  Proof.
    intros op mi mj n cs. revert n.
    induction cs as [|c0 cs IH]; intros n i c y Hsafe Hrange Hnth Hre.
    - destruct i; discriminate Hnth.
    - destruct i as [|i']; simpl in Hnth.
      + injection Hnth as <-. simpl in Hsafe.
        rewrite Nat.add_0_r in Hrange.
        assert (Hrange' : (mi <? n)%nat && (n <? mj)%nat = true).
        { apply andb_true_iff. split; apply Nat.ltb_lt; lia. }
        rewrite Hrange' in Hsafe.
        apply andb_prop in Hsafe as [Hhd _].
        apply negb_true_iff in Hhd.
        eapply cmd_touches_any_read_sound; eauto.
      + simpl in Hsafe. apply andb_prop in Hsafe as [_ Hsafe_tl].
        apply (IH (S n) i' c y); auto. lia.
  Qed.

  (** Bridge: match_fully_valid_b implies valid_match_at. *)
  Lemma match_fully_valid_b_implies_valid :
    forall cs m,
      match_fully_valid_b cs m = true ->
      valid_match_at cs m.
  Proof.
    intros cs [[[[[mi mj] hi] lo] a] b] H.
    cbn in H.
    apply andb_prop in H as [H Hb_safe].
    apply andb_prop in H as [H Ha_safe].
    apply andb_prop in H as [H Hhi_safe].
    apply andb_prop in H as [H Hhi_lo].
    apply andb_prop in H as [H Hlo_b].
    apply andb_prop in H as [H Hlo_a].
    apply andb_prop in H as [H Hmj].
    apply andb_prop in H as [Hlt Hmi].
    apply Nat.ltb_lt in Hlt.
    apply negb_true_iff in Hlo_a, Hlo_b, Hhi_lo.
    apply String.eqb_neq in Hhi_lo.
    destruct (nth_error cs mi) as [c_mi|] eqn:Enth_mi; [|discriminate Hmi].
    destruct c_mi; try discriminate Hmi. destruct e; try discriminate Hmi.
    apply andb_prop in Hmi as [Hmi Hb_eq].
    apply andb_prop in Hmi as [Hlo_eq Ha_eq].
    apply String.eqb_eq in Hlo_eq.
    apply expr_eqb_full_sound in Ha_eq, Hb_eq.
    subst lo. subst e1. subst e2.
    destruct (nth_error cs mj) as [c_mj|] eqn:Enth_mj; [|discriminate Hmj].
    destruct c_mj; try discriminate Hmj. destruct e; try discriminate Hmj.
    apply andb_prop in Hmj as [Hmj Hb_mj_eq].
    apply andb_prop in Hmj as [Hhi_eq Ha_mj_eq].
    apply String.eqb_eq in Hhi_eq.
    apply expr_eqb_full_sound in Ha_mj_eq, Hb_mj_eq.
    subst hi. subst e1. subst e2.
    split; [exact Hlt|].
    split.
    { eexists. eexists. split; [exact Enth_mi|]. split; [exact Enth_mj|].
      split; intros ev; reflexivity. }
    split.
    { intros c i Hrange Hnth_i.
      split; [|split].
      - eapply stmts_between_safe_nth with (n := 0%nat);
          [exact Hhi_safe| |exact Hnth_i]. lia.
      - intros y Hreads.
        eapply stmts_between_operand_safe_nth with (n := 0%nat);
          [exact Ha_safe| |exact Hnth_i|exact Hreads]. lia.
      - intros y Hreads.
        eapply stmts_between_operand_safe_nth with (n := 0%nat);
          [exact Hb_safe| |exact Hnth_i|exact Hreads]. lia. }
    split; [exact Hlo_a|]. split; [exact Hlo_b|]. exact Hhi_lo.
  Qed.

  (** Helper: matches_position_disjoint_b implies match_disjoint. *)
  Lemma matches_position_disjoint_b_implies :
    forall m1 m2,
      matches_position_disjoint_b m1 m2 = true ->
      match_disjoint m1 m2.
  Proof.
    intros [[[[[i1 j1] hi1] lo1] a1] b1] [[[[[i2 j2] hi2] lo2] a2] b2] H.
    unfold matches_position_disjoint_b in H.
    apply Bool.andb_true_iff in H as [H Hjj].
    apply Bool.andb_true_iff in H as [H Hji].
    apply Bool.andb_true_iff in H as [Hii Hij].
    apply Bool.negb_true_iff, Nat.eqb_neq in Hii, Hij, Hji, Hjj.
    unfold match_disjoint. auto.
  Qed.

  (** Helper: expr_reads_all_safe bool implies the Prop form. *)
  Lemma expr_reads_all_safe_implies :
    forall hi1 lo1 a1 b1 op,
      expr_reads_all_safe hi1 lo1 a1 b1 op = true ->
      forall y, expr_reads y op = true ->
      y <> hi1 /\ y <> lo1 /\ expr_reads y a1 = false /\ expr_reads y b1 = false.
  Proof.
    intros hi1 lo1 a1 b1 op.
    induction op; intros H y Hry; simpl in H, Hry.
    - (* JEvar x *)
      apply String.eqb_eq in Hry. subst y.
      apply andb_prop in H as [H Hb].
      apply andb_prop in H as [H Ha].
      apply andb_prop in H as [Hhi Hlo].
      apply negb_true_iff in Hhi, Hlo, Ha, Hb.
      apply String.eqb_neq in Hhi, Hlo.
      repeat split; auto.
    - (* JElit *) discriminate.
    - (* JEadd *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEsub *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEmul *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEmulhuu *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEand *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEor *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JExor *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEshr *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEshl *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEltu *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEeq *)
      apply andb_prop in H as [Hu Hv]. apply orb_prop in Hry as [Hry|Hry];
        [apply IHop1 | apply IHop2]; auto.
    - (* JEload *) apply IHop; auto.
  Qed.

  (** Helper: pair_names_disjoint_b implies match_names_disjoint. *)
  Lemma pair_names_disjoint_b_implies :
    forall m1 m2,
      pair_names_disjoint_b m1 m2 = true ->
      match_names_disjoint m1 m2.
  Proof.
    intros [[[[[i1 j1] hi1] lo1] a1] b1] [[[[[i2 j2] hi2] lo2] a2] b2] H.
    unfold pair_names_disjoint_b in H.
    apply Bool.andb_true_iff in H as [H Hsb].
    apply Bool.andb_true_iff in H as [H Hsa].
    apply Bool.andb_true_iff in H as [H Hhi_b].
    apply Bool.andb_true_iff in H as [H Hhi_a].
    apply Bool.andb_true_iff in H as [Hhihi Hhilo].
    apply Bool.negb_true_iff in Hhihi, Hhilo, Hhi_a, Hhi_b.
    apply String.eqb_neq in Hhihi, Hhilo.
    unfold match_names_disjoint.
    split; [exact Hhihi|].
    split; [exact Hhilo|].
    split; [exact Hhi_a|].
    split; [exact Hhi_b|].
    split.
    - intros y Hry. apply (expr_reads_all_safe_implies _ _ _ _ _ Hsa); auto.
    - intros y Hry. apply (expr_reads_all_safe_implies _ _ _ _ _ Hsb); auto.
  Qed.

  (** Bridge: pairwise boolean disjoint implies matches_strong_disjoint. *)
  Lemma all_pair_disjoint_implies_strong :
    forall ms,
      all_pairwise_disjoint_b ms = true ->
      all_pair_names_disjoint_b ms = true ->
      matches_strong_disjoint ms.
  Proof.
    intros ms Hp Hn. unfold matches_strong_disjoint.
    intros m1 m2 Hin1 Hin2 Hneq.
    revert m1 m2 Hin1 Hin2 Hneq.
    induction ms as [|m ms IH]; intros m1 m2 Hin1 Hin2 Hneq;
      [inversion Hin1|].
    simpl in Hp. apply Bool.andb_true_iff in Hp as [Hpm Hprest].
    simpl in Hn. apply Bool.andb_true_iff in Hn as [Hn Hnrest].
    apply Bool.andb_true_iff in Hn as [Hnm Hnm'].
    destruct Hin1 as [Heq1|Hin1]; destruct Hin2 as [Heq2|Hin2].
    - subst. contradiction.
    - subst m1.
      rewrite forallb_forall in Hpm. specialize (Hpm m2 Hin2).
      rewrite forallb_forall in Hnm. specialize (Hnm m2 Hin2).
      split.
      + apply matches_position_disjoint_b_implies; exact Hpm.
      + apply pair_names_disjoint_b_implies; exact Hnm.
    - subst m2.
      rewrite forallb_forall in Hpm. specialize (Hpm m1 Hin1).
      rewrite forallb_forall in Hnm'. specialize (Hnm' m1 Hin1).
      (* match_disjoint and match_names_disjoint are not symmetric; but
         matches_position_disjoint_b m1 m2 = matches_position_disjoint_b m2 m1
         up to swapping i1/j1 with i2/j2.  We need a symmetry lemma. *)
      split.
      + apply matches_position_disjoint_b_implies.
        destruct m1 as [[[[[i1 j1] hi1] lo1] a1] b1].
        destruct m as [[[[[im jm] him] lom] am] bm].
        unfold matches_position_disjoint_b in Hpm |- *.
        apply Bool.andb_true_iff in Hpm as [Hpm Hjj].
        apply Bool.andb_true_iff in Hpm as [Hpm Hji].
        apply Bool.andb_true_iff in Hpm as [Hii Hij].
        apply Bool.negb_true_iff, Nat.eqb_neq in Hii, Hij, Hji, Hjj.
        repeat (apply Bool.andb_true_iff; split);
          apply Bool.negb_true_iff, Nat.eqb_neq; auto.
      + apply pair_names_disjoint_b_implies; exact Hnm'.
    - apply IH; auto.
  Qed.

  (** Helper: matches_position_disjoint_b implies m1 <> m2. *)
  Lemma matches_position_disjoint_b_neq :
    forall m1 m2,
      matches_position_disjoint_b m1 m2 = true ->
      m1 <> m2.
  Proof.
    intros [[[[[i1 j1] hi1] lo1] a1] b1] [[[[[i2 j2] hi2] lo2] a2] b2] H.
    unfold matches_position_disjoint_b in H.
    apply Bool.andb_true_iff in H as [H _].
    apply Bool.andb_true_iff in H as [H _].
    apply Bool.andb_true_iff in H as [Hi _].
    apply Bool.negb_true_iff in Hi. apply Nat.eqb_neq in Hi.
    intros Heq. injection Heq. contradiction.
  Qed.

  (** Bridge: pairwise position-disjoint implies NoDup. *)
  Lemma all_pairwise_disjoint_b_nodup :
    forall ms,
      all_pairwise_disjoint_b ms = true ->
      NoDup ms.
  Proof.
    induction ms as [|m ms IH]; intros H.
    - constructor.
    - simpl in H. apply Bool.andb_true_iff in H as [Hm Hrest].
      constructor.
      + intros Hin.
        rewrite forallb_forall in Hm.
        specialize (Hm m Hin).
        apply matches_position_disjoint_b_neq in Hm. contradiction.
      + apply IH. exact Hrest.
  Qed.

  (** The scan invariant under the STRONG wf predicate, proved by the
      three bridge lemmas above. *)
  Theorem scan_mulx_pairs_valid_strong :
    forall cs,
      wf_mulx_list_strong_b cs = true ->
      scan_output_valid_b cs.
  Proof.
    intros cs Hwf. unfold wf_mulx_list_strong_b in Hwf.
    apply Bool.andb_true_iff in Hwf as [Hwf Hnames].
    apply Bool.andb_true_iff in Hwf as [Hforall Hpos].
    split; [|split].
    - rewrite Forall_forall. intros m Hin.
      apply match_fully_valid_b_implies_valid.
      rewrite forallb_forall in Hforall. apply Hforall. exact Hin.
    - apply all_pair_disjoint_implies_strong; assumption.
    - apply all_pairwise_disjoint_b_nodup; exact Hpos.
  Qed.

  (** Note: the weak form
        [forall cs, wf_mulx_list cs = true -> scan_output_valid_b cs]
      is NOT a theorem of this development and is not provable as
      stated.  The scan's operand-matching uses [equiv_cp] under a
      running [def_map], which gives operand equality only for
      environments consistent with the def-map — not universally,
      as the [forall ev, eval_jexpr ev a = eval_jexpr ev a''] clause
      of [valid_match_at] demands.  Closing it would require
      refactoring [valid_match_at] to take a def-map parameter and
      threading [defmap_consistent] through the rewrite proofs.

      The canonical soundness API uses the Qed'd strong variant
      [scan_mulx_pairs_valid_strong] above: users extracting a
      concrete program [vm_compute] the decidable check
      [wf_mulx_list_strong_b cs] and compose with
      [lower_mulx_pairs_list_correct_via_scan_check] for end-to-end
      zero-conjecture soundness. *)

  (** Step 4 composition auxiliary: single-match form.
      Given valid_match_at cs m (which entails disjoint operand/target
      conditions), applying rewrite_mulx_aux 0 [m] preserves jeval_list. *)
  Lemma rewrite_mulx_aux_sound_single :
    forall m cs e e',
      valid_match_at cs m ->
      jeval_list e cs e' ->
      jeval_list e (rewrite_mulx_aux 0 [m] cs) e'.
  Proof.
    intros [[[[[mi mj] hi] lo] a] b] cs e e' Hval Hev.
    pose proof Hval as Hval0.
    destruct Hval as [_ [_ [_ [Hla [Hlb Hne]]]]].
    eapply rewrite_mulx_one_match_sound; [|exact Hne|exact Hla|exact Hlb|exact Hev].
    apply (rewrite_mulx_aux_single_is_rewrite cs (mi,mj,hi,lo,a,b) Hval0).
  Qed.

  (** Preservation of valid_match_at under strong-disjoint rewrite.
      If m and m' are position-and-name disjoint and both valid, then
      m' remains valid after applying m via rewrite_mulx_aux.
      Uses the unchanged-positions property of rewrite_mulx_aux outside
      of m's range, plus the name-disjoint conditions to show the
      potentially-modified positions in m's range still satisfy the
      touches/reads conditions from m''s middle-safety. *)
  (** [rewrite_mulx_aux_nth_unchanged_at]: for positions that don't match
      m's mul_idx or mulhuu_idx, the rewritten list has the same
      element at that position. *)
  Lemma rewrite_mulx_aux_nth_unchanged_at :
    forall mi mj hi lo a b cs i,
      i <> mi -> i <> mj ->
      nth_error (rewrite_mulx_aux 0 [(mi,mj,hi,lo,a,b)] cs) i
      = nth_error cs i.
  Proof.
    intros mi mj hi lo a b cs i Hi Hj.
    revert cs i Hi Hj.
    (* Generalize the offset n and correlate n+position_in_rewrite with
       the absolute index. *)
    assert (Hgen : forall n cs k,
      (n + k)%nat <> mi ->
      (n + k)%nat <> mj ->
      nth_error (rewrite_mulx_aux n [(mi,mj,hi,lo,a,b)] cs) k
      = nth_error cs k).
    { intros n cs k. revert n k. induction cs as [|c cs IH]; intros n k Hki Hkj.
      - destruct k; reflexivity.
      - rewrite rewrite_mulx_aux_step. destruct k as [|k']; simpl.
        + cbn [find_mul_match is_mulhuu_idx].
          rewrite Bool.orb_false_r.
          assert (Hni : Nat.eqb n mi = false)
            by (apply Nat.eqb_neq; rewrite Nat.add_0_r in Hki; exact Hki).
          assert (Hnj : Nat.eqb n mj = false)
            by (apply Nat.eqb_neq; rewrite Nat.add_0_r in Hkj; exact Hkj).
          rewrite Hni, Hnj. reflexivity.
        + apply IH;
            [replace (S n + k')%nat with (n + S k')%nat by lia; exact Hki
            |replace (S n + k')%nat with (n + S k')%nat by lia; exact Hkj]. }
    intros cs i Hi Hj. apply (Hgen 0%nat cs i); rewrite Nat.add_0_l; assumption.
  Qed.

  (** cmd_touches is preserved through JCmulx insertion when variables
      are disjoint. *)
  Lemma cmd_touches_JCmulx_iff_names :
    forall x hi lo a b,
      x <> hi -> x <> lo ->
      expr_reads x a = false -> expr_reads x b = false ->
      cmd_touches x (JCmulx hi lo a b) = false.
  Proof.
    intros x hi lo a b Hxh Hxl Ha Hb. cbn.
    destruct (String.eqb x hi) eqn:E1; [apply String.eqb_eq in E1; contradiction|].
    destruct (String.eqb x lo) eqn:E2; [apply String.eqb_eq in E2; contradiction|].
    rewrite Ha, Hb. reflexivity.
  Qed.

  (** cmd_touches is always false on JCskip. *)
  Lemma cmd_touches_JCskip :
    forall x, cmd_touches x JCskip = false.
  Proof. reflexivity. Qed.

  (** Helper: when a single match's positions are disjoint from a target
      position, the rewrite produces [Some (JCmulx ...)] at mi. *)
  Lemma rewrite_mulx_aux_nth_at_mi :
    forall mi mj hi lo a b cs,
      (mi < mj)%nat ->
      nth_error cs mi = Some (JCset lo (JEmul a b)) ->
      nth_error (rewrite_mulx_aux 0%nat [(mi,mj,hi,lo,a,b)] cs) mi
      = Some (JCmulx hi lo a b).
  Proof.
    intros mi mj hi lo a b cs Hlt Hnth.
    assert (Hgen : forall n cs0 k,
              nth_error cs0 k = Some (JCset lo (JEmul a b)) ->
              (n + k)%nat = mi ->
              (mi < mj)%nat ->
              nth_error (rewrite_mulx_aux n [(mi,mj,hi,lo,a,b)] cs0) k
              = Some (JCmulx hi lo a b)).
    { clear. intros n cs0 k. revert n k.
      induction cs0 as [|c0 cs0 IH]; intros n k Hnth Hsum Hmm;
        [destruct k; discriminate|].
      rewrite rewrite_mulx_aux_step. destruct k as [|k']; simpl.
      - rewrite Nat.add_0_r in Hsum. subst n.
        cbn [find_mul_match is_mulhuu_idx].
        rewrite Nat.eqb_refl. reflexivity.
      - apply IH;
          [simpl in Hnth; exact Hnth
          |replace (S n + k')%nat with (n + S k')%nat by lia; exact Hsum
          |exact Hmm]. }
    apply (Hgen 0%nat cs mi Hnth); [lia | exact Hlt].
  Qed.

  (** Similarly for mj: position becomes JCskip. *)
  Lemma rewrite_mulx_aux_nth_at_mj :
    forall mi mj hi lo a b cs,
      (mi < mj)%nat ->
      nth_error (rewrite_mulx_aux 0%nat [(mi,mj,hi,lo,a,b)] cs) mj
      = match nth_error cs mj with Some _ => Some JCskip | None => None end.
  Proof.
    intros mi mj hi lo a b cs Hlt.
    assert (Hgen : forall n cs0 k,
              (n + k)%nat = mj ->
              (mi < mj)%nat ->
              nth_error (rewrite_mulx_aux n [(mi,mj,hi,lo,a,b)] cs0) k
              = match nth_error cs0 k with Some _ => Some JCskip | None => None end).
    { clear. intros n cs0 k. revert n k.
      induction cs0 as [|c0 cs0 IH]; intros n k Hsum Hmm.
      - destruct k; reflexivity.
      - rewrite rewrite_mulx_aux_step. destruct k as [|k']; simpl.
        + rewrite Nat.add_0_r in Hsum. subst n.
          cbn [find_mul_match is_mulhuu_idx].
          assert (Hneq : Nat.eqb mj mi = false)
            by (apply Nat.eqb_neq; lia).
          rewrite Hneq, Nat.eqb_refl. cbn [orb]. reflexivity.
        + apply IH;
            [replace (S n + k')%nat with (n + S k')%nat by lia; exact Hsum
            |exact Hmm]. }
    apply (Hgen 0%nat cs mj); [lia | exact Hlt].
  Qed.

  (** Full preservation: if m and m' are disjoint (position+name), then
      m' remains valid at the post-rewrite list. *)
  Lemma valid_match_at_preserved :
    forall cs m m',
      valid_match_at cs m ->
      valid_match_at cs m' ->
      match_disjoint m m' ->
      match_names_disjoint m m' ->
      valid_match_at (rewrite_mulx_aux 0%nat [m] cs) m'.
  Proof.
    intros cs [[[[[mi mj] hi] lo] a] b] [[[[[mi' mj'] hi'] lo'] a'] b']
           Hvm Hvm' Hposd Hnamed.
    destruct Hposd as [Hii' [Hij' [Hji' Hjj']]].
    destruct Hnamed as [Hhi'hi [Hhi'lo [Hhi'a [Hhi'b [HRa HRb]]]]].
    destruct Hvm as [Hij_m [[a2 [b2 [Hnth_m _]]] _]].
    destruct Hvm' as [Hij_lt' [[a'' [b'' [Hnth_m' [Hnth_mh' [Hae' Hbe']]]]]
                      [Hmid' [Hla' [Hlb' Hne']]]]].
    split; [exact Hij_lt'|].
    split.
    { exists a'', b''. split; [|split; [|split; [exact Hae' | exact Hbe']]].
      - rewrite rewrite_mulx_aux_nth_unchanged_at by auto.
        exact Hnth_m'.
      - rewrite rewrite_mulx_aux_nth_unchanged_at by auto.
        exact Hnth_mh'. }
    split.
    { intros c i HiRange Hnth_new.
      destruct (Nat.eq_dec i mi) as [Heq_mi | Hneq_mi].
      - (* i = mi: now JCmulx hi lo a b *)
        subst i.
        pose proof (rewrite_mulx_aux_nth_at_mi mi mj hi lo a b cs Hij_m Hnth_m) as Hmulx.
        (* Debug: see the state *)
        idtac.
        assert (Hceq : c = JCmulx hi lo a b).
        { assert (Some c = Some (JCmulx hi lo a b)).
          { rewrite <- Hnth_new. exact Hmulx. }
          congruence. }
        subst c.
        split; [|split].
        + (* cmd_touches hi' (JCmulx hi lo a b) = false *)
          cbn.
          destruct (String.eqb hi' hi) eqn:E1;
            [apply String.eqb_eq in E1; contradiction|].
          destruct (String.eqb hi' lo) eqn:E2;
            [apply String.eqb_eq in E2; contradiction|].
          rewrite Hhi'a, Hhi'b. reflexivity.
        + (* x reads a' -> x doesn't touch JCmulx hi lo a b *)
          intros x Hrx.
          specialize (HRa x Hrx) as [Hxhi [Hxlo [Hxa Hxb]]].
          cbn.
          destruct (String.eqb x hi) eqn:E1;
            [apply String.eqb_eq in E1; contradiction|].
          destruct (String.eqb x lo) eqn:E2;
            [apply String.eqb_eq in E2; contradiction|].
          rewrite Hxa, Hxb. reflexivity.
        + (* x reads b' -> similar *)
          intros x Hrx.
          specialize (HRb x Hrx) as [Hxhi [Hxlo [Hxa Hxb]]].
          cbn.
          destruct (String.eqb x hi) eqn:E1;
            [apply String.eqb_eq in E1; contradiction|].
          destruct (String.eqb x lo) eqn:E2;
            [apply String.eqb_eq in E2; contradiction|].
          rewrite Hxa, Hxb. reflexivity.
      - destruct (Nat.eq_dec i mj) as [Heq_mj | Hneq_mj].
        + (* i = mj: now JCskip *)
          subst i.
          pose proof (rewrite_mulx_aux_nth_at_mj mi mj hi lo a b cs Hij_m) as Hskip.
          destruct (nth_error cs mj) eqn:Hnth_mj.
          * assert (c = JCskip).
            { assert (Some c = Some JCskip) by (rewrite <- Hnth_new; exact Hskip).
              congruence. }
            subst c.
            split; [reflexivity | split; intros; reflexivity].
          * (* Hnth_new says ... = Some c but Hskip says ... = None *)
            assert (Some c = None) by (rewrite <- Hnth_new; exact Hskip).
            discriminate.
        + (* i ∉ {mi, mj}: position unchanged *)
          rewrite rewrite_mulx_aux_nth_unchanged_at in Hnth_new by auto.
          apply (Hmid' c i HiRange Hnth_new). }
    split; [exact Hla'|]. split; [exact Hlb'|]. exact Hne'.
  Qed.

  (** Strong-disjoint is preserved on the tail after removing head. *)
  Lemma matches_strong_disjoint_tail :
    forall m ms,
      matches_strong_disjoint (m :: ms) ->
      matches_strong_disjoint ms.
  Proof.
    intros m ms H. unfold matches_strong_disjoint in *.
    intros m1 m2 Hin1 Hin2 Hneq.
    apply H; [right; exact Hin1 | right; exact Hin2 | exact Hneq].
  Qed.

  (** Preservation: Forall valid_match_at after rewriting the head. *)
  Lemma Forall_valid_match_at_preserved :
    forall m ms cs,
      valid_match_at cs m ->
      Forall (valid_match_at cs) ms ->
      Forall (match_disjoint m) ms ->
      Forall (match_names_disjoint m) ms ->
      Forall (valid_match_at (rewrite_mulx_aux 0 [m] cs)) ms.
  Proof.
    intros m ms cs Hm_val Hval Hpos_d Hname_d.
    apply Forall_forall. intros m' Hin.
    rewrite Forall_forall in Hval, Hpos_d, Hname_d.
    apply valid_match_at_preserved; auto.
  Qed.

  (** The core iterative composition, Qed modulo [valid_match_at_preserved]. *)
  Lemma rewrite_mulx_aux_sound_iter :
    forall ms cs e e',
      Forall (valid_match_at cs) ms ->
      matches_strong_disjoint ms ->
      NoDup ms ->
      jeval_list e cs e' ->
      jeval_list e (rewrite_mulx_aux 0 ms cs) e'.
  Proof.
    induction ms as [|m ms IH]; intros cs e e' Hval Hdisj Hnodup Hev.
    - rewrite rewrite_mulx_aux_nil_id. exact Hev.
    - inversion Hnodup as [|m0 ms0 Hnin Hnodup_tl]; subst.
      assert (Hm_disj_pos : Forall (match_disjoint m) ms).
      { apply Forall_forall. intros m' Hin'.
        assert (m <> m') by (intros ->; contradiction).
        apply Hdisj; [left; reflexivity | right; exact Hin' | assumption]. }
      assert (Hm_names_d : Forall (match_names_disjoint m) ms).
      { apply Forall_forall. intros m' Hin'.
        assert (m <> m') by (intros ->; contradiction).
        apply Hdisj; [left; reflexivity | right; exact Hin' | assumption]. }
      rewrite rewrite_mulx_aux_cons by exact Hm_disj_pos.
      apply Forall_inv in Hval as Hm_val.
      pose proof (Forall_inv_tail Hval) as Hms_val.
      apply IH.
      + apply Forall_valid_match_at_preserved;
          [exact Hm_val|exact Hms_val|exact Hm_disj_pos|exact Hm_names_d].
      + apply matches_strong_disjoint_tail with (m := m); exact Hdisj.
      + exact Hnodup_tl.
      + apply rewrite_mulx_aux_sound_single; [exact Hm_val|exact Hev].
  Qed.

  (** Soundness of the pass given a post-hoc scan-output validity
      proof.  [scan_mulx_pairs_valid_strong] above provides the
      Qed'd path from the decidable [wf_mulx_list_strong_b] check
      to this hypothesis. *)
  Theorem lower_mulx_pairs_list_correct_via_scan_check :
    forall cs e e',
      scan_output_valid_b cs ->
      jeval_list e cs e' ->
      jeval_list e (lower_mulx_pairs cs) e'.
  Proof.
    intros cs e e' [Hval [Hdisj Hnodup]] Hev.
    unfold lower_mulx_pairs.
    apply rewrite_mulx_aux_sound_iter; assumption.
  Qed.

  (** The canonical list-level soundness theorem: under the decidable
      strong well-formedness check [wf_mulx_list_strong_b cs = true],
      the [lower_mulx_pairs] pass preserves [jeval_list].  Fully Qed,
      no conjectures. *)
  Theorem lower_mulx_pairs_list_correct_final :
    forall cs e e',
      wf_mulx_list_strong_b cs = true ->
      jeval_list e cs e' ->
      jeval_list e (lower_mulx_pairs cs) e'.
  Proof.
    intros cs e e' Hwf Hev.
    apply lower_mulx_pairs_list_correct_via_scan_check;
      [apply scan_mulx_pairs_valid_strong; exact Hwf | exact Hev].
  Qed.

  (** Soundness in the empty-scan case, proved via [mulx_rewrite_star_sound]. *)
  Theorem lower_mulx_pairs_list_correct_via_star_empty :
    forall cs e e',
      scan_mulx_pairs cs = nil ->
      jeval_list e cs e' ->
      jeval_list e (lower_mulx_pairs cs) e'.
  Proof.
    intros cs e e' Hscan Hev.
    eapply mulx_rewrite_star_sound.
    - apply lower_mulx_pairs_to_star_empty. exact Hscan.
    - exact Hev.
  Qed.

  (* =================================================================== *)
  (* End-to-end demo: a concrete program passing the strong check, with  *)
  (* zero-conjecture Qed'd soundness for the [lower_mulx_pairs] pass.    *)
  (* =================================================================== *)

  (** A minimal program exhibiting the MUL/MULHUU pair pattern with a
      non-MULX-related intervening statement: [x := a * b; y := c + d;
      z := MULHUU a b].  The pass should fuse [x]/[z] into a single
      [JCmulx z x a b] while the [y := c + d] statement remains. *)
  Definition demo_body : jasmin_cmd :=
    JCseq (JCset "x" (JEmul (JEvar "a") (JEvar "b")))
    (JCseq (JCset "y" (JEadd (JEvar "c") (JEvar "d")))
           (JCset "z" (JEmulhuu (JEvar "a") (JEvar "b")))).

  Definition demo_body_list : list jasmin_cmd := cmd_to_list demo_body.

  (** The decidable strong check passes on this concrete program. *)
  Lemma demo_strong_check : wf_mulx_list_strong_b demo_body_list = true.
  Proof. vm_compute. reflexivity. Qed.

  (** End-to-end conjecture-free soundness: the [lower_mulx_pairs]
      rewrite preserves [jeval_list] on [demo_body_list], proved without
      the generic scan-invariant conjecture. *)
  Theorem demo_lower_sound :
    forall e e',
      jeval_list e demo_body_list e' ->
      jeval_list e (lower_mulx_pairs demo_body_list) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply demo_strong_check.
  Qed.

End WithWordCmd.
