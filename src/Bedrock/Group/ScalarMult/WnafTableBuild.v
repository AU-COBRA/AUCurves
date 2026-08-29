(** * The wNAF precomputed table of odd multiples, built and verified.

    The verified single-scalar wNAF chain
    ([wNAF_Single_HornerAlgebra.horner_step_single], and through it
    [BN254_wNAF_Instance.wnaf_single_full]) takes the precomputed table
    as a HYPOTHESIS:

      length table_entries = 4
      forall i, (i < 4)%nat -> nth i table_entries id = sm (2*i+1) P

    with [sm := BLS12_GLV_LoopInvariant.scmul Fzero Fone curve_add] and
    [id := (Fzero, Fone, Fzero)].  In the P-256 instantiation
    ([P256_wNAF_Instance.p256_table_ok]) that hypothesis is carried all
    the way into the end-to-end statement, because the table is
    caller-supplied memory (docs/nist_scalar_mult_plan.md, gap G7).

    The Leibniz form of that hypothesis is not satisfiable by any
    builder over the RCB addition: [rcb_add_general_gallina] returns a
    projective representative, not a canonical triple
    (BLS12_wNAF_PointOppInverse.v).  With
    [Bedrock.Group.CurveAdd.RcbProjectiveLaws] available the hypothesis
    can be restated up to [pt_eq], and in that form it is DISCHARGED
    here by an explicit builder.

    Contents:
      §1  Parameter-free Gallina builder [build_odd_table] over an
          abstract binary operation, with its [length] and [nth] laws.
      §2  Correctness over an abstract setoid-group interface whose
          hypotheses are, verbatim, the shapes proved in
          RcbProjectiveLaws (§4 of that file).
      §3  Instantiation at [cadd] / [pt_eq] / [oncurve], i.e. at the
          derived general-a RCB addition.
      §4  What this does and does not discharge.

    Honesty ledger: no [Admitted] and no [Axiom] in this file, and none
    inherited: RcbProjectiveLaws is now [Admitted]-free
    ([not_exceptional_of_no_two_torsion] is Qed).  The totality of
    [Projective.add] still enters here — as there — only through the
    [Hexcept] hypothesis of §3, which a caller may discharge from
    [RcbProjectiveLaws.not_exceptional_of_no_two_torsion]. *)

From Stdlib Require Import ZArith Znumtheory Lia List.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.

(* ==================================================================== *)
(** ** 1. The builder                                                    *)
(* ==================================================================== *)

(** [addn add i T Q] is [T + i*Q], computed by [i] additions of [Q]. *)
Fixpoint addn {A : Type} (add : A -> A -> A) (i : nat) (T Q : A) : A :=
  match i with
  | O => T
  | S m => addn add m (add T Q) Q
  end.

(** [build_aux add n T Q] = [T; T+Q; T+2Q; ...; T+(n-1)Q]. *)
Fixpoint build_aux {A : Type} (add : A -> A -> A) (n : nat) (T Q : A)
  : list A :=
  match n with
  | O => @nil A
  | S m => T :: build_aux add m (add T Q) Q
  end.

(** The table of the first [n] odd multiples of [P]: start at [P] and
    step by [Q := P + P].  No identity element, no negation, no field
    inversion: [n] additions in total (one for [Q], [n-1] for the
    steps). *)
Definition build_odd_table_gen {A : Type} (add : A -> A -> A) (n : nat)
  (P : A) : list A := build_aux add n P (add P P).

(** Window [w = 4] uses digits [d] with [|d| < 2^(w-1) = 8], so the
    signed-digit recoding needs the odd multiples [1P .. 15P]: eight
    entries.  See §4 for why the chain as written asks for only the
    first four. *)
Definition build_odd_table {A : Type} (add : A -> A -> A) (P : A)
  : list A := build_odd_table_gen add 8%nat P.

Lemma addn_O : forall {A : Type} (add : A -> A -> A) (T Q : A),
  addn add 0%nat T Q = T.
Proof. intros. reflexivity. Qed.

Lemma addn_S : forall {A : Type} (add : A -> A -> A) (j : nat) (T Q : A),
  addn add (S j) T Q = addn add j (add T Q) Q.
Proof. intros. reflexivity. Qed.

Lemma build_aux_length : forall {A : Type} (add : A -> A -> A) (n : nat)
    (T Q : A), length (build_aux add n T Q) = n.
Proof.
  intros A add n. induction n as [|m IH]; intros T Q; cbn [build_aux length].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma build_odd_table_gen_length :
  forall {A : Type} (add : A -> A -> A) (n : nat) (P : A),
    length (build_odd_table_gen add n P) = n.
Proof. intros. unfold build_odd_table_gen. apply build_aux_length. Qed.

Lemma build_odd_table_length :
  forall {A : Type} (add : A -> A -> A) (P : A),
    length (build_odd_table add P) = 8%nat.
Proof. intros. unfold build_odd_table. apply build_odd_table_gen_length. Qed.

Lemma build_aux_nth : forall {A : Type} (add : A -> A -> A) (n i : nat)
    (T Q d : A),
    (i < n)%nat -> nth i (build_aux add n T Q) d = addn add i T Q.
Proof.
  intros A add n. induction n as [|m IH]; intros i T Q d Hi.
  - exfalso. lia.
  - destruct i as [|j]; cbn [build_aux nth addn].
    + reflexivity.
    + apply IH. lia.
Qed.

(* ==================================================================== *)
(** ** 2. Correctness over the abstract setoid group                     *)
(* ==================================================================== *)

(** The hypotheses below are, one for one, the statements proved in
    [RcbProjectiveLaws] §1/§3/§4: [pt_eq_refl], [pt_eq_sym],
    [pt_eq_trans], [oncurve_id], [oncurve_cadd], [cadd_Proper],
    [cadd_comm], [cadd_assoc], [cadd_id_r], [cadd_id_l].  Nothing is
    reproved here; §3 supplies them. *)

Section AbstractOddTable.

  (** The carrier is named [A], not [F]: [Crypto.Spec.ModularArithmetic]
      exports [Notation F := F.F], which a section variable named [F]
      would shadow. *)
  Context {A : Type}.
  Context (Fzero Fone : A).

  Local Notation Pt := (A * A * A)%type.
  Local Notation ID := (Fzero, Fone, Fzero).

  Context (add : Pt -> Pt -> Pt).
  Context (eqp : Pt -> Pt -> Prop).
  Context (onc : Pt -> Prop).

  Context (eqp_refl : forall p, eqp p p).
  Context (eqp_sym : forall p q, eqp p q -> eqp q p).
  Context (eqp_trans : forall p q r, eqp p q -> eqp q r -> eqp p r).

  Context (onc_id : onc ID).
  Context (onc_add : forall p q, onc p -> onc q -> onc (add p q)).

  Context (add_Proper : forall p p' q q',
              eqp p p' -> eqp q q' ->
              onc p -> onc p' -> onc q -> onc q' ->
              eqp (add p q) (add p' q')).
  Context (add_comm : forall p q, onc p -> onc q -> eqp (add p q) (add q p)).
  Context (add_assoc : forall p q r, onc p -> onc q -> onc r ->
              eqp (add p (add q r)) (add (add p q) r)).
  Context (add_id_r : forall p, onc p -> eqp (add p ID) p).
  Context (add_id_l : forall p, onc p -> eqp (add ID p) p).

  (** The chain's scalar multiple, verbatim. *)
  Local Notation scm := (BLS12_GLV_LoopInvariant.scmul Fzero Fone add).

  Lemma scm_O : forall P, scm 0%nat P = ID.
  Proof. intros. reflexivity. Qed.

  Lemma scm_S : forall n P, scm (S n) P = add P (scm n P).
  Proof. intros. reflexivity. Qed.

  (** *** 2a. One-sided congruences (evar-free to apply). *)

  Lemma add_Proper_l : forall p p' q,
    eqp p p' -> onc p -> onc p' -> onc q -> eqp (add p q) (add p' q).
  Proof.
    intros p p' q E Hp Hp' Hq.
    apply add_Proper; first [ exact E | apply eqp_refl | assumption ].
  Qed.

  Lemma add_Proper_r : forall p q q',
    eqp q q' -> onc p -> onc q -> onc q' -> eqp (add p q) (add p q').
  Proof.
    intros p q q' E Hp Hq Hq'.
    apply add_Proper; first [ exact E | apply eqp_refl | assumption ].
  Qed.

  (** *** 2b. [scm] is on-curve-preserving, congruent, and additive. *)

  Lemma onc_scm : forall n P, onc P -> onc (scm n P).
  Proof.
    intros n. induction n as [|m IH]; intros P HP.
    - rewrite scm_O. exact onc_id.
    - rewrite scm_S. apply onc_add; [ exact HP | apply IH; exact HP ].
  Qed.

  Lemma scm_Proper : forall n P P',
    onc P -> onc P' -> eqp P P' -> eqp (scm n P) (scm n P').
  Proof.
    intros n. induction n as [|m IH]; intros P P' HP HP' E.
    - rewrite scm_O, scm_O. apply eqp_refl.
    - rewrite scm_S, scm_S.
      apply add_Proper.
      + exact E.
      + apply IH; assumption.
      + exact HP.
      + exact HP'.
      + apply onc_scm; exact HP.
      + apply onc_scm; exact HP'.
  Qed.

  Lemma scm_add_eq : forall m n P, onc P ->
    eqp (scm (m + n)%nat P) (add (scm m P) (scm n P)).
  Proof.
    intros m. induction m as [|m' IH]; intros n P HP.
    - rewrite scm_O. change (0 + n)%nat with n.
      apply eqp_sym. apply add_id_l. apply onc_scm; exact HP.
    - replace (S m' + n)%nat with (S (m' + n))%nat by lia.
      rewrite scm_S, scm_S.
      apply (eqp_trans _ (add P (add (scm m' P) (scm n P))) _).
      + apply add_Proper_r.
        * apply IH; exact HP.
        * exact HP.
        * apply onc_scm; exact HP.
        * apply onc_add; apply onc_scm; exact HP.
      + apply add_assoc;
          [ exact HP | apply onc_scm; exact HP | apply onc_scm; exact HP ].
  Qed.

  Lemma scm_1 : forall P, onc P -> eqp (scm 1%nat P) P.
  Proof.
    intros P HP. rewrite scm_S, scm_O. apply add_id_r. exact HP.
  Qed.

  Lemma scm_2 : forall P, onc P -> eqp (scm 2%nat P) (add P P).
  Proof.
    intros P HP. rewrite (scm_S 1%nat P).
    apply add_Proper_r.
    - apply scm_1; exact HP.
    - exact HP.
    - apply onc_scm; exact HP.
    - exact HP.
  Qed.

  (** Stepping by the doubled point advances the scalar by two. *)
  Lemma scm_double : forall i P, onc P ->
    eqp (scm i (add P P)) (scm (2 * i)%nat P).
  Proof.
    intros i. induction i as [|j IH]; intros P HP.
    - replace (2 * 0)%nat with 0%nat by lia.
      rewrite scm_O, scm_O. apply eqp_refl.
    - replace (2 * S j)%nat with (2 + 2 * j)%nat by lia.
      rewrite (scm_S j (add P P)).
      apply (eqp_trans _ (add (add P P) (scm (2 * j)%nat P)) _).
      + apply add_Proper_r.
        * apply IH; exact HP.
        * apply onc_add; exact HP.
        * apply onc_scm; apply onc_add; exact HP.
        * apply onc_scm; exact HP.
      + apply eqp_sym.
        apply (eqp_trans _ (add (scm 2%nat P) (scm (2 * j)%nat P)) _).
        * apply scm_add_eq; exact HP.
        * apply add_Proper_l.
          -- apply scm_2; exact HP.
          -- apply onc_scm; exact HP.
          -- apply onc_add; exact HP.
          -- apply onc_scm; exact HP.
  Qed.

  (** *** 2c. The builder's entries. *)

  Lemma onc_addn : forall i T Q, onc T -> onc Q -> onc (addn add i T Q).
  Proof.
    intros i. induction i as [|j IH]; intros T Q HT HQ.
    - rewrite addn_O. exact HT.
    - rewrite addn_S. apply IH; [ apply onc_add; assumption | assumption ].
  Qed.

  Lemma addn_spec : forall i T Q, onc T -> onc Q ->
    eqp (addn add i T Q) (add (scm i Q) T).
  Proof.
    intros i. induction i as [|j IH]; intros T Q HT HQ.
    - rewrite addn_O, scm_O. apply eqp_sym. apply add_id_l. exact HT.
    - rewrite addn_S, scm_S.
      assert (HTQ : onc (add T Q)) by (apply onc_add; assumption).
      assert (HA : onc (scm j Q)) by (apply onc_scm; exact HQ).
      apply (eqp_trans _ (add (scm j Q) (add T Q)) _).
      + apply IH; assumption.
      + apply (eqp_trans _ (add (add T Q) (scm j Q)) _).
        * apply add_comm; assumption.
        * apply (eqp_trans _ (add T (add Q (scm j Q))) _).
          -- apply eqp_sym. apply add_assoc; assumption.
          -- apply add_comm; [ exact HT | apply onc_add; assumption ].
  Qed.

  Lemma build_aux_Forall : forall n T Q, onc T -> onc Q ->
    Forall onc (build_aux add n T Q).
  Proof.
    intros n. induction n as [|m IH]; intros T Q HT HQ;
      cbn [build_aux].
    - constructor.
    - constructor;
        [ exact HT | apply IH; [ apply onc_add; assumption | assumption ] ].
  Qed.

  (** *** 2d. The two deliverables. *)

  Theorem build_odd_table_gen_oncurve : forall n P, onc P ->
    Forall onc (build_odd_table_gen add n P).
  Proof.
    intros n P HP. unfold build_odd_table_gen.
    apply build_aux_Forall; [ exact HP | apply onc_add; exact HP ].
  Qed.

  Theorem build_odd_table_gen_correct : forall n P i d,
    onc P -> (i < n)%nat ->
    onc (nth i (build_odd_table_gen add n P) d)
    /\ eqp (nth i (build_odd_table_gen add n P) d)
           (scm (2 * i + 1)%nat P).
  Proof.
    intros n P i d HP Hi.
    unfold build_odd_table_gen.
    rewrite (build_aux_nth add n i P (add P P) d Hi).
    assert (HQ : onc (add P P)) by (apply onc_add; exact HP).
    split; [ apply onc_addn; assumption | ].
    apply (eqp_trans _ (add (scm i (add P P)) P) _).
    - apply addn_spec; assumption.
    - apply (eqp_trans _ (add (scm (2 * i)%nat P) P) _).
      + apply add_Proper_l.
        * apply scm_double; exact HP.
        * apply onc_scm; exact HQ.
        * apply onc_scm; exact HP.
        * exact HP.
      + apply eqp_sym.
        apply (eqp_trans _ (add (scm (2 * i)%nat P) (scm 1%nat P)) _).
        * apply scm_add_eq; exact HP.
        * apply add_Proper_r.
          -- apply scm_1; exact HP.
          -- apply onc_scm; exact HP.
          -- apply onc_scm; exact HP.
          -- exact HP.
  Qed.

  Theorem build_odd_table_oncurve : forall P, onc P ->
    Forall onc (build_odd_table add P).
  Proof.
    intros P HP. unfold build_odd_table.
    apply build_odd_table_gen_oncurve; exact HP.
  Qed.

  Theorem build_odd_table_correct : forall P i d,
    onc P -> (i < 8)%nat ->
    onc (nth i (build_odd_table add P) d)
    /\ eqp (nth i (build_odd_table add P) d) (scm (2 * i + 1)%nat P).
  Proof.
    intros P i d HP Hi. unfold build_odd_table.
    apply build_odd_table_gen_correct; assumption.
  Qed.

End AbstractOddTable.

(* ==================================================================== *)
(** ** 3. Instantiation at the derived general-a RCB addition            *)
(* ==================================================================== *)

(** The context is that of [RcbProjectiveLaws], verbatim: the same field
    parameters, the same characteristic bound, the same curve constants
    and discriminant side condition, and the same [Hexcept] totality
    hypothesis for [Projective.add]. *)

Section RcbOddTable.

  Local Open Scope F_scope.

  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.

  Local Notation F := (F M_pos).

  (** No local [prime] instance is declared here: RcbProjectiveLaws
      exports [prime_M_pos], and a second, opaque proof of the same
      Prop would make [F.field_modulo]'s instance argument differ from
      the one baked into that file's theorems — [Znumtheory.prime] is
      an ordinary Prop, so the two would not be convertible.  The ring
      below needs no primality. *)
  Add Ring Fp_ring_tbl : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Context (M_gt_27 : (27 < M_pos)%positive).

  Context (a b three_b : F).
  Context (Hthree_b : three_b = (b + b + b)%F).
  Context (Hdisc : id
    ((((1 + 1 + 1 + 1) * a * a * a
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)%F)).

  Local Notation Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul a b).

  Local Notation Pnot_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div a b _ (char_ge_3 M_gt_27) _).

  Context (Hexcept : forall P Q : Ppoint, Pnot_exceptional P Q).

  (** The addition the chain runs: [cadd] of RcbProjectiveLaws, which is
      [rcb_add_general_gallina] on plain triples and is
      [NistWnafWrappers.curve_add_general_triple a three_b]. *)
  Local Notation Add := (cadd a three_b).
  Local Notation Onc := (oncurve a b).
  Local Notation Scm :=
    (BLS12_GLV_LoopInvariant.scmul (@F.zero M_pos) (@F.one M_pos)
       (cadd a three_b)).

  Definition rcb_build_odd_table (P : F * F * F) : list (F * F * F) :=
    build_odd_table Add P.

  Definition rcb_build_table4 (P : F * F * F) : list (F * F * F) :=
    build_odd_table_gen Add 4%nat P.

  (* ---------------------------------------------------------------- *)
  (** *** 3a. The ten abstract hypotheses, as named closed lemmas       *)
  (* ---------------------------------------------------------------- *)

  (** Each is one theorem of RcbProjectiveLaws §1/§3/§4, restated in the
      exact shape §2 expects.  They are separate [Qed]s on purpose: if
      a Section variable of RcbProjectiveLaws discharged differently
      from what [eapply] can recover, the failure is reported HERE, at
      the single law that broke, instead of surfacing as a residual
      goal at the end of a composite proof. *)

  (** [Hexcept], [Hdisc], [Hthree_b] and [M_gt_27] are the arguments the
      discharged RcbProjectiveLaws theorems take besides [a], [b] and
      [three_b]; [eassumption] supplies each from this Section's own
      context. *)
  Local Ltac rcb_ctx :=
    first [ eassumption
          | exact M_gt_27 | exact Hthree_b | exact Hdisc | exact Hexcept ].

  (** The curve constants [a], [b], [three_b] must sometimes be pinned
      by hand.  A RcbProjectiveLaws theorem is generalised over every
      Section variable its PROOF TERM mentions, not only those in its
      statement, and [fsatz] / [ring] emit [abstract]ed subproofs that
      are generalised over the whole ambient context.  So e.g.
      [oncurve_id], whose conclusion is [oncurve a b id_pt], still
      takes [three_b] — which [apply] cannot infer.  The alternation
      below tries the pinnings from most to least specific; a binding
      name absent from a given lemma makes that branch fail and the
      next one run.  The alternations are written out per lemma rather
      than factored into a tactic taking the lemma as an argument,
      because a [with (x := t)] binding name must be resolved against a
      concrete constant. *)

  Lemma rcb_eqp_refl : forall p : F * F * F, pt_eq p p.
  Proof. intros p. apply pt_eq_refl. Qed.

  Lemma rcb_eqp_sym : forall p q : F * F * F, pt_eq p q -> pt_eq q p.
  Proof. intros p q H. apply pt_eq_sym; exact H. Qed.

  Lemma rcb_eqp_trans : forall p q r : F * F * F,
    pt_eq p q -> pt_eq q r -> pt_eq p r.
  Proof. intros p q r H1 H2. eapply pt_eq_trans; eassumption. Qed.

  Lemma rcb_onc_id : Onc id_pt.
  Proof.
    first
      [ eapply oncurve_id with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply oncurve_id with (b := b) (three_b := three_b); rcb_ctx
      | eapply oncurve_id with (three_b := three_b); rcb_ctx
      | eapply oncurve_id with (b := b); rcb_ctx
      | eapply oncurve_id; rcb_ctx
      | (* Independent of the discharge shape: [oncurve] and [id_pt] are
           plain definitions, so unfold and compute.  This is the script
           of [RcbProjectiveLaws.oncurve_id] itself. *)
        cbv [oncurve id_pt]; split; [ ring | intros _; fsatz ] ].
  Qed.

  Lemma rcb_onc_add : forall p q, Onc p -> Onc q -> Onc (Add p q).
  Proof.
    intros p q Hp Hq.
    first
      [ eapply oncurve_cadd with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply oncurve_cadd with (b := b) (three_b := three_b); rcb_ctx
      | eapply oncurve_cadd with (three_b := three_b); rcb_ctx
      | eapply oncurve_cadd with (b := b); rcb_ctx
      | eapply oncurve_cadd; rcb_ctx ].
  Qed.

  Lemma rcb_add_Proper : forall p p' q q',
    pt_eq p p' -> pt_eq q q' -> Onc p -> Onc p' -> Onc q -> Onc q' ->
    pt_eq (Add p q) (Add p' q').
  Proof.
    intros p p' q q' E1 E2 Hp Hp' Hq Hq'.
    first
      [ eapply cadd_Proper with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_Proper with (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_Proper with (three_b := three_b); rcb_ctx
      | eapply cadd_Proper with (b := b); rcb_ctx
      | eapply cadd_Proper; rcb_ctx ].
  Qed.

  Lemma rcb_add_comm : forall p q, Onc p -> Onc q ->
    pt_eq (Add p q) (Add q p).
  Proof.
    intros p q Hp Hq.
    first
      [ eapply cadd_comm with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_comm with (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_comm with (three_b := three_b); rcb_ctx
      | eapply cadd_comm with (b := b); rcb_ctx
      | eapply cadd_comm; rcb_ctx ].
  Qed.

  Lemma rcb_add_assoc : forall p q r, Onc p -> Onc q -> Onc r ->
    pt_eq (Add p (Add q r)) (Add (Add p q) r).
  Proof.
    intros p q r Hp Hq Hr.
    first
      [ eapply cadd_assoc with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_assoc with (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_assoc with (three_b := three_b); rcb_ctx
      | eapply cadd_assoc with (b := b); rcb_ctx
      | eapply cadd_assoc; rcb_ctx ].
  Qed.

  Lemma rcb_add_id_r : forall p, Onc p -> pt_eq (Add p id_pt) p.
  Proof.
    intros p Hp.
    first
      [ eapply cadd_id_r with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_id_r with (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_id_r with (three_b := three_b); rcb_ctx
      | eapply cadd_id_r with (b := b); rcb_ctx
      | eapply cadd_id_r; rcb_ctx ].
  Qed.

  Lemma rcb_add_id_l : forall p, Onc p -> pt_eq (Add id_pt p) p.
  Proof.
    intros p Hp.
    first
      [ eapply cadd_id_l with (a := a) (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_id_l with (b := b) (three_b := three_b); rcb_ctx
      | eapply cadd_id_l with (three_b := three_b); rcb_ctx
      | eapply cadd_id_l with (b := b); rcb_ctx
      | eapply cadd_id_l; rcb_ctx ].
  Qed.

  (** Discharges one goal of §2's telescope by a CLOSED term: no evar
      is created, so nothing can be silently shelved and resurface at
      [Qed]. *)
  Local Ltac rcb_discharge :=
    first [ exact rcb_eqp_refl | exact rcb_eqp_sym | exact rcb_eqp_trans
          | exact rcb_onc_id | exact rcb_onc_add | exact rcb_add_Proper
          | exact rcb_add_comm | exact rcb_add_assoc
          | exact rcb_add_id_r | exact rcb_add_id_l
          | eassumption | lia ].

  (** Any goal that survives the discharge prints itself rather than
      waiting for [Qed] to report "incomplete proof".  [all: ...] runs
      on zero goals without error, so a fully closed proof passes
      through.  There is no [Unshelve] guard because the primary branch
      of each proof below is a closed [exact] term: it creates no evar
      that could be shelved. *)
  Local Ltac no_residual :=
    lazymatch goal with
    | |- ?G => fail 99 "TABLE-RESIDUAL" G
    end.

  (* ---------------------------------------------------------------- *)
  (** *** 3b. The instantiated statements                              *)
  (* ---------------------------------------------------------------- *)

  Lemma rcb_build_odd_table_length :
    forall P, length (rcb_build_odd_table P) = 8%nat.
  Proof.
    intros P. unfold rcb_build_odd_table. apply build_odd_table_length.
  Qed.

  Lemma rcb_build_table4_length :
    forall P, length (rcb_build_table4 P) = 4%nat.
  Proof.
    intros P. unfold rcb_build_table4. apply build_odd_table_gen_length.
  Qed.

  Theorem rcb_build_odd_table_oncurve :
    forall P, Onc P -> Forall Onc (rcb_build_odd_table P).
  Proof.
    intros P HP. unfold rcb_build_odd_table.
    first
      [ exact (build_odd_table_oncurve Add Onc rcb_onc_add P HP)
      | apply build_odd_table_oncurve with (add := Add) (onc := Onc)
      | apply build_odd_table_oncurve ].
    all: try rcb_discharge.
    all: no_residual.
  Qed.

  Theorem rcb_build_table4_oncurve :
    forall P, Onc P -> Forall Onc (rcb_build_table4 P).
  Proof.
    intros P HP. unfold rcb_build_table4.
    first
      [ exact (build_odd_table_gen_oncurve Add Onc rcb_onc_add 4%nat P HP)
      | apply build_odd_table_gen_oncurve with (add := Add) (onc := Onc)
      | apply build_odd_table_gen_oncurve ].
    all: try rcb_discharge.
    all: no_residual.
  Qed.

  (** The full window-4 table: [1P; 3P; 5P; ...; 15P]. *)
  Theorem rcb_build_odd_table_correct :
    forall (P : F * F * F) (i : nat),
      Onc P -> (i < 8)%nat ->
      Onc (nth i (rcb_build_odd_table P) id_pt)
      /\ pt_eq (nth i (rcb_build_odd_table P) id_pt)
               (Scm (2 * i + 1)%nat P).
  Proof.
    intros P i HP Hi. unfold rcb_build_odd_table.
    first
      [ exact (build_odd_table_correct
                 (@F.zero M_pos) (@F.one M_pos) Add pt_eq Onc
                 rcb_eqp_refl rcb_eqp_sym rcb_eqp_trans
                 rcb_onc_id rcb_onc_add rcb_add_Proper
                 rcb_add_comm rcb_add_assoc rcb_add_id_r rcb_add_id_l
                 P i id_pt HP Hi)
      | apply build_odd_table_correct
          with (Fzero := @F.zero M_pos) (Fone := @F.one M_pos)
               (add := Add) (eqp := pt_eq) (onc := Onc)
      | apply build_odd_table_correct ].
    all: try rcb_discharge.
    all: no_residual.
  Qed.

  (** The table the chain actually asks for: [1P; 3P; 5P; 7P], i.e. the
      shape of [P256_wNAF_Instance.p256_table_ok] restated with
      [pt_eq]. *)
  Theorem rcb_build_table4_correct :
    forall (P : F * F * F) (i : nat),
      Onc P -> (i < 4)%nat ->
      Onc (nth i (rcb_build_table4 P) id_pt)
      /\ pt_eq (nth i (rcb_build_table4 P) id_pt)
               (Scm (2 * i + 1)%nat P).
  Proof.
    intros P i HP Hi. unfold rcb_build_table4.
    first
      [ exact (build_odd_table_gen_correct
                 (@F.zero M_pos) (@F.one M_pos) Add pt_eq Onc
                 rcb_eqp_refl rcb_eqp_sym rcb_eqp_trans
                 rcb_onc_id rcb_onc_add rcb_add_Proper
                 rcb_add_comm rcb_add_assoc rcb_add_id_r rcb_add_id_l
                 4%nat P i id_pt HP Hi)
      | apply build_odd_table_gen_correct
          with (Fzero := @F.zero M_pos) (Fone := @F.one M_pos)
               (add := Add) (eqp := pt_eq) (onc := Onc)
      | apply build_odd_table_gen_correct ].
    all: try rcb_discharge.
    all: no_residual.
  Qed.

  (** The chain's table hypothesis, in the [pt_eq] form of
      RcbProjectiveLaws §5, is now a THEOREM about
      [rcb_build_table4]. *)
  Theorem rcb_table4_ok :
    forall (P : F * F * F), Onc P ->
      length (rcb_build_table4 P) = 4%nat
      /\ forall i, (i < 4)%nat ->
           Onc (nth i (rcb_build_table4 P) id_pt)
           /\ pt_eq (nth i (rcb_build_table4 P) id_pt)
                    (Scm (2 * i + 1)%nat P).
  Proof.
    intros P HP. split.
    - exact (rcb_build_table4_length P).
    - intros i Hi. exact (rcb_build_table4_correct P i HP Hi).
  Qed.

End RcbOddTable.

(* ==================================================================== *)
(** ** 4. What this discharges, and what remains                         *)
(* ==================================================================== *)

(** *** Discharged

    [wNAF_Single_HornerAlgebra.horner_step_single] (and
    [digit_point_is_sm_Z] beneath it) assumes

      Htable : length table_entries = 4%nat
            /\ forall i, (i < 4)%nat ->
                 nth i table_entries id = sm (2 * i + 1)%nat (Px,Py,Pz)

    with [sm = BLS12_GLV_LoopInvariant.scmul Fzero Fone curve_add] and
    [id = (Fzero, Fone, Fzero)].  At [curve_add := cadd a three_b] the
    Leibniz equality is false (BLS12_wNAF_PointOppInverse.v); the
    [pt_eq] restatement recorded in RcbProjectiveLaws §5,

      forall i, (i < 4)%nat ->
        oncurve (nth i table_entries id_pt)
        /\ pt_eq (nth i table_entries id_pt) (sm (2*i+1) P)

    together with [length table_entries = 4], is exactly
    [rcb_table4_ok] above, for [table_entries := rcb_build_table4 P].
    It is Qed, on the sole hypothesis [oncurve a b P].

    In [P256_wNAF_Instance.v] this is the [Htable]/[p256_table_ok]
    argument of [p256_Hhorner_step] and the [G7] table half of
    [p256_wnaf_single_full].  Feeding it there is a one-line
    substitution once those two statements are themselves quotiented by
    [pt_eq] (plan item G6); until then [p256_table_ok] is stated with
    Leibniz equality and cannot accept this theorem.

    [rcb_build_odd_table] is the same construction at the full window
    size.  The chain needs only four entries because its digits are
    bounded by [2^(w-1) - 1 = 7] ([p256_digits_bounded]), so the odd
    multiples that [digit_point] can select are [1,3,5,7]; a recoding
    that emitted digits up to 15 would use all eight.

    *** NOT discharged: the memory-level obligation

    This file is pure Gallina.  It says nothing about bedrock2, and in
    particular it does NOT claim:

    - that any bedrock2 function POPULATES the caller's table buffer
      with [rcb_build_table4 P].  Writing eight (or twenty-four) field
      elements into memory, establishing
      [Table4 pT (rcb_build_table4 P)] from an uninitialised buffer,
      and threading the separation-logic frame through the three
      [curve_add] calls the builder needs, is a separate weakest-
      precondition proof over a [precompute_w4] function that does not
      yet exist.
    - anything about [Table4]'s representation predicate, alignment, or
      the digit array.
    - that the P-256 caller (Rust or otherwise) supplies a table at
      all.

    Gap G7 therefore splits: its ALGEBRAIC half (the table contents are
    the right group elements) is closed here; its MEMORY half (some
    verified code puts those elements in the buffer) is open. *)
