(** * P-256 single-scalar wNAF scalar multiplication over the Rupicola
      general-a RCB addition.

    Instantiates the verified single-scalar wNAF chain
    ([BN254_wNAF_Instance.wnaf_single_full], Qed, Section-parametric)
    at the P-256 field representation [p256_frep] with the point
    addition [rcb_add_general_gallina] derived in CurveAddGeneralA.v and
    instantiated in CurveAddGeneralA_P256.v.

    Layout:
      §1  Gallina model: [p256_curve_add], [p256_scmul], constants.
      §2  bedrock2 function table: the derived add, its two constant
          loaders, the wrappers of NistWnafWrappers.v, felem_copy, and
          the wNAF driver [p256_wnaf_single_func] (257 digits, w = 4).
      §3  Arithmetic discharges at len = 257 (mirroring
          BLS12_wNAF_GLV_Instance.v at 129) and the digit-load lemma.
      §4  Callee-spec discharges from the function table.
      §5  [p256_wnaf_single_full]: the end-to-end statement.

    Status of the plan items (docs/nist_scalar_mult_plan.md):
      - G5  CLOSED.  The four generic files take an [opp_name]
            parameter, and this file passes "opp_inplace" — the name of
            [NistWnafWrappers.opp_inplace_func], the aliasing-tolerant
            wrapper.  (fiat-crypto's synthesized [p256_coord_opp] has
            no aliasing spec, so the wrapper name, not the
            [FieldParameters] field [opp], is the right value.)
            [NistWnafWrappers.opp_inplace_ok] is now Qed, so
            [p256_HOppInplace_spec] DISCHARGES both negation shapes
            from the function table; the final theorem no longer takes
            a negation hypothesis.
      - G6  DISCHARGED from RcbProjectiveLaws.v, not assumed.  The chain
            is now quotiented by [RcbProjectiveLaws.pt_eq] and carries
            [RcbProjectiveLaws.oncurve]; §1b below proves every group
            hypothesis the chain asks for.
            HONESTY: this trades the (false) Leibniz laws for five
            genuine side conditions on the curve, taken as hypotheses
            here: the curve constant [p256_b_val] with
            [three_b = 3b], the characteristic bound [27 < M],
            non-vanishing of the discriminant, and totality of
            [Projective.add] ([p256_Hexcept]).  The last is the one that
            is not a routine computation: it says the P-256 curve has no
            F-rational point of order two.  It corresponds to
            RcbProjectiveLaws' single Admitted
            ([not_exceptional_of_no_two_torsion]), which this file does
            NOT use — it takes the conclusion as a hypothesis instead.
      - G7  Digit array and table contents are caller-supplied.  The
            table hypothesis is now STRONGER than before: each entry
            must be on the curve as well as [pt_eq] to the odd multiple.

    Honesty ledger (this file): 0 Admitted.
    [p256_wnaf_single_full] is Qed, on the Section hypotheses listed
    under G6 above plus the caller's G7 data.  [p256_Hhorner_step] /
    [p256_Hhorner_oncurve] are proved from
    [wNAF_Single_HornerAlgebra]; the four function-body wrapper lemmas
    of NistWnafWrappers.v are Qed as of be20f7b.  What the theorem
    still RESTS ON, and what a reader should check:
      - the five curve-level hypotheses of §1b, of which
        [p256_Hexcept] (no F-rational 2-torsion) is the only
        non-routine one;
      - [p256_wnaf_table_ok] / [p256_wnaf_leaf_specs] — the caller's
        function table and fiat-crypto's synthesized field leaves;
      - G7: the caller's digit array and table buffers hold
        [wnaf_digits 4 k 257] and on-curve points [pt_eq] to
        [1P;3P;5P;7P].  [WnafTableBuild.rcb_table4_ok] (Qed) supplies
        the Gallina half of the table obligation; the memory-level
        half (that a bedrock2 function POPULATES the buffer) is not
        claimed by any file yet. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Field.Synthesis.Examples.p256_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Instance.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoadAndProcess.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_Proof.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_HornerAlgebra.
Require Import Bedrock.Field.Synthesis.Examples.BN254_wNAF_Instance.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.WNAFTable.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256_Loaders.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section P256_wNAF.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (* ============================================================== *)
  (* §1. Gallina model                                               *)
  (* ============================================================== *)

  Definition p256_a_val : F := feval (proj1_sig p256_a_felem).
  Definition p256_three_b_val : F := feval (proj1_sig p256_three_b_felem).

  (** The chain's [curve_add] at P-256: the derived RCB formula on
      plain triples.  [RcbProjectiveLaws.cadd] is the same forty-step
      chain as [NistWnafWrappers.curve_add_general_triple] (see
      [p256_curve_add_is_wrapper] below); it is used here so that the
      group laws of RcbProjectiveLaws.v apply without a transport. *)
  Definition p256_curve_add : F * F * F -> F * F * F -> F * F * F :=
    RcbProjectiveLaws.cadd p256_a_val p256_three_b_val.

  Lemma p256_curve_add_is_wrapper :
    p256_curve_add = curve_add_general_triple p256_a_val p256_three_b_val.
  Proof. reflexivity. Qed.

  Definition p256_point_opp : F * F * F -> F * F * F :=
    RcbProjectiveLaws.point_opp_triple.

  (* ============================================================== *)
  (* §1b. G6: the projective equivalence and the group laws          *)
  (* ============================================================== *)

  (** The side conditions of RcbProjectiveLaws.v, as hypotheses.

      [p256_b_val] is the curve constant b (the chain only ever sees
      [three_b]); [p256_M_gt_27] is the characteristic bound the
      [Ring.char_ge] instances need; [p256_Hdisc] is
      4a^3 + 27b^2 <> 0 in the expanded form Projective.v expects;
      [p256_Hexcept] is totality of [Projective.add], equivalently that
      the curve has no F-rational point of order two. *)
  Context (p256_b_val : F).
  Context (p256_M_gt_27 : (27 < M_pos)%positive).
  Context (p256_Hthree_b :
    p256_three_b_val = (p256_b_val + p256_b_val + p256_b_val)%F).
  Context (p256_Hdisc : id
    ((((1 + 1 + 1 + 1) * p256_a_val * p256_a_val * p256_a_val
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * p256_b_val * p256_b_val) <> 0)%F)).

  Local Instance p256_char_ge_3 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 3%positive :=
    RcbProjectiveLaws.char_ge_3 p256_M_gt_27.

  Local Notation P256_Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul p256_a_val p256_b_val).

  Local Notation P256_not_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div p256_a_val p256_b_val _ p256_char_ge_3 _).

  Context (p256_Hexcept : forall P Q : P256_Ppoint, P256_not_exceptional P Q).

  (** The chain's [pt_eq] and [oncurve] at P-256. *)
  Definition p256_pt_eq : F * F * F -> F * F * F -> Prop :=
    RcbProjectiveLaws.pt_eq.

  Definition p256_oncurve : F * F * F -> Prop :=
    RcbProjectiveLaws.oncurve p256_a_val p256_b_val.

  (** No local [prime] instance is declared here: RcbProjectiveLaws
      exports [prime_M_pos], and a second, opaque proof of the same
      Prop would make [F.field_modulo]'s instance argument differ from
      the one baked into that file's theorems — [Znumtheory.prime] is
      an ordinary Prop, so the two would not be convertible.  The ring
      below needs no primality; it exists only for the [ring] fallback
      of [p256_oncurve_id]. *)
  Add Ring Fp_ring_p256 : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Local Ltac rcb :=
    unfold p256_pt_eq, p256_oncurve, p256_curve_add, p256_point_opp in *.

  (** The curve constants [b] and [three_b] must be pinned by hand at
      every discharge below.  A RcbProjectiveLaws theorem is generalised
      over every Section variable its PROOF TERM mentions, not only
      those in its statement, and [ring] / [fsatz] emit [abstract]ed
      subproof constants that Coq generalises over the WHOLE ambient
      section context.  So e.g. [pt_eq_Equivalence], whose statement
      mentions neither [b] nor [three_b], still takes both — and
      [apply] / [eapply] cannot invent them ("Unable to find an
      instance for the variables b, three_b").

      The alternation tries the pinnings from most to least specific; a
      binding name absent from a given lemma makes that branch fail and
      the next one run.  The alternations are written out per lemma
      rather than factored into a tactic taking the lemma as an
      argument, because a [with (x := t)] binding name must be resolved
      against a concrete constant.  This is the §3a pattern of
      WnafTableBuild.v, which compiles against the same file. *)
  Local Ltac rcb_ctx :=
    first [ eassumption
          | exact p256_M_gt_27 | exact p256_Hthree_b
          | exact p256_Hdisc   | exact p256_Hexcept ].

  Lemma p256_pt_eq_refl : forall p, p256_pt_eq p p.
  Proof.
    intros p. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_refl
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl; rcb_ctx ].
  Qed.

  Lemma p256_pt_eq_sym : forall p q, p256_pt_eq p q -> p256_pt_eq q p.
  Proof.
    intros p q H. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_sym
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym; rcb_ctx ].
  Qed.

  Lemma p256_pt_eq_trans : forall p q r,
    p256_pt_eq p q -> p256_pt_eq q r -> p256_pt_eq p r.
  Proof.
    intros p q r H1 H2. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_trans
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans; rcb_ctx ].
  Qed.

  Lemma p256_pt_eq_equiv : Equivalence p256_pt_eq.
  Proof.
    constructor;
      [ exact p256_pt_eq_refl | exact p256_pt_eq_sym | exact p256_pt_eq_trans ].
  Qed.

  Lemma p256_oncurve_id : p256_oncurve (Fzero,Fone,Fzero).
  Proof.
    rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_id
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id; rcb_ctx
      | (* Independent of the discharge shape: [oncurve] and [id_pt] are
           plain definitions, so unfold and compute.  This is the script
           of [RcbProjectiveLaws.oncurve_id] itself. *)
        cbv [RcbProjectiveLaws.oncurve RcbProjectiveLaws.id_pt];
        split; [ ring | intros _; fsatz ] ].
  Qed.

  Lemma p256_oncurve_curve_add : forall P Q,
    p256_oncurve P -> p256_oncurve Q -> p256_oncurve (p256_curve_add P Q).
  Proof.
    intros P Q HP HQ. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_cadd
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd; rcb_ctx ].
  Qed.

  Lemma p256_oncurve_point_opp : forall P,
    p256_oncurve P -> p256_oncurve (p256_point_opp P).
  Proof.
    intros P HP. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_opp
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp; rcb_ctx ].
  Qed.

  Lemma p256_curve_add_Proper : forall P P' Q Q',
    p256_oncurve P -> p256_oncurve P' -> p256_oncurve Q -> p256_oncurve Q' ->
    p256_pt_eq P P' -> p256_pt_eq Q Q' ->
    p256_pt_eq (p256_curve_add P Q) (p256_curve_add P' Q').
  Proof.
    intros P P' Q Q' Hp Hp' Hq Hq' E1 E2. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_Proper
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper; rcb_ctx ].
  Qed.

  Lemma p256_point_opp_Proper : forall P P',
    p256_oncurve P -> p256_oncurve P' -> p256_pt_eq P P' ->
    p256_pt_eq (p256_point_opp P) (p256_point_opp P').
  Proof.
    intros P P' Hp Hp' E. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_Proper
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper; rcb_ctx ].
  Qed.

  Lemma p256_curve_add_id_r : forall x y z,
    p256_oncurve (x,y,z) ->
    p256_pt_eq (p256_curve_add (x,y,z) (Fzero,Fone,Fzero)) (x,y,z).
  Proof.
    intros x y z Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_r
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r; rcb_ctx ].
  Qed.

  Lemma p256_curve_add_id_l : forall x y z,
    p256_oncurve (x,y,z) ->
    p256_pt_eq (p256_curve_add (Fzero,Fone,Fzero) (x,y,z)) (x,y,z).
  Proof.
    intros x y z Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_l
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l; rcb_ctx ].
  Qed.

  Lemma p256_curve_add_assoc : forall P Q R,
    p256_oncurve P -> p256_oncurve Q -> p256_oncurve R ->
    p256_pt_eq (p256_curve_add P (p256_curve_add Q R))
               (p256_curve_add (p256_curve_add P Q) R).
  Proof.
    intros P Q R Hp Hq Hr. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_assoc
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc; rcb_ctx ].
  Qed.

  Lemma p256_curve_add_comm : forall P Q,
    p256_oncurve P -> p256_oncurve Q ->
    p256_pt_eq (p256_curve_add P Q) (p256_curve_add Q P).
  Proof.
    intros P Q Hp Hq. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_comm
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm; rcb_ctx ].
  Qed.

  Lemma p256_point_opp_inverse : forall P,
    p256_oncurve P ->
    p256_pt_eq (p256_curve_add P (p256_point_opp P)) (Fzero,Fone,Fzero).
  Proof.
    intros P Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_inverse
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse with (b := p256_b_val);
        rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse; rcb_ctx ].
  Qed.

  (** [scmul] of BLS12_GLV_LoopInvariant.v, the chain's [scmul_s].
      Qualified: WNAFTable.v (imported later) also exports a [scmul]
      whose [Fzero]/[Fone] are implicit, so the short name resolves to
      the wrong one. *)
  Definition p256_scmul : nat -> F * F * F -> F * F * F :=
    BLS12_GLV_LoopInvariant.scmul Fzero Fone p256_curve_add.

  (** wNAF parameters: 256-bit scalars, window 4, hence 257 digits
      (cf. 129 digits for 128-bit GLV halves in the BLS12 chain). *)
  Definition p256_num_digits : nat := 257%nat.

  Lemma p256_felem_size_in_bytes_eq : felem_size_in_bytes = 32.
  Proof. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Function table                                              *)
  (* ============================================================== *)

  Definition p256_curve_add_inplace_func : function_t :=
    curve_add_inplace_general_func.
  Definition p256_curve_double_func : function_t :=
    curve_double_general_func.
  Definition p256_opp_inplace_func : function_t :=
    opp_inplace_func.
  Definition p256_store_zero_func : function_t :=
    store_zero_from_word_func.

  (** The wNAF driver.  Same shape as [bn254_wnaf_single_func]
      (wNAF_GLV_Func.v) with 257 iterations; [felem_size_in_bytes]
      is kept symbolic so the body matches [wnaf_single_full]'s
      statement syntactically ([p256_felem_size_in_bytes_eq] gives 32
      for extraction). *)
  Definition p256_wnaf_single_func : function_t :=
    ("p256_wnaf_single",
     (["outx"; "outy"; "outz";
       "table_P"; "digits_k";
       "auxx"; "auxy"; "auxz"],
      []%list,
      wnaf_single_func_body "curve_add" "curve_double" "store_zero"
        felem_copy "opp_inplace" (Z.of_nat p256_num_digits)
        felem_size_in_bytes
        "digits_k" "table_P")).

  (** Function-table membership bundle used by the discharges below.
      The five field leaves (mul/add/sub/opp/from_word) are the
      fiat-crypto syntheses of p256_prime.v and enter through their
      [spec_of_*] instances rather than by body. *)
  Definition p256_wnaf_table_ok (functions : Semantics.env) : Prop :=
    map.get functions "curve_add_general" = Some p256_curve_add_general_func
    /\ map.get functions "p256_three_b" = Some p256_three_b_func
    /\ map.get functions "p256_a_const" = Some p256_a_const_func
    /\ map.get functions "curve_add" = Some (snd p256_curve_add_inplace_func)
    /\ map.get functions "curve_double" = Some (snd p256_curve_double_func)
    /\ map.get functions "store_zero" = Some (snd p256_store_zero_func)
    (* G5: the aliasing-tolerant negation wrapper the chain now calls *)
    /\ map.get functions "opp_inplace" = Some (snd p256_opp_inplace_func)
    /\ map.get functions felem_copy = Some p256_coord_felem_copy.

  Definition p256_wnaf_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_BinOp bin_mul functions
    /\ spec_of_BinOp bin_add functions
    /\ spec_of_BinOp bin_sub functions
    /\ spec_of_UnOp un_opp functions
    /\ spec_of_from_word functions.

  (* ============================================================== *)
  (* §3. Arithmetic discharges at len = 257                          *)
  (* ============================================================== *)

  Definition p256_digits (k : Z) : list Z := wnaf_digits 4 k p256_num_digits.

  Lemma p256_digits_length : forall k, length (p256_digits k) = p256_num_digits.
  Proof. intros. apply wnaf_digits_length. Qed.

  Lemma p256_digits_wsum : forall k,
    0 <= k < 2 ^ 256 -> wsum (p256_digits k) = k.
  Proof.
    intros k Hk. unfold p256_digits, p256_num_digits.
    apply wnaf_correct; [lia | lia |].
    replace (Z.of_nat (257 - 1)) with 256 by lia. exact Hk.
  Qed.

  Lemma p256_digits_Hws_nn : forall k,
    0 <= k < 2 ^ 256 ->
    forall n, (n <= p256_num_digits)%nat ->
    0 <= weighted_sum (skipn n (p256_digits k)) 0.
  Proof.
    intros k Hk n Hn. unfold p256_digits, p256_num_digits in *.
    apply (weighted_sum_skipn_wnaf_nonneg 4 k 257 n);
      [lia | split; [lia|]; replace (Z.of_nat (257 - 1)) with 256 by lia; lia
       | exact Hn].
  Qed.

  Lemma p256_digits_bounded : forall k,
    0 <= k ->
    forall i, (i < p256_num_digits)%nat -> -7 <= nth i (p256_digits k) 0 <= 7.
  Proof.
    intros k Hk i Hi. unfold p256_digits, p256_num_digits in *.
    assert (Hb : Z.abs (nth i (wnaf_digits 4 k 257) 0) < 2 ^ (Z.of_nat 4 - 1)).
    { apply (wnaf_digit_bound 4 k 257 i).
      - lia.
      - exact Hk.
      - apply nth_error_nth' with (d := 0). rewrite wnaf_digits_length. exact Hi. }
    change (Z.of_nat 4 - 1) with 3 in Hb. simpl (2^3) in Hb.
    apply Z.abs_lt in Hb. lia.
  Qed.

  (** Non-zero wNAF digits are odd (script of
      [BLS12_wNAF_GLV_Instance.wnaf_digits_odd] with 129 -> 257). *)
  Lemma p256_digits_odd : forall k,
    0 <= k ->
    forall i, (i < p256_num_digits)%nat ->
    Z.odd (nth i (p256_digits k) 0) = true \/ nth i (p256_digits k) 0 = 0.
  Proof.
    intros k Hk i Hi. unfold p256_digits, p256_num_digits in *.
    destruct (Z.eq_dec (nth i (wnaf_digits 4 k 257) 0) 0) as [Hz|Hnz].
    - right. exact Hz.
    - left.
      revert k Hk i Hi Hnz. induction (257)%nat as [|len IH]; intros k Hk i Hi Hnz.
      { exfalso. lia. }
      simpl wnaf_digits. destruct i as [|i'];
      [ simpl nth in Hnz |- *; unfold wnaf_digit in Hnz |- *;
        destruct (Z.odd k) eqn:Hok; [|exfalso; apply Hnz; reflexivity];
        set (m := k mod 2 ^ Z.of_nat 4) in *;
        assert (Hmodd : Z.odd m = true)
          by (subst m; pose proof (Z.div_mod k (2^Z.of_nat 4) ltac:(simpl;lia)) as Hkdm;
              assert (Z.odd (k mod 2^Z.of_nat 4) = Z.odd k)
                by (rewrite Hkdm at 2; rewrite Z.odd_add, Z.odd_mul; simpl; ring_simplify; reflexivity);
              congruence);
        destruct (m >=? 2 ^ (Z.of_nat 4 - 1));
        [ rewrite <- Z.negb_even, Z.even_sub; simpl (Z.even (2 ^ Z.of_nat 4));
          rewrite <- Z.negb_even in Hmodd; apply Bool.negb_true_iff in Hmodd;
          rewrite Hmodd; reflexivity
        | exact Hmodd ]
      | simpl nth in Hnz |- *;
        apply IH; [apply wnaf_shift_nonneg; lia | lia | exact Hnz] ].
  Qed.

  Lemma p256_Hnbound : Z.of_nat p256_num_digits < 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_Hfs_pos : 0 < felem_size_in_bytes.
  Proof. rewrite p256_felem_size_in_bytes_eq. lia. Qed.

  Lemma p256_Hfs_small : 12 * felem_size_in_bytes < 2 ^ 64.
  Proof. rewrite p256_felem_size_in_bytes_eq. vm_compute. reflexivity. Qed.

  (** Digit load: the generic lemma of BLS12_wNAF_GLV_Instance.v §2
      already has the required shape (its [DigitArray] is the one of
      BLS12_wNAF_ProcessDigits.v used by the chain). *)
  Lemma p256_Hdigit_load : forall (dk : list Z) (n : nat) (base : word)
      (m : BasicC64Semantics.mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word BasicC64Semantics.mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0)).
  Proof.
    intros. eapply digit_load_from_array; eassumption.
  Qed.

  (* ============================================================== *)
  (* §4. Callee-spec discharges from the table                       *)
  (* ============================================================== *)

  (** The derived add meets its FElem-level spec
      (CurveAddGeneralA_P256_Loaders.p256_curve_add_general_full). *)
  Lemma p256_rcb_add_general_spec :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions (Hadd & Htb & Ha & _ & _ & _ & _ & _) (Hmul & Hfadd & Hsub & _ & _).
    (* Explicit discharge, as in P384_wNAF_Instance.v: a fully applied term
       instead of [eapply ...; eassumption], whose cost is the conclusion
       unification rather than the assumption lookup. *)
    refine (p256_curve_add_general_full functions _ Htb Ha Hmul Hfadd Hsub).
    exact Hadd.
  Qed.

  Lemma p256_felem_copy_spec :
    forall functions,
      p256_wnaf_table_ok functions ->
      spec_of_felem_copy functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & _ & _ & Hcopy).
    (* [p256_felem_copy_ok : program_logic_goal_for_function! p256_coord_felem_copy]
       unfolds to [map.get functions felem_copy = Some p256_coord_felem_copy ->
       spec_of_felem_copy functions] (bedrock2 program_logic_goal_for). *)
    exact (p256_felem_copy_ok functions Hcopy).
  Qed.

  (** [curve_add_g] of NistWnafWrappers.v at the P-256 constants is
      [p256_curve_add] (both are [curve_add_general_triple] at
      [feval (proj1_sig p256_a_felem)] / [feval (proj1_sig p256_three_b_felem)]). *)
  Lemma p256_curve_add_g_eq :
    curve_add_g p256_three_b_felem p256_a_felem = p256_curve_add.
  Proof. reflexivity. Qed.

  Lemma p256_HCurveAddInplace :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_curve_add_inplace_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & Hca & _ & _ & _ & _).
    eapply curve_add_inplace_general_ok;
      eauto using p256_rcb_add_general_spec, p256_felem_copy_spec.
  Qed.

  Lemma p256_HCurveDouble :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_curve_double_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & Hcd & _ & _ & _).
    eapply curve_double_general_ok;
      eauto using p256_rcb_add_general_spec, p256_felem_copy_spec.
  Qed.

  Lemma p256_HStoreZero :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        p256_field_parameters p256_frep functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & Hsz & _ & _) (_ & _ & _ & _ & Hfw).
    (* After Section discharge [store_zero_from_word_ok] takes, before
       [functions]: 6 implicits (width, BW, word, mem, locals,
       ext_spec), the four ok-hypotheses (word.ok, map.ok mem,
       map.ok locals, ext_spec.ok), field_parameters +
       FieldParameters_ok, field_representation +
       FieldRepresentation_ok, the bounds equation, and the two
       constant felems of the Section (three_b, a_const — unused by
       this lemma's conclusion, so any well-typed felems serve).
       Hence the fully applied form below; [_] for the ten class
       arguments, which unification and the ambient Existing Instances
       resolve.  [p256_store_zero_func] is [store_zero_from_word_func]
       at these instances, so [Hsz] matches the table premise by
       conversion. *)
    first
      [ exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 p256_bounds_eq p256_three_b_felem p256_a_felem
                 functions Hsz Hfw)
      | eapply store_zero_from_word_ok with (functions := functions);
        [ solve [ typeclasses eauto | exact _ ] ..
        | exact p256_bounds_eq
        | exact p256_three_b_felem
        | exact p256_a_felem
        | exact Hsz
        | exact Hfw ]
      | eapply store_zero_from_word_ok with (functions := functions);
        repeat first
          [ exact p256_bounds_eq
          | exact p256_three_b_felem
          | exact p256_a_felem
          | exact Hsz
          | exact Hfw
          | solve [ typeclasses eauto | exact _ ] ] ].
  Qed.

  (** G5: both shapes of the negation the chain needs, at the wrapper
      name "opp_inplace".  [NistWnafWrappers.opp_inplace_ok] is Qed, so
      this is a discharge and not an assumption.  Same three-way
      alternation as [p256_HStoreZero]: the Section variables of
      NistWnafWrappers' [Specs] section become leading arguments
      ([Hbounds_eq] and the two constant felems among them), and the
      alternation avoids committing to how many. *)
  Lemma p256_HOppInplace_spec :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_opp_inplace functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & _ & _ & Hoi & _).
    pose proof Hleaf as (_ & _ & _ & Hopp & _).
    pose proof (p256_felem_copy_spec functions Htab) as Hcopy.
    first
      [ exact (@opp_inplace_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 p256_bounds_eq p256_three_b_felem p256_a_felem
                 functions Hoi Hopp Hcopy)
      | eapply opp_inplace_ok with (functions := functions);
        [ solve [ typeclasses eauto | exact _ ] ..
        | exact p256_bounds_eq
        | exact p256_three_b_felem
        | exact p256_a_felem
        | exact Hoi
        | exact Hopp
        | exact Hcopy ]
      | eapply opp_inplace_ok with (functions := functions);
        repeat first
          [ exact p256_bounds_eq
          | exact p256_three_b_felem
          | exact p256_a_felem
          | exact Hoi
          | exact Hopp
          | exact Hcopy
          | solve [ typeclasses eauto | exact _ ] ] ].
  Qed.

  (* ============================================================== *)
  (* §5. End-to-end statement                                        *)
  (* ============================================================== *)

  (** Table correctness, in the chain's quotiented form (plan G7).

      HONESTY: this is STRICTLY STRONGER than the Leibniz version it
      replaces on the [oncurve] conjunct, and strictly weaker on the
      equation ([pt_eq] instead of [=]).  Both changes are forced: the
      RCB table produced by any doubling/addition chain is only
      projectively equal to the odd multiples, and [oncurve] does not
      follow from [pt_eq] (e.g. [pt_eq (0,0,0) (0,1,0)] holds and
      (0,0,0) is not a projective point). *)
  Definition p256_table_ok (Px Py Pz : F) (table_entries : list (F * F * F)) : Prop :=
    length table_entries = 4%nat /\
    forall i, (i < 4)%nat ->
      p256_oncurve (nth i table_entries (Fzero,Fone,Fzero))
      /\ p256_pt_eq (nth i table_entries (Fzero,Fone,Fzero))
                    (p256_scmul (2 * i + 1) (Px, Py, Pz)).

  (** Horner step, from [wNAF_Single_HornerAlgebra.horner_step_single]
      (whose [sm] is definitionally [p256_scmul] and whose
      [digit_point_local] is definitionally ProcessDigits' [digit_point]
      at [point_opp := p256_point_opp]). *)
  Lemma p256_Hhorner_step :
    forall k, 0 <= k < 2 ^ 256 ->
    forall Px Py Pz table_entries,
      p256_oncurve (Px,Py,Pz) ->
      p256_table_ok Px Py Pz table_entries ->
      forall n (Ox Oy Oz : F),
        (n < p256_num_digits)%nat ->
        let ws_old := weighted_sum (skipn (S n) (p256_digits k)) 0 in
        p256_oncurve (Ox,Oy,Oz) ->
        p256_pt_eq (Ox,Oy,Oz) (p256_scmul (Z.to_nat (2 * ws_old)) (Px,Py,Pz)) ->
        let d := nth n (p256_digits k) 0 in
        p256_pt_eq
          (if d =? 0 then (Ox,Oy,Oz)
           else p256_curve_add (Ox,Oy,Oz) (digit_point d table_entries))
          (p256_scmul (Z.to_nat (weighted_sum (skipn n (p256_digits k)) 0)) (Px,Py,Pz)).
  Proof.
    intros k Hk Px Py Pz tab HPoc Htab n Ox Oy Oz Hn ws_old Hoc Hacc d.
    destruct Htab as (Hlen4 & Hcorr).
    assert (Hlen : length (p256_digits k) = p256_num_digits)
      by apply p256_digits_length.
    assert (Hn' : (n < length (p256_digits k))%nat)
      by (rewrite Hlen; exact Hn).
    assert (Hodd : forall i, (i < length (p256_digits k))%nat ->
              Z.odd (nth i (p256_digits k) 0) = true \/ nth i (p256_digits k) 0 = 0).
    { intros i Hi. apply p256_digits_odd; [lia | rewrite <- Hlen; exact Hi]. }
    assert (Hb : forall i, (i < length (p256_digits k))%nat ->
              -7 <= nth i (p256_digits k) 0 <= 7).
    { intros i Hi. apply p256_digits_bounded; [lia | rewrite <- Hlen; exact Hi]. }
    assert (Hws : forall j, (j <= length (p256_digits k))%nat ->
              0 <= weighted_sum (skipn j (p256_digits k)) 0).
    { intros j Hj. apply p256_digits_Hws_nn; [exact Hk | rewrite <- Hlen; exact Hj]. }
    (* [sm] of wNAF_Single_HornerAlgebra.v is [p256_scmul] and its
       [digit_point_local] is ProcessDigits' [digit_point] by
       conversion (same fixpoint / same [point_opp]), so the
       instantiated statement is the goal up to delta.  The argument
       order is the Section declaration order of [SingleHornerAlgebra]. *)
    pose proof (horner_step_single
                  Fzero Fone p256_curve_add p256_point_opp
                  p256_pt_eq p256_pt_eq_equiv p256_oncurve
                  p256_oncurve_id p256_oncurve_curve_add
                  p256_oncurve_point_opp
                  p256_curve_add_Proper p256_point_opp_Proper
                  p256_curve_add_id_r p256_curve_add_id_l
                  p256_curve_add_assoc p256_curve_add_comm
                  p256_point_opp_inverse
                  (p256_digits k) Px Py Pz tab
                  HPoc Hlen4 Hcorr Hodd Hb Hws
                  n Ox Oy Oz Hn' Hoc Hacc) as Hstep.
    first [ exact Hstep | apply Hstep ].
  Qed.

  (** On-curve closure of one Horner step: the [oncurve] half of the
      chain's [Hhorner_oncurve], from [digit_point_local_oncurve]. *)
  Lemma p256_Hhorner_oncurve :
    forall k, 0 <= k ->
    forall Px Py Pz table_entries,
      p256_table_ok Px Py Pz table_entries ->
      forall n (Ox Oy Oz : F),
        (n < p256_num_digits)%nat ->
        p256_oncurve (Ox,Oy,Oz) ->
        let d := nth n (p256_digits k) 0 in
        p256_oncurve
          (if d =? 0 then (Ox,Oy,Oz)
           else p256_curve_add (Ox,Oy,Oz) (digit_point d table_entries)).
  Proof.
    intros k Hk Px Py Pz tab Htab n Ox Oy Oz Hn Hoc d.
    destruct Htab as (Hlen4 & Hcorr).
    assert (Hdoc : p256_oncurve (digit_point d tab)).
    { assert (Hentries : forall i, (i < 4)%nat ->
                p256_oncurve (nth i tab (Fzero,Fone,Fzero)))
        by (intros i Hi; exact (proj1 (Hcorr i Hi))).
      pose proof (digit_point_oncurve_full
                    Fzero Fone p256_curve_add p256_point_opp
                    p256_pt_eq p256_pt_eq_equiv p256_oncurve
                    p256_oncurve_id p256_oncurve_curve_add
                    p256_oncurve_point_opp
                    p256_curve_add_Proper p256_point_opp_Proper
                    p256_curve_add_id_r p256_curve_add_id_l
                    p256_curve_add_assoc p256_curve_add_comm
                    p256_point_opp_inverse
                    tab d Hlen4 Hentries
                    (p256_digits_odd k Hk n Hn)
                    (p256_digits_bounded k Hk n Hn)) as Hdp.
      first [ exact Hdp | apply Hdp ]. }
    destruct (d =? 0); [exact Hoc | apply p256_oncurve_curve_add; assumption].
  Qed.

  (** The citable statement.  Under the function table, the field leaf
      specs, and G7's caller-supplied data, the body of
      [p256_wnaf_single_func] computes [k * P] in the chain's sense
      ([p256_scmul (Z.to_nat k) P]) UP TO PROJECTIVE EQUIVALENCE, and
      the result is on the curve.

      HONESTY: the conclusion is weaker than a Leibniz equation between
      triples — it is [p256_pt_eq], i.e. equality of the projective
      points the triples represent.  A consumer that needs a canonical
      representative must normalise (divide through by Z, mapping Z = 0
      to (0,1,0)); [pt_eq] is exactly the equivalence under which that
      normalisation is sound.  The G6 group laws are no longer assumed;
      the curve-level side conditions they rest on ([p256_b_val],
      [p256_M_gt_27], [p256_Hthree_b], [p256_Hdisc], [p256_Hexcept])
      are Section hypotheses of this file. *)
  Theorem p256_wnaf_single_full :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      (* G5 is no longer a hypothesis: both shapes of the negation come
         from [p256_HOppInplace_spec], i.e. from the function table's
         "opp_inplace" entry plus the field leaf specs. *)
      forall k, 0 <= k < 2 ^ 256 ->
      forall Px Py Pz table_entries,
        (* G7: the base point is on the curve *)
        p256_oncurve (Px,Py,Pz) ->
        (* G7: the caller's table holds on-curve points ~ [1P;3P;5P;7P] *)
        p256_table_ok Px Py Pz table_entries ->
      forall pOx pOy pOz pAx pAy pAz pT pDK
        (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
        (Rinner : BasicC64Semantics.mem -> Prop) tr m l,
      map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
      map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
      map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
      map.get l "table_P" = Some pT ->
      map.get l "digits_k" = Some pDK ->
      (* G7: the caller's digit array holds [wnaf_digits 4 k 257] *)
      (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
       ⋆ DigitArray pDK (p256_digits k) ⋆ Table4 pT table_entries
       ⋆ Rinner) m ->
      WeakestPrecondition.cmd functions
        (snd (snd p256_wnaf_single_func))
        tr m l
        (fun t m' l' =>
          exists Rx Ry Rz Ax' Ay' Az',
          p256_oncurve (Rx,Ry,Rz)
          /\ p256_pt_eq (Rx,Ry,Rz) (p256_scmul (Z.to_nat k) (Px,Py,Pz))
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
              ⋆ DigitArray pDK (p256_digits k) ⋆ Table4 pT table_entries
              ⋆ Rinner) m').
  Proof.
    intros functions Htab Hleaf k Hk Px Py Pz tab HPoc Htable.
    intros pOx pOy pOz pAx pAy pAz pT pDK
           Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Rinner tr m l
           Hlox Hloy Hloz Hlax Hlay Hlaz Hlt Hldk Hsep.
    assert (Hknn : 0 <= k) by lia.

    (* Every hypothesis [wnaf_single_full] asks for, as a named term in
       the context, so that the discharge below is [eassumption] and
       does not depend on the order in which Section discharge presents
       [wnaf_single_full]'s arguments. *)
    pose proof p256_bounds_eq as Hbe.
    (* G6: the group interface, proved in §1b from RcbProjectiveLaws.v *)
    pose proof p256_pt_eq_equiv as Heqv.
    pose proof p256_oncurve_id as Hoid.
    pose proof p256_oncurve_curve_add as Hoadd.
    pose proof p256_curve_add_Proper as HcaP.
    pose proof p256_curve_add_id_l as Hidl.
    pose proof p256_curve_add_assoc as Hass.
    (* callee specs, from the function table and the field leaves *)
    pose proof (p256_HCurveDouble functions Htab Hleaf) as HDbl.
    pose proof (p256_HCurveAddInplace functions Htab Hleaf) as HAdd.
    pose proof (felem_copy_HFelemCopy functions
                  (p256_felem_copy_spec functions Htab)) as HCopy.
    pose proof (p256_HOppInplace_spec functions Htab Hleaf) as HOI.
    cbv [spec_of_opp_inplace] in HOI.
    destruct HOI as [HOppNonAliased HOppAliased].
    pose proof (p256_HStoreZero functions Htab Hleaf) as HSZ.
    (* data *)
    pose proof (p256_digits_length k) as Hlen.
    pose proof p256_Hnbound as Hnb.
    pose proof (p256_digits_bounded k Hknn) as Hdb.
    pose proof p256_Hfs_pos as Hfp.
    pose proof p256_Hfs_small as Hfsm.
    pose proof (proj1 Htable) as Htl.
    pose proof (p256_Hdigit_load (p256_digits k)) as Hdl.
    pose proof (p256_digits_Hws_nn k Hk) as Hws.
    pose proof (p256_Hhorner_step k Hk Px Py Pz tab HPoc Htable) as Hhs.
    pose proof (p256_Hhorner_oncurve k Hknn Px Py Pz tab Htable) as Hho.
    pose proof (p256_digits_wsum k Hk) as Hwsum.

    (* The two callee specs are [Definition]s; unfold them so that
       [eassumption] meets the raw shape the chain declares. *)
    cbv [spec_of_curve_double_general spec_of_curve_add_inplace_general]
      in HDbl, HAdd.

    (* Expose the function body and the chain's [scmul]. *)
    cbv [p256_wnaf_single_func snd].
    unfold p256_scmul.

    first
      [ eapply wnaf_single_full
          with (curve_add_name := "curve_add")
               (curve_double_name := "curve_double")
               (opp_name := "opp_inplace")
               (curve_add := p256_curve_add)
               (pt_eq := p256_pt_eq)
               (oncurve := p256_oncurve)
               (dk := p256_digits k)
               (num_iters := p256_num_digits)
               (table_entries := tab)
               (Px := Px) (Py := Py) (Pz := Pz)
               (k := k)
      | eapply wnaf_single_full
          with (curve_add := p256_curve_add)
               (pt_eq := p256_pt_eq)
               (oncurve := p256_oncurve)
               (k := k)
      | eapply wnaf_single_full ].

    all: try eassumption.
    all: try ecancel_assumption.
    all: try lia.
    all: try (unfold p256_pt_eq, p256_oncurve, p256_curve_add,
                     p256_point_opp in *; eassumption).
    (* Anything left prints itself instead of surfacing as an opaque
       "incomplete proof" at [Qed]. *)
    all: lazymatch goal with
         | |- ?G => fail 99 "P256-FULL-RESIDUAL" G
         end.
  Qed.

End P256_wNAF.

(** * Adapter-lemma inventory

    NistWnafWrappers.v — proved
      felem_copy_HFelemCopy          spec_of_felem_copy (bytes dst) -> FElem-dst shape
      opp_HOpp                       spec_of_UnOp un_opp -> HOpp shape (loose->tight by Hbounds_eq)
      FElem2_elim_frame / _intro_frame   one-leaf transport across the FElem layers
    NistWnafWrappers.v — proved (all four wrapper bodies, be20f7b)
      curve_add_inplace_general_ok   spec_of_rcb_add_general + spec_of_felem_copy
                                      -> HCurveAddInplace shape at "curve_add"
      curve_double_general_ok        same inputs -> HCurveDouble shape at "curve_double"
      opp_inplace_ok                 spec_of_UnOp un_opp + spec_of_felem_copy
                                      -> both negation shapes at "opp_inplace"
      store_zero_from_word_ok        spec_of_from_word -> StoreZero.spec_of_store_zero
    This file
      §1b group laws                 PROVED from RcbProjectiveLaws.v, under the
                                      curve side conditions p256_b_val /
                                      p256_M_gt_27 / p256_Hthree_b / p256_Hdisc /
                                      p256_Hexcept (Section hypotheses)
      p256_HOppInplace_spec          PROVED from opp_inplace_ok (G5)
      p256_Hhorner_step              proved from horner_step_single (quotiented)
      p256_Hhorner_oncurve           proved from digit_point_oncurve_full
      p256_wnaf_single_full          PROVED: composition into wnaf_single_full *)
