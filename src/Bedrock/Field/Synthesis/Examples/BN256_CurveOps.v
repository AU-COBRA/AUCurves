(** * BN256 Curve Operations: point_double, store_zero, point_negate,
    curve_add_inplace.

    Instantiates the generic curve operations from [CurveAdd/] for BN256
    (y^2 = x^3 + 3, so 3b = 9).

    Provides:
    - [bn256_point_double] : dedicated doubling (RCB 2015 Algorithm 9,
      the HOMOGENEOUS a = 0 formula, from [PointDoubleA0.v]).  The
      earlier binding of [PointDouble.point_double_body] (dbl-2009-l)
      was removed: dbl-2009-l is JACOBIAN, and every other component of
      this chain -- [ladderstep_gallina], [store_zero],
      [RcbProjectiveLaws.oncurve] -- is homogeneous, so on the
      representatives this chain produces it returned 2P in neither
      reading.  See the header of [PointDouble.v].
    - [bn256_store_zero]   : store the identity point (0:1:0)
    - [bn256_point_negate_func] : negate Y coordinate
    - [bn256_curve_add_inplace] : ladderstep with in-place output

    These are used by the wNAF scalar multiplication chain
    ([BN256_wNAF_Instance.v]), which expects [HCurveDouble] and
    [HCurveAddInplace] function specs. *)

Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn256_three_b.
Require Import Bedrock.Field.Synthesis.Examples.BN256_G1.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.PointNegate.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CurveAddInplaceWrapper.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Rupicola.Lib.Api.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(* ================================================================== *)
(** * Section 1: Concrete BN256 function definitions                   *)
(* ================================================================== *)

Section BN256_CurveOps.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn256_field_parameters
    bn256_field_parameters_ok
    bn256_frep
    bn256_frep_ok.

  Local Notation F := (F M_pos).

  (** ** Point doubling: RCB 2015 Algorithm 9, homogeneous, a = 0.

      Uses the generic [rcb_double_a0_body] from [PointDoubleA0.v],
      derived by Rupicola compilation from [rcb_double_a0_gallina].
      The body calls [mul], [add], [sub] and the 3b loader -- exactly
      the callee list [ladderstep_body] uses, so BN256 needs no leaf it
      does not already have; the loader is "bn256_three_b", the same
      constant [bn256_G1_add] passes to [ladderstep_body].

      The function key is "curve_double_a0", not "curve_double":
      [rcb_double_a0_correct] demands
      [map.get functions "curve_double_a0" = Some (rcb_double_a0_body _)],
      and [spec_of_rcb_double_a0] is a [spec_of "curve_double_a0"].
      Consumers parameterised by a [curve_double_name] (the wNAF chain)
      instantiate it with that string.

      Note: [rcb_double_a0_body] is a Derived bedrock2 cmd.  After
      section closure in PointDoubleA0.v it depends on field_parameters
      (for the leaf name strings) and on the loader name; [three_b] and
      [Hbounds_eq] are proof-level and erased from the cmd. *)
  Definition bn256_point_double : function_t :=
    ("curve_double_a0", rcb_double_a0_body "bn256_three_b").

  (** ** Store zero (identity point): (0 : 1 : 0) in Jacobian coords.

      The generic [store_zero_func] from [StoreZero.v] takes [zero_name]
      and [one_name] as implicit string arguments (section variables).
      We supply "bn256_from_word" for both, since the from_word function
      can store any small constant (0 or 1) given a word-sized argument.

      However, the store_zero protocol expects zero/one as nullary
      functions (no word argument -- they just write a fixed constant).
      We therefore define the body directly, calling [from_word] with
      the appropriate literal constants 0 and 1.

      This matches the pattern in [BN256_wNAF_Extract.v] and
      [StorePointAtInfinity.v] where function bodies are defined inline. *)
  Definition bn256_store_zero : function_t :=
    ("store_zero",
     (["outx"; "outy"; "outz"],
      []:list String.string,
      bedrock_func_body:(
        coq:(cmd.call [] from_word [expr.var "outx"; expr.literal 0]);
        coq:(cmd.call [] from_word [expr.var "outy"; expr.literal 1]);
        coq:(cmd.call [] from_word [expr.var "outz"; expr.literal 0])
      ))).

  (** ** Curve add inplace wrapper: calls ladderstep with stack temps,
      then copies result back via felem_copy. Used by wNAF digit
      processing where output aliases input1. *)
  Definition bn256_curve_add_inplace : function_t :=
    @curve_add_inplace_wrapper _ _ _ _ bn256_field_parameters bn256_frep.

  (** ** Point negation: negate Y coordinate via [opp]. *)
  Definition bn256_point_negate_func : function_t :=
    @point_negate_func bn256_field_parameters.

End BN256_CurveOps.

(* ================================================================== *)
(** * Section 2: Spec statements for downstream consumers              *)
(* ================================================================== *)

Section BN256_CurveOps_Specs.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn256_field_parameters
    bn256_field_parameters_ok
    bn256_frep
    bn256_frep_ok.

  Local Notation F := (F M_pos).

  (** The point_double spec: calling "curve_double_a0" with 6 DISJOINT
      pointers (3 input + 3 output) computes [rcb_double_a0_gallina]
      at [three_b_val = feval three_b].

      This is NOT yet [BN256_wNAF_Instance.HCurveDouble].  That
      hypothesis calls with [pX;pY;pZ;pX;pY;pZ] -- input buffers
      aliased with the output buffers -- which this (and every
      Rupicola-derived) spec excludes by its separating conjunction,
      and it carries no on-curve side condition.  See
      [bn256_double_is_curve_add] below for what is available, and the
      note after it for what is missing. *)
  Definition bn256_point_double_spec
    (three_b : Crypto.Bedrock.Specs.Field.felem)
    (functions : Semantics.env) : Prop :=
    PointDoubleA0.spec_of_rcb_double_a0
      (field_parameters:=bn256_field_parameters)
      (field_representation:=bn256_frep)
      three_b functions.

  (** The store_zero spec: writing the identity (0,1,0) to 3 output FElems. *)
  Definition bn256_store_zero_spec
    (functions : Semantics.env) : Prop :=
    StoreZero.spec_of_store_zero
      (field_parameters:=bn256_field_parameters)
      (field_representation:=bn256_frep)
      functions.

  (** The ladderstep (curve_add) spec, parameterized by three_b witness.
      BN256 uses three_b = 9; the bounded witness is in [bn256_three_b.v]. *)
  Definition bn256_curve_add_spec
    (three_b : Crypto.Bedrock.Specs.Field.felem)
    (functions : Semantics.env) : Prop :=
    CurveAdd.spec_of_ladderstep
      (field_parameters:=bn256_field_parameters)
      (field_representation:=bn256_frep)
      three_b functions.

  (** The point_negate spec: negate Y coordinate. *)
  Definition bn256_point_negate_spec
    (functions : Semantics.env) : Prop :=
    PointNegate.spec_of_point_negate
      (field_parameters:=bn256_field_parameters)
      (field_representation:=bn256_frep)
      functions.

  (** ** Correctness lemmas.

      These bridge the gap between the generic specs and the concrete
      BN256 functions. The proofs require showing that the Derived
      function bodies satisfy their specs given field op correctness.

      The point_double proof requires [Hbounds_eq : loose_bounds = tight_bounds],
      which holds for Montgomery-form field operations (the tight and
      loose bounds coincide for word-by-word Montgomery arithmetic).

      The store_zero proof requires [spec_of_from_word] which is
      provided by the bn256 field synthesis.

      [bn256_point_double_correct] is Qed from
      [PointDoubleA0.rcb_double_a0_correct];
      [bn256_store_zero_correct] is Qed from
      [NistWnafWrappers.store_zero_from_word_ok]. *)

  Lemma bn256_point_double_correct :
    forall (three_b : Crypto.Bedrock.Specs.Field.felem) functions,
      (* The point_double function is in the environment *)
      map.get functions "curve_double_a0" = Some (snd bn256_point_double) ->
      (* Field operation specs are in the environment *)
      spec_of_BinOp bin_mul (field_representation:=bn256_frep) functions ->
      spec_of_BinOp bin_add (field_representation:=bn256_frep) functions ->
      spec_of_BinOp bin_sub (field_representation:=bn256_frep) functions ->
      (* The 3b loader is in the environment *)
      PointDoubleA0.spec_of_three_b_loader_a0
        (field_parameters:=bn256_field_parameters)
        (field_representation:=bn256_frep)
        three_b "bn256_three_b" functions ->
      bn256_point_double_spec three_b functions.
  Proof.
    intros three_b functions Henv Hmul Hadd Hsub Hloader.
    (* loose_bounds = tight_bounds for BN256 word-by-word Montgomery *)
    assert (Hbe : loose_bounds = tight_bounds) by reflexivity.
    exact (@rcb_double_a0_correct
             _ _ _ _ _ _ _ _ _ _
             bn256_field_parameters bn256_frep bn256_frep_ok
             Hbe three_b "bn256_three_b" I
             functions Henv Hmul Hadd Hsub Hloader).
  Qed.

  (** ** The doubling really doubles.

      [rcb_double_a0_correct] says the body computes
      [rcb_double_a0_gallina]; this says [rcb_double_a0_gallina] is the
      chain's own addition on a repeated argument, coordinate for
      coordinate (Leibniz, not up to projective equivalence), for every
      on-curve input.  BN256 is y^2 = x^3 + 3, so b = 3 and 3b = 9.

      The [feval three_b = 9] hypothesis is the same obligation
      [BN254_wNAF_Laws] lists as [bn254_Hthree_b] (that file is shared
      by all three a = 0 BN curves); the bounded witness lives in
      [bn256_three_b.v]. *)
  Lemma bn256_double_is_curve_add
    (three_b : Crypto.Bedrock.Specs.Field.felem)
    (Hthree_b : feval (proj1_sig three_b)
                = ModularArithmetic.F.of_Z M_pos 9) :
    forall P,
      PointDoubleA0.oncurve_a0 (ModularArithmetic.F.of_Z M_pos 3) P ->
      PointDoubleA0.rcb_double_a0_triple (feval (proj1_sig three_b)) P
      = PointDoubleA0.ladderstep_triple (feval (proj1_sig three_b)) P P.
  Proof.
    intros P HP.
    apply (PointDoubleA0.rcb_double_a0_eq_ladderstep
             (ModularArithmetic.F.of_Z M_pos 3)); [ | exact HP ].
    rewrite Hthree_b.
    rewrite <- !ModularArithmeticTheorems.F.of_Z_add. reflexivity.
  Qed.

  (** ** What is still missing before [HCurveDouble] follows.

      [BN256_wNAF_Instance.HCurveDouble] is

        forall pX pY pZ X Y Z R0 tr0 m0,
          (FElem pX X * FElem pY Y * FElem pZ Z * R0) m0 ->
          call functions curve_double_name tr0 m0 [pX;pY;pZ;pX;pY;pZ]
            (... curve_add (X,Y,Z) (X,Y,Z) ...)

      and two things separate it from the two lemmas above.

      (1) ALIASING.  The call passes the input pointers again as the
      output pointers.  [spec_of_rcb_double_a0] -- like every
      Rupicola-derived spec, and like [spec_of_ladderstep] -- puts the
      six buffers in a separating conjunction, so it says nothing about
      that call.  Algorithm 9 is not in-place safe either: D8 writes
      Xout and D9 writes Yout, while D16 still reads X1 and Y1.  The
      fix is the wrapper [CurveAddInplaceWrapper.v] already describes
      for the addition -- three [stackalloc]s, the disjoint call, three
      [felem_copy]s -- which for the addition is itself still only a
      proof blueprint, not a theorem.

      (2) ON-CURVE.  [HCurveDouble] asserts the equality for arbitrary
      (X,Y,Z).  [rcb_double_a0_eq_ladderstep] holds only on the curve,
      and that is not slack in the proof: the cofactors against the
      curve polynomial are 6*3b*Z for Y3 and 6*Y for Z3, so off the
      curve Algorithm 9 and the addition genuinely differ.  Deriving
      [HCurveDouble] needs the hypothesis in the wNAF chain weakened to
      carry [oncurve], as its point-level algebra already does. *)

  Lemma bn256_store_zero_correct :
    forall functions,
      spec_of_from_word (field_representation:=bn256_frep) functions ->
      map.get functions "store_zero" = Some (snd bn256_store_zero) ->
      bn256_store_zero_spec functions.
  Proof.
    intros functions Hfw Hsz.
    (* [bn256_store_zero] is [NistWnafWrappers.store_zero_from_word_func]
       at these instances (same three [from_word] calls with literals
       0, 1, 0, same parameter names), so [Hsz] meets the table premise
       of [store_zero_from_word_ok] by conversion.

       [StoreZero.store_zero_ok] is NOT the lemma to use here: it is
       [program_logic_goal_for store_zero_func True], proved by
       [exact I], and carries no information about the body.

       The 13 arguments before [functions] are the six bedrock2
       parameters, the four ok-classes, [field_parameters],
       [field_representation] and [FieldRepresentation_ok]; all are
       determined by unification against the conclusion.  Fully applied
       [exact] rather than [eapply] so the cost is one conversion. *)
    exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             functions Hsz Hfw).
  Qed.

End BN256_CurveOps_Specs.

(* ================================================================== *)
(** * Section 3: All BN256 curve operation functions                   *)
(* ================================================================== *)

Section BN256_AllCurveOps.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn256_field_parameters
    bn256_field_parameters_ok
    bn256_frep
    bn256_frep_ok.

  (** Complete list of curve operation functions for extraction.
      These are the bedrock2 functions needed for wNAF scalar
      multiplication on BN256 G1 (beyond the leaf Fp operations). *)
  Definition bn256_curve_op_funcs : list function_t :=
    [ bn256_G1_add;            (* ladderstep: "curve_add" *)
      bn256_point_double;      (* RCB Alg. 9 doubling: "curve_double_a0" *)
      bn256_store_zero;        (* identity point: "store_zero" *)
      bn256_curve_add_inplace; (* inplace wrapper: "curve_add_inplace" *)
      bn256_point_negate_func  (* Y negation: "point_negate" *)
    ].

End BN256_AllCurveOps.
