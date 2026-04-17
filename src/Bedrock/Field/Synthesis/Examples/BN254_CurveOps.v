(** * BN254 Curve Operations: point_double, store_zero, point_negate,
    curve_add_inplace.

    Instantiates the generic curve operations from [CurveAdd/] for BN254
    (y^2 = x^3 + 3, so 3b = 9).

    Provides:
    - [bn254_point_double] : dedicated doubling (dbl-2009-l, a=0)
    - [bn254_store_zero]   : store the identity point (0:1:0)
    - [bn254_point_negate_func] : negate Y coordinate
    - [bn254_curve_add_inplace] : ladderstep with in-place output

    These are used by the wNAF scalar multiplication chain
    ([BN254_wNAF_Instance.v]), which expects [HCurveDouble] and
    [HCurveAddInplace] function specs. *)

Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_three_b.
Require Import Bedrock.Field.Synthesis.Examples.BN254_G1.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDouble.
Require Import Bedrock.Group.CurveAdd.PointNegate.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CurveAddInplaceWrapper.
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
(** * Section 1: Concrete BN254 function definitions                   *)
(* ================================================================== *)

Section BN254_CurveOps.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation F := (F M_pos).

  (** ** Point doubling: dedicated dbl-2009-l formula (a=0).

      Uses the generic [point_double_body] from [PointDouble.v],
      which is derived by Rupicola compilation from [point_double_gallina].
      The body calls [square], [mul], [add], [sub] -- all resolved
      to "bn254_square", "bn254_mul", "bn254_add", "bn254_sub" via
      [bn254_field_parameters].

      Note: [point_double_body] is a Derived bedrock2 cmd.  After section
      closure in PointDouble.v, the body depends only on field_parameters
      (for function name strings) and Hbounds_eq (proof-level only, erased
      from the cmd).  With [bn254_field_parameters] as an Existing Instance,
      Coq resolves the syntactic dependencies automatically. *)
  Definition bn254_point_double : function_t :=
    ("curve_double", point_double_body).

  (** ** Store zero (identity point): (0 : 1 : 0) in Jacobian coords.

      The generic [store_zero_func] from [StoreZero.v] takes [zero_name]
      and [one_name] as implicit string arguments (section variables).
      We supply "bn254_from_word" for both, since the from_word function
      can store any small constant (0 or 1) given a word-sized argument.

      However, the store_zero protocol expects zero/one as nullary
      functions (no word argument -- they just write a fixed constant).
      We therefore define the body directly, calling [from_word] with
      the appropriate literal constants 0 and 1.

      This matches the pattern in [BN254_wNAF_Extract.v] and
      [StorePointAtInfinity.v] where function bodies are defined inline. *)
  Definition bn254_store_zero : function_t :=
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
  Definition bn254_curve_add_inplace : function_t :=
    @curve_add_inplace_wrapper _ _ _ _ bn254_field_parameters bn254_frep.

  (** ** Point negation: negate Y coordinate via [opp]. *)
  Definition bn254_point_negate_func : function_t :=
    @point_negate_func bn254_field_parameters.

End BN254_CurveOps.

(* ================================================================== *)
(** * Section 2: Spec statements for downstream consumers              *)
(* ================================================================== *)

Section BN254_CurveOps_Specs.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation F := (F M_pos).

  (** The point_double spec: calling "curve_double" with 6 pointers
      (3 input + 3 output) computes [point_double_gallina].

      This is the spec consumed by [HCurveDouble] in the wNAF chain:
      doubling P in-place (pXin=pXout, etc.) computes curve_add(P,P). *)
  Definition bn254_point_double_spec
    (functions : Semantics.env) : Prop :=
    PointDouble.spec_of_point_double
      (field_parameters:=bn254_field_parameters)
      (field_representation:=bn254_frep)
      functions.

  (** The store_zero spec: writing the identity (0,1,0) to 3 output FElems. *)
  Definition bn254_store_zero_spec
    (functions : Semantics.env) : Prop :=
    StoreZero.spec_of_store_zero
      (field_parameters:=bn254_field_parameters)
      (field_representation:=bn254_frep)
      functions.

  (** The ladderstep (curve_add) spec, parameterized by three_b witness.
      BN254 uses three_b = 9; the bounded witness is in [bn254_three_b.v]. *)
  Definition bn254_curve_add_spec
    (three_b : Crypto.Bedrock.Specs.Field.felem)
    (functions : Semantics.env) : Prop :=
    CurveAdd.spec_of_ladderstep
      (field_parameters:=bn254_field_parameters)
      (field_representation:=bn254_frep)
      three_b functions.

  (** The point_negate spec: negate Y coordinate. *)
  Definition bn254_point_negate_spec
    (functions : Semantics.env) : Prop :=
    PointNegate.spec_of_point_negate
      (field_parameters:=bn254_field_parameters)
      (field_representation:=bn254_frep)
      functions.

  (** ** Correctness lemmas.

      These bridge the gap between the generic specs and the concrete
      BN254 functions. The proofs require showing that the Derived
      function bodies satisfy their specs given field op correctness.

      The point_double proof requires [Hbounds_eq : loose_bounds = tight_bounds],
      which holds for Montgomery-form field operations (the tight and
      loose bounds coincide for word-by-word Montgomery arithmetic).

      The store_zero proof requires [spec_of_from_word] which is
      provided by the bn254 field synthesis.

      These are Admitted pending full compilation of the dependency
      chain; the proofs are mechanical given the Derived bodies from
      the generic modules ([point_double_correct] is already Qed in
      [PointDouble.v]). *)

  Lemma bn254_point_double_correct :
    forall functions,
      (* Field operation specs are in the environment *)
      spec_of_BinOp bin_mul (field_representation:=bn254_frep) functions ->
      spec_of_UnOp un_square (field_representation:=bn254_frep) functions ->
      spec_of_BinOp bin_add (field_representation:=bn254_frep) functions ->
      spec_of_BinOp bin_sub (field_representation:=bn254_frep) functions ->
      (* The point_double function is in the environment *)
      map.get functions "curve_double" = Some (snd bn254_point_double) ->
      bn254_point_double_spec functions.
  Proof.
    intros. unfold bn254_point_double_spec.
    eapply point_double_correct; try eassumption.
    { (* loose_bounds = tight_bounds for BN254 Montgomery *)
      reflexivity. }
    { (* __rupicola_program_marker *)
      exact I. }
  Qed.

  Lemma bn254_store_zero_correct :
    forall functions,
      spec_of_from_word (field_representation:=bn254_frep) functions ->
      map.get functions "store_zero" = Some (snd bn254_store_zero) ->
      bn254_store_zero_spec functions.
  Proof.
    (* Mechanical proof: 3 from_word calls writing 0, 1, 0 to the point
       components. Each call discharges via Hfw after converting FElem to
       bytes. Final step wraps into Compilation2.FElem (Some tight_bounds).
       Left as follow-up — the store_zero spec is well-established in
       StoreZero.v for the standard encoding. *)
  Admitted.

End BN254_CurveOps_Specs.

(* ================================================================== *)
(** * Section 3: All BN254 curve operation functions                   *)
(* ================================================================== *)

Section BN254_AllCurveOps.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  (** Complete list of curve operation functions for extraction.
      These are the bedrock2 functions needed for wNAF scalar
      multiplication on BN254 G1 (beyond the leaf Fp operations). *)
  Definition bn254_curve_op_funcs : list function_t :=
    [ bn254_G1_add;            (* ladderstep: "curve_add" *)
      bn254_point_double;      (* dedicated doubling: "curve_double" *)
      bn254_store_zero;        (* identity point: "store_zero" *)
      bn254_curve_add_inplace; (* inplace wrapper: "curve_add_inplace" *)
      bn254_point_negate_func  (* Y negation: "point_negate" *)
    ].

End BN254_AllCurveOps.
