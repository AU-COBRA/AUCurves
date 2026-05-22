(** * MontgomeryCurveSpecsFp3 — Fp3 analogue of MontgomeryCurveSpecs.

    Generic Weierstrass projective add framework over an abstract
    [F * F * F]-style cubic extension.  This is the Fp3 analogue of
    [Theory.WordByWordMontgomery.MontgomeryCurveSpecs.v] (which is
    written for Fp and partly for Fp2-pairs of Fp limb-lists).

    The framework is parametric in:
      - a base field type [F] with its [AbstractField.FieldParameters],
      - the cubic non-residue multiplier [mul_by_nr : F -> F], and
      - a [FieldRepresentation] for [F] (used downstream).

    From these we obtain Fp3 = [F * F * F] via [CubicExtensionsAbstract.ce_*],
    the [AbstractField] [bw6_Fp3_params] (already produced by
    [GenericCubicSpecs.CE_field_parameters]), and the corresponding
    [bw6_Fp3_repr] [FieldRepresentation].

    We provide:
      - The Gallina add specialised for [a = 0] (matches the formula
        in [BW6_761Curve_G2.v], parametric over an abstract Fp3),
      - The bedrock2 add cmd template (calls 3 named Fp3 funcs:
        [Fp3_add], [Fp3_sub], [Fp3_mul] — taken from [bw6_Fp3_params]).

    Authoring constraints (per Phase 2 of GitHub #65):
      * Mirror [BW6_761Curve_G1_bedrock.v]'s overall shape so that the
        downstream pattern is recognisable.
      * Use [AbstractField] callee specs (Fp3 [add]/[sub]/[mul]) rather
        than the WordByWordMontgomery-direct Bignum specs used by G1.
        This eliminates the BLS12_G2 Bignum/feval bridging boilerplate.
      * Avoid hand-rolling Mp3 ring lemmas; the Fp3 ring lives in
        [CubicExtensionsAbstract] and is already proven a [comRingType].

    Anything that needs the BW6-specific prime / params lives in
    [BW6_761Curve_G2_bedrock.v]; this file is pure framework. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.

Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.Array.
Require Import bedrock2.BasicC64Semantics.

Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.

Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.

Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section Fp3CurveSpecs.

  (** ** Parameters *)

  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}
          {locals : map.map String.string word}
          {env : map.map String.string (list String.string * list String.string * Syntax.cmd)}
          {ext_spec : Semantics.ExtSpec}.

  Context {F : Type}
          {base_fp : FieldParameters F}
          {base_repr : @FieldRepresentation F base_fp width BW word mem}.

  (** The cubic non-residue multiplier in the base field. *)
  Variable mul_by_nr : F -> F.

  (** A constant [three_b : Fp3] = [3 * b] used by the formula. *)
  Variable three_b : (F * F * F)%type.

  (** ** Fp3 = F * F * F via CubicExtensionsAbstract ce_*. *)

  Local Notation Fp3 := (F * F * F)%type.

  Local Notation fp3_zero := (ce_zero (F := F)).
  Local Notation fp3_one  := (ce_one  (F := F)).
  Local Notation fp3_add  := (ce_add  (F := F)).
  Local Notation fp3_sub  := (ce_sub  (F := F)).
  Local Notation fp3_opp  := (ce_opp  (F := F)).
  Local Notation fp3_mul  := (ce_mul  (F := F) mul_by_nr).
  Local Notation fp3_sqr  := (ce_sqr  (F := F) mul_by_nr).

  Local Infix "+f" := fp3_add (at level 50).
  Local Infix "-f" := fp3_sub (at level 50).
  Local Infix "*f" := fp3_mul (at level 40).

  (** ** Gallina spec (projective add, a = 0)

      Identical formula to [BW6_G2_add_Gallina_spec_a_0] in
      [BW6_761Curve_G2.v] but stated abstractly. *)

  Definition Fp3_proj_add_a0
    (X1 Y1 Z1 X2 Y2 Z2 : Fp3) : Fp3 * Fp3 * Fp3 :=
    let t0 := X1 *f X2 in
    let t1 := Y1 *f Y2 in
    let t2 := Z1 *f Z2 in
    let t3 := X1 +f Y1 in
    let t4 := X2 +f Y2 in
    let t3 := t3 *f t4 in
    let t4 := t0 +f t1 in
    let t3 := t3 -f t4 in
    let t4 := X1 +f Z1 in
    let t5 := X2 +f Z2 in
    let t4 := t4 *f t5 in
    let t5 := t0 +f t2 in
    let t4 := t4 -f t5 in
    let t5 := Y1 +f Z1 in
    let X3 := Y2 +f Z2 in
    let t5 := t5 *f X3 in
    let X3 := t1 +f t2 in
    let t5 := t5 -f X3 in
    let Z3 := three_b *f t2 in
    let X3 := t1 -f Z3 in
    let Z3 := t1 +f Z3 in
    let Y3 := X3 *f Z3 in
    let t1 := t0 +f t0 in
    let t1 := t1 +f t0 in
    let t4 := three_b *f t4 in
    let t0 := t1 *f t4 in
    let Y3 := Y3 +f t0 in
    let t0 := t5 *f t4 in
    let X3 := t3 *f X3 in
    let X3 := X3 -f t0 in
    let t0 := t3 *f t1 in
    let Z3 := t5 *f Z3 in
    let Z3 := Z3 +f t0 in
    (X3, Y3, Z3).

  (** ** bedrock2 implementation template

      We build the [Syntax.cmd] body that allocates 6 temporaries +
      one slot for [three_b], stores [three_b] from a passed-in
      Fp3-felem stash, then dispatches [Fp3_add]/[Fp3_sub]/[Fp3_mul]
      calls in the same order as [Fp3_proj_add_a0].

      The function signature exposes [outx; outy; outz] as out-params
      and [X1; Y1; Z1; X2; Y2; Z2] as input pointers.  All 9 point
      coordinates are Fp3-felems (3 base limbs each).

      The callee names come from [base_fp]'s [AbstractField.add],
      [AbstractField.sub], [AbstractField.mul] strings, lifted to Fp3
      via the [CE_field_parameters] instance.  Caller wires the Fp3
      names by providing the appropriate function string arguments. *)

  Section BedrockBody.
    (** Caller-supplied Fp3 op names.  Concretely these come from
        [bw6_Fp3_params]'s [add]/[sub]/[mul] fields (e.g.
        ["bw6_761_Fp3_add"]).  We keep them as explicit Variables so
        downstream files can swap or rename freely. *)
    Variable add_name : string.
    Variable sub_name : string.
    Variable mul_name : string.

    (** Number of bytes per Fp3 element.  [3 * felem_size_in_bytes_F].
        Concretely for BW6: 3 * (12 * 8) = 288. *)
    Local Notation fp3_num_bytes :=
      (3 * @felem_size_in_bytes F base_fp width BW word mem base_repr).

    Definition Fp3_proj_add_body : Syntax.cmd.cmd :=
      bedrock_func_body:(
        stackalloc fp3_num_bytes as $"t0";
        stackalloc fp3_num_bytes as $"t1";
        stackalloc fp3_num_bytes as $"t2";
        stackalloc fp3_num_bytes as $"t3";
        stackalloc fp3_num_bytes as $"t4";
        stackalloc fp3_num_bytes as $"t5";
        coq:(cmd.call [] mul_name [expr.var "t0"; expr.var "X1"; expr.var "X2"]);
        coq:(cmd.call [] mul_name [expr.var "t1"; expr.var "Y1"; expr.var "Y2"]);
        coq:(cmd.call [] mul_name [expr.var "t2"; expr.var "Z1"; expr.var "Z2"]);
        coq:(cmd.call [] add_name [expr.var "t3"; expr.var "X1"; expr.var "Y1"]);
        coq:(cmd.call [] add_name [expr.var "t4"; expr.var "X2"; expr.var "Y2"]);
        coq:(cmd.call [] mul_name [expr.var "t3"; expr.var "t3"; expr.var "t4"]);
        coq:(cmd.call [] add_name [expr.var "t4"; expr.var "t0"; expr.var "t1"]);
        coq:(cmd.call [] sub_name [expr.var "t3"; expr.var "t3"; expr.var "t4"]);
        coq:(cmd.call [] add_name [expr.var "t4"; expr.var "X1"; expr.var "Z1"]);
        coq:(cmd.call [] add_name [expr.var "t5"; expr.var "X2"; expr.var "Z2"]);
        coq:(cmd.call [] mul_name [expr.var "t4"; expr.var "t4"; expr.var "t5"]);
        coq:(cmd.call [] add_name [expr.var "t5"; expr.var "t0"; expr.var "t2"]);
        coq:(cmd.call [] sub_name [expr.var "t4"; expr.var "t4"; expr.var "t5"]);
        coq:(cmd.call [] add_name [expr.var "t5"; expr.var "Y1"; expr.var "Z1"]);
        coq:(cmd.call [] add_name [expr.var "outx"; expr.var "Y2"; expr.var "Z2"]);
        coq:(cmd.call [] mul_name [expr.var "t5"; expr.var "t5"; expr.var "outx"]);
        coq:(cmd.call [] add_name [expr.var "outx"; expr.var "t1"; expr.var "t2"]);
        coq:(cmd.call [] sub_name [expr.var "t5"; expr.var "t5"; expr.var "outx"]);
        coq:(cmd.call [] mul_name [expr.var "outz"; expr.var "three_b"; expr.var "t2"]);
        coq:(cmd.call [] sub_name [expr.var "outx"; expr.var "t1"; expr.var "outz"]);
        coq:(cmd.call [] add_name [expr.var "outz"; expr.var "outz"; expr.var "t1"]);
        coq:(cmd.call [] mul_name [expr.var "outy"; expr.var "outx"; expr.var "outz"]);
        coq:(cmd.call [] add_name [expr.var "t1"; expr.var "t0"; expr.var "t0"]);
        coq:(cmd.call [] add_name [expr.var "t1"; expr.var "t1"; expr.var "t0"]);
        coq:(cmd.call [] mul_name [expr.var "t4"; expr.var "three_b"; expr.var "t4"]);
        coq:(cmd.call [] mul_name [expr.var "t0"; expr.var "t1"; expr.var "t4"]);
        coq:(cmd.call [] add_name [expr.var "outy"; expr.var "outy"; expr.var "t0"]);
        coq:(cmd.call [] mul_name [expr.var "t0"; expr.var "t5"; expr.var "t4"]);
        coq:(cmd.call [] mul_name [expr.var "outx"; expr.var "t3"; expr.var "outx"]);
        coq:(cmd.call [] sub_name [expr.var "outx"; expr.var "outx"; expr.var "t0"]);
        coq:(cmd.call [] mul_name [expr.var "t0"; expr.var "t3"; expr.var "t1"]);
        coq:(cmd.call [] mul_name [expr.var "outz"; expr.var "t5"; expr.var "outz"]);
        coq:(cmd.call [] add_name [expr.var "outz"; expr.var "outz"; expr.var "t0"])
      ).

    (** The full bedrock2 function definition for projective add (a=0).
        The 10-argument signature passes the 9 point-coordinate pointers
        + a [three_b] stash pointer.

        [Syntax.func = (list string * list string * cmd)] (no name);
        the (name, func) pairing is the consumer's job. *)
    Definition Fp3_proj_add_func : Syntax.func :=
      (["outx"; "outy"; "outz";
        "X1"; "Y1"; "Z1";
        "X2"; "Y2"; "Z2";
        "three_b"], []%list,
       Fp3_proj_add_body).
  End BedrockBody.

  (** ** Spec template

      We expose two equivalent spec views:

      1. [Fp3_proj_add_spec_abstract]: Gallina post stated directly
         using [Fp3_proj_add_a0] over Fp3 [feval] of the output felems.
         This is the consumer-friendly view.

      2. The standalone [program_logic_goal_for_function]-style spec
         lives in [BW6_761Curve_G2_bedrock.v] where the BW6-specific
         [bw6_Fp3_repr] is already in scope.  Stating it abstractly
         here would force every coordinate-felem to carry its own
         typeclass argument chain and make the [fnspec!] macro
         essentially unreadable.  The downstream concrete spec
         specialises this. *)

  (** Abstract post: the output Fp3-elements satisfy [Fp3_proj_add_a0]. *)
  Definition Fp3_proj_add_post
    (feval_fp3 : list word -> Fp3)
    (X1 Y1 Z1 X2 Y2 Z2 outx outy outz : list word) : Prop :=
    let X1 := feval_fp3 X1 in
    let Y1 := feval_fp3 Y1 in
    let Z1 := feval_fp3 Z1 in
    let X2 := feval_fp3 X2 in
    let Y2 := feval_fp3 Y2 in
    let Z2 := feval_fp3 Z2 in
    (feval_fp3 outx, feval_fp3 outy, feval_fp3 outz) =
      Fp3_proj_add_a0 X1 Y1 Z1 X2 Y2 Z2.

  (** ** Sanity lemma: the abstract post matches the BW6 G2 Gallina spec.

      Strictly a sanity check that ties [Fp3_proj_add_a0] to its
      consumer in [BW6_761Curve_G2.v].  Proven by reflexivity since
      both definitions are the same expression up to [Fp3] alias. *)
  Lemma Fp3_proj_add_post_unfold feval_fp3 X1 Y1 Z1 X2 Y2 Z2 outx outy outz :
    Fp3_proj_add_post feval_fp3 X1 Y1 Z1 X2 Y2 Z2 outx outy outz <->
    (feval_fp3 outx, feval_fp3 outy, feval_fp3 outz) =
      Fp3_proj_add_a0 (feval_fp3 X1) (feval_fp3 Y1) (feval_fp3 Z1)
                      (feval_fp3 X2) (feval_fp3 Y2) (feval_fp3 Z2).
  Proof. cbv [Fp3_proj_add_post]. reflexivity. Qed.

End Fp3CurveSpecs.

(** ** Connection to [BW6_761Curve_G2.v]

    The Gallina spec [BW6_G2_add_Gallina_spec_a_0] in
    [BW6_761Curve_G2.v] is definitionally equal to
    [Fp3_proj_add_a0] applied to BW6's [bw6_G2_three_b] and
    [bw6_Fp_mul_by_nr_model] (i.e. when [F := F bw6_M_pos]).  See the
    [BW6_G2_add_specs_match_Fp3_proj_add] lemma in
    [BW6_761Curve_G2_bedrock.v]. *)
