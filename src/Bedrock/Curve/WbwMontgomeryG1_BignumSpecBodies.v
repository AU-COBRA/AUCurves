(** Shared Bignum-style [spec_of] predicate bodies for WBW Montgomery
    G1 coordinate operations (mul/add/sub/square/opp).

    Each per-curve WiredSpecs file currently declares 5 [Instance]s of the
    form [spec_of "<curve>_coord_<op>"] with ~25 lines of identical
    predicate body. Extracting the bodies here reduces each per-curve
    instance declaration to a 1-liner:

    {[
      Instance spec_of_<curve>_mul_bignum : spec_of "<curve>_coord_mul"
        := mul_bignum_body.
    ]}

    Saves ~24 LoC × 5 ops × 7 curves = ~840 LoC once adopted.

    The body is parameterized over [field_parameters] and
    [field_representation] (via typeclass inference), so a curve's
    [Existing Instance <curve>_frep] makes the correct [m, n, bw] bind. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Import ListNotations.
Local Open Scope Z_scope.

Section SpecBodies.
  Context {field_parameters : FieldParameters}.
  Context {field_representation : FieldRepresentation}.

  Local Notation bw := 64%Z.
  Local Notation n  := (felem_size_in_words (FieldRepresentation := field_representation)).
  Local Notation m  := (Z.pos M_pos).
  Local Notation m' := (@Field.m' bw field_parameters).
  Local Notation eval     := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation toZ       := (List.map Interface.word.unsigned).

  (** BinOp predicate body: mul-style. *)
  Definition binop_mul_body : Semantics.env -> Prop :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        WordByWordMontgomery.valid bw n m (toZ wsx) ->
        WordByWordMontgomery.valid bw n m (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        call functions Field.mul tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               WordByWordMontgomery.valid bw n m (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m *
                (eval (from_mont (toZ wsy))) mod m) mod m).

  (** BinOp predicate body: add-style. *)
  Definition binop_add_body : Semantics.env -> Prop :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        WordByWordMontgomery.valid bw n m (toZ wsx) ->
        WordByWordMontgomery.valid bw n m (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        call functions Field.add tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               WordByWordMontgomery.valid bw n m (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m +
                (eval (from_mont (toZ wsy))) mod m) mod m).

  (** BinOp predicate body: sub-style. *)
  Definition binop_sub_body : Semantics.env -> Prop :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        WordByWordMontgomery.valid bw n m (toZ wsx) ->
        WordByWordMontgomery.valid bw n m (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        call functions Field.sub tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               WordByWordMontgomery.valid bw n m (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m -
                (eval (from_mont (toZ wsy))) mod m) mod m).

  (** UnOp predicate body: square-style. *)
  Definition unop_square_body : Semantics.env -> Prop :=
    fun functions =>
      forall (wsx old_out : list word.rep)
             (px pout : word.rep)
             (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        WordByWordMontgomery.valid bw n m (toZ wsx) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        call functions Field.square tr mem0
          [pout; px]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               WordByWordMontgomery.valid bw n m (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m *
                (eval (from_mont (toZ wsx))) mod m) mod m).

  (** UnOp predicate body: opp-style. *)
  Definition unop_opp_body : Semantics.env -> Prop :=
    fun functions =>
      forall (wsx old_out : list word.rep)
             (px pout : word.rep)
             (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        WordByWordMontgomery.valid bw n m (toZ wsx) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        call functions Field.opp tr mem0
          [pout; px]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               WordByWordMontgomery.valid bw n m (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               (- (eval (from_mont (toZ wsx))) mod m) mod m).

End SpecBodies.

(** Usage in per-curve WiredSpecs:

    {[
      Existing Instance <curve>_field_parameters.
      Existing Instance <curve>_frep.
      Existing Instance <curve>_frep_ok.

      Instance spec_of_<curve>_mul_bignum    : spec_of "<curve>_coord_mul"    := binop_mul_body.
      Instance spec_of_<curve>_add_bignum    : spec_of "<curve>_coord_add"    := binop_add_body.
      Instance spec_of_<curve>_sub_bignum    : spec_of "<curve>_coord_sub"    := binop_sub_body.
      Instance spec_of_<curve>_square_bignum : spec_of "<curve>_coord_square" := unop_square_body.
      Instance spec_of_<curve>_opp_bignum    : spec_of "<curve>_coord_opp"    := unop_opp_body.
    ]}

    Saves ~25 LoC → 1 LoC per instance × 5 × 7 curves = ~840 LoC. *)
