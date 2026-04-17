(** * BLS24-509 tower instantiation: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24.

    Connects the generic extension modules (GenericQuadratic, GenericCubic)
    to the concrete BLS24-509 base field from bls24_509_Fp.v.

    Tower structure:
      Fp2  = Fp[u]/(u^2+1),    nonresidue beta = -1 in Fp
      Fp4  = Fp2[v]/(v^2-xi),  nonresidue xi = (1,1) in Fp2
      Fp8  = Fp4[w]/(w^2-v),   nonresidue v = ((0,1),(0,0)) in Fp4
      Fp24 = Fp8[t]/(t^3-w),   nonresidue w, mul_by_nr = fp8_mul_by_w

    This file defines:
      - AbstractField instances for Fp, Fp2, Fp4, Fp8, Fp24
      - mul_by_nonresidue bedrock2 function bodies for each layer
      - Function name prefixes and FieldNames instances *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section BLS24.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (* ================================================================ *)
  (* Fp: base field via PrimeFieldParameters bridge                    *)
  (* ================================================================ *)

  Definition bls24_M_pos : positive :=
    Eval vm_compute in (Z.to_pos bls24_509_modulus).

  Instance bls24_prime_params : PrimeFieldParameters := {|
    PrimeField.M_pos := bls24_M_pos;
    PrimeField.a24 := F.of_Z _ 0;
    PrimeField.mul := "bls24_509_mul";
    PrimeField.add := "bls24_509_add";
    PrimeField.sub := "bls24_509_sub";
    PrimeField.opp := "bls24_509_opp";
    PrimeField.square := "bls24_509_square";
    PrimeField.scmula24 := "bls24_509_scmula24";
    PrimeField.inv := "bls24_509_inv";
    PrimeField.from_bytes := "bls24_509_from_bytes";
    PrimeField.to_bytes := "bls24_509_to_bytes";
    PrimeField.select_znz := "bls24_509_select_znz";
    PrimeField.felem_copy := "bls24_509_felem_copy";
    PrimeField.from_word := "bls24_509_from_word";
    PrimeField.from_list := "bls24_509_from_list";
  |}.

  Instance bls24_prime_params_ok : PrimeFieldParameters_ok.
  Proof. constructor. exact prime_bls24_509. Qed.

  Existing Instance prime_field_parameters.

  (* Bridge from Specs.Field.FieldRepresentation to
     AbstractField.FieldRepresentation for F M_pos *)
  Let bls24_m := bls24_509_Fp.m.
  Existing Instance bls24_509_field_parameters.

  Local Instance bls24_frep : Field.FieldRepresentation :=
    field_representation bls24_m.

  Instance bls24_Fp_repr : AbstractField.FieldRepresentation
    (F := F PrimeField.M_pos) :=
    {| AbstractField.feval := @Field.feval _ _ _ _ _ bls24_frep;
       AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls24_frep;
       AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls24_frep;
       AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls24_frep;
       AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls24_frep;
       AbstractField.bounds := @Field.bounds _ _ _ _ _ bls24_frep;
       AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls24_frep;
       AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls24_frep;
       AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls24_frep |}.

  Instance bls24_Fp_repr_ok : AbstractField.FieldRepresentation_ok
    (F := F PrimeField.M_pos).
  Proof.
    constructor. intros X H.
    cbv [AbstractField.bounded_by bls24_Fp_repr] in *.
    cbv [Field.bounded_by bls24_frep field_representation
         Signature.field_representation Representation.frep] in *.
    exact H.
  Defined.

  Instance bls24_Fp_names : FieldNames (F := F PrimeField.M_pos) :=
    field_names_prefixed "bls24_509_".

  (* Shorthand for the base field type *)
  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.
  Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

  (* Decidable equality for stacking *)
  Definition Fp_eq_dec : forall x y : Fp, {x = y} + {x <> y} :=
    @F.eq_dec bls24_M_pos.

  Definition Fp2_eq_dec : forall x y : Fp2, {x = y} + {x <> y} :=
    @eq_dec_QE _ Fp_eq_dec.

  Definition Fp4_eq_dec : forall x y : Fp4, {x = y} + {x <> y} :=
    @eq_dec_QE _ Fp2_eq_dec.

  Definition Fp8_eq_dec : forall x y : Fp8, {x = y} + {x <> y} :=
    @eq_dec_QE _ Fp4_eq_dec.

  (* ================================================================ *)
  (* Fp2 = Fp[u]/(u^2+1), beta = -1                                   *)
  (* ================================================================ *)

  Definition bls24_beta : Fp := F.of_Z PrimeField.M_pos (-1).

  Let fp2_prefix := "bls24_Fp2_".

  (** Fp2 FieldParameters: QE over Fp with nonresidue beta = -1.
      @QE_field_parameters : BaseField -> base_fp -> nonresidue -> prefix -> eq_dec -> ... *)
  Instance bls24_Fp2_params : AbstractField.FieldParameters Fp2 :=
    @QE_field_parameters Fp prime_field_parameters
      bls24_beta fp2_prefix Fp_eq_dec.

  Instance bls24_Fp2_repr : AbstractField.FieldRepresentation (F := Fp2) :=
    @QE_field_representation _ _ _ _ Fp prime_field_parameters bls24_Fp_repr
      bls24_beta fp2_prefix Fp_eq_dec.

  Instance bls24_Fp2_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp2) :=
    @QE_field_representation_ok _ _ _ _ Fp prime_field_parameters bls24_Fp_repr bls24_Fp_repr_ok
      bls24_beta fp2_prefix Fp_eq_dec.

  Instance bls24_Fp2_names : FieldNames (F := Fp2) :=
    field_names_prefixed fp2_prefix.

  (* mul_by_nonresidue for Fp2: multiply by beta = -1, i.e., Fp.opp *)
  Definition bls24_Fp2_mul_by_nr_name := "bls24_Fp2_mul_by_nr".

  Import Syntax.

  Definition bls24_Fp2_mul_by_nr_func : string * Syntax.func :=
    (bls24_Fp2_mul_by_nr_name,
     (["out"; "x"], []:list String.string,
      cmd.call [] (AbstractField.opp (F := Fp)) [expr.var "out"; expr.var "x"])).

  (* ================================================================ *)
  (* Fp2 mul_by_xi: multiply Fp2 element by xi = (1,1) = 1+u          *)
  (*   (a0, a1) |-> (a0 - a1, a0 + a1)                                *)
  (* ================================================================ *)

  Definition bls24_Fp2_mul_xi_name := "bls24_Fp2_mul_xi".

  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp _ _ _ _ _ bls24_Fp_repr)).

  Definition fp2_2nd (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal fp_felem_offset).

  Definition bls24_Fp2_mul_xi_func : string * Syntax.func :=
    (bls24_Fp2_mul_xi_name,
     (["out"; "x"], []:list String.string,
      bedrock_func_body:(
        stackalloc (@AbstractField.felem_size_in_bytes Fp _ _ _ _ _ bls24_Fp_repr) as atmp;
        (* tmp = a0 + a1 *)
        coq:(cmd.call [] (AbstractField.add (F := Fp))
              [expr.var "atmp"; expr.var "x"; fp2_2nd (expr.var "x")]);
        (* out.re = a0 - a1 *)
        coq:(cmd.call [] (AbstractField.sub (F := Fp))
              [expr.var "out"; expr.var "x"; fp2_2nd (expr.var "x")]);
        (* out.im = tmp *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp))
              [fp2_2nd (expr.var "out"); expr.var "atmp"])
      ))).

  (* ================================================================ *)
  (* Fp4 = Fp2[v]/(v^2 - (1+u)), nonresidue = (1,1) in Fp2           *)
  (* mul_by_nr for Fp4 is fp2_mul_xi                                   *)
  (* ================================================================ *)

  Definition bls24_xi : Fp2 := (@F.one PrimeField.M_pos, @F.one PrimeField.M_pos).

  Let fp4_prefix := "bls24_Fp4_".

  Instance bls24_Fp4_params : AbstractField.FieldParameters Fp4 :=
    @QE_field_parameters Fp2 bls24_Fp2_params
      bls24_xi fp4_prefix Fp2_eq_dec.

  Instance bls24_Fp4_repr : AbstractField.FieldRepresentation (F := Fp4) :=
    @QE_field_representation _ _ _ _ Fp2 bls24_Fp2_params bls24_Fp2_repr
      bls24_xi fp4_prefix Fp2_eq_dec.

  Instance bls24_Fp4_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp4) :=
    @QE_field_representation_ok _ _ _ _ Fp2 bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
      bls24_xi fp4_prefix Fp2_eq_dec.

  Instance bls24_Fp4_names : FieldNames (F := Fp4) :=
    field_names_prefixed fp4_prefix.

  (* mul_by_nonresidue for Fp4: fp2_mul_xi *)
  Definition bls24_Fp4_mul_by_nr_name := bls24_Fp2_mul_xi_name.
  Definition bls24_Fp4_mul_by_nr_func := bls24_Fp2_mul_xi_func.

  (* ================================================================ *)
  (* Fp4 mul_by_v: multiply Fp4 = (c0, c1) by v                       *)
  (*   (c0, c1) |-> (fp2_mul_xi(c1), c0)                              *)
  (* ================================================================ *)

  Definition bls24_Fp4_mul_by_v_name := "bls24_Fp4_mul_by_v".

  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp2 _ _ _ _ _ bls24_Fp2_repr)).

  Definition fp4_2nd (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).

  Definition bls24_Fp4_mul_by_v_func : string * Syntax.func :=
    (bls24_Fp4_mul_by_v_name,
     (["out"; "x"], []:list String.string,
      bedrock_func_body:(
        stackalloc (@AbstractField.felem_size_in_bytes Fp2 _ _ _ _ _ bls24_Fp2_repr) as vtmp;
        (* vtmp = fp2_mul_xi(x.im = c1) *)
        coq:(cmd.call [] bls24_Fp2_mul_xi_name
              [expr.var "vtmp"; fp4_2nd (expr.var "x")]);
        (* out.im = c0 (copy first half of x to second half of out) *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp2))
              [fp4_2nd (expr.var "out"); expr.var "x"]);
        (* out.re = vtmp *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp2))
              [expr.var "out"; expr.var "vtmp"])
      ))).

  (* ================================================================ *)
  (* Fp8 = Fp4[w]/(w^2 - v), nonresidue = v in Fp4                   *)
  (*   v = (Fp2.zero, Fp2.one) in Fp4 = Fp2 x Fp2                    *)
  (*   mul_by_nr for Fp8 is fp4_mul_by_v                               *)
  (* ================================================================ *)

  (** The Fp4 element v = (Fp2.zero, Fp2.one) = ((0,0),(1,0)) in Fp *)
  Definition bls24_v_in_Fp4 : Fp4 :=
    ((@F.zero PrimeField.M_pos, @F.zero PrimeField.M_pos),
     (@F.one PrimeField.M_pos, @F.zero PrimeField.M_pos)).

  Let fp8_prefix := "bls24_Fp8_".

  Instance bls24_Fp8_params : AbstractField.FieldParameters Fp8 :=
    @QE_field_parameters Fp4 bls24_Fp4_params
      bls24_v_in_Fp4 fp8_prefix Fp4_eq_dec.

  Instance bls24_Fp8_repr : AbstractField.FieldRepresentation (F := Fp8) :=
    @QE_field_representation _ _ _ _ Fp4 bls24_Fp4_params bls24_Fp4_repr
      bls24_v_in_Fp4 fp8_prefix Fp4_eq_dec.

  Instance bls24_Fp8_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp8) :=
    @QE_field_representation_ok _ _ _ _ Fp4 bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
      bls24_v_in_Fp4 fp8_prefix Fp4_eq_dec.

  Instance bls24_Fp8_names : FieldNames (F := Fp8) :=
    field_names_prefixed fp8_prefix.

  (* mul_by_nonresidue for Fp8: fp4_mul_by_v *)
  Definition bls24_Fp8_mul_by_nr_name := bls24_Fp4_mul_by_v_name.
  Definition bls24_Fp8_mul_by_nr_func := bls24_Fp4_mul_by_v_func.

  (* ================================================================ *)
  (* Fp8 mul_by_w: multiply Fp8 = (e0, e1) by w                       *)
  (*   (e0, e1) |-> (fp4_mul_by_v(e1), e0)                            *)
  (* ================================================================ *)

  Definition bls24_Fp8_mul_by_w_name := "bls24_Fp8_mul_by_w".

  Local Notation fp4_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp4 _ _ _ _ _ bls24_Fp4_repr)).

  Definition fp8_2nd (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal fp4_felem_offset).

  Definition bls24_Fp8_mul_by_w_func : string * Syntax.func :=
    (bls24_Fp8_mul_by_w_name,
     (["out"; "x"], []:list String.string,
      bedrock_func_body:(
        stackalloc (@AbstractField.felem_size_in_bytes Fp4 _ _ _ _ _ bls24_Fp4_repr) as wtmp;
        (* wtmp = fp4_mul_by_v(x.im = e1) *)
        coq:(cmd.call [] bls24_Fp4_mul_by_v_name
              [expr.var "wtmp"; fp8_2nd (expr.var "x")]);
        (* out.im = e0 (copy first half of x to second half of out) *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp4))
              [fp8_2nd (expr.var "out"); expr.var "x"]);
        (* out.re = wtmp *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp4))
              [expr.var "out"; expr.var "wtmp"])
      ))).

  (* ================================================================ *)
  (* Fp24 = Fp8[t]/(t^3 - w), nonresidue = w, mul_by_nr = fp8_mul_by_w *)
  (* ================================================================ *)

  (** The Fp8 element w = (Fp4.zero, Fp4.one) = Fp8 generator *)
  Definition bls24_w_in_Fp8 : Fp8 :=
    let fp2z := (@F.zero PrimeField.M_pos, @F.zero PrimeField.M_pos) in
    let fp2o := (@F.one PrimeField.M_pos, @F.zero PrimeField.M_pos) in
    let fp4z := (fp2z, fp2z) in
    let fp4o := (fp2o, fp2z) in
    (fp4z, fp4o).

  (** The Gallina mul_by_nr model for the cubic extension.
      For Fp24 = Fp8[t]/(t^3 - w), the cubic nonresidue is w.
      Multiplying by w in Fp8 = Fp4[w]/(w^2-v):
        w * (e0 + e1*w) = v*e1 + e0*w = (fp4_mul_by_v(e1), e0) *)
  Definition bls24_Fp8_mul_by_w_model (x : Fp8) : Fp8 :=
    let fp2_mul_xi_model (a : Fp2) : Fp2 :=
      (F.sub (fst a) (snd a), F.add (fst a) (snd a)) in
    let fp4_mul_by_v_model (c : Fp4) : Fp4 :=
      (fp2_mul_xi_model (snd c), fst c) in
    (fp4_mul_by_v_model (snd x), fst x).

  Let fp24_prefix := "bls24_Fp24_".

  Instance bls24_Fp24_params : AbstractField.FieldParameters Fp24 :=
    @CE_field_parameters Fp8 bls24_Fp8_params
      bls24_Fp8_mul_by_w_model fp24_prefix Fp8_eq_dec.

  Instance bls24_Fp24_repr : AbstractField.FieldRepresentation (F := Fp24) :=
    @CE_field_representation _ _ _ _ Fp8 bls24_Fp8_params bls24_Fp8_repr
      bls24_Fp8_mul_by_w_model fp24_prefix Fp8_eq_dec.

  Instance bls24_Fp24_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp24) :=
    @CE_field_representation_ok _ _ _ _ Fp8 bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
      bls24_Fp8_mul_by_w_model fp24_prefix Fp8_eq_dec.

  Instance bls24_Fp24_names : FieldNames (F := Fp24) :=
    field_names_prefixed fp24_prefix.

  (* mul_by_nonresidue for Fp24: fp8_mul_by_w *)
  Definition bls24_Fp24_mul_by_nr_name := bls24_Fp8_mul_by_w_name.
  Definition bls24_Fp24_mul_by_nr_func := bls24_Fp8_mul_by_w_func.

  (* ================================================================ *)
  (* spec_of instances for base field operations                       *)
  (* ================================================================ *)

  Instance spec_of_bls24_add : spec_of (AbstractField.add (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_add.
  Instance spec_of_bls24_sub : spec_of (AbstractField.sub (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_sub.
  Instance spec_of_bls24_mul : spec_of (AbstractField.mul (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_mul.
  Instance spec_of_bls24_opp : spec_of (AbstractField.opp (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_opp.
  Instance spec_of_bls24_sqr : spec_of (AbstractField.square (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_square.
  Instance spec_of_bls24_inv : spec_of (AbstractField.inv (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_inv.
  Instance spec_of_bls24_copy : spec_of (AbstractField.felem_copy (F := Fp)) :=
    AbstractField.spec_of_felem_copy.

  (* ================================================================ *)
  (* Collected function lists for each layer                           *)
  (* ================================================================ *)

  (** All mul_by_nonresidue helper functions. *)
  Definition bls24_mul_by_nr_funcs : list (string * Syntax.func) :=
    [ bls24_Fp2_mul_by_nr_func;
      bls24_Fp2_mul_xi_func;
      bls24_Fp4_mul_by_v_func;
      bls24_Fp8_mul_by_w_func ].

End BLS24.
