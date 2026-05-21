(** * BW6-761 tower instantiation: Fp -> Fp3 -> Fp6.

    Connects the generic extension modules (GenericQuadratic,
    GenericCubic) to the concrete BW6-761 base field from
    bw6_761_prime.v.

    Tower structure (M-type):
      Fp3 = Fp[zeta]/(zeta^3 + 4),  nonresidue nr = -4 in Fp
      Fp6 = Fp3[w]/(w^2 - zeta),    nonresidue = zeta in Fp3

    Per gnark-crypto/ecc/bw6-761 and El Housni-Guillevic
    "Families of SNARK-friendly 2-chains" (eprint.iacr.org/2021/1359).

    This file defines:
      - AbstractField instances for Fp, Fp3, Fp6
      - mul_by_nonresidue bedrock2 function bodies for each layer
      - Function name prefixes and FieldNames instances

    Cf. BLS24_509_Instances.v for the parallel BLS24 layout (Fp,
    Fp2, Fp4, Fp8, Fp24).  BW6 is shorter (2 layers vs 4) but the
    first extension is cubic instead of quadratic. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.
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

Section BW6.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (* ================================================================ *)
  (* Fp: base field via PrimeFieldParameters bridge                    *)
  (* ================================================================ *)

  Definition bw6_M_pos : positive :=
    Eval vm_compute in (Z.to_pos bw6_761_prime.m).

  Instance bw6_prime_params : PrimeFieldParameters := {|
    PrimeField.M_pos := bw6_M_pos;
    PrimeField.a24 := F.of_Z _ 0;
    PrimeField.mul := "bw6_761_mul";
    PrimeField.add := "bw6_761_add";
    PrimeField.sub := "bw6_761_sub";
    PrimeField.opp := "bw6_761_opp";
    PrimeField.square := "bw6_761_square";
    PrimeField.scmula24 := "bw6_761_scmula24";
    PrimeField.inv := "bw6_761_inv";
    PrimeField.from_bytes := "bw6_761_from_bytes";
    PrimeField.to_bytes := "bw6_761_to_bytes";
    PrimeField.select_znz := "bw6_761_select_znz";
    PrimeField.felem_copy := "bw6_761_felem_copy";
    PrimeField.from_word := "bw6_761_from_word";
    PrimeField.from_list := "bw6_761_from_list";
  |}.

  Instance bw6_prime_params_ok : PrimeFieldParameters_ok.
  Proof. constructor. exact prime_bw6_761. Qed.

  Existing Instance prime_field_parameters.

  (* Bridge from Specs.Field.FieldRepresentation to
     AbstractField.FieldRepresentation for F M_pos *)
  Let bw6_m := bw6_761_prime.m.
  Existing Instance bw6_761_field_parameters.

  Local Instance bw6_frep : Field.FieldRepresentation :=
    field_representation bw6_m.

  Instance bw6_Fp_repr : AbstractField.FieldRepresentation
    (F := F PrimeField.M_pos) :=
    {| AbstractField.feval := @Field.feval _ _ _ _ _ bw6_frep;
       AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bw6_frep;
       AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bw6_frep;
       AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bw6_frep;
       AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bw6_frep;
       AbstractField.bounds := @Field.bounds _ _ _ _ _ bw6_frep;
       AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bw6_frep;
       AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bw6_frep;
       AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bw6_frep |}.

  Instance bw6_Fp_repr_ok : AbstractField.FieldRepresentation_ok
    (F := F PrimeField.M_pos).
  Proof.
    constructor. intros X H.
    cbv [AbstractField.bounded_by bw6_Fp_repr] in *.
    cbv [Field.bounded_by bw6_frep field_representation
         Signature.field_representation Representation.frep] in *.
    exact H.
  Defined.

  Instance bw6_Fp_names : FieldNames (F := F PrimeField.M_pos) :=
    field_names_prefixed "bw6_761_".

  (* Shorthand for the tower types *)
  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  (* Decidable equality for stacking *)
  Definition Fp_eq_dec : forall x y : Fp, {x = y} + {x <> y} :=
    @F.eq_dec bw6_M_pos.

  Definition Fp3_eq_dec : forall x y : Fp3, {x = y} + {x <> y} :=
    @eq_dec_CE _ Fp_eq_dec.

  (* ================================================================ *)
  (* Fp3 = Fp[zeta]/(zeta^3 + 4), cubic nonresidue nr = -4            *)
  (* ================================================================ *)

  (** Gallina model: multiplication by -4 in Fp. *)
  Definition bw6_Fp_mul_by_nr_model (x : Fp) : Fp :=
    F.mul (F.opp (F.of_Z _ 4)) x.

  Let fp3_prefix := "bw6_761_Fp3_".

  Instance bw6_Fp3_params : AbstractField.FieldParameters Fp3 :=
    @CE_field_parameters Fp prime_field_parameters
      bw6_Fp_mul_by_nr_model fp3_prefix Fp_eq_dec.

  Instance bw6_Fp3_repr : AbstractField.FieldRepresentation (F := Fp3) :=
    @CE_field_representation _ _ _ _ Fp prime_field_parameters bw6_Fp_repr
      bw6_Fp_mul_by_nr_model fp3_prefix Fp_eq_dec.

  Instance bw6_Fp3_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp3) :=
    @CE_field_representation_ok _ _ _ _ Fp prime_field_parameters bw6_Fp_repr bw6_Fp_repr_ok
      bw6_Fp_mul_by_nr_model fp3_prefix Fp_eq_dec.

  Instance bw6_Fp3_names : FieldNames (F := Fp3) :=
    field_names_prefixed fp3_prefix.

  (** mul_by_nonresidue for Fp3: multiply x by -4 in Fp.
      Implemented as: tmp = 2x; tmp = 2*tmp = 4x; out = -tmp = -4x. *)
  Definition bw6_Fp_mul_by_nr_name := "bw6_761_mul_by_nr_n4".

  Import Syntax.

  Definition bw6_Fp_mul_by_nr_func : string * Syntax.func :=
    (bw6_Fp_mul_by_nr_name,
     (["out"; "x"], []:list String.string,
      bedrock_func_body:(
        (* out := x + x  (= 2x) *)
        coq:(cmd.call [] (AbstractField.add (F := Fp))
              [expr.var "out"; expr.var "x"; expr.var "x"]);
        (* out := out + out  (= 4x) *)
        coq:(cmd.call [] (AbstractField.add (F := Fp))
              [expr.var "out"; expr.var "out"; expr.var "out"]);
        (* out := -out  (= -4x) *)
        coq:(cmd.call [] (AbstractField.opp (F := Fp))
              [expr.var "out"; expr.var "out"])
      ))).

  (* ================================================================ *)
  (* Fp6 = Fp3[w]/(w^2 - zeta), quadratic nonresidue = zeta in Fp3   *)
  (*                                                                  *)
  (* zeta is the cubic generator of Fp3 = Fp[zeta]/(zeta^3 + 4).      *)
  (* As an Fp3 element, zeta = (0, 1, 0).                             *)
  (* Multiplication by zeta in Fp3:                                   *)
  (*   zeta * (a + b*zeta + c*zeta^2) = a*zeta + b*zeta^2 + c*zeta^3  *)
  (*                                   = -4c + a*zeta + b*zeta^2     *)
  (*   (a, b, c) |-> (-4c, a, b)                                      *)
  (* ================================================================ *)

  Definition bw6_zeta_in_Fp3 : Fp3 :=
    (@F.zero PrimeField.M_pos, @F.one PrimeField.M_pos, @F.zero PrimeField.M_pos).

  (** Gallina model for multiplication by zeta in Fp3. *)
  Definition bw6_Fp3_mul_by_zeta_model (x : Fp3) : Fp3 :=
    (bw6_Fp_mul_by_nr_model (snd x), fst (fst x), snd (fst x)).

  Let fp6_prefix := "bw6_761_Fp6_".

  Instance bw6_Fp6_params : AbstractField.FieldParameters Fp6 :=
    @QE_field_parameters Fp3 bw6_Fp3_params
      bw6_zeta_in_Fp3 fp6_prefix Fp3_eq_dec.

  Instance bw6_Fp6_repr : AbstractField.FieldRepresentation (F := Fp6) :=
    @QE_field_representation _ _ _ _ Fp3 bw6_Fp3_params bw6_Fp3_repr
      bw6_zeta_in_Fp3 fp6_prefix Fp3_eq_dec.

  Instance bw6_Fp6_repr_ok : AbstractField.FieldRepresentation_ok (F := Fp6) :=
    @QE_field_representation_ok _ _ _ _ Fp3 bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok
      bw6_zeta_in_Fp3 fp6_prefix Fp3_eq_dec.

  Instance bw6_Fp6_names : FieldNames (F := Fp6) :=
    field_names_prefixed fp6_prefix.

  (** mul_by_zeta on Fp3: (a,b,c) -> (mul_by_nr(c), a, b).
      Memory layout: an Fp3 is 3 consecutive Fp slots [c0; c1; c2].
      Both input and output share the same layout. *)
  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp _ _ _ _ _ bw6_Fp_repr)).

  Definition fp3_c0 (x : Syntax.expr) : Syntax.expr := x.
  Definition fp3_c1 (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal fp_felem_offset).
  Definition fp3_c2 (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal (2 * fp_felem_offset)).

  Definition bw6_Fp3_mul_by_zeta_name := "bw6_761_Fp3_mul_by_zeta".

  Definition bw6_Fp3_mul_by_zeta_func : string * Syntax.func :=
    (bw6_Fp3_mul_by_zeta_name,
     (["out"; "x"], []:list String.string,
      bedrock_func_body:(
        (* Need ztmp to compute -4*x.c2 before writing into out.c0,
           and btmp to save x.c1 before writing into out.c2. *)
        stackalloc (@AbstractField.felem_size_in_bytes Fp _ _ _ _ _ bw6_Fp_repr) as ztmp;
        stackalloc (@AbstractField.felem_size_in_bytes Fp _ _ _ _ _ bw6_Fp_repr) as btmp;
        (* ztmp = mul_by_nr(x.c2) = -4 * x.c2 *)
        coq:(cmd.call [] bw6_Fp_mul_by_nr_name
              [expr.var "ztmp"; fp3_c2 (expr.var "x")]);
        (* btmp = x.c1 *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp))
              [expr.var "btmp"; fp3_c1 (expr.var "x")]);
        (* out.c1 = x.c0 *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp))
              [fp3_c1 (expr.var "out"); fp3_c0 (expr.var "x")]);
        (* out.c0 = ztmp = -4 * x.c2 *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp))
              [fp3_c0 (expr.var "out"); expr.var "ztmp"]);
        (* out.c2 = btmp = original x.c1 *)
        coq:(cmd.call [] (AbstractField.felem_copy (F := Fp))
              [fp3_c2 (expr.var "out"); expr.var "btmp"])
      ))).

  (* mul_by_nonresidue for Fp6: multiply by zeta in Fp3 *)
  Definition bw6_Fp6_mul_by_nr_name := bw6_Fp3_mul_by_zeta_name.
  Definition bw6_Fp6_mul_by_nr_func := bw6_Fp3_mul_by_zeta_func.

  (* ================================================================ *)
  (* spec_of instances for base field operations                       *)
  (* ================================================================ *)

  Instance spec_of_bw6_add : spec_of (AbstractField.add (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_add.
  Instance spec_of_bw6_sub : spec_of (AbstractField.sub (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_sub.
  Instance spec_of_bw6_mul : spec_of (AbstractField.mul (F := Fp)) :=
    AbstractField.binop_spec AbstractField.bin_mul.
  Instance spec_of_bw6_opp : spec_of (AbstractField.opp (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_opp.
  Instance spec_of_bw6_sqr : spec_of (AbstractField.square (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_square.
  Instance spec_of_bw6_inv : spec_of (AbstractField.inv (F := Fp)) :=
    AbstractField.unop_spec AbstractField.un_inv.
  Instance spec_of_bw6_copy : spec_of (AbstractField.felem_copy (F := Fp)) :=
    AbstractField.spec_of_felem_copy.

End BW6.
