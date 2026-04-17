(* BN254 (alt_bn128) Fp2 = Fp[u]/(u² + 1) where β = -1 is a QNR.
   p ≡ 3 mod 4, so -1 is a QNR in Fp.

   β = -1 simplifies mul/sqr: no multiply-by-|β| chains needed.
   Fp2 mul: (a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u  [Karatsuba]
   Fp2 sqr: (a+bu)² = (a² - b²) + 2ab·u

   Fp6 nonresidue ξ = 9 + u = (9, 1) ∈ Fp2
   mul_xi: (a+bu)·(9+u) = (9a - b) + (a + 9b)u *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bn254_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_prime_parameters : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul";
      PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub";
      PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square";
      PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv";
      PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes";
      PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy";
      PrimeField.from_word := "bn254_from_word";
      PrimeField.from_list := "bn254_from_list";
    |}.

    Instance bn254_prime_parameters_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    Instance bn254_field_representation : AbstractField.FieldRepresentation
      (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_field_representation_ok : AbstractField.FieldRepresentation_ok
      (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_field_representation] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Instance bn254_field_names : FieldNames (F:=F PrimeField.M_pos) :=
      field_names_prefixed "bn254_".

    Local Notation F := (F PrimeField.M_pos).
    Local Notation Fp2 := (F * F)%type.

    Local Definition felem_offset : Z := AbstractField.felem_size_in_bytes (F:=F).
    Local Definition expr_2nd_felem (x : Syntax.expr) :=
      expr.op bopname.add x (expr.literal felem_offset).

    (* ================================================================ *)
    (* Component-wise operations                                         *)
    (* ================================================================ *)

    Definition Fp2_felem_copy : string * Syntax.func :=
      ("bn254_Fp2_felem_copy", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

    Definition Fp2_add : string * Syntax.func :=
      ("bn254_Fp2_add", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    Definition Fp2_sub : string * Syntax.func :=
      ("bn254_Fp2_sub", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    Definition Fp2_zero : string * Syntax.func :=
      ("bn254_Fp2_zero", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 0]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    Definition Fp2_one : string * Syntax.func :=
      ("bn254_Fp2_one", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 1]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    (* ================================================================ *)
    (* β-dependent operations: mul, sqr, inv                             *)
    (* β = -1: ac - bd replaces ac + β·bd, a² - b² replaces a² + β·b²  *)
    (* ================================================================ *)

    (* Fp2 multiplication: (a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u
       Karatsuba with 3 Fp muls, 2 Fp adds, 3 Fp subs. No multiply-by-|β|! *)
    Definition Fp2_mul : string * Syntax.func :=
      ("bn254_Fp2_mul", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v2;
        (* v0 = a * c *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v0"; expr.var "inx"; expr.var "iny"]);
        (* v1 = b * d *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")]);
        (* v2 = a + b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = c + d *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "iny"; expr_2nd_felem (expr.var "iny")]);
        (* out.im = (a+b)(c+d) *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v2"]);
        (* out.im -= v0 *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v0"]);
        (* out.im -= v1 = ad + bc *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v1"]);
        (* out.re = v0 - v1 = ac - bd  (β = -1, so ac + β·bd = ac - bd) *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
      ))).

    (* Fp2 squaring: (a+bu)² = (a² - b²) + 2ab·u
       Uses 2 Fp squarings + 1 Fp mul. *)
    Definition Fp2_sqr : string * Syntax.func :=
      ("bn254_Fp2_square", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        (* v0 = a² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v0"; expr.var "inx"]);
        (* v1 = b² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = a * b *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = 2*a*b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out")]);
        (* out.re = a² - b²  (β = -1, so a² + β·b² = a² - b²) *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
      ))).

    (* Fp2 inversion: (a+bu)^(-1) = (a, -b) / (a² + b²)
       norm = a² - β·b² = a² + b²  (since β = -1)
       Then: re = a / norm, im = -b / norm *)
    Definition Fp2_inv : string * Syntax.func :=
      ("bn254_Fp2_inv", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as asq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as bsq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as norm;
        (* asq = a² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "asq"; expr.var "inx"]);
        (* bsq = b² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "bsq"; expr_2nd_felem (expr.var "inx")]);
        (* norm = a² + b² *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "norm"; expr.var "asq"; expr.var "bsq"]);
        (* norm = 1/norm *)
        coq:(cmd.call [] (AbstractField.inv (F:=F)) [expr.var "norm"; expr.var "norm"]);
        (* out.re = a * norm_inv *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "norm"]);
        (* Negate b: asq = 0 - b (reuse asq as temp) *)
        coq:(cmd.call [] (@AbstractField.opp _ prime_field_parameters) [expr.var "asq"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = (-b) * norm_inv *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "asq"; expr.var "norm"])
      ))).

    (* ================================================================ *)
    (* fp2_mul_xi: multiply by ξ = (9, 1) ∈ Fp2                         *)
    (* (a + bu)·(9 + u) = (9a + β·b) + (a + 9b)u = (9a - b) + (a + 9b)u*)
    (* Multiply-by-9: x -> 2x -> 4x -> 8x -> 8x+x                      *)
    (* ================================================================ *)

    Definition Fp2_mul_xi : string * Syntax.func :=
      ("bn254_Fp2_mul_xi", (["out"; "x"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as tmp_a9;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as tmp_b9;
        (* tmp_a9 = 9*a: 2a -> 4a -> 8a -> 8a+a *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a9"; expr.var "x"; expr.var "x"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "x"]);
        (* tmp_b9 = 9*b: 2b -> 4b -> 8b -> 8b+b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b9"; expr_2nd_felem (expr.var "x"); expr_2nd_felem (expr.var "x")]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b9"; expr.var "tmp_b9"; expr_2nd_felem (expr.var "x")]);
        (* out.re = 9a - b *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "tmp_a9"; expr_2nd_felem (expr.var "x")]);
        (* out.im = a + 9b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "x"; expr.var "tmp_b9"])
      ))).

    (* Fp2 conjugate: conj(a + bu) = a - bu *)
    Definition Fp2_conjugate : string * Syntax.func :=
      ("bn254_Fp2_conjugate", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (@AbstractField.opp _ prime_field_parameters) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

End bn254_Fp2.
