(* BLS12-377 Fp2 = Fp[u]/(u² + 5) where β = -5 is a QNR.
   Unlike BLS12-381 (β = -1, p ≡ 3 mod 4), BLS12-377 has p ≡ 1 mod 8.

   All operations except mul and sqr are component-wise (same as BLS12-381).
   Mul and sqr inline the multiply-by-5 as 3 adds. *)

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
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bls377_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_prime_parameters : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul";
      PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub";
      PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square";
      PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv";
      PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes";
      PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy";
      PrimeField.from_word := "bls377_from_word";
      PrimeField.from_list := "bls377_from_list";
    |}.

    Instance bls377_prime_parameters_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    Instance bls377_field_representation : AbstractField.FieldRepresentation
      (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_field_representation_ok : AbstractField.FieldRepresentation_ok
      (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_field_representation] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Instance bls377_field_names : FieldNames (F:=F PrimeField.M_pos) :=
      field_names_prefixed "bls377_".

    Local Notation F := (F PrimeField.M_pos).
    Local Notation Fp2 := (F * F)%type.

    Local Definition felem_offset : Z := AbstractField.felem_size_in_bytes (F:=F).
    Local Definition expr_2nd_felem (x : Syntax.expr) :=
      expr.op bopname.add x (expr.literal felem_offset).

    (* ================================================================ *)
    (* Component-wise operations (identical to BLS12-381)                *)
    (* ================================================================ *)

    Definition Fp2_felem_copy : string * Syntax.func :=
      ("bls377_Fp2_felem_copy", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

    Definition Fp2_add : string * Syntax.func :=
      ("bls377_Fp2_add", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    Definition Fp2_sub : string * Syntax.func :=
      ("bls377_Fp2_sub", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    (* select_znz needs Fp2 AbstractField instances — deferred until needed *)

    Definition Fp2_zero : string * Syntax.func :=
      ("bls377_Fp2_zero", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 0]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    Definition Fp2_one : string * Syntax.func :=
      ("bls377_Fp2_one", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 1]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    (* ================================================================ *)
    (* β-dependent operations: mul, sqr                                  *)
    (* ================================================================ *)

    (* Fp2 multiplication: (a+bu)(c+du) = (ac + β·bd) + ((a+b)(c+d)-ac-bd)u
       β = -5, so ac + β·bd = ac - 5·bd.
       Karatsuba with 3 Fp muls + inlined multiply-by-5 (3 adds + 1 sub). *)
    Definition Fp2_mul : string * Syntax.func :=
      ("bls377_Fp2_mul", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
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
        (* out.im = (c+d) * (a+b) *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v2"]);
        (* out.im -= v0 *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v0"]);
        (* out.im -= v1 = ad + bc *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v1"]);
        (* Compute 5*v1: v2 = 2*v1; v2 = 4*v1; v2 = 5*v1 *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v1"; expr.var "v1"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v2"; expr.var "v2"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v2"; expr.var "v1"]);
        (* out.re = v0 - 5*v1 = ac + β·bd *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v2"])
      ))).

    (* Fp2 squaring: (a+bu)² = (a² + β·b²) + 2ab·u
       β = -5, so a² + β·b² = a² - 5·b².
       Uses 2 Fp squarings + 1 Fp mul + inlined multiply-by-5. *)
    Definition Fp2_sqr : string * Syntax.func :=
      ("bls377_Fp2_square", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        (* v0 = a * a *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v0"; expr.var "inx"]);
        (* v1 = b * b *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = a * b *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = 2*a*b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out")]);
        (* Compute 5*v1: reuse out.re as temp *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "v1"; expr.var "v1"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "out"; expr.var "out"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "out"; expr.var "v1"]);
        (* out.re = v0 - 5*v1 = a² - 5b² *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "out"])
      ))).

    (* Fp2 inversion: (a+bu)^(-1) = (a, -b) / (a² - β·b²)
       norm = a² - β·b² = a² + 5·b² (since β = -5, -β = 5)
       Then: re = a / norm, im = -b / norm *)
    Definition Fp2_inv : string * Syntax.func :=
      ("bls377_Fp2_inv", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as asq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as bsq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as norm;
        (* asq = a² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "asq"; expr.var "inx"]);
        (* bsq = b² *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "bsq"; expr_2nd_felem (expr.var "inx")]);
        (* Compute 5*bsq in norm *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "norm"; expr.var "bsq"; expr.var "bsq"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "norm"; expr.var "norm"; expr.var "norm"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "norm"; expr.var "norm"; expr.var "bsq"]);
        (* norm = a² + 5*b² = a² - β·b² (since β = -5, -β = 5) *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "norm"; expr.var "asq"; expr.var "norm"]);
        (* norm = 1/norm *)
        coq:(cmd.call [] (AbstractField.inv (F:=F)) [expr.var "norm"; expr.var "norm"]);
        (* out.re = a * norm_inv *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "norm"]);
        (* Negate b first using sub: asq = 0 - b (reuse asq as temp) *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "asq"; expr.var "bsq"; expr.var "bsq"]);
        (* asq = 0 now *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "asq"; expr.var "asq"; expr_2nd_felem (expr.var "inx")]);
        (* asq = -b *)
        (* out.im = (-b) * norm_inv *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "asq"; expr.var "norm"])
      ))).

    (* ================================================================ *)
    (* fp2_mul_xi: multiply by ξ = u = (0,1) in Fp2                    *)
    (* (a0 + a1·u) · u = a1·u² + a0·u = β·a1 + a0·u = -5·a1 + a0·u  *)
    (* Result: (-5·a1, a0)                                              *)
    (* ================================================================ *)

    (* Restructured: all x-reads via stack temp, out-writes last.
       This avoids the cross-disjointness issue in the WP proof. *)
    Definition Fp2_mul_xi : string * Syntax.func :=
      ("bls377_Fp2_mul_xi", (["out"; "x"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as tmp;
        (* tmp = 5*x.im: v = x.im+x.im; v = v+v; v = v+x.im *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp"; expr_2nd_felem (expr.var "x"); expr_2nd_felem (expr.var "x")]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp"; expr.var "tmp"; expr.var "tmp"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp"; expr.var "tmp"; expr_2nd_felem (expr.var "x")]);
        (* out.im = x.re *)
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "x"]);
        (* out.re = 0 - tmp = -5*x.im *)
        coq:(cmd.call [] (@AbstractField.opp _ prime_field_parameters) [expr.var "out"; expr.var "tmp"])
      ))).

    (* Fp2 conjugate: conj(a + bu) = a - bu
       Uses copy(out.re, inx.re) + opp(out.im, inx.im). *)
    Definition Fp2_conjugate : string * Syntax.func :=
      ("bls377_Fp2_conjugate", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (@AbstractField.opp _ prime_field_parameters) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

End bls377_Fp2.
