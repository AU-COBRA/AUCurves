(* BN446 Fp2 = Fp[u]/(u^2 + 1) where beta = -1 is a QNR.
   p = 3 mod 4, so -1 is a QNR in Fp.

   beta = -1 simplifies mul/sqr: no multiply-by-|beta| chains needed.
   Fp2 mul: (a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u  [Karatsuba]
   Fp2 sqr: (a+bu)^2 = (a^2 - b^2) + 2ab*u

   Fp6 nonresidue xi = 2 + 3u = (2, 3) in Fp2
   mul_xi: (a+bu)*(2+3u) = (2a - 3b) + (3a + 2b)u *)

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
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bn446_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_prime_parameters : PrimeFieldParameters := {|
      PrimeField.M_pos := bn446_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn446_mul";
      PrimeField.add := "bn446_add";
      PrimeField.sub := "bn446_sub";
      PrimeField.opp := "bn446_opp";
      PrimeField.square := "bn446_square";
      PrimeField.scmula24 := "bn446_scmula24";
      PrimeField.inv := "bn446_inv";
      PrimeField.from_bytes := "bn446_from_bytes";
      PrimeField.to_bytes := "bn446_to_bytes";
      PrimeField.select_znz := "bn446_select_znz";
      PrimeField.felem_copy := "bn446_felem_copy";
      PrimeField.from_word := "bn446_from_word";
      PrimeField.from_list := "bn446_from_list";
    |}.

    Instance bn446_prime_parameters_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn446. Qed.

    Existing Instance prime_field_parameters.

    Instance bn446_field_representation : AbstractField.FieldRepresentation
      (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn446_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn446_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn446_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn446_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn446_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn446_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn446_frep |}.

    Instance bn446_field_representation_ok : AbstractField.FieldRepresentation_ok
      (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn446_field_representation] in *.
      cbv [Field.bounded_by bn446_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Instance bn446_field_names : FieldNames (F:=F PrimeField.M_pos) :=
      field_names_prefixed "bn446_".

    Local Notation F := (F PrimeField.M_pos).
    Local Notation Fp2 := (F * F)%type.

    Local Definition felem_offset : Z := AbstractField.felem_size_in_bytes (F:=F).
    Local Definition expr_2nd_felem (x : Syntax.expr) :=
      expr.op bopname.add x (expr.literal felem_offset).

    (* ================================================================ *)
    (* Component-wise operations                                         *)
    (* ================================================================ *)

    Definition Fp2_felem_copy : string * Syntax.func :=
      ("bn446_Fp2_felem_copy", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

    Definition Fp2_add : string * Syntax.func :=
      ("bn446_Fp2_add", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    Definition Fp2_sub : string * Syntax.func :=
      ("bn446_Fp2_sub", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "inx"; expr.var "iny"]);
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")])
      ))).

    Definition Fp2_zero : string * Syntax.func :=
      ("bn446_Fp2_zero", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 0]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    Definition Fp2_one : string * Syntax.func :=
      ("bn446_Fp2_one", (["out"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr.var "out"; expr.literal 1]);
        coq:(cmd.call [] (AbstractField.from_word (F:=F)) [expr_2nd_felem (expr.var "out"); expr.literal 0])
      ))).

    (* ================================================================ *)
    (* beta-dependent operations: mul, sqr, inv                          *)
    (* beta = -1: ac - bd replaces ac + beta*bd, etc.                    *)
    (* ================================================================ *)

    (* Fp2 multiplication: (a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u
       Karatsuba with 3 Fp muls, 2 Fp adds, 3 Fp subs. No multiply-by-|beta|! *)
    Definition Fp2_mul : string * Syntax.func :=
      ("bn446_Fp2_mul", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
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
        (* out.re = v0 - v1 = ac - bd  (beta = -1) *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
      ))).

    (* Fp2 squaring: (a+bu)^2 = (a^2 - b^2) + 2ab*u *)
    Definition Fp2_sqr : string * Syntax.func :=
      ("bn446_Fp2_square", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        (* v0 = a^2 *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v0"; expr.var "inx"]);
        (* v1 = b^2 *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = a * b *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = 2*a*b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out")]);
        (* out.re = a^2 - b^2  (beta = -1) *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
      ))).

    (* Fp2 inversion: (a+bu)^(-1) = (a, -b) / (a^2 + b^2)
       norm = a^2 - beta*b^2 = a^2 + b^2  (since beta = -1) *)
    Definition Fp2_inv : string * Syntax.func :=
      ("bn446_Fp2_inv", (["out"; "inx"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as asq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as bsq;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as norm;
        (* asq = a^2 *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "asq"; expr.var "inx"]);
        (* bsq = b^2 *)
        coq:(cmd.call [] (AbstractField.square (F:=F)) [expr.var "bsq"; expr_2nd_felem (expr.var "inx")]);
        (* norm = a^2 + b^2 *)
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
    (* fp2_mul_xi: multiply by xi = (2, 3) in Fp2                       *)
    (* (a + bu)*(2 + 3u) = (2a - 3b) + (3a + 2b)u                      *)
    (* Multiply-by-2: x -> x+x (1 add)                                  *)
    (* Multiply-by-3: x -> x+x -> x+x+x (2 adds)                       *)
    (* ================================================================ *)

    Definition Fp2_mul_xi : string * Syntax.func :=
      ("bn446_Fp2_mul_xi", (["out"; "x"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as tmp_a3;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as tmp_b3;
        (* tmp_a3 = 3*a: 2a -> 2a+a *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a3"; expr.var "x"; expr.var "x"]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_a3"; expr.var "tmp_a3"; expr.var "x"]);
        (* tmp_b3 = 3*b: 2b -> 2b+b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b3"; expr_2nd_felem (expr.var "x"); expr_2nd_felem (expr.var "x")]);
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "tmp_b3"; expr.var "tmp_b3"; expr_2nd_felem (expr.var "x")]);
        (* out.re = 2a - 3b: first compute 2a *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "x"; expr.var "x"]);
        (* out.re = 2a - 3b *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "out"; expr.var "tmp_b3"]);
        (* out.im = 3a + 2b: first compute 2b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x"); expr_2nd_felem (expr.var "x")]);
        (* out.im = 3a + 2b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "tmp_a3"; expr_2nd_felem (expr.var "out")])
      ))).

    (* Fp2 conjugate: conj(a + bu) = a - bu *)
    Definition Fp2_conjugate : string * Syntax.func :=
      ("bn446_Fp2_conjugate", (["out"; "x"], []:list String.string, bedrock_func_body:(
        coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
        coq:(cmd.call [] (@AbstractField.opp _ prime_field_parameters) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
      ))).

End bn446_Fp2.
