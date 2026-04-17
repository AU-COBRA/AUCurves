(** * BLS24-509 Final Exponentiation — bedrock2 function bodies.

    Defines the bedrock2 function bodies for the BLS24-509 final
    exponentiation. The final exponentiation computes f^{(p^24-1)/r}
    in two parts:

    Easy part: f^{(p^12-1)(p^4+1)}
      - p^12-1: conjugate(f) * inv(f)
      - p^4+1:  frobenius_p4(result) * result

    Hard part: f^{3*(p^8-p^4+1)/r} using the decomposition:
      3*(p^8-p^4+1)/r = (u-1)^2 * (u+p) * (u^2+p^2) * (u^4+p^4-1) + 3

    where u = z = -0x800000ffff801 (the BLS24 seed, 52 bits).

    Functions defined:
    - bls24_fp24_conjugate: negate c1 component of Fp24
    - bls24_fp24_pow_abs_z: exponentiate by |z| (square-and-multiply)
    - bls24_fp24_pow_z: exponentiate by z (pow_abs_z then conjugate)
    - bls24_fp24_frob: Frobenius pi (x -> x^p) on Fp24
    - bls24_fp24_frob_p2: Frobenius pi^2 (x -> x^{p^2}) on Fp24
    - bls24_fp24_frob_p4: Frobenius pi^4 (x -> x^{p^4}) on Fp24
    - bls24_final_exp_easy: easy part of final exponentiation
    - bls24_final_exp_hard: hard part using addition chain
    - bls24_final_exp: combines easy + hard
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BLS24_FinalExp.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BLS24-509 prime parameters (from Instances)                     *)
    (* ============================================================== *)

    Existing Instances
      bls24_prime_params
      bls24_prime_params_ok
      prime_field_parameters
      bls24_Fp_repr
      bls24_Fp_repr_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := (Fp * Fp)%type.
    Local Notation Fp4 := (Fp2 * Fp2)%type.
    Local Notation Fp8 := (Fp4 * Fp4)%type.
    Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

    (* ============================================================== *)
    (* Field extension instances (from Instances)                      *)
    (* ============================================================== *)

    Existing Instances
      bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
      bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
      bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
      bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok.

    (* ============================================================== *)
    (* Offset and address helpers                                      *)
    (* ============================================================== *)

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Definition expr_fp_snd (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp_felem_offset).

    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
    Local Definition expr_fp4_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp4_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp2_felem_offset).

    Local Notation fp4_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp4))).
    Local Definition expr_fp8_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp8_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp4_felem_offset).

    Local Notation fp8_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp8))).
    Local Definition expr_fp24_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp24_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp8_felem_offset).
    Local Definition expr_fp24_c2 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal (2 * fp8_felem_offset)).

    (* ============================================================== *)
    (* Function name helpers                                           *)
    (* ============================================================== *)

    Let fp_opp_name : string := PrimeField.opp.
    Let fp_copy_name : string := PrimeField.felem_copy.
    Let from_word_name : string := PrimeField.from_word.
    Let fp2_mul_name : string := AbstractField.mul (F:=Fp2).
    Let fp2_copy_name : string := AbstractField.felem_copy (F:=Fp2).
    Let fp4_mul_name : string := AbstractField.mul (F:=Fp4).
    Let fp4_copy_name : string := AbstractField.felem_copy (F:=Fp4).
    Let fp8_mul_name : string := AbstractField.mul (F:=Fp8).
    Let fp8_opp_name : string := AbstractField.opp (F:=Fp8).
    Let fp8_copy_name : string := AbstractField.felem_copy (F:=Fp8).
    Let fp24_mul_name : string := AbstractField.mul (F:=Fp24).
    Let fp24_sqr_name : string := AbstractField.square (F:=Fp24).
    Let fp24_inv_name : string := AbstractField.inv (F:=Fp24).
    Let fp24_copy_name : string := AbstractField.felem_copy (F:=Fp24).

    (* ============================================================== *)
    (* FElem type notations                                            *)
    (* ============================================================== *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation FElem_Fp4 := (@AbstractField.FElem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation FElem_Fp8 := (@AbstractField.FElem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation FElem_Fp24 := (@AbstractField.FElem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_bounded := (@AbstractField.bounded_by _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_tight := (@AbstractField.tight_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_loose := (@AbstractField.loose_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_felem := (@AbstractField.felem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp8_bounded := (@AbstractField.bounded_by _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp8_tight := (@AbstractField.tight_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp8_felem := (@AbstractField.felem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp4_felem := (@AbstractField.felem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp2_felem := (@AbstractField.felem _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).

    Local Typeclasses Opaque bls24_Fp24_params.
    Local Typeclasses Opaque bls24_Fp8_params.
    Local Typeclasses Opaque bls24_Fp4_params.
    Local Typeclasses Opaque bls24_Fp2_params.

    (* ============================================================== *)
    (* cmd_seq_list helper                                              *)
    (* ============================================================== *)

    Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cmds with
      | [] => cmd.skip
      | [c] => c
      | c :: rest => cmd.seq c (cmd_seq_list rest)
      end.

    (* ============================================================== *)
    (* BLS24-509 parameter                                             *)
    (* ============================================================== *)

    Let bls24_z_abs : Z := 0x800000ffff801.

    (* ============================================================== *)
    (* Fp24 conjugation                                                *)
    (*                                                                  *)
    (* For Fp24 = Fp8[t]/(t^3-w) = (c0, c1, c2):                     *)
    (*   conjugate(c0, c1, c2) = (c0, -c1, c2)                       *)
    (* This is the unitary inverse for elements in the p^12-1         *)
    (* cyclotomic subgroup.                                            *)
    (* ============================================================== *)

    Let fp24_conjugate_name : string := "bls24_fp24_conjugate".

    Definition bls24_fp24_conjugate : function_t :=
      (fp24_conjugate_name,
       (["out"; "x"], []:list String.string,
        cmd_seq_list [
          (* out.c0 = x.c0 *)
          cmd.call [] fp8_copy_name
            [expr_fp24_c0 (expr.var "out");
             expr_fp24_c0 (expr.var "x")];
          (* out.c1 = -x.c1 *)
          cmd.call [] fp8_opp_name
            [expr_fp24_c1 (expr.var "out");
             expr_fp24_c1 (expr.var "x")];
          (* out.c2 = x.c2 *)
          cmd.call [] fp8_copy_name
            [expr_fp24_c2 (expr.var "out");
             expr_fp24_c2 (expr.var "x")]
        ])).

    (* ============================================================== *)
    (* Fp24 exponentiation by |z|                                      *)
    (*                                                                  *)
    (* |z| = 0x800000ffff801 (52 bits)                                *)
    (* Left-to-right binary method.                                    *)
    (* MSB (bit 51) initializes result = base.                         *)
    (* Loop processes bits 50..0:                                      *)
    (*   result = result^2                                             *)
    (*   if bit is set: result = result * base                         *)
    (* ============================================================== *)

    Let fp24_pow_abs_z_name : string := "bls24_fp24_pow_abs_z".

    Local Definition pow_abs_z_loop : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        (* result = result^2 *)
        cmd.call [] fp24_sqr_name
          [expr.var "result"; expr.var "result"];
        (* if bit i of |z| is set: result = result * base *)
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal bls24_z_abs) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp24_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bls24_fp24_pow_abs_z : function_t :=
      (fp24_pow_abs_z_name,
       (["out"; "x"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as base;
          coq:(cmd_seq_list [
            (* base = x *)
            cmd.call [] fp24_copy_name
              [expr.var "base"; expr.var "x"];
            (* result = base (bit 51 = MSB = 1) *)
            cmd.call [] fp24_copy_name
              [expr.var "result"; expr.var "base"];
            (* loop from i=51 down to i=0 (51 iterations) *)
            cmd.set "i" (expr.literal 51);
            cmd.while (expr.var "i") pow_abs_z_loop;
            (* copy result to out *)
            cmd.call [] fp24_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).

    (* ============================================================== *)
    (* Fp24 exponentiation by z                                        *)
    (*                                                                  *)
    (* z = -|z|, so f^z = conjugate(f^{|z|})                          *)
    (* (conjugate = unitary inverse in cyclotomic subgroup)             *)
    (* ============================================================== *)

    Let fp24_pow_z_name : string := "bls24_fp24_pow_z".

    Definition bls24_fp24_pow_z : function_t :=
      (fp24_pow_z_name,
       (["out"; "x"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as tmp;
          coq:(cmd_seq_list [
            (* tmp = x^{|z|} *)
            cmd.call [] fp24_pow_abs_z_name
              [expr.var "tmp"; expr.var "x"];
            (* out = conjugate(tmp) = x^z since z < 0 *)
            cmd.call [] fp24_conjugate_name
              [expr.var "out"; expr.var "tmp"]
          ])
        ))).

    (* ============================================================== *)
    (* Frobenius endomorphisms on the tower                            *)
    (*                                                                  *)
    (* The Frobenius pi: x -> x^p on each layer of the tower:         *)
    (*                                                                  *)
    (* fp2_frob(a0, a1) = (a0, -a1)  [since u^p = -u, p = 3 mod 4]  *)
    (*                                                                  *)
    (* fp4_frob(a0, a1) =                                              *)
    (*   (fp2_frob(a0), fp2_mul(fp2_frob(a1), gamma_fp4))             *)
    (*   where gamma_fp4 = xi^{(p-1)/2} in Fp2                        *)
    (*                                                                  *)
    (* fp8_frob(a0, a1) =                                              *)
    (*   (fp4_frob(a0), fp4_mul(fp4_frob(a1), gamma_fp8))             *)
    (*   where gamma_fp8 = v^{(p-1)/2} in Fp4                         *)
    (*                                                                  *)
    (* fp24_frob(c0, c1, c2) =                                         *)
    (*   (fp8_frob(c0),                                                *)
    (*    fp8_mul(fp8_frob(c1), gamma_fp24_1),                         *)
    (*    fp8_mul(fp8_frob(c2), gamma_fp24_2))                         *)
    (*   where gamma_fp24_i = w^{i(p-1)/3} in Fp8                     *)
    (*                                                                  *)
    (* For frob_p2: fp2_frob_p2 = identity on Fp2 (p^2 = 1 mod Fp2)  *)
    (*   fp4_frob_p2(a0, a1) = (a0, fp2_mul(a1, gamma_fp4_p2))       *)
    (*   fp8_frob_p2(a0, a1) =                                         *)
    (*     (fp4_frob_p2(a0), fp4_mul(fp4_frob_p2(a1), gamma_fp8_p2)) *)
    (*   fp24_frob_p2 analogous                                        *)
    (*                                                                  *)
    (* For frob_p4: similar pattern with p^4 gamma constants.          *)
    (*                                                                  *)
    (* Each Frobenius function takes the precomputed gamma constants   *)
    (* as pointer parameters.                                          *)
    (* ============================================================== *)

    (* -------------------------------------------------------------- *)
    (* Inline fp2_frob: (a0, a1) -> (a0, -a1)                         *)
    (* Applied in-place by negating the second Fp component.           *)
    (* -------------------------------------------------------------- *)

    Local Definition fp2_frob_inline (p_out p_in : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] fp_copy_name [p_out; p_in];
        cmd.call [] fp_opp_name [expr_fp_snd p_out; expr_fp_snd p_in]
      ].

    (* -------------------------------------------------------------- *)
    (* Inline fp4_frob: (a0, a1) -> (fp2_frob(a0), fp2_mul(fp2_frob(a1), gamma))  *)
    (* p_gamma_fp4 points to the Fp2 constant gamma_fp4               *)
    (* Needs an Fp2-sized temp for fp2_frob(a1) before multiply.      *)
    (* -------------------------------------------------------------- *)

    Local Definition fp4_frob_inline
      (p_out p_in p_gamma_fp4 p_tmp_fp2 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* out.c0 = fp2_frob(in.c0) *)
        fp2_frob_inline (expr_fp4_c0 p_out) (expr_fp4_c0 p_in);
        (* tmp_fp2 = fp2_frob(in.c1) *)
        fp2_frob_inline p_tmp_fp2 (expr_fp4_c1 p_in);
        (* out.c1 = tmp_fp2 * gamma_fp4 *)
        cmd.call [] fp2_mul_name
          [expr_fp4_c1 p_out; p_tmp_fp2; p_gamma_fp4]
      ].

    (* -------------------------------------------------------------- *)
    (* Inline fp8_frob: (e0, e1) -> (fp4_frob(e0), fp4_mul(fp4_frob(e1), gamma_fp8)) *)
    (* p_gamma_fp8 points to the Fp4 constant gamma_fp8               *)
    (* Needs Fp4-sized temp for fp4_frob(e1) and Fp2-sized temp.      *)
    (* -------------------------------------------------------------- *)

    Local Definition fp8_frob_inline
      (p_out p_in p_gamma_fp4 p_gamma_fp8
       p_tmp_fp2 p_tmp_fp4 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* out.c0 = fp4_frob(in.c0) *)
        fp4_frob_inline (expr_fp8_c0 p_out) (expr_fp8_c0 p_in)
          p_gamma_fp4 p_tmp_fp2;
        (* tmp_fp4 = fp4_frob(in.c1) *)
        fp4_frob_inline p_tmp_fp4 (expr_fp8_c1 p_in)
          p_gamma_fp4 p_tmp_fp2;
        (* out.c1 = tmp_fp4 * gamma_fp8 *)
        cmd.call [] fp4_mul_name
          [expr_fp8_c1 p_out; p_tmp_fp4; p_gamma_fp8]
      ].

    (* -------------------------------------------------------------- *)
    (* bls24_fp24_frob: Frobenius pi on Fp24                           *)
    (*                                                                  *)
    (* Parameters:                                                     *)
    (*   out:          output Fp24                                     *)
    (*   x:            input Fp24                                      *)
    (*   gamma_fp4:    Fp2 constant xi^{(p-1)/2}                       *)
    (*   gamma_fp8:    Fp4 constant v^{(p-1)/2}                        *)
    (*   gamma_fp24_1: Fp8 constant w^{(p-1)/3}                        *)
    (*   gamma_fp24_2: Fp8 constant w^{2(p-1)/3}                       *)
    (* -------------------------------------------------------------- *)

    Let fp24_frob_name : string := "bls24_fp24_frob".

    Definition bls24_fp24_frob : function_t :=
      (fp24_frob_name,
       (["out"; "x"; "gamma_fp4"; "gamma_fp8"; "gamma_fp24_1"; "gamma_fp24_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp_fp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp4)) as tmp_fp4;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp8)) as tmp_fp8;
          coq:(cmd_seq_list [
            (* out.c0 = fp8_frob(x.c0) *)
            fp8_frob_inline
              (expr_fp24_c0 (expr.var "out")) (expr_fp24_c0 (expr.var "x"))
              (expr.var "gamma_fp4") (expr.var "gamma_fp8")
              (expr.var "tmp_fp2") (expr.var "tmp_fp4");
            (* tmp_fp8 = fp8_frob(x.c1) *)
            fp8_frob_inline
              (expr.var "tmp_fp8") (expr_fp24_c1 (expr.var "x"))
              (expr.var "gamma_fp4") (expr.var "gamma_fp8")
              (expr.var "tmp_fp2") (expr.var "tmp_fp4");
            (* out.c1 = tmp_fp8 * gamma_fp24_1 *)
            cmd.call [] fp8_mul_name
              [expr_fp24_c1 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_1"];
            (* tmp_fp8 = fp8_frob(x.c2) *)
            fp8_frob_inline
              (expr.var "tmp_fp8") (expr_fp24_c2 (expr.var "x"))
              (expr.var "gamma_fp4") (expr.var "gamma_fp8")
              (expr.var "tmp_fp2") (expr.var "tmp_fp4");
            (* out.c2 = tmp_fp8 * gamma_fp24_2 *)
            cmd.call [] fp8_mul_name
              [expr_fp24_c2 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_2"]
          ])
        ))).

    (* -------------------------------------------------------------- *)
    (* Frobenius p^2 inlines                                           *)
    (*                                                                  *)
    (* fp2_frob_p2 = identity (p^2 = 1 in the Fp2 Galois group)      *)
    (* fp4_frob_p2(a0, a1) = (a0, fp2_mul(a1, gamma_fp4_p2))         *)
    (* fp8_frob_p2(e0, e1) =                                          *)
    (*   (fp4_frob_p2(e0), fp4_mul(fp4_frob_p2(e1), gamma_fp8_p2))   *)
    (* -------------------------------------------------------------- *)

    Local Definition fp4_frob_p2_inline
      (p_out p_in p_gamma_fp4_p2 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* out.c0 = in.c0 (identity on Fp2) *)
        cmd.call [] fp2_copy_name
          [expr_fp4_c0 p_out; expr_fp4_c0 p_in];
        (* out.c1 = fp2_mul(in.c1, gamma_fp4_p2) *)
        cmd.call [] fp2_mul_name
          [expr_fp4_c1 p_out; expr_fp4_c1 p_in; p_gamma_fp4_p2]
      ].

    Local Definition fp8_frob_p2_inline
      (p_out p_in p_gamma_fp4_p2 p_gamma_fp8_p2
       p_tmp_fp4 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* out.c0 = fp4_frob_p2(in.c0) *)
        fp4_frob_p2_inline (expr_fp8_c0 p_out) (expr_fp8_c0 p_in)
          p_gamma_fp4_p2;
        (* tmp_fp4 = fp4_frob_p2(in.c1) *)
        fp4_frob_p2_inline p_tmp_fp4 (expr_fp8_c1 p_in)
          p_gamma_fp4_p2;
        (* out.c1 = tmp_fp4 * gamma_fp8_p2 *)
        cmd.call [] fp4_mul_name
          [expr_fp8_c1 p_out; p_tmp_fp4; p_gamma_fp8_p2]
      ].

    Let fp24_frob_p2_name : string := "bls24_fp24_frob_p2".

    Definition bls24_fp24_frob_p2 : function_t :=
      (fp24_frob_p2_name,
       (["out"; "x"; "gamma_fp4_p2"; "gamma_fp8_p2";
         "gamma_fp24_p2_1"; "gamma_fp24_p2_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp4)) as tmp_fp4;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp8)) as tmp_fp8;
          coq:(cmd_seq_list [
            (* out.c0 = fp8_frob_p2(x.c0) *)
            fp8_frob_p2_inline
              (expr_fp24_c0 (expr.var "out")) (expr_fp24_c0 (expr.var "x"))
              (expr.var "gamma_fp4_p2") (expr.var "gamma_fp8_p2")
              (expr.var "tmp_fp4");
            (* tmp_fp8 = fp8_frob_p2(x.c1) *)
            fp8_frob_p2_inline
              (expr.var "tmp_fp8") (expr_fp24_c1 (expr.var "x"))
              (expr.var "gamma_fp4_p2") (expr.var "gamma_fp8_p2")
              (expr.var "tmp_fp4");
            (* out.c1 = tmp_fp8 * gamma_fp24_p2_1 *)
            cmd.call [] fp8_mul_name
              [expr_fp24_c1 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_p2_1"];
            (* tmp_fp8 = fp8_frob_p2(x.c2) *)
            fp8_frob_p2_inline
              (expr.var "tmp_fp8") (expr_fp24_c2 (expr.var "x"))
              (expr.var "gamma_fp4_p2") (expr.var "gamma_fp8_p2")
              (expr.var "tmp_fp4");
            (* out.c2 = tmp_fp8 * gamma_fp24_p2_2 *)
            cmd.call [] fp8_mul_name
              [expr_fp24_c2 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_p2_2"]
          ])
        ))).

    (* -------------------------------------------------------------- *)
    (* Frobenius p^4 inlines                                           *)
    (*                                                                  *)
    (* Same structure as frob_p2 but with p^4 gamma constants.         *)
    (* fp4_frob_p4(a0, a1) = (a0, fp2_mul(a1, gamma_fp4_p4))         *)
    (* fp8_frob_p4(e0, e1) =                                          *)
    (*   (fp4_frob_p4(e0), fp4_mul(fp4_frob_p4(e1), gamma_fp8_p4))   *)
    (* -------------------------------------------------------------- *)

    Local Definition fp4_frob_p4_inline
      (p_out p_in p_gamma_fp4_p4 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] fp2_copy_name
          [expr_fp4_c0 p_out; expr_fp4_c0 p_in];
        cmd.call [] fp2_mul_name
          [expr_fp4_c1 p_out; expr_fp4_c1 p_in; p_gamma_fp4_p4]
      ].

    Local Definition fp8_frob_p4_inline
      (p_out p_in p_gamma_fp4_p4 p_gamma_fp8_p4
       p_tmp_fp4 : Syntax.expr.expr) : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp4_frob_p4_inline (expr_fp8_c0 p_out) (expr_fp8_c0 p_in)
          p_gamma_fp4_p4;
        fp4_frob_p4_inline p_tmp_fp4 (expr_fp8_c1 p_in)
          p_gamma_fp4_p4;
        cmd.call [] fp4_mul_name
          [expr_fp8_c1 p_out; p_tmp_fp4; p_gamma_fp8_p4]
      ].

    Let fp24_frob_p4_name : string := "bls24_fp24_frob_p4".

    Definition bls24_fp24_frob_p4 : function_t :=
      (fp24_frob_p4_name,
       (["out"; "x"; "gamma_fp4_p4"; "gamma_fp8_p4";
         "gamma_fp24_p4_1"; "gamma_fp24_p4_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp4)) as tmp_fp4;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp8)) as tmp_fp8;
          coq:(cmd_seq_list [
            fp8_frob_p4_inline
              (expr_fp24_c0 (expr.var "out")) (expr_fp24_c0 (expr.var "x"))
              (expr.var "gamma_fp4_p4") (expr.var "gamma_fp8_p4")
              (expr.var "tmp_fp4");
            fp8_frob_p4_inline
              (expr.var "tmp_fp8") (expr_fp24_c1 (expr.var "x"))
              (expr.var "gamma_fp4_p4") (expr.var "gamma_fp8_p4")
              (expr.var "tmp_fp4");
            cmd.call [] fp8_mul_name
              [expr_fp24_c1 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_p4_1"];
            fp8_frob_p4_inline
              (expr.var "tmp_fp8") (expr_fp24_c2 (expr.var "x"))
              (expr.var "gamma_fp4_p4") (expr.var "gamma_fp8_p4")
              (expr.var "tmp_fp4");
            cmd.call [] fp8_mul_name
              [expr_fp24_c2 (expr.var "out");
               expr.var "tmp_fp8"; expr.var "gamma_fp24_p4_2"]
          ])
        ))).

    (* ============================================================== *)
    (* Easy part of final exponentiation                               *)
    (*                                                                  *)
    (* f^{(p^12 - 1)(p^4 + 1)}:                                       *)
    (*   Step 1: r1 = conjugate(f) * inv(f)   = f^{p^12 - 1}         *)
    (*   Step 2: result = frob_p4(r1) * r1    = r1^{p^4 + 1}         *)
    (* ============================================================== *)

    Let final_exp_easy_name : string := "bls24_final_exp_easy".

    Local Definition final_exp_easy_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* t0 = conjugate(f) *)
        cmd.call [] fp24_conjugate_name
          [expr.var "t0"; expr.var "f"];
        (* t1 = inv(f) *)
        cmd.call [] fp24_inv_name
          [expr.var "t1"; expr.var "f"];
        (* t0 = t0 * t1 = f^{p^12-1} *)
        cmd.call [] fp24_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];
        (* t1 = frob_p4(t0) *)
        cmd.call [] fp24_frob_p4_name
          [expr.var "t1"; expr.var "t0";
           expr.var "gamma_fp4_p4"; expr.var "gamma_fp8_p4";
           expr.var "gamma_fp24_p4_1"; expr.var "gamma_fp24_p4_2"];
        (* out = t1 * t0 = t0^{p^4+1} *)
        cmd.call [] fp24_mul_name
          [expr.var "out"; expr.var "t1"; expr.var "t0"]
      ].

    Definition bls24_final_exp_easy : function_t :=
      (final_exp_easy_name,
       (["out"; "f";
         "gamma_fp4_p4"; "gamma_fp8_p4";
         "gamma_fp24_p4_1"; "gamma_fp24_p4_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as t1;
          coq:(final_exp_easy_body)
        ))).

    (* ============================================================== *)
    (* Hard part of final exponentiation                               *)
    (*                                                                  *)
    (* 3*(p^8-p^4+1)/r = (u-1)^2*(u+p)*(u^2+p^2)*(u^4+p^4-1) + 3    *)
    (*                                                                  *)
    (* Following the Pairing.v spec (final_exp_hard):                  *)
    (*   t0 = f^u                                                      *)
    (*   t1 = t0 * conj(f)           = f^{u-1}                        *)
    (*   t2 = t1^u                   = f^{u(u-1)}                     *)
    (*   t3 = t2 * conj(t1)          = f^{(u-1)^2}                    *)
    (*   t4 = t3^u                   = f^{u(u-1)^2}                   *)
    (*   t5 = frob(t3)               = f^{p(u-1)^2}                   *)
    (*   t6 = t4 * t5                = f^{(u+p)(u-1)^2}               *)
    (*   t7 = t6^u                   = f^{u(u+p)(u-1)^2}              *)
    (*   t8 = t7^u                   = f^{u^2(u+p)(u-1)^2}            *)
    (*   t9 = frob_p2(t6)            = f^{p^2(u+p)(u-1)^2}            *)
    (*   t10 = t8 * t9               = f^{(u^2+p^2)(u+p)(u-1)^2}      *)
    (*   t11 = t10^u                 = f^{u(...)}                      *)
    (*   t12 = t11^u                 = f^{u^2(...)}                    *)
    (*   t13 = t12^u                 = f^{u^3(...)}                    *)
    (*   t14 = t13^u                 = f^{u^4(u^2+p^2)(u+p)(u-1)^2}   *)
    (*   t15 = frob_p4(t10)          = f^{p^4(u^2+p^2)(u+p)(u-1)^2}   *)
    (*   t16 = t14 * t15             = f^{(u^4+p^4)(...)}              *)
    (*   t17 = conj(t10)             = f^{-(u^2+p^2)(u+p)(u-1)^2}     *)
    (*   t18 = t16 * t17             = f^{(u^4+p^4-1)(...)}            *)
    (*   f_cubed = f^2 * f           = f^3                             *)
    (*   result = t18 * f_cubed      = f^{3*(p^8-p^4+1)/r}            *)
    (*                                                                  *)
    (* We reuse stack slots to minimize stack allocation.               *)
    (* Variable mapping (reusing 6 Fp24 slots):                        *)
    (*   a, b, c, d, e, g                                              *)
    (* ============================================================== *)

    Let final_exp_hard_name : string := "bls24_final_exp_hard".

    (* Inline pow_z call: out = pow_z(in) *)
    Local Definition inline_pow_z (out_var in_var : string) : Syntax.cmd.cmd :=
      cmd.call [] fp24_pow_z_name
        [expr.var out_var; expr.var in_var].

    Local Definition final_exp_hard_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Step 1: a = f^u *)
        inline_pow_z "a" "f";

        (* Step 2: b = a * conj(f) = f^{u-1} *)
        cmd.call [] fp24_conjugate_name
          [expr.var "b"; expr.var "f"];
        cmd.call [] fp24_mul_name
          [expr.var "b"; expr.var "a"; expr.var "b"];

        (* Step 3: a = b^u = f^{u(u-1)} *)
        inline_pow_z "a" "b";

        (* Step 4: c = a * conj(b) = f^{(u-1)^2} *)
        cmd.call [] fp24_conjugate_name
          [expr.var "c"; expr.var "b"];
        cmd.call [] fp24_mul_name
          [expr.var "c"; expr.var "a"; expr.var "c"];

        (* Step 5: a = c^u = f^{u(u-1)^2} *)
        inline_pow_z "a" "c";

        (* Step 6: b = frob(c) = f^{p(u-1)^2} *)
        cmd.call [] fp24_frob_name
          [expr.var "b"; expr.var "c";
           expr.var "gamma_fp4"; expr.var "gamma_fp8";
           expr.var "gamma_fp24_1"; expr.var "gamma_fp24_2"];

        (* Step 7: d = a * b = f^{(u+p)(u-1)^2} *)
        cmd.call [] fp24_mul_name
          [expr.var "d"; expr.var "a"; expr.var "b"];

        (* Step 8: a = d^u = f^{u(u+p)(u-1)^2} *)
        inline_pow_z "a" "d";

        (* Step 9: a = a^u = f^{u^2(u+p)(u-1)^2} *)
        inline_pow_z "a" "a";

        (* Step 10: b = frob_p2(d) = f^{p^2(u+p)(u-1)^2} *)
        cmd.call [] fp24_frob_p2_name
          [expr.var "b"; expr.var "d";
           expr.var "gamma_fp4_p2"; expr.var "gamma_fp8_p2";
           expr.var "gamma_fp24_p2_1"; expr.var "gamma_fp24_p2_2"];

        (* Step 11: e = a * b = f^{(u^2+p^2)(u+p)(u-1)^2} *)
        cmd.call [] fp24_mul_name
          [expr.var "e"; expr.var "a"; expr.var "b"];

        (* Steps 12-15: a = e^{u^4} (4 successive pow_z) *)
        inline_pow_z "a" "e";
        inline_pow_z "a" "a";
        inline_pow_z "a" "a";
        inline_pow_z "a" "a";

        (* Step 16: b = frob_p4(e) = f^{p^4(u^2+p^2)(u+p)(u-1)^2} *)
        cmd.call [] fp24_frob_p4_name
          [expr.var "b"; expr.var "e";
           expr.var "gamma_fp4_p4"; expr.var "gamma_fp8_p4";
           expr.var "gamma_fp24_p4_1"; expr.var "gamma_fp24_p4_2"];

        (* Step 17: a = a * b = f^{(u^4+p^4)(...)} *)
        cmd.call [] fp24_mul_name
          [expr.var "a"; expr.var "a"; expr.var "b"];

        (* Step 18: c = conj(e) = f^{-(u^2+p^2)(u+p)(u-1)^2} *)
        cmd.call [] fp24_conjugate_name
          [expr.var "c"; expr.var "e"];

        (* Step 19: a = a * c = f^{(u^4+p^4-1)(u^2+p^2)(u+p)(u-1)^2} *)
        cmd.call [] fp24_mul_name
          [expr.var "a"; expr.var "a"; expr.var "c"];

        (* Step 20: f^3 = f * f * f *)
        cmd.call [] fp24_sqr_name
          [expr.var "b"; expr.var "f"];
        cmd.call [] fp24_mul_name
          [expr.var "b"; expr.var "b"; expr.var "f"];

        (* result = a * f^3 = f^{(u-1)^2(u+p)(u^2+p^2)(u^4+p^4-1) + 3} *)
        cmd.call [] fp24_mul_name
          [expr.var "out"; expr.var "a"; expr.var "b"]
      ].

    Definition bls24_final_exp_hard : function_t :=
      (final_exp_hard_name,
       (["out"; "f";
         "gamma_fp4"; "gamma_fp8"; "gamma_fp24_1"; "gamma_fp24_2";
         "gamma_fp4_p2"; "gamma_fp8_p2"; "gamma_fp24_p2_1"; "gamma_fp24_p2_2";
         "gamma_fp4_p4"; "gamma_fp8_p4"; "gamma_fp24_p4_1"; "gamma_fp24_p4_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as a;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as b;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as c;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as d;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as e;
          coq:(final_exp_hard_body)
        ))).

    (* ============================================================== *)
    (* Full final exponentiation                                       *)
    (*                                                                  *)
    (* final_exp(f) = final_exp_hard(final_exp_easy(f))                *)
    (* ============================================================== *)

    Definition bls24_final_exp : function_t :=
      ("bls24_final_exp",
       (["out"; "f";
         "gamma_fp4"; "gamma_fp8"; "gamma_fp24_1"; "gamma_fp24_2";
         "gamma_fp4_p2"; "gamma_fp8_p2"; "gamma_fp24_p2_1"; "gamma_fp24_p2_2";
         "gamma_fp4_p4"; "gamma_fp8_p4"; "gamma_fp24_p4_1"; "gamma_fp24_p4_2"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp24)) as easy_result;
          coq:(cmd_seq_list [
            (* Easy part *)
            cmd.call [] final_exp_easy_name
              [expr.var "easy_result"; expr.var "f";
               expr.var "gamma_fp4_p4"; expr.var "gamma_fp8_p4";
               expr.var "gamma_fp24_p4_1"; expr.var "gamma_fp24_p4_2"];
            (* Hard part *)
            cmd.call [] final_exp_hard_name
              [expr.var "out"; expr.var "easy_result";
               expr.var "gamma_fp4"; expr.var "gamma_fp8";
               expr.var "gamma_fp24_1"; expr.var "gamma_fp24_2";
               expr.var "gamma_fp4_p2"; expr.var "gamma_fp8_p2";
               expr.var "gamma_fp24_p2_1"; expr.var "gamma_fp24_p2_2";
               expr.var "gamma_fp4_p4"; expr.var "gamma_fp8_p4";
               expr.var "gamma_fp24_p4_1"; expr.var "gamma_fp24_p4_2"]
          ])
        ))).

    (* ============================================================== *)
    (* Specs (Admitted -- proofs TBD)                                   *)
    (* ============================================================== *)

    Instance spec_of_bls24_fp24_conjugate : spec_of fp24_conjugate_name :=
      fnspec! fp24_conjugate_name (pout px : word)
        / (old_out x : Fp24_felem) Rr,
      { requires tr mem :=
          Fp24_bounded Fp24_tight x /\
          (FElem_Fp24 pout old_out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem' }.

    Instance spec_of_bls24_fp24_pow_abs_z : spec_of fp24_pow_abs_z_name :=
      fnspec! fp24_pow_abs_z_name (pout px : word)
        / (old_out x : Fp24_felem) Rr,
      { requires tr mem :=
          Fp24_bounded Fp24_tight x /\
          (FElem_Fp24 pout old_out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem' }.

    Instance spec_of_bls24_fp24_pow_z : spec_of fp24_pow_z_name :=
      fnspec! fp24_pow_z_name (pout px : word)
        / (old_out x : Fp24_felem) Rr,
      { requires tr mem :=
          Fp24_bounded Fp24_tight x /\
          (FElem_Fp24 pout old_out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out ⋆ (FElem_Fp24 px x ⋆ Rr)) mem' }.

    Instance spec_of_bls24_final_exp : spec_of "bls24_final_exp" :=
      fnspec! "bls24_final_exp"
        (pout pf
         p_gamma_fp4 p_gamma_fp8 p_gamma_fp24_1 p_gamma_fp24_2
         p_gamma_fp4_p2 p_gamma_fp8_p2 p_gamma_fp24_p2_1 p_gamma_fp24_p2_2
         p_gamma_fp4_p4 p_gamma_fp8_p4 p_gamma_fp24_p4_1 p_gamma_fp24_p4_2
           : word)
        / (old_out f : Fp24_felem) Rr,
      { requires tr mem :=
          Fp24_bounded Fp24_tight f /\
          (FElem_Fp24 pf f ⋆ (FElem_Fp24 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out ⋆ (FElem_Fp24 pf f ⋆ Rr)) mem' }.

    (* ============================================================== *)
    (* Collected function list                                         *)
    (* ============================================================== *)

    Definition bls24_final_exp_funcs : list function_t :=
      [ bls24_fp24_conjugate;
        bls24_fp24_pow_abs_z;
        bls24_fp24_pow_z;
        bls24_fp24_frob;
        bls24_fp24_frob_p2;
        bls24_fp24_frob_p4;
        bls24_final_exp_easy;
        bls24_final_exp_hard;
        bls24_final_exp ].

End BLS24_FinalExp.
