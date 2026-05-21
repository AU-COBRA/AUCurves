(** * BW6-761 Final Exponentiation — bedrock2 function bodies.

    Defines the bedrock2 function bodies for the BW6-761 final
    exponentiation. The final exponentiation computes f^{(p^6-1)/r}
    in two parts:

    Easy part: f^{(p^3-1)(p+1)}
      - p^3-1: conjugate(f) * inv(f) on Fp6 = Fp3[w]/(w^2-zeta)
        (here "conjugate" negates the c1 component since w^{p^3} = -w)
      - p+1:  frob(result) * result

    Hard part: f^{h/r} where h = (p^6-p^3+1)/3 (Brezing-Weng / Hayashida).
      For BW6-761 with seed u = 0x8508c00000000001 (64 bits), the
      hard part is implemented as a composition of pow_u, frob (pi),
      frob_p2 (pi^2), frob_p3 (pi^3), and multiplications, following
      the structure of Hayashida-Hayasaka-Teruya 2020.

    Note: this file fixes the *body* — i.e. the bedrock2 cmd.cmd
    AST — together with its boilerplate specs. Algebraic correctness
    (showing the body computes f^{(p^6-1)/r}) is NOT proven here; the
    specs only guarantee bound preservation (loose Fp6 output), the
    same style as BLS24_509_FinalExp.v.

    Functions defined:
    - bw6_fp6_conjugate: negate c1 component of Fp6
    - bw6_fp6_pow_abs_u: exponentiate by |u| (square-and-multiply)
    - bw6_fp6_pow_u: exponentiate by u (= pow_abs_u, u positive)
    - bw6_fp6_frob: Frobenius pi (x -> x^p) on Fp6
    - bw6_fp6_frob_p2: Frobenius pi^2 (x -> x^{p^2}) on Fp6
    - bw6_fp6_frob_p3: Frobenius pi^3 (x -> x^{p^3}) on Fp6
    - bw6_final_exp_easy: easy part of final exponentiation
    - bw6_final_exp_hard: hard part (Hayashida-style chain)
    - bw6_final_exp: combines easy + hard
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
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BW6_FinalExp.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BW6-761 base field via Instances                                *)
    (* ============================================================== *)

    Existing Instances
      bw6_prime_params
      bw6_prime_params_ok
      prime_field_parameters
      bw6_Fp_repr
      bw6_Fp_repr_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp3 := (Fp * Fp * Fp)%type.
    Local Notation Fp6 := (Fp3 * Fp3)%type.

    (* ============================================================== *)
    (* Field extension instances                                       *)
    (* ============================================================== *)

    Existing Instances
      bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok
      bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok.

    (* ============================================================== *)
    (* Offset and address helpers                                      *)
    (* ============================================================== *)

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Notation fp3_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp3))).

    (* Fp3 component offsets (slots c0, c1, c2 each fp_felem_offset apart). *)
    Local Definition expr_fp3_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp3_c1 (x : Syntax.expr.expr) :=
      Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp_felem_offset).
    Local Definition expr_fp3_c2 (x : Syntax.expr.expr) :=
      Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal (2 * fp_felem_offset)).

    (* Fp6 component offsets (slots c0, c1 each fp3_felem_offset apart). *)
    Local Definition expr_fp6_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp6_c1 (x : Syntax.expr.expr) :=
      Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp3_felem_offset).

    (* ============================================================== *)
    (* Function name helpers                                           *)
    (* ============================================================== *)

    Let fp3_opp_name : string := AbstractField.opp (F:=Fp3).
    Let fp3_copy_name : string := AbstractField.felem_copy (F:=Fp3).
    Let fp3_mul_name : string := AbstractField.mul (F:=Fp3).
    Let fp6_mul_name : string := AbstractField.mul (F:=Fp6).
    Let fp6_sqr_name : string := AbstractField.square (F:=Fp6).
    Let fp6_inv_name : string := AbstractField.inv (F:=Fp6).
    Let fp6_copy_name : string := AbstractField.felem_copy (F:=Fp6).

    (* ============================================================== *)
    (* FElem type notations                                            *)
    (* ============================================================== *)

    Local Notation FElem_Fp6 :=
      (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
    Local Notation FElem_Fp3 :=
      (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
    Local Notation Fp6_bounded :=
      (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
    Local Notation Fp6_tight :=
      (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
    Local Notation Fp6_loose :=
      (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
    Local Notation Fp6_felem :=
      (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
    Local Notation Fp3_felem :=
      (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
    Local Notation Fp3_bounded :=
      (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
    Local Notation Fp3_tight :=
      (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).

    Local Typeclasses Opaque bw6_Fp6_params.
    Local Typeclasses Opaque bw6_Fp3_params.

    (* ============================================================== *)
    (* cmd_seq_list helper                                              *)
    (* ============================================================== *)

    Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cmds with
      | [] => Syntax.cmd.skip
      | [c] => c
      | c :: rest => Syntax.cmd.seq c (cmd_seq_list rest)
      end.

    (* ============================================================== *)
    (* BW6-761 parameter                                               *)
    (* ============================================================== *)

    (** Seed u = 0x8508c00000000001 (64 bits, positive — same seed as BLS12-377). *)
    Let bw6_u_abs : Z := 0x8508c00000000001.

    (* ============================================================== *)
    (* Fp6 conjugation                                                 *)
    (*                                                                  *)
    (* For Fp6 = Fp3[w]/(w^2-zeta) = (c0, c1):                        *)
    (*   conjugate(c0, c1) = (c0, -c1)                                *)
    (* This is the unitary inverse for elements in the p^3-1            *)
    (* cyclotomic subgroup.                                            *)
    (* The Fp3 representation is 3 consecutive Fp slots, so negating   *)
    (* "c1 of Fp6" means negating the Fp3 starting at offset           *)
    (* fp3_felem_offset.                                               *)
    (* ============================================================== *)

    Let fp6_conjugate_name : string := "bw6_fp6_conjugate".

    Definition bw6_fp6_conjugate : function_t :=
      (fp6_conjugate_name,
       (["out"; "x"], []:list String.string,
        cmd_seq_list [
          (* out.c0 = x.c0 *)
          Syntax.cmd.call [] fp3_copy_name
            [expr_fp6_c0 (Syntax.expr.var "out");
             expr_fp6_c0 (Syntax.expr.var "x")];
          (* out.c1 = -x.c1 *)
          Syntax.cmd.call [] fp3_opp_name
            [expr_fp6_c1 (Syntax.expr.var "out");
             expr_fp6_c1 (Syntax.expr.var "x")]
        ])).

    (* ============================================================== *)
    (* Fp6 exponentiation by |u| = u (BW6 seed is positive)            *)
    (*                                                                  *)
    (* u = 0x8508c00000000001 (64 bits)                                *)
    (* Left-to-right binary method, MSB-first.                         *)
    (* MSB (bit 63) initializes result = base.                         *)
    (* Loop processes bits 62..0:                                      *)
    (*   result = result^2                                             *)
    (*   if bit is set: result = result * base                         *)
    (* ============================================================== *)

    Let fp6_pow_abs_u_name : string := "bw6_fp6_pow_abs_u".

    Local Definition pow_abs_u_loop : Syntax.cmd.cmd :=
      cmd_seq_list [
        Syntax.cmd.set "i"
          (Syntax.expr.op Syntax.bopname.sub
            (Syntax.expr.var "i") (Syntax.expr.literal 1));
        (* result = result^2 *)
        Syntax.cmd.call [] fp6_sqr_name
          [Syntax.expr.var "result"; Syntax.expr.var "result"];
        (* if bit i of u is set: result = result * base *)
        Syntax.cmd.set "bit"
          (Syntax.expr.op Syntax.bopname.and
            (Syntax.expr.op Syntax.bopname.sru
              (Syntax.expr.literal bw6_u_abs) (Syntax.expr.var "i"))
            (Syntax.expr.literal 1));
        Syntax.cmd.cond (Syntax.expr.var "bit")
          (Syntax.cmd.call [] fp6_mul_name
            [Syntax.expr.var "result";
             Syntax.expr.var "result";
             Syntax.expr.var "base"])
          Syntax.cmd.skip
      ].

    Definition bw6_fp6_pow_abs_u : function_t :=
      (fp6_pow_abs_u_name,
       (["out"; "x"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as base;
          coq:(cmd_seq_list [
            (* base = x *)
            Syntax.cmd.call [] fp6_copy_name
              [Syntax.expr.var "base"; Syntax.expr.var "x"];
            (* result = base (bit 63 = MSB = 1) *)
            Syntax.cmd.call [] fp6_copy_name
              [Syntax.expr.var "result"; Syntax.expr.var "base"];
            (* loop from i = 63 down to i = 0 (63 iterations) *)
            Syntax.cmd.set "i" (Syntax.expr.literal 63);
            Syntax.cmd.while (Syntax.expr.var "i") pow_abs_u_loop;
            (* copy result to out *)
            Syntax.cmd.call [] fp6_copy_name
              [Syntax.expr.var "out"; Syntax.expr.var "result"]
          ])
        ))).

    (* ============================================================== *)
    (* Fp6 exponentiation by u (positive seed: same as |u|)            *)
    (* ============================================================== *)

    Let fp6_pow_u_name : string := "bw6_fp6_pow_u".

    Definition bw6_fp6_pow_u : function_t :=
      (fp6_pow_u_name,
       (["out"; "x"], []:list String.string,
        bedrock_func_body:(
          coq:(cmd_seq_list [
            Syntax.cmd.call [] fp6_pow_abs_u_name
              [Syntax.expr.var "out"; Syntax.expr.var "x"]
          ])
        ))).

    (* ============================================================== *)
    (* Frobenius endomorphisms on the tower                            *)
    (*                                                                  *)
    (* Following gnark-crypto/ecc/bw6-761/internal/fptower/frobenius:  *)
    (* the Frobenius pi acts on Fp6 = Fp3[w]/(w^2 - zeta) by           *)
    (* per-Fp-component scaling.  For B0 = (a0, a1, a2) and            *)
    (* B1 = (b0, b1, b2):                                              *)
    (*                                                                  *)
    (*   pi(B0 + B1·w) = (a0,        alpha·a1,           alpha^2·a2)   *)
    (*                 + (sa·b0,     sa·alpha·b1,        sa·alpha^2·b2)·w *)
    (*                                                                  *)
    (*  where alpha = (-4)^((p-1)/3) mod p is a primitive cube root    *)
    (*  of 1 in Fp, and sa = sqrt(alpha) mod p.                        *)
    (*                                                                  *)
    (* Five Fp scalars per Frobenius level: (alpha, alpha^2) for c0    *)
    (* and (sa, sa·alpha, sa·alpha^2) for c1.  pi^2 uses each scalar   *)
    (* squared.  pi^3 acts trivially on Fp3 (alpha^3 = 1) and pi^3(w) *)
    (* = -w, so only the c1 component is negated by mul-by-(-1).      *)
    (*                                                                  *)
    (* Per-function calling convention:                                *)
    (*  - [gamma_fp3]:  pointer to an Fp3-shaped blob storing          *)
    (*                  [g_a0=ignored; alpha; alpha^2] (Fp slots 1,2).*)
    (*  - [gamma_fp6]:  pointer to an Fp3-shaped blob storing          *)
    (*                  [sa; sa·alpha; sa·alpha^2] (all three slots).  *)
    (*  - [gamma_fp6_p3] (pi^3 only): pointer to an Fp3 blob whose    *)
    (*                  c0 slot holds -1 (other slots ignored).        *)
    (* ============================================================== *)

    (* -------------------------------------------------------------- *)
    (* bw6_fp6_frob: Frobenius pi on Fp6                               *)
    (*                                                                  *)
    (* Parameters:                                                     *)
    (*   out:          output Fp6                                      *)
    (*   x:            input Fp6                                       *)
    (*   gamma_fp3:    Fp3 blob holding [_; alpha; alpha^2]            *)
    (*   gamma_fp6:    Fp3 blob holding [sa; sa·alpha; sa·alpha^2]     *)
    (* -------------------------------------------------------------- *)

    Let fp_mul_name  : string := AbstractField.mul (F:=Fp).
    Let fp_copy_name : string := AbstractField.felem_copy (F:=Fp).

    Let fp6_frob_name : string := "bw6_fp6_frob".

    Definition bw6_fp6_frob : function_t :=
      (fp6_frob_name,
       (["out"; "x"; "gamma_fp3"; "gamma_fp6"],
        []:list String.string,
        bedrock_func_body:(
          coq:(cmd_seq_list [
            (* c0 of Fp6 = Fp3 (a0, a1, a2): a0 identity, scale a1, a2 *)
            (* out.c0.a0 = x.c0.a0 *)
            Syntax.cmd.call [] fp_copy_name
              [expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "x"))];
            (* out.c0.a1 = x.c0.a1 * gamma_fp3.c1 (= alpha) *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "x"));
               expr_fp3_c1 (Syntax.expr.var "gamma_fp3")];
            (* out.c0.a2 = x.c0.a2 * gamma_fp3.c2 (= alpha^2) *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "x"));
               expr_fp3_c2 (Syntax.expr.var "gamma_fp3")];
            (* c1 of Fp6 = Fp3 (b0, b1, b2): scale each by gamma_fp6's slots *)
            (* out.c1.b0 = x.c1.b0 * gamma_fp6.c0 (= sa) *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c0 (Syntax.expr.var "gamma_fp6")];
            (* out.c1.b1 = x.c1.b1 * gamma_fp6.c1 (= sa·alpha) *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c1 (Syntax.expr.var "gamma_fp6")];
            (* out.c1.b2 = x.c1.b2 * gamma_fp6.c2 (= sa·alpha^2) *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c2 (Syntax.expr.var "gamma_fp6")]
          ])
        ))).

    (* -------------------------------------------------------------- *)
    (* bw6_fp6_frob_p2: Frobenius pi^2 on Fp6                          *)
    (* Same shape as pi, but with each gamma squared.                  *)
    (* -------------------------------------------------------------- *)

    Let fp6_frob_p2_name : string := "bw6_fp6_frob_p2".

    Definition bw6_fp6_frob_p2 : function_t :=
      (fp6_frob_p2_name,
       (["out"; "x"; "gamma_fp3_p2"; "gamma_fp6_p2"],
        []:list String.string,
        bedrock_func_body:(
          coq:(cmd_seq_list [
            Syntax.cmd.call [] fp_copy_name
              [expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "x"))];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "x"));
               expr_fp3_c1 (Syntax.expr.var "gamma_fp3_p2")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "x"));
               expr_fp3_c2 (Syntax.expr.var "gamma_fp3_p2")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c0 (Syntax.expr.var "gamma_fp6_p2")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c1 (Syntax.expr.var "gamma_fp6_p2")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c2 (Syntax.expr.var "gamma_fp6_p2")]
          ])
        ))).

    (* -------------------------------------------------------------- *)
    (* bw6_fp6_frob_p3: Frobenius pi^3 on Fp6                          *)
    (* p^3 acts trivially on Fp3, so the c0 component is COPIED and    *)
    (* the c1 component is multiplied by -1 per Fp slot.               *)
    (* gamma_fp6_p3 has its c0 slot = -1 (mod p); other slots ignored. *)
    (* -------------------------------------------------------------- *)

    Let fp6_frob_p3_name : string := "bw6_fp6_frob_p3".

    Definition bw6_fp6_frob_p3 : function_t :=
      (fp6_frob_p3_name,
       (["out"; "x"; "gamma_fp6_p3"],
        []:list String.string,
        bedrock_func_body:(
          coq:(cmd_seq_list [
            (* Copy c0 (pi^3 trivial on Fp3) *)
            Syntax.cmd.call [] fp_copy_name
              [expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "x"))];
            Syntax.cmd.call [] fp_copy_name
              [expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "x"))];
            Syntax.cmd.call [] fp_copy_name
              [expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "x"))];
            (* Negate c1 by mul-by-(-1), per Fp slot *)
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c0 (Syntax.expr.var "gamma_fp6_p3")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c0 (Syntax.expr.var "gamma_fp6_p3")];
            Syntax.cmd.call [] fp_mul_name
              [expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "out"));
               expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "x"));
               expr_fp3_c0 (Syntax.expr.var "gamma_fp6_p3")]
          ])
        ))).

    (* ============================================================== *)
    (* Easy part of final exponentiation                               *)
    (*                                                                  *)
    (* f^{(p^3 - 1)(p + 1)}:                                          *)
    (*   Step 1: r1 = conjugate(f) * inv(f)   = f^{p^3 - 1}           *)
    (*   Step 2: result = frob(r1) * r1       = r1^{p + 1}            *)
    (* ============================================================== *)

    Let final_exp_easy_name : string := "bw6_final_exp_easy".

    Local Definition final_exp_easy_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* t0 = conjugate(f) *)
        Syntax.cmd.call [] fp6_conjugate_name
          [Syntax.expr.var "t0"; Syntax.expr.var "f"];
        (* t1 = inv(f) *)
        Syntax.cmd.call [] fp6_inv_name
          [Syntax.expr.var "t1"; Syntax.expr.var "f"];
        (* t0 = t0 * t1 = f^{p^3 - 1} *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "t0"; Syntax.expr.var "t0"; Syntax.expr.var "t1"];
        (* t1 = frob(t0) *)
        Syntax.cmd.call [] fp6_frob_name
          [Syntax.expr.var "t1"; Syntax.expr.var "t0";
           Syntax.expr.var "gamma_fp3"; Syntax.expr.var "gamma_fp6"];
        (* out = t1 * t0 = t0^{p + 1} *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "out"; Syntax.expr.var "t1"; Syntax.expr.var "t0"]
      ].

    Definition bw6_final_exp_easy : function_t :=
      (final_exp_easy_name,
       (["out"; "f"; "gamma_fp3"; "gamma_fp6"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t1;
          coq:(final_exp_easy_body)
        ))).

    (* ============================================================== *)
    (* Hard part of final exponentiation                               *)
    (*                                                                  *)
    (* For BW6-761 with seed u, the hard part h/r factors through      *)
    (* the Hayashida-Hayasaka-Teruya addition chain, which uses        *)
    (* roughly 8 calls to pow_u (= "Expt"), 3 calls to frob/frob_p2/   *)
    (* frob_p3, and ~10 mul/conjugate operations.                     *)
    (*                                                                  *)
    (* The chain below mirrors gnark-crypto's structure at the level    *)
    (* of which operations are sequenced. Local variables: a, b, c, d. *)
    (*                                                                  *)
    (* Steps (simplified — actual gnark uses ExptMinus1, ExptPlus1,     *)
    (* Expc1, Expc2 to fold the seed differences into combined chains  *)
    (* for performance; we use plain pow_u + corrections):              *)
    (*                                                                  *)
    (*  1. a = pow_u(f)             = f^u                              *)
    (*  2. b = a * f                = f^{u+1}                          *)
    (*  3. a = pow_u(b)             = f^{u(u+1)}                       *)
    (*  4. b = conj(b); b = a * b   = f^{(u-1)(u+1)} = f^{u^2-1}      *)
    (*  5. c = frob(b)              = f^{p(u^2-1)}                     *)
    (*  6. d = b * c                = f^{(p+1)(u^2-1)}                 *)
    (*  7. a = pow_u(d)                                                 *)
    (*  8. b = pow_u(a)                                                 *)
    (*  9. c = frob_p2(d)                                               *)
    (* 10. a = a * c                                                    *)
    (* 11. b = pow_u(b)                                                 *)
    (* 12. c = frob_p3(d)                                               *)
    (* 13. b = b * c                                                    *)
    (* 14. a = a * b                                                    *)
    (* 15. b = sqr(f); b = b * f    = f^3                              *)
    (* 16. out = a * b                                                  *)
    (* ============================================================== *)

    Let final_exp_hard_name : string := "bw6_final_exp_hard".

    (* Inline pow_u call: out = pow_u(in) *)
    Local Definition inline_pow_u (out_var in_var : string) : Syntax.cmd.cmd :=
      Syntax.cmd.call [] fp6_pow_u_name
        [Syntax.expr.var out_var; Syntax.expr.var in_var].

    Local Definition final_exp_hard_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Step 1: a = pow_u(f) *)
        inline_pow_u "a" "f";

        (* Step 2: b = a * f *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "b"; Syntax.expr.var "a"; Syntax.expr.var "f"];

        (* Step 3: a = pow_u(b) *)
        inline_pow_u "a" "b";

        (* Step 4a: c = conj(b) — out-of-place to avoid aliasing *)
        Syntax.cmd.call [] fp6_conjugate_name
          [Syntax.expr.var "c"; Syntax.expr.var "b"];

        (* Step 4b: b = a * c *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "b"; Syntax.expr.var "a"; Syntax.expr.var "c"];

        (* Step 5: c = frob(b) *)
        Syntax.cmd.call [] fp6_frob_name
          [Syntax.expr.var "c"; Syntax.expr.var "b";
           Syntax.expr.var "gamma_fp3"; Syntax.expr.var "gamma_fp6"];

        (* Step 6: d = b * c *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "d"; Syntax.expr.var "b"; Syntax.expr.var "c"];

        (* Step 7: a = pow_u(d) *)
        inline_pow_u "a" "d";

        (* Step 8: b = pow_u(a) *)
        inline_pow_u "b" "a";

        (* Step 9: c = frob_p2(d) *)
        Syntax.cmd.call [] fp6_frob_p2_name
          [Syntax.expr.var "c"; Syntax.expr.var "d";
           Syntax.expr.var "gamma_fp3_p2"; Syntax.expr.var "gamma_fp6_p2"];

        (* Step 10: a = a * c *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "a"; Syntax.expr.var "a"; Syntax.expr.var "c"];

        (* Step 11: b = pow_u(b) *)
        inline_pow_u "b" "b";

        (* Step 12: c = frob_p3(d) *)
        Syntax.cmd.call [] fp6_frob_p3_name
          [Syntax.expr.var "c"; Syntax.expr.var "d";
           Syntax.expr.var "gamma_fp6_p3"];

        (* Step 13: b = b * c *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "b"; Syntax.expr.var "b"; Syntax.expr.var "c"];

        (* Step 14: a = a * b *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "a"; Syntax.expr.var "a"; Syntax.expr.var "b"];

        (* Step 15a: b = sqr(f) *)
        Syntax.cmd.call [] fp6_sqr_name
          [Syntax.expr.var "b"; Syntax.expr.var "f"];

        (* Step 15b: b = b * f *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "b"; Syntax.expr.var "b"; Syntax.expr.var "f"];

        (* Step 16: out = a * b *)
        Syntax.cmd.call [] fp6_mul_name
          [Syntax.expr.var "out"; Syntax.expr.var "a"; Syntax.expr.var "b"]
      ].

    Definition bw6_final_exp_hard : function_t :=
      (final_exp_hard_name,
       (["out"; "f";
         "gamma_fp3"; "gamma_fp6";
         "gamma_fp3_p2"; "gamma_fp6_p2";
         "gamma_fp6_p3"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as a;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as b;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as c;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as d;
          coq:(final_exp_hard_body)
        ))).

    (* ============================================================== *)
    (* Full final exponentiation                                       *)
    (*                                                                  *)
    (* final_exp(f) = final_exp_hard(final_exp_easy(f))                *)
    (* ============================================================== *)

    Definition bw6_final_exp : function_t :=
      ("bw6_final_exp",
       (["out"; "f";
         "gamma_fp3"; "gamma_fp6";
         "gamma_fp3_p2"; "gamma_fp6_p2";
         "gamma_fp6_p3"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as easy_result;
          coq:(cmd_seq_list [
            (* Easy part *)
            Syntax.cmd.call [] final_exp_easy_name
              [Syntax.expr.var "easy_result"; Syntax.expr.var "f";
               Syntax.expr.var "gamma_fp3"; Syntax.expr.var "gamma_fp6"];
            (* Hard part *)
            Syntax.cmd.call [] final_exp_hard_name
              [Syntax.expr.var "out"; Syntax.expr.var "easy_result";
               Syntax.expr.var "gamma_fp3"; Syntax.expr.var "gamma_fp6";
               Syntax.expr.var "gamma_fp3_p2"; Syntax.expr.var "gamma_fp6_p2";
               Syntax.expr.var "gamma_fp6_p3"]
          ])
        ))).

    (* ============================================================== *)
    (* Specs                                                            *)
    (* ============================================================== *)

    Instance spec_of_bw6_fp6_conjugate : spec_of fp6_conjugate_name :=
      fnspec! fp6_conjugate_name (pout px : word)
        / (old_out x : Fp6_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          (FElem_Fp6 pout old_out * (FElem_Fp6 px x * Rr))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out * (FElem_Fp6 px x * Rr))%sep mem' }.

    Instance spec_of_bw6_fp6_pow_abs_u : spec_of fp6_pow_abs_u_name :=
      fnspec! fp6_pow_abs_u_name (pout px : word)
        / (old_out x : Fp6_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          (FElem_Fp6 pout old_out * (FElem_Fp6 px x * Rr))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out * (FElem_Fp6 px x * Rr))%sep mem' }.

    Instance spec_of_bw6_fp6_pow_u : spec_of fp6_pow_u_name :=
      fnspec! fp6_pow_u_name (pout px : word)
        / (old_out x : Fp6_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          (FElem_Fp6 pout old_out * (FElem_Fp6 px x * Rr))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out * (FElem_Fp6 px x * Rr))%sep mem' }.

    Instance spec_of_bw6_fp6_frob : spec_of fp6_frob_name :=
      fnspec! fp6_frob_name
        (pout px p_gfp3 p_gfp6 : word)
        / (old_out x : Fp6_felem) (gfp3 gfp6 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          Fp3_bounded Fp3_tight gfp3 /\
          Fp3_bounded Fp3_tight gfp6 /\
          (FElem_Fp6 pout old_out *
           (FElem_Fp6 px x *
            (FElem_Fp3 p_gfp3 gfp3 *
             (FElem_Fp3 p_gfp6 gfp6 * Rr))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 px x *
              (FElem_Fp3 p_gfp3 gfp3 *
               (FElem_Fp3 p_gfp6 gfp6 * Rr))))%sep mem' }.

    Instance spec_of_bw6_fp6_frob_p2 : spec_of fp6_frob_p2_name :=
      fnspec! fp6_frob_p2_name
        (pout px p_gfp3_p2 p_gfp6_p2 : word)
        / (old_out x : Fp6_felem) (gfp3 gfp6 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          Fp3_bounded Fp3_tight gfp3 /\
          Fp3_bounded Fp3_tight gfp6 /\
          (FElem_Fp6 pout old_out *
           (FElem_Fp6 px x *
            (FElem_Fp3 p_gfp3_p2 gfp3 *
             (FElem_Fp3 p_gfp6_p2 gfp6 * Rr))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 px x *
              (FElem_Fp3 p_gfp3_p2 gfp3 *
               (FElem_Fp3 p_gfp6_p2 gfp6 * Rr))))%sep mem' }.

    Instance spec_of_bw6_fp6_frob_p3 : spec_of fp6_frob_p3_name :=
      fnspec! fp6_frob_p3_name
        (pout px p_gfp6_p3 : word)
        / (old_out x : Fp6_felem) (gfp6 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight x /\
          Fp3_bounded Fp3_tight gfp6 /\
          (FElem_Fp6 pout old_out *
           (FElem_Fp6 px x *
            (FElem_Fp3 p_gfp6_p3 gfp6 * Rr)))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 px x *
              (FElem_Fp3 p_gfp6_p3 gfp6 * Rr)))%sep mem' }.

    Instance spec_of_bw6_final_exp_easy : spec_of final_exp_easy_name :=
      fnspec! final_exp_easy_name
        (pout pf p_gfp3 p_gfp6 : word)
        / (old_out f : Fp6_felem) (gfp3 gfp6 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight f /\
          Fp3_bounded Fp3_tight gfp3 /\
          Fp3_bounded Fp3_tight gfp6 /\
          (FElem_Fp6 pf f *
           (FElem_Fp6 pout old_out *
            (FElem_Fp3 p_gfp3 gfp3 *
             (FElem_Fp3 p_gfp6 gfp6 * Rr))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 pf f *
              (FElem_Fp3 p_gfp3 gfp3 *
               (FElem_Fp3 p_gfp6 gfp6 * Rr))))%sep mem' }.

    Instance spec_of_bw6_final_exp_hard : spec_of final_exp_hard_name :=
      fnspec! final_exp_hard_name
        (pout pf
         p_gfp3 p_gfp6
         p_gfp3_p2 p_gfp6_p2
         p_gfp6_p3 : word)
        / (old_out f : Fp6_felem)
          (gfp3 gfp6 gfp3_p2 gfp6_p2 gfp6_p3 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight f /\
          Fp3_bounded Fp3_tight gfp3 /\
          Fp3_bounded Fp3_tight gfp6 /\
          Fp3_bounded Fp3_tight gfp3_p2 /\
          Fp3_bounded Fp3_tight gfp6_p2 /\
          Fp3_bounded Fp3_tight gfp6_p3 /\
          (FElem_Fp6 pf f *
           (FElem_Fp6 pout old_out *
            (FElem_Fp3 p_gfp3 gfp3 *
             (FElem_Fp3 p_gfp6 gfp6 *
              (FElem_Fp3 p_gfp3_p2 gfp3_p2 *
               (FElem_Fp3 p_gfp6_p2 gfp6_p2 *
                (FElem_Fp3 p_gfp6_p3 gfp6_p3 * Rr)))))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 pf f *
              (FElem_Fp3 p_gfp3 gfp3 *
               (FElem_Fp3 p_gfp6 gfp6 *
                (FElem_Fp3 p_gfp3_p2 gfp3_p2 *
                 (FElem_Fp3 p_gfp6_p2 gfp6_p2 *
                  (FElem_Fp3 p_gfp6_p3 gfp6_p3 * Rr)))))))%sep mem' }.

    Instance spec_of_bw6_final_exp : spec_of "bw6_final_exp" :=
      fnspec! "bw6_final_exp"
        (pout pf
         p_gfp3 p_gfp6
         p_gfp3_p2 p_gfp6_p2
         p_gfp6_p3 : word)
        / (old_out f : Fp6_felem)
          (gfp3 gfp6 gfp3_p2 gfp6_p2 gfp6_p3 : Fp3_felem) Rr,
      { requires tr mem :=
          Fp6_bounded Fp6_tight f /\
          Fp3_bounded Fp3_tight gfp3 /\
          Fp3_bounded Fp3_tight gfp6 /\
          Fp3_bounded Fp3_tight gfp3_p2 /\
          Fp3_bounded Fp3_tight gfp6_p2 /\
          Fp3_bounded Fp3_tight gfp6_p3 /\
          (FElem_Fp6 pf f *
           (FElem_Fp6 pout old_out *
            (FElem_Fp3 p_gfp3 gfp3 *
             (FElem_Fp3 p_gfp6 gfp6 *
              (FElem_Fp3 p_gfp3_p2 gfp3_p2 *
               (FElem_Fp3 p_gfp6_p2 gfp6_p2 *
                (FElem_Fp3 p_gfp6_p3 gfp6_p3 * Rr)))))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp6_bounded Fp6_loose out /\
            (FElem_Fp6 pout out *
             (FElem_Fp6 pf f *
              (FElem_Fp3 p_gfp3 gfp3 *
               (FElem_Fp3 p_gfp6 gfp6 *
                (FElem_Fp3 p_gfp3_p2 gfp3_p2 *
                 (FElem_Fp3 p_gfp6_p2 gfp6_p2 *
                  (FElem_Fp3 p_gfp6_p3 gfp6_p3 * Rr)))))))%sep mem' }.

    (* In-place pow_u spec: pout = px.  The function overwrites its input. *)
    Definition spec_of_bw6_fp6_pow_u_inplace
      (functions : @map.rep String.string
        (list String.string * list String.string * Syntax.cmd.cmd) _) : Prop :=
      forall p_x (x : Fp6_felem) Rr tr mem,
        Fp6_bounded Fp6_tight x ->
        (FElem_Fp6 p_x x * Rr)%sep mem ->
        WeakestPrecondition.call functions fp6_pow_u_name
          tr mem [p_x; p_x]
          (fun tr' mem' rets =>
             rets = [] /\ tr = tr' /\ exists out,
               Fp6_bounded Fp6_loose out /\
               (FElem_Fp6 p_x out * Rr)%sep mem').

    (* ============================================================== *)
    (* Collected function list                                         *)
    (* ============================================================== *)

    Definition bw6_final_exp_funcs : list function_t :=
      [ bw6_fp6_conjugate;
        bw6_fp6_pow_abs_u;
        bw6_fp6_pow_u;
        bw6_fp6_frob;
        bw6_fp6_frob_p2;
        bw6_fp6_frob_p3;
        bw6_final_exp_easy;
        bw6_final_exp_hard;
        bw6_final_exp ].

End BW6_FinalExp.
