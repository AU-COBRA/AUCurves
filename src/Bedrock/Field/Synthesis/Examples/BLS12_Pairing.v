(** * BLS12-381 Pairing — bedrock2 compilation top-level.

    Instantiates the full field tower (Fp → Fp2 → Fp6 → Fp12) for
    BLS12-381 and defines bedrock2 function bodies for the optimal Ate
    pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 63 bits of the BLS parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (square-and-multiply with 1268-bit h3 exponent)
    - Top-level pairing chaining Miller loop + final exponentiation

    WP correctness proofs are in separate files:
    - BLS12_PowX.v: bls12_Fp12_pow_x_ok
    - BLS12_FinalExp.v: bls12_final_exp_ok
    - BLS12_MillerLoop.v: bls12_miller_loop_ok
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Algebra.Ring.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BLS12_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BLS12-381 prime parameters                                      *)
    (* ============================================================== *)

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_prime_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_prime_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bls12_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bls12_beta_nz : bls12_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bls12_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bls12_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    Lemma M_mod_4_3 : (Z.pos PrimeField.M_pos mod 4 =? 3) = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma bls12_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls12_beta).
    Proof.
      change bls12_beta with (QuadraticExtensionsFiat.Quad_non_res PrimeField.M_pos).
      exact (QuadraticExtensionsFiat.beta_is_non_res PrimeField.M_pos
               prime_bls12_381 bls12_M_big M_mod_4_3).
    Qed.

    (* Ring structure for Fp, needed by feval proofs *)
    Local Lemma Fp_ring_theory : ring_theory (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos) (@F.add PrimeField.M_pos) (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos) (@F.opp PrimeField.M_pos) eq.
    Proof. exact (Algebra.Ring.ring_theory_for_stdlib_tactic (zero:=@F.zero PrimeField.M_pos) (one:=@F.one PrimeField.M_pos)). Qed.
    Add Ring Fp_ring : Fp_ring_theory.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* ============================================================== *)
    (* Type notations                                                  *)
    (* ============================================================== *)

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* ============================================================== *)
    (* Fp2 instances                                                   *)
    (* ============================================================== *)

    Instance bls12_Fp2_params : AbstractField.FieldParameters Fp2 :=
      Fp2_field_parameters bls12_beta fp2_prefix.
    Instance bls12_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      Fp2_field_representation bls12_beta fp2_prefix.
    Instance bls12_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bls12_Fp6_params : AbstractField.FieldParameters Fp6 :=
      Fp6_field_parameters bls12_beta bls12_xi_re bls12_xi_im (fp6_prefix:=fp6_prefix).
    Instance bls12_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      Fp6_field_representation bls12_beta bls12_xi_re bls12_xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bls12_Fp12_params : AbstractField.FieldParameters Fp12 :=
      Fp12_field_parameters bls12_beta bls12_xi_re bls12_xi_im (fp12_prefix:=fp12_prefix).
    Instance bls12_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      Fp12_field_representation bls12_beta bls12_xi_re bls12_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bls12_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bls12_".

    (* ============================================================== *)
    (* Offset and address helpers                                      *)
    (* ============================================================== *)

    (* Fp-level offset within Fp2 *)
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Definition expr_fp_snd (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp_felem_offset).

    (* Fp2-level offsets within Fp6 *)
    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
    Local Definition expr_fp6_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp6_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp2_felem_offset).
    Local Definition expr_fp6_c2 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

    (* Fp6-level offsets within Fp12 *)
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
    Local Definition expr_fp12_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp12_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp6_felem_offset).

    (* ============================================================== *)
    (* Function name helpers                                           *)
    (* ============================================================== *)

    Let fp_add_name : string := PrimeField.add.
    Let fp_sub_name : string := PrimeField.sub.
    Let fp_mul_name : string := PrimeField.mul.
    Let fp_copy_name : string := PrimeField.felem_copy.
    Let from_word_name : string := PrimeField.from_word.
    Let fp2_add_name : string := AbstractField.add (F:=Fp2).
    Let fp2_sub_name : string := AbstractField.sub (F:=Fp2).
    Let fp2_mul_name : string := AbstractField.mul (F:=Fp2).
    Let fp2_sqr_name : string := AbstractField.square (F:=Fp2).
    Let fp2_inv_name : string := AbstractField.inv (F:=Fp2).
    Let fp2_opp_name : string := AbstractField.opp (F:=Fp2).
    Let fp2_copy_name : string := AbstractField.felem_copy (F:=Fp2).
    Let fp12_add_name : string := AbstractField.add (F:=Fp12).
    Let fp12_mul_name : string := AbstractField.mul (F:=Fp12).
    Let fp12_sqr_name : string := AbstractField.square (F:=Fp12).
    Let fp12_inv_name : string := AbstractField.inv (F:=Fp12).
    Let fp12_copy_name : string := AbstractField.felem_copy (F:=Fp12).
    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Let fp12_frobenius_p3_name : string := (fp12_prefix ++ "frobenius_p3")%string.
    Let fp2_mul_fp_name : string := "bls12_Fp2_mul_fp".
    Let make_line_name : string := "bls12_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by ξ = 1+u                    *)
    (*   (a0 + a1*u)(1 + u) = (a0 - a1) + (a0 + a1)*u  [since β=-1] *)
    (* ============================================================== *)

    Definition bls12_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd.call [] fp_copy_name
           [expr.var "tmp"; expr.var "x"]);
         coq:(cmd.call [] fp_copy_name
           [expr_fp_snd (expr.var "tmp"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp"; expr_fp_snd (expr.var "tmp")]);
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "tmp"; expr_fp_snd (expr.var "tmp")])
       ))).

    (* The bls12_Fp2_mul_xi WP correctness proofs (bls12_Fp2_mul_xi_nested,
       array_scalar_precise, FElem_Fp_precise, FElem_Fp2_precise,
       bls12_Fp2_mul_xi_ok) live in BLS12_Fp2_MulXi_Proof.v as a separately-
       cached compilation unit.  Inlined here, the 301-line nested proof body
       added ~30 min to every BLS12_Pairing.v rebuild.  Nothing downstream
       consumes these lemmas, so they are not re-exported from this file. *)


    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bls12_Fp6_funcs : list function_t :=
      Fp6_funcs bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix bls12_Fp2_mul_xi.

    Definition bls12_Fp12_funcs : list function_t :=
      Fp12_funcs bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bls12_pairing_ops : list function_t :=
      PairingOps_funcs bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix.

    (* ============================================================== *)
    (* Helper: fold a list of cmds into nested cmd.seq                 *)
    (* ============================================================== *)

    Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cmds with
      | [] => cmd.skip
      | [c] => c
      | c :: rest => cmd.seq c (cmd_seq_list rest)
      end.

    (* ============================================================== *)
    (* fp2_mul_fp: multiply Fp2 by Fp scalar (2 Fp muls)              *)
    (* ============================================================== *)

    Definition bls12_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).

    (* WP proof: see BLS12_PairingHelpers.v *)

    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (*   c0 = (lambda*x_T - y_T, -(lambda*x_P), 0)                   *)
    (*   c1 = (0, (y_P, 0), 0)                                        *)
    (* ============================================================== *)

    Definition bls12_make_line : function_t :=
      (make_line_name,
       (["out"; "lam"; "x_t"; "y_t"; "x_p"; "y_p"],
        []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd_seq_list [
           (* out.c0.c0 = lam * x_t *)
           cmd.call [] fp2_mul_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr.var "lam"; expr.var "x_t"];
           (* out.c0.c0 -= y_t *)
           cmd.call [] fp2_sub_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr_fp6_c0 (expr_fp12_c0 (expr.var "out")); expr.var "y_t"];
           (* tmp = lam * x_p (Fp2 scaled by Fp) *)
           cmd.call [] fp2_mul_fp_name
             [expr.var "tmp"; expr.var "lam"; expr.var "x_p"];
           (* out.c0.c1 = -tmp *)
           cmd.call [] fp2_opp_name
             [expr_fp6_c1 (expr_fp12_c0 (expr.var "out")); expr.var "tmp"];
           (* out.c0.c2 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c0 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c0 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c0 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c0 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c1 = (y_p, 0) *)
           cmd.call [] fp_copy_name
             [expr_fp6_c1 (expr_fp12_c1 (expr.var "out")); expr.var "y_p"];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c1 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c2 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0]
         ])
       ))).

    (* WP proof: see BLS12_MillerLoop.v *)

    (* ============================================================== *)
    (* Frobenius constant loaders for BLS12-381                        *)
    (*                                                                  *)
    (* Values are in Montgomery form, precomputed for BLS12-381.       *)
    (* Only the p²-Frobenius constants are needed for final exp:       *)
    (*   gamma1_p2 = ξ^{(p²-1)/3}                                     *)
    (*   gamma2_p2 = ξ^{2(p²-1)/3}                                    *)
    (*   w_frob_p2_c1 = ξ^{(p²-1)/6}                                  *)
    (* ============================================================== *)

    (* Helper: store an Fp2 constant = (real, 0) where real is 6 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 l4 l5 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal l0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal l1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal l2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal l3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal l4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal l5);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 64)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 72)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 80)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 88)) (expr.literal 0)
      ].

    (* γ₁^{p²} = ξ^{(p²-1)/3} — cube root of unity in Fp *)
    (* BUG FIX (2026-04-10): previous values were wrong (copy-paste from
       a different field or wrong exponent). Correct value is
       xi^{(p²-1)/3} in Montgomery form, computed by Python. *)
    Definition bls12_load_gamma1_p2 : function_t :=
      ("bls12_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x30f1361b798a64e8 0xf3b8ddab7ece5a2a
          0x16a8ca3ac61577f7 0xc26a2ff874fd029b
          0x3636b76660701c6e 0x051ba4ab241b6160)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* γ₂^{p²} = ξ^{2(p²-1)/3} *)
    Definition bls12_load_gamma2_p2 : function_t :=
      ("bls12_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xcd03c9e48671f071 0x5dab22461fcda5d2
          0x587042afd3851b95 0x8eb60ebe01bacb9e
          0x03f97d6e83d050d2 0x18f0206554638741)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* w^{p²} coefficient = ξ^{(p²-1)/6} *)
    Definition bls12_load_w_frob_p2_c1 : function_t :=
      ("bls12_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xecfb361b798dba3a 0xc100ddb891865a2c
          0x0ec08ff1232bda8e 0xd5c13cc6f1ca4721
          0x47222a47bf7b5c04 0x0110f184e51c5f59)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* ============================================================== *)
    (* Frobenius p constant loaders (for DSD final exponentiation)    *)
    (* Constants computed via Python: xi^{(p-1)/3} etc. in Montgomery *)
    (* ============================================================== *)

    Local Definition store_fp2_full (v : string)
      (r0 r1 r2 r3 r4 r5 i0 i1 i2 i3 i4 i5 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal r0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal r1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal r2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal r3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal r4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal r5);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal i0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal i1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 64)) (expr.literal i2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 72)) (expr.literal i3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 80)) (expr.literal i4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 88)) (expr.literal i5)
      ].

    (* γ₁ = ξ^{(p-1)/3} — purely imaginary *)
    Definition bls12_load_gamma1 : function_t :=
      ("bls12_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x0000000000000000 0x0000000000000000
          0x0000000000000000 0x0000000000000000
          0x0000000000000000 0x0000000000000000
          0xcd03c9e48671f071 0x5dab22461fcda5d2
          0x587042afd3851b95 0x8eb60ebe01bacb9e
          0x03f97d6e83d050d2 0x18f0206554638741)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* γ₂ = ξ^{2(p-1)/3} — purely real *)
    Definition bls12_load_gamma2 : function_t :=
      ("bls12_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x890dc9e4867545c3 0x2af322533285a5d5
          0x50880866309b7e2c 0xa20d1b8c7e881024
          0x14e4f04fe2db9068 0x14e56d3f1564853a)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* w^p coefficient = ξ^{(p-1)/6} — both components nonzero *)
    Definition bls12_load_w_frob_c1 : function_t :=
      ("bls12_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x07089552b319d465 0xc6695f92b50a8313
          0x97e83cccd117228f 0xa35baecab2dc29ee
          0x1ce393ea5daace4d 0x08f2220fb0fb66eb
          0xb2f66aad4ce5d646 0x5842a06bfc497cec
          0xcf4895d42599d394 0xc11b9cba40a8e8d0
          0x2e3813cbe5a0de89 0x110eefda88847faf)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* w^{p³} coefficient = ξ^{(p³-1)/6} — both components nonzero *)
    Definition bls12_load_w_frob_p3_c1 : function_t :=
      ("bls12_load_w_frob_p3_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x3e2f585da55c9ad1 0x4294213d86c18183
          0x382844c88b623732 0x92ad2afd19103e18
          0x1d794e4fac7cf0b9 0x0bd592fc7d825ec8
          0x7bcfa7a25aa30fda 0xdc17dec12a927e7c
          0x2f088dd86b4ebef1 0xd1ca2087da74d4a7
          0x2da2596696cebc1d 0x0e2b7eedbbfd87d2)).

    (* WP proof: see BLS12_FinalExp.v *)

    (* ============================================================== *)
    (* Helper: set an Fp12 element to the multiplicative identity      *)
    (* (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) in Fp components        *)
    (* ============================================================== *)

    Local Definition fp12_set_one (v : string) : Syntax.cmd.cmd :=
      let p := expr.var v in
      cmd_seq_list [
        cmd.call [] from_word_name [p; expr.literal 1];
        cmd.call [] from_word_name [expr_fp_snd p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c1 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c2 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c2 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp12_c1 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c1 (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c1 (expr_fp12_c1 p)); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c2 (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 p)); expr.literal 0]
      ].

    (* ============================================================== *)
    (* Fp12_pow_x: raise Fp12 element to the BLS parameter x          *)
    (*   Uses left-to-right binary square-and-multiply on              *)
    (*   |x| = 0xd201000000010000 (64-bit, top bit always set)        *)
    (* ============================================================== *)

    Local Definition pow_x_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.call [] fp12_sqr_name
          [expr.var "result"; expr.var "result"];
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0xd201000000010000) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    (* Cyclotomic squaring loop body — uses Fp6_mul + Fp6_mul_by_v instead
       of generic Fp12_square. Only valid in the cyclotomic subgroup GΦ₁₂. *)
    Let fp6_mul_name : string := AbstractField.mul (F:=Fp6).
    Let fp6_add_name : string := AbstractField.add (F:=Fp6).
    Let fp6_sub_name : string := AbstractField.sub (F:=Fp6).
    Let fp6_copy_name : string := AbstractField.felem_copy (F:=Fp6).
    Let fp6_mul_by_v_name : string := (fp6_prefix ++ "mul_by_v")%string.

    Local Definition cyc_sqr_body (out f : string) : Syntax.cmd.cmd :=
      (* out = cyc_sqr(f) where f = (c0, c1) in Fp6 × Fp6
         new_c0 = 1 + 2*v*c1^2,  new_c1 = 2*c0*c1
         Requires cyc_t0, cyc_t1 (Fp6 buffers) and cyc_one (Fp buffer holding
         the field element 1) to be in scope, stackalloc'd by the caller. *)
      let c0 := expr.var f in
      let c1 := expr.op bopname.add (expr.var f) (expr.literal (AbstractField.felem_size_in_bytes (F:=Fp6))) in
      let out_c0 := expr.var out in
      let out_c1 := expr.op bopname.add (expr.var out) (expr.literal (AbstractField.felem_size_in_bytes (F:=Fp6))) in
      cmd_seq_list [
        (* t0 = c1^2 (Fp6 mul) *)
        cmd.call [] fp6_mul_name [expr.var "cyc_t0"; c1; c1];
        (* t1 = c0*c1 (Fp6 mul) *)
        cmd.call [] fp6_mul_name [expr.var "cyc_t1"; c0; c1];
        (* t0 = mul_by_v(t0) *)
        cmd.call [] fp6_mul_by_v_name [expr.var "cyc_t0"; expr.var "cyc_t0"];
        (* out_c0 = 2*t0 *)
        cmd.call [] fp6_add_name [out_c0; expr.var "cyc_t0"; expr.var "cyc_t0"];
        (* out_c0 += 1 (add 1 to the deepest Fp component of out_c0, which
           corresponds to adding 1 to the Fp12 identity).  cyc_one is an Fp
           buffer pre-loaded with 1 by the caller. *)
        cmd.call [] (AbstractField.add (F:=Fp)) [out_c0; out_c0; expr.var "cyc_one"];
        (* out_c1 = 2*t1 *)
        cmd.call [] fp6_add_name [out_c1; expr.var "cyc_t1"; expr.var "cyc_t1"]
      ].

    (* pow_x with cyclotomic squaring — for use in final exp hard part *)
    Local Definition pow_x_cyc_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cyc_sqr_body "result" "result";
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0xd201000000010000) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    (* pow_x_half with cyclotomic squaring: exp by |x|/2 = 0x6900800000008000 *)
    Local Definition pow_x_half_cyc_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cyc_sqr_body "result" "result";
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x6900800000008000) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bls12_Fp12_pow_x : function_t :=
      ("bls12_Fp12_pow_x",
       (["out"; "base"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          coq:(cmd_seq_list [
            cmd.call [] fp12_copy_name
              [expr.var "result"; expr.var "base"];
            cmd.set "i" (expr.literal 63);
            cmd.while (expr.var "i") pow_x_loop_body;
            cmd.call [] fp12_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).

    (* WP proof: see BLS12_PowX.v *)

    (* ============================================================== *)

    (* Corrected DSD hard part: Hayashida-Hayasaka-Teruya, eprint 2020/875.
       Computes f^[3 h3] using inline exp-by-x with cyclotomic squaring.
       Proved: 3 h3 = 3 + [u^2-1+p^2] [u+1]^2 [p-u] in FinalExpEquiv.v.
       Uses inline exp-by-x loops, not function calls, to avoid overhead.
       Each exp-by-x: 63 squarings + about 5 Fp12 multiplications. *)

    (* Helper: inline exp-by-x loop body.
       Uses cyclotomic squaring (cyc_sqr_body) instead of dense Fp12_sqr;
       requires cyc_t0 and cyc_t1 (Fp6 buffers) to be in scope, stackalloc'd
       by the caller bls12_final_exp_hard_dsd below. *)
    Local Definition dsd_exp_x_loop : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cyc_sqr_body "result" "result";
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0xd201000000010000) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    (* Helper: inline exp-by-x/2 loop body. Same cyc_sqr substitution. *)
    Local Definition dsd_exp_x_half_loop : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cyc_sqr_body "result" "result";
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x6900800000008000) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    (* Inline exp_x_signed: result = base^{-|x|} = conjugate(base^{|x|}) *)
    Local Definition dsd_inline_exp_x (out_var base_var : string) : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] fp12_copy_name [expr.var "result"; expr.var base_var];
        cmd.call [] fp12_copy_name [expr.var "base"; expr.var base_var];
        cmd.set "i" (expr.literal 63);
        cmd.while (expr.var "i") dsd_exp_x_loop;
        cmd.call [] fp12_conjugate_name [expr.var out_var; expr.var "result"]
      ].

    (* Inline exp_x_half_signed: result = base^{-|x|/2}

       BUG FIX (2026-04-10): the previous version copied [base] into
       [result] before the loop, which implicitly adds a leading 1-bit
       at position 63. That is correct for [exp_x] (since |x| has
       bit 63 set), but WRONG for [exp_x_half] since |x|/2 =
       0x6900800000008000 has bit 63 = 0 (MSB is at bit 62). The
       implicit leading 1 computed f^{2^63 + |x|/2} instead of f^{|x|/2}.

       Fix: initialize [result] to 1 (Fp12 identity) so the 63-bit loop
       scans all 63 bits without a spurious implicit bit. Since |x|/2 has
       bit 62 set, the first effective multiply happens at i=62. *)
    Local Definition dsd_inline_exp_x_half (out_var base_var : string) : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "result";
        cmd.call [] fp12_copy_name [expr.var "base"; expr.var base_var];
        cmd.set "i" (expr.literal 63);
        cmd.while (expr.var "i") dsd_exp_x_half_loop;
        cmd.call [] fp12_conjugate_name [expr.var out_var; expr.var "result"]
      ].

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bls12_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bls12_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bls12_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* t0 = f² *)
        cmd.call [] fp12_sqr_name [expr.var "t0"; expr.var "f"];

        (* t1 = t0^{-|x|/2} = f^{-|x|} *)
        dsd_inline_exp_x_half "t1" "t0";

        (* t2 = f^{-1} *)
        cmd.call [] fp12_conjugate_name [expr.var "t2"; expr.var "f"];

        (* t1 = t1 * t2 = f^{-|x|-1} *)
        cmd.call [] fp12_mul_name [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t2 = t1^{-|x|} = f^{|x|²+|x|} *)
        dsd_inline_exp_x "t2" "t1";

        (* t1 = t1^{-1} = f^{|x|+1} *)
        cmd.call [] fp12_conjugate_name [expr.var "t1"; expr.var "t1"];

        (* t1 = t1 * t2 = f^{(|x|+1)²} *)
        cmd.call [] fp12_mul_name [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t2 = t1^{-|x|} = f^{-|x|(|x|+1)²} *)
        dsd_inline_exp_x "t2" "t1";

        (* t1 = Frob(t1) = f^{p(|x|+1)²} *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "t1";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];

        (* t1 = t1 * t2 = f^{(|x|+1)²(p-|x|)} *)
        cmd.call [] fp12_mul_name [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t3 = f * t0 = f³ *)
        cmd.call [] fp12_mul_name [expr.var "t3"; expr.var "f"; expr.var "t0"];

        (* t0 = t1^{-|x|} *)
        dsd_inline_exp_x "t0" "t1";

        (* t2 = t0^{-|x|} *)
        dsd_inline_exp_x "t2" "t0";

        (* t0 = Frob²(t1) — needs gamma1_p2, gamma2_p2, w_frob_p2_c1 *)
        cmd.call [] fp12_frobenius_p2_name
          [expr.var "t0"; expr.var "t1";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"];

        (* t1 = t1^{-1} *)
        cmd.call [] fp12_conjugate_name [expr.var "t1"; expr.var "t1"];

        (* t1 = t1 * t2 *)
        cmd.call [] fp12_mul_name [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t1 = t1 * t0 *)
        cmd.call [] fp12_mul_name [expr.var "t1"; expr.var "t1"; expr.var "t0"];

        (* out = t3 * t1 = f³ · f^{...} = f^{3·h3} *)
        cmd.call [] fp12_mul_name [expr.var "out"; expr.var "t3"; expr.var "t1"]
      ].

    (* DSD now needs frobenius_p2 constants too *)
    Definition bls12_final_exp_hard_dsd : function_t :=
      ("bls12_final_exp_hard_dsd",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t3;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as base;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_c1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as cyc_t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as cyc_t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as cyc_one;
          coq:(cmd.seq (cmd.call [] from_word_name [expr.var "cyc_one"; expr.literal 1])
                       final_exp_hard_dsd_body)
        ))).

    (* WP proof: see BLS12_FinalExp.v *)

    (* ============================================================== *)
    (* Miller loop (real body — processes 63 bits of BLS parameter)    *)
    (* ============================================================== *)

    (* BLS parameter |x| = 0xd201000000010000 *)
    Let bls_x : Z := 0xd201000000010000.

    (* One iteration of the Miller loop:
       - Decrement i
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of bls_x is set *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* === Doubling step === *)
        (* lambda = 3*t_x^2 / (2*t_y) *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_add_name
          [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp1"];
        cmd.call [] fp2_add_name
          [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_add_name
          [expr.var "tmp1"; expr.var "t_y"; expr.var "t_y"];
        cmd.call [] fp2_inv_name
          [expr.var "tmp1"; expr.var "tmp1"];
        cmd.call [] fp2_mul_name
          [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];

        (* Line evaluation at P *)
        cmd.call [] make_line_name
          [expr.var "line"; expr.var "lambda";
           expr.var "t_x"; expr.var "t_y";
           expr.var "p_x"; expr.var "p_y"];

        (* f = f^2 * line_d *)
        cmd.call [] fp12_sqr_name
          [expr.var "f"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "f"; expr.var "f"; expr.var "line"];

        (* T = 2T: new_x = lambda^2 - 2*t_x *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "lambda"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp2"; expr.var "tmp1"; expr.var "t_x"];
        (* new_y = lambda*(t_x - new_x) - t_y *)
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_sub_name
          [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
        cmd.call [] fp2_copy_name
          [expr.var "t_x"; expr.var "tmp2"];

        (* === Conditional addition step === *)
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal bls_x) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd_seq_list [
            (* Chord slope: lambda_a = (q_y - t_y) / (q_x - t_x) *)
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "q_x"; expr.var "t_x"];
            cmd.call [] fp2_inv_name
              [expr.var "tmp2"; expr.var "tmp2"];
            cmd.call [] fp2_mul_name
              [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];
            (* Line evaluation at P *)
            cmd.call [] make_line_name
              [expr.var "line"; expr.var "lambda";
               expr.var "t_x"; expr.var "t_y";
               expr.var "p_x"; expr.var "p_y"];
            (* f = f * line_a *)
            cmd.call [] fp12_mul_name
              [expr.var "f"; expr.var "f"; expr.var "line"];
            (* T = T + Q: new_x = lambda^2 - t_x - q_x *)
            cmd.call [] fp2_sqr_name
              [expr.var "tmp1"; expr.var "lambda"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "tmp1"; expr.var "q_x"];
            (* new_y = lambda*(t_x - new_x) - t_y *)
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
            cmd.call [] fp2_mul_name
              [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
            cmd.call [] fp2_sub_name
              [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
            cmd.call [] fp2_copy_name
              [expr.var "t_x"; expr.var "tmp2"]
          ])
          cmd.skip
      ].

    (* Full Miller loop: init + while loop + copy to output.
       Processes bits 62 down to 0 of |x| (bit 63 = MSB initializes T = Q). *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        cmd.set "i" (expr.literal 63);
        cmd.while (expr.var "i") miller_loop_iteration;
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bls12_miller_loop : function_t :=
      ("bls12_miller_loop",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          coq:(miller_loop_full_body)
        ))).

    (* WP proof: see BLS12_MillerLoop.v *)

    (* ============================================================== *)
    (* Final exponentiation                                            *)
    (*   f^{(p^12-1)/r} = f^{(p^6-1)(p^2+1)*h3}                     *)
    (*   Easy part: conjugate + inv + mul + frobenius_p2 + mul         *)
    (*   Hard part: square-and-multiply with h3 (1268-bit exponent)    *)
    (* ============================================================== *)

    (* Store h3 = (p^4 - p^2 + 1)/r exponent as 20 little-endian u64 limbs *)
    Local Definition h3_store_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word
          (expr.var "h3") (expr.literal 0xe516c3f438e3ba79);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 8))
          (expr.literal 0xfa9912aae208ccf1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 16))
          (expr.literal 0x905ce937335d5b68);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 24))
          (expr.literal 0xc71a2629b0dea236);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 32))
          (expr.literal 0x83774940996754c8);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 40))
          (expr.literal 0x21d160aeb6a1e799);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 48))
          (expr.literal 0x2ed0b283ed237db4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 56))
          (expr.literal 0x915c97f36c6f1821);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 64))
          (expr.literal 0x67f17fcbde783765);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 72))
          (expr.literal 0x2378b9039096d1b7);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 80))
          (expr.literal 0x7988f8761bdc51dc);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 88))
          (expr.literal 0x2076995003fc77a1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 96))
          (expr.literal 0x827eca0ba621315b);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 104))
          (expr.literal 0xe5a72bce8d63cb9f);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 112))
          (expr.literal 0xf68f7764c28b6f8a);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 120))
          (expr.literal 0x2f230063cf081517);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 128))
          (expr.literal 0x94506632528d6a9a);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 136))
          (expr.literal 0xd3cde88eeb996ca3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 144))
          (expr.literal 0xc0bd38c3195c899e);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 152))
          (expr.literal 0x000f686b3d807d01)
      ].

    (* One iteration of left-to-right binary square-and-multiply:
       - Decrement i
       - Extract bit from h3 array
       - If started: square the accumulator
       - If bit set: multiply by base (or initialize if first bit) *)
    Local Definition h3_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        (* Extract bit i from h3: word = h3[i/64], bit = (word >> (i%64)) & 1 *)
        cmd.set "word" (expr.load access_size.word
          (expr.op bopname.add (expr.var "h3")
            (expr.op bopname.slu
              (expr.op bopname.sru (expr.var "i") (expr.literal 6))
              (expr.literal 3))));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word")
            (expr.op bopname.and (expr.var "i") (expr.literal 63)))
          (expr.literal 1));
        (* if started: result = sqr(result) *)
        cmd.cond (expr.var "started")
          (cmd.call [] fp12_sqr_name
            [expr.var "result"; expr.var "result"])
          cmd.skip;
        (* if bit set: multiply or initialize *)
        cmd.cond (expr.var "bit")
          (cmd.cond (expr.var "started")
            (cmd.call [] fp12_mul_name
              [expr.var "result"; expr.var "result"; expr.var "base"])
            (cmd.seq
              (cmd.call [] fp12_copy_name
                [expr.var "result"; expr.var "base"])
              (cmd.set "started" (expr.literal 1))))
          cmd.skip
      ].

    (* Full final exponentiation:

       Easy part 1: result = conj(f) x inv(f) = f^[p^6-1]
       Easy part 2: result = frob_p2(result) x result = result^[p^2+1]
       Hard part:   result = DSD(result) = result^[3 h3] *)
    Local Definition final_exp_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Easy part 1: f^{p^6-1} *)
        cmd.call [] fp12_conjugate_name
          [expr.var "result"; expr.var "f"];
        cmd.call [] fp12_inv_name
          [expr.var "tmp"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "result"; expr.var "tmp"];
        (* Easy part 2: result^{p^2+1} *)
        cmd.call [] fp12_frobenius_p2_name
          [expr.var "tmp"; expr.var "result";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "tmp"; expr.var "result"];
        (* Hard part: DSD = result^{3*h3} *)
        cmd.call [] "bls12_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bls12_final_exp : function_t :=
      ("bls12_final_exp",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          coq:(final_exp_full_body)
        ))).

    (* WP proof: see BLS12_FinalExp.v *)

    (* ============================================================== *)
    (* Projective Miller loop (inversion-free)                         *)
    (*                                                                  *)
    (* Uses Jacobian projective coordinates for the running point T    *)
    (* on E'(Fp2), eliminating all Fp2_inv calls from the loop.        *)
    (*                                                                  *)
    (* Fp12_mul_by_024: sparse Fp12 multiply by line evaluation result *)
    (* miller_loop_proj: full projective Miller loop                    *)
    (* ============================================================== *)

    (* Fp6-level function name helpers *)
    Let fp6_mul_fp2_name : string := (fp6_prefix ++ "mul_fp2")%string.

    (* Fp12_mul_by_024: sparse multiplication of Fp12 by a line evaluation.
       The line is represented as three Fp2 elements (ell0, ell2, ell4)
       forming a sparse Fp12 = ((ell0, ell2, 0), (ell4, 0, 0)).

       Formula:
         b = (ell0, ell2, 0) ∈ Fp6
         t0 = a.c0 * b                         [Fp6_mul]
         t1 = Fp6_mul_fp2(a.c1, ell4)          [Fp6 scaled by Fp2]
         out.c0 = t0 + mul_by_v(t1)            [shift + mul_xi]
         t2 = a.c1 * b                         [Fp6_mul]
         t3 = Fp6_mul_fp2(a.c0, ell4)          [Fp6 scaled by Fp2]
         out.c1 = t2 + t3                      [Fp6_add]
    *)
    Local Definition mul_by_024_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Construct sparse Fp6 b = (ell0, ell2, 0) in 'b' *)
        cmd.call [] fp2_copy_name
          [expr_fp6_c0 (expr.var "b"); expr.var "ell0"];
        cmd.call [] fp2_copy_name
          [expr_fp6_c1 (expr.var "b"); expr.var "ell2"];
        cmd.call [] from_word_name
          [expr_fp6_c2 (expr.var "b"); expr.literal 0];
        cmd.call [] from_word_name
          [expr_fp_snd (expr_fp6_c2 (expr.var "b")); expr.literal 0];

        (* t0 = a.c0 * b *)
        cmd.call [] fp6_mul_name
          [expr.var "t0"; expr_fp12_c0 (expr.var "a"); expr.var "b"];
        (* t1 = Fp6_mul_fp2(a.c1, ell4) *)
        cmd.call [] fp6_mul_fp2_name
          [expr.var "t1"; expr_fp12_c1 (expr.var "a"); expr.var "ell4"];
        (* u = mul_by_v(t1) *)
        cmd.call [] fp6_mul_by_v_name
          [expr.var "u"; expr.var "t1"];
        (* out.c0 = t0 + u *)
        cmd.call [] fp6_add_name
          [expr_fp12_c0 (expr.var "out"); expr.var "t0"; expr.var "u"];

        (* t2 = a.c1 * b *)
        cmd.call [] fp6_mul_name
          [expr.var "t2"; expr_fp12_c1 (expr.var "a"); expr.var "b"];
        (* t3 = Fp6_mul_fp2(a.c0, ell4) *)
        cmd.call [] fp6_mul_fp2_name
          [expr.var "t1"; expr_fp12_c0 (expr.var "a"); expr.var "ell4"];
        (* out.c1 = t2 + t3 *)
        cmd.call [] fp6_add_name
          [expr_fp12_c1 (expr.var "out"); expr.var "t2"; expr.var "t1"]
      ].

    Definition bls12_Fp12_mul_by_024 : function_t :=
      ("bls12_Fp12_mul_by_024",
       (["out"; "a"; "ell0"; "ell2"; "ell4"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as b;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as u;
          coq:(mul_by_024_body)
        ))).

    (* WP proof: see BLS12_MillerLoop.v *)

    (* Projective Miller loop: inline Jacobian doubling + mixed addition.
       Eliminates all Fp2_inv calls.  T = (T_X : T_Y : T_Z) in Jacobian,
       representing affine (T_X/T_Z², T_Y/T_Z³).

       Doubling formulas (a=0 for BLS12-381 twist):
         A = T_X²
         B = T_Y²
         C = B²  (= T_Y⁴)
         D = 4*T_X*B  (= 2*((T_X+B)² - A - C))
         E = 3*A      (= 3*T_X², tangent numerator)
         F = E²
         X3 = F - 2*D
         Y3 = E*(D - X3) - 8*C
         Z3 = (T_Y + T_Z)² - B - T_Z²

       Line at P(xP, yP):
         ell_0  = E*T_X - 2*B         (Fp2)
         ell_VV = -(E * xP * T_Z)     (Fp * Fp2)
         ell_VW = Z3 * yP             (Fp * Fp2)

       Mixed addition (T + Q, Q affine):
         Z_sq = T_Z²
         U2 = Q_X * Z_sq
         S2 = Q_Y * Z_sq * T_Z
         H  = U2 - T_X
         r  = S2 - T_Y
         HH = H²
         V  = T_X * HH
         J  = HH * H
         X3 = r² - J - 2*V
         Y3 = r*(V - X3) - T_Y*J
         Z3 = H * T_Z

       Line at P:
         ell_0  = r*Q_X - T_Y         (Fp2)
         ell_VV = -(r * xP)           (Fp * Fp2)
         ell_VW = Z3 * yP             (Fp * Fp2)
    *)

    (* Inline doubling step: updates t_x/t_y/t_z and sets ell0/ellVW/ellVV *)
    Local Definition proj_doubling_step : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* A = t_x² *)
        cmd.call [] fp2_sqr_name
          [expr.var "A"; expr.var "t_x"];
        (* B = t_y² *)
        cmd.call [] fp2_sqr_name
          [expr.var "B"; expr.var "t_y"];
        (* C = B² *)
        cmd.call [] fp2_sqr_name
          [expr.var "C"; expr.var "B"];
        (* D = 4*t_x*B: first t_x*B, then double twice *)
        cmd.call [] fp2_mul_name
          [expr.var "D"; expr.var "t_x"; expr.var "B"];
        cmd.call [] fp2_add_name
          [expr.var "D"; expr.var "D"; expr.var "D"];
        cmd.call [] fp2_add_name
          [expr.var "D"; expr.var "D"; expr.var "D"];
        (* E = 3*A *)
        cmd.call [] fp2_add_name
          [expr.var "E"; expr.var "A"; expr.var "A"];
        cmd.call [] fp2_add_name
          [expr.var "E"; expr.var "E"; expr.var "A"];

        (* Line evaluation (before point update, uses old t_x, t_y, t_z) *)
        (* ell_0 = E*t_x - 2*B *)
        cmd.call [] fp2_mul_name
          [expr.var "ell0"; expr.var "E"; expr.var "t_x"];
        cmd.call [] fp2_add_name
          [expr.var "tmp1"; expr.var "B"; expr.var "B"];
        cmd.call [] fp2_sub_name
          [expr.var "ell0"; expr.var "ell0"; expr.var "tmp1"];
        (* ell_VV = -(E * xP * t_z) *)
        cmd.call [] fp2_mul_fp_name
          [expr.var "tmp1"; expr.var "E"; expr.var "p_x"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_z"];
        cmd.call [] fp2_opp_name
          [expr.var "ellVV"; expr.var "tmp1"];

        (* F = E² *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "E"];
        (* X3 = F - 2*D *)
        cmd.call [] fp2_add_name
          [expr.var "tmp2"; expr.var "D"; expr.var "D"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp2"; expr.var "tmp1"; expr.var "tmp2"];
        (* Y3 = E*(D - X3) - 8*C *)
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "D"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "E"; expr.var "tmp1"];
        (* 8*C = 2*2*2*C *)
        cmd.call [] fp2_add_name
          [expr.var "C"; expr.var "C"; expr.var "C"];
        cmd.call [] fp2_add_name
          [expr.var "C"; expr.var "C"; expr.var "C"];
        cmd.call [] fp2_add_name
          [expr.var "C"; expr.var "C"; expr.var "C"];
        cmd.call [] fp2_sub_name
          [expr.var "A"; expr.var "tmp1"; expr.var "C"];
        (* Z3 = (t_y + t_z)² - B - t_z² *)
        cmd.call [] fp2_add_name
          [expr.var "tmp1"; expr.var "t_y"; expr.var "t_z"];
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "tmp1"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "B"];
        cmd.call [] fp2_sqr_name
          [expr.var "C"; expr.var "t_z"];
        cmd.call [] fp2_sub_name
          [expr.var "C"; expr.var "tmp1"; expr.var "C"];

        (* ell_VW = Z3 * yP (uses new Z3 which is in C) *)
        cmd.call [] fp2_mul_fp_name
          [expr.var "ellVW"; expr.var "C"; expr.var "p_y"];

        (* Update T *)
        cmd.call [] fp2_copy_name
          [expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_copy_name
          [expr.var "t_y"; expr.var "A"];
        cmd.call [] fp2_copy_name
          [expr.var "t_z"; expr.var "C"]
      ].

    (* Inline mixed addition step: T = T + Q, sets ell0/ellVW/ellVV *)
    Local Definition proj_addition_step : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Z_sq = t_z² *)
        cmd.call [] fp2_sqr_name
          [expr.var "A"; expr.var "t_z"];
        (* U2 = q_x * Z_sq *)
        cmd.call [] fp2_mul_name
          [expr.var "B"; expr.var "q_x"; expr.var "A"];
        (* S2 = q_y * Z_sq * t_z *)
        cmd.call [] fp2_mul_name
          [expr.var "C"; expr.var "A"; expr.var "t_z"];
        cmd.call [] fp2_mul_name
          [expr.var "C"; expr.var "q_y"; expr.var "C"];
        (* H = U2 - t_x *)
        cmd.call [] fp2_sub_name
          [expr.var "D"; expr.var "B"; expr.var "t_x"];
        (* r = S2 - t_y *)
        cmd.call [] fp2_sub_name
          [expr.var "E"; expr.var "C"; expr.var "t_y"];

        (* Line evaluation (uses r, old t_y, old t_z) *)
        (* ell_0 = r*q_x - t_y *)
        cmd.call [] fp2_mul_name
          [expr.var "ell0"; expr.var "E"; expr.var "q_x"];
        cmd.call [] fp2_sub_name
          [expr.var "ell0"; expr.var "ell0"; expr.var "t_y"];
        (* ell_VV = -(r * xP) *)
        cmd.call [] fp2_mul_fp_name
          [expr.var "tmp1"; expr.var "E"; expr.var "p_x"];
        cmd.call [] fp2_opp_name
          [expr.var "ellVV"; expr.var "tmp1"];

        (* HH = H² *)
        cmd.call [] fp2_sqr_name
          [expr.var "A"; expr.var "D"];
        (* V = t_x * HH *)
        cmd.call [] fp2_mul_name
          [expr.var "B"; expr.var "t_x"; expr.var "A"];
        (* J = HH * H *)
        cmd.call [] fp2_mul_name
          [expr.var "A"; expr.var "A"; expr.var "D"];
        (* X3 = r² - J - 2*V *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "E"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "A"];
        cmd.call [] fp2_add_name
          [expr.var "tmp2"; expr.var "B"; expr.var "B"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp2"; expr.var "tmp1"; expr.var "tmp2"];
        (* Y3 = r*(V - X3) - t_y*J *)
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "B"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "E"; expr.var "tmp1"];
        cmd.call [] fp2_mul_name
          [expr.var "C"; expr.var "t_y"; expr.var "A"];
        cmd.call [] fp2_sub_name
          [expr.var "C"; expr.var "tmp1"; expr.var "C"];
        (* Z3 = H * t_z *)
        cmd.call [] fp2_mul_name
          [expr.var "A"; expr.var "D"; expr.var "t_z"];

        (* ell_VW = Z3 * yP *)
        cmd.call [] fp2_mul_fp_name
          [expr.var "ellVW"; expr.var "A"; expr.var "p_y"];

        (* Update T *)
        cmd.call [] fp2_copy_name
          [expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_copy_name
          [expr.var "t_y"; expr.var "C"];
        cmd.call [] fp2_copy_name
          [expr.var "t_z"; expr.var "A"]
      ].

    (* One iteration of the projective Miller loop *)
    Local Definition proj_miller_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* === Doubling step === *)
        proj_doubling_step;

        (* f = f² * line *)
        cmd.call [] fp12_sqr_name
          [expr.var "f"; expr.var "f"];
        cmd.call [] "bls12_Fp12_mul_by_024"
          [expr.var "f"; expr.var "f";
           expr.var "ell0"; expr.var "ellVW"; expr.var "ellVV"];

        (* === Conditional addition step === *)
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal bls_x) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd_seq_list [
            proj_addition_step;
            cmd.call [] "bls12_Fp12_mul_by_024"
              [expr.var "f"; expr.var "f";
               expr.var "ell0"; expr.var "ellVW"; expr.var "ellVV"]
          ])
          cmd.skip
      ].

    (* Full projective Miller loop body *)
    Local Definition proj_miller_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        (* Initialize T = Q in projective: Z = 1 (Montgomery) *)
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        (* Z.re = 1 in Montgomery form, Z.im = 0 *)
        cmd.call [] from_word_name [expr.var "t_z"; expr.literal 1];
        cmd.call [] from_word_name
          [expr_fp_snd (expr.var "t_z"); expr.literal 0];
        (* Loop from bit 62 down to 0 *)
        cmd.set "i" (expr.literal 63);
        cmd.while (expr.var "i") proj_miller_iteration;
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bls12_miller_loop_proj : function_t :=
      ("bls12_miller_loop_proj",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_z;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as ell0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as ellVW;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as ellVV;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as A;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as B;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as C;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as D;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as E;
          coq:(proj_miller_full_body)
        ))).

    (* WP proof: see BLS12_MillerLoop.v *)

    (* ============================================================== *)
    (* Top-level pairing: e(P, Q) = final_exp(miller_loop(P, Q))      *)
    (* ============================================================== *)

    Local Definition pairing_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bls12_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bls12_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bls12_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bls12_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation *)
        cmd.call [] "bls12_final_exp"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bls12_pairing : function_t :=
      ("bls12_pairing",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_full_body)
        ))).

    (* WP proof: see BLS12_PairingTop.v *)

    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bls12_all_pairing_funcs : list function_t :=
      bls12_Fp6_funcs ++
      bls12_Fp12_funcs ++
      bls12_pairing_ops ++
      [ bls12_Fp2_mul_fp;
        bls12_make_line;
        bls12_load_gamma1_p2;
        bls12_load_gamma2_p2;
        bls12_load_w_frob_p2_c1;
        bls12_load_gamma1;
        bls12_load_gamma2;
        bls12_load_w_frob_c1;
        bls12_load_w_frob_p3_c1;
        bls12_Fp12_pow_x;
        bls12_final_exp_hard_dsd;
        bls12_miller_loop;
        bls12_final_exp;
        bls12_Fp12_mul_by_024;
        bls12_miller_loop_proj;
        bls12_pairing ].

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bls12_pairing" on G1 point P = (p_x, p_y)   *)
    (* and G2 point Q = (q_x, q_y) produces the optimal Ate pairing    *)
    (* e(P, Q) as an Fp12 element.                                     *)
    (* ============================================================== *)

End BLS12_Pairing.
