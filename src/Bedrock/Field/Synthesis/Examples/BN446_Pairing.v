(** * BN446 Pairing -- bedrock2 compilation top-level.

    Instantiates the full field tower (Fp -> Fp2 -> Fp6 -> Fp12) for
    BN446 and defines bedrock2 function bodies for the optimal
    Ate pairing: Miller loop, final exponentiation, and top-level pairing.

    BN446 differences from BN254:
    - beta = -1 (same), xi = (2, 3) (not (9, 1))
    - Fp = 7 words (not 4), 446-bit prime
    - u = 0x4000000000000000001000000001 (111 bits, positive)
    - |6u+2| = 0x18000000000000000006000000008 (113 bits, 2 words)
    - b = 257, 3b = 771

    WP proofs are in companion files (PairingHelpers, MillerLoop, etc.).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
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
Require Import Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(* NOTE: This file defines function BODIES only. WP correctness proofs
   are in the companion files: BN446_PairingHelpers.v, BN446_MillerLoop.v,
   BN446_PowU.v, BN446_FinalExpHardDSD.v, BN446_FinalExpDSD.v,
   BN446_PairingTop.v. *)

Section BN446_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BN446 prime parameters                                          *)
    (* ============================================================== *)

    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_pf_params : PrimeFieldParameters := {|
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

    Instance bn446_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn446. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bn446_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn446_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn446_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn446_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn446_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn446_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn446_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn446_frep |}.

    Instance bn446_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn446_fp_rep] in *.
      cbv [Field.bounded_by bn446_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* beta = -1 for BN446 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn446_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (2, 3) for BN446 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn446_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 2.
    Let bn446_xi_im : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.

    Lemma bn446_beta_nz : bn446_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bn446_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bn446_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* BN446: p = 3 mod 4, so -1 is a QNR. *)
    Lemma bn446_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bn446_beta).
    Proof.
      intro H.
      assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
        by exact prime_bn446.
      assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bn446_M_big.
      apply (proj2 (@F.euler_criterion _ Hprime Hbig bn446_beta bn446_beta_nz)) in H.
      assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bn446_beta
        (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
      { vm_cast_no_check (eq_refl false). }
      apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
      rewrite Z.eqb_refl in Hcheck. discriminate.
    Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bn446_Fp2_".
    Let fp6_prefix := "bn446_Fp6_".
    Let fp12_prefix := "bn446_Fp12_".

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

    Instance bn446_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn446_beta "bn446_") in exact v).
    Instance bn446_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn446_beta "bn446_") in exact v).
    Instance bn446_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bn446_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bn446_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bn446_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bn446_".

    (* ============================================================== *)
    (* Offset and address helpers                                      *)
    (* ============================================================== *)

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Definition expr_fp_snd (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp_felem_offset).

    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
    Local Definition expr_fp6_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp6_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp2_felem_offset).
    Local Definition expr_fp6_c2 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

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
    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Let fp2_mul_fp_name : string := "bn446_Fp2_mul_fp".
    Let make_line_name : string := "bn446_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by xi = (2, 3)                *)
    (*   (a0 + a1*u) * (2 + 3u) = (2*a0 - 3*a1) + (3*a0 + 2*a1)*u   *)
    (*   Multiply-by-2: x -> x+x                                      *)
    (*   Multiply-by-3: x -> 2x -> 2x+x                               *)
    (* ============================================================== *)

    Definition bn446_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_a3;
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_b3;
         (* tmp_a3 = 3*a: 2a -> 2a+a *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a3"; expr.var "x"; expr.var "x"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a3"; expr.var "tmp_a3"; expr.var "x"]);
         (* tmp_b3 = 3*b: 2b -> 2b+b *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b3"; expr_fp_snd (expr.var "x"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b3"; expr.var "tmp_b3"; expr_fp_snd (expr.var "x")]);
         (* out.re = 2a - 3b: first compute 2a *)
         coq:(cmd.call [] fp_add_name
           [expr.var "out"; expr.var "x"; expr.var "x"]);
         (* out.re = 2a - 3b *)
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "out"; expr.var "tmp_b3"]);
         (* out.im = 3a + 2b: first compute 2b *)
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr_fp_snd (expr.var "x")]);
         (* out.im = 3a + 2b *)
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "tmp_a3"; expr_fp_snd (expr.var "out")])
       ))).

    Lemma bn446_Fp2_mul_xi_name_eq : fst bn446_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bn446_Fp6_funcs : list function_t :=
      Fp6_funcs bn446_beta bn446_xi_re bn446_xi_im fp6_prefix fp2_prefix bn446_Fp2_mul_xi.

    Definition bn446_Fp12_funcs : list function_t :=
      Fp12_funcs bn446_beta bn446_xi_re bn446_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bn446_pairing_ops : list function_t :=
      PairingOps_funcs bn446_beta bn446_xi_re bn446_xi_im fp12_prefix fp6_prefix fp2_prefix.

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

    Definition bn446_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).
    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (* ============================================================== *)

    Definition bn446_make_line : function_t :=
      (make_line_name,
       (["out"; "lam"; "x_t"; "y_t"; "x_p"; "y_p"],
        []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd_seq_list [
           cmd.call [] fp2_mul_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr.var "lam"; expr.var "x_t"];
           cmd.call [] fp2_sub_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr_fp6_c0 (expr_fp12_c0 (expr.var "out")); expr.var "y_t"];
           cmd.call [] fp2_mul_fp_name
             [expr.var "tmp"; expr.var "lam"; expr.var "x_p"];
           cmd.call [] fp2_opp_name
             [expr_fp6_c1 (expr_fp12_c0 (expr.var "out")); expr.var "tmp"];
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c0 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp6_c0 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c0 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           cmd.call [] fp_copy_name
             [expr_fp6_c1 (expr_fp12_c1 (expr.var "out")); expr.var "y_p"];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c1 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0]
         ])
       ))).
    (* ============================================================== *)
    (* Frobenius constant loaders for BN446                            *)
    (* ============================================================== *)

    (* Helper: store an Fp2 constant = (real, 0) where real is 7 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 l4 l5 l6 : Z) :=
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
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal l6);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 64)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 72)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 80)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 88)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 96)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 104)) (expr.literal 0)
      ].

    (* Helper: store a full Fp2 constant (real + imaginary, 14 limbs) *)
    Local Definition store_fp2_full (v : string)
      (r0 r1 r2 r3 r4 r5 r6 i0 i1 i2 i3 i4 i5 i6 : Z) :=
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
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal r6);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal i0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 64)) (expr.literal i1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 72)) (expr.literal i2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 80)) (expr.literal i3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 88)) (expr.literal i4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 96)) (expr.literal i5);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 104)) (expr.literal i6)
      ].

    (* gamma1_p2 = xi^{(p^2-1)/3} for BN446 in Montgomery form *)
    Definition bn446_load_gamma1_p2 : function_t :=
      ("bn446_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x5557523555553909 0x1589955556E87955 0x110000022DBC0000
          0x0000086A000000B2 0x0019D28000005A84 0x027C000000B8B000
          0x1C00000156000000)).
    (* gamma2_p2 = xi^{2(p^2-1)/3} for BN446 in Montgomery form *)
    Definition bn446_load_gamma2_p2 : function_t :=
      ("bn446_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xAAA946CAAAAACA2F 0xED346AAAA92266AA 0x26FFFFFE2A63FFFF
          0xFFFFF855FFFFFF52 0xFFE6997FFFFFB65B 0xFEA3FFFFFF5DCFFF
          0x03FFFFFEA9FFFFFF)).
    (* w_frob_p2_c1 = xi^{(p^2-1)/6} for BN446 in Montgomery form *)
    Definition bn446_load_w_frob_p2_c1 : function_t :=
      ("bn446_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x5556CC5555553638 0x1323555556DEF555 0x60000001E0A00000
          0x000007C2000000AE 0x0019740000004BC0 0x0180000000A50000
          0x2000000156000000)).
    (* ============================================================== *)
    (* Helper: set an Fp12 element to the multiplicative identity      *)
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
    (* Miller loop (processes 113 bits of |6u+2|, 2-word parameter)   *)
    (* ============================================================== *)

    (* BN446 parameter u = 0x4000000000000000001000000001 (positive)
       |6u+2| = 0x18000000000000000006000000008 (113 bits)
       Stored as 2 x 64-bit words on stack:
         lo = 0x0000006000000008
         hi = 0x0001800000000000
       MSB is bit 112; after consuming it at init, iterate 112 bits (bits 111..0).
       Bit extraction: word_idx = i / 64, bit_in_word = i mod 64 *)

    Definition bn446_6u2_lo : Z := 0x0000006000000008.
    Definition bn446_6u2_hi : Z := 0x0001800000000000.

    (* Store the 2-word 6u+2 parameter on stack *)
    Local Definition store_6u2_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var "u6p2") (expr.literal bn446_6u2_lo);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "u6p2") (expr.literal 8)) (expr.literal bn446_6u2_hi)
      ].

    (* One iteration of the Miller loop:
       - Decrement i
       - Extract bit i from the 2-word 6u+2
       - Doubling step + conditional addition step *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* Extract bit i from two-word u6p2:
           word = u6p2[(i >> 6) << 3], bit = (word >> (i & 63)) & 1 *)
        cmd.set "word" (expr.load access_size.word
          (expr.op bopname.add (expr.var "u6p2")
            (expr.op bopname.slu
              (expr.op bopname.sru (expr.var "i") (expr.literal 6))
              (expr.literal 3))));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word")
            (expr.op bopname.and (expr.var "i") (expr.literal 63)))
          (expr.literal 1));

        (* === Doubling step === *)
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

        cmd.call [] make_line_name
          [expr.var "line"; expr.var "lambda";
           expr.var "t_x"; expr.var "t_y";
           expr.var "p_x"; expr.var "p_y"];

        cmd.call [] fp12_sqr_name
          [expr.var "f"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "f"; expr.var "f"; expr.var "line"];

        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "lambda"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp2"; expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_sub_name
          [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
        cmd.call [] fp2_copy_name
          [expr.var "t_x"; expr.var "tmp2"];

        (* === Conditional addition step === *)
        cmd.cond (expr.var "bit")
          (cmd_seq_list [
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "q_x"; expr.var "t_x"];
            cmd.call [] fp2_inv_name
              [expr.var "tmp2"; expr.var "tmp2"];
            cmd.call [] fp2_mul_name
              [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];
            cmd.call [] make_line_name
              [expr.var "line"; expr.var "lambda";
               expr.var "t_x"; expr.var "t_y";
               expr.var "p_x"; expr.var "p_y"];
            cmd.call [] fp12_mul_name
              [expr.var "f"; expr.var "f"; expr.var "line"];
            cmd.call [] fp2_sqr_name
              [expr.var "tmp1"; expr.var "lambda"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "tmp1"; expr.var "q_x"];
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
       Processes bits 111 down to 0 of |6u+2| (bit 112 = MSB initializes T = Q).
       BN446 has positive u, so NO conjugation after the loop. *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 112);
        cmd.while (expr.var "i") miller_loop_iteration;
        (* No conjugation needed: BN446 has positive u *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bn446_miller_loop : function_t :=
      ("bn446_miller_loop",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          stackalloc 16 as u6p2;
          coq:(miller_loop_full_body)
        ))).
    (* ============================================================== *)
    (* Fp12_pow_u: raise Fp12 element to the BN parameter u            *)
    (*   u = 2^110 + 2^36 + 1  (Hamming weight 3)                     *)
    (*   Exploits sparse weight: f^u = f * f^(2^36) * f^(2^110)       *)
    (*   = 110 squarings + 2 multiplications + copies. No loop needed. *)
    (* ============================================================== *)

    (* Simple squaring loop body: result = sqr(result); i = i - 1 *)
    Local Definition sqr_loop_body : Syntax.cmd.cmd :=
      cmd.seq
        (cmd.call [] fp12_sqr_name [expr.var "temp"; expr.var "temp"])
        (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1))).

    Definition bn446_Fp12_pow_u : function_t :=
      ("bn446_Fp12_pow_u",
       (["out"; "base"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as temp;
          coq:(cmd_seq_list [
            (* result = base (f^1) *)
            cmd.call [] fp12_copy_name
              [expr.var "result"; expr.var "base"];
            (* temp = base *)
            cmd.call [] fp12_copy_name
              [expr.var "temp"; expr.var "base"];
            (* Square temp 36 times: temp = f^(2^36) *)
            cmd.set "i" (expr.literal 36);
            cmd.while (expr.var "i") sqr_loop_body;
            (* result = result * temp = f^(1 + 2^36) *)
            cmd.call [] fp12_mul_name
              [expr.var "result"; expr.var "result"; expr.var "temp"];
            (* Square temp 74 more times: temp = f^(2^110) *)
            cmd.set "i" (expr.literal 74);
            cmd.while (expr.var "i") sqr_loop_body;
            (* result = result * temp = f^(1 + 2^36 + 2^110) = f^u *)
            cmd.call [] fp12_mul_name
              [expr.var "result"; expr.var "result"; expr.var "temp"];
            (* Copy to output *)
            cmd.call [] fp12_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).

    (* ============================================================== *)
    (* Frobenius p constant loaders (for DSD final exponentiation)    *)
    (* ============================================================== *)

    (* gamma1 = xi^{(p-1)/3} for BN446 in Montgomery form (full Fp2) *)
    Definition bn446_load_gamma1 : function_t :=
      ("bn446_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0xA9707F06A2911FE5 0x6CD56EF01CE2A9D1 0x83DAF2BFFA06227C
          0xB167E5173810465F 0xEC6829AD1B03A057 0x3D6454F6835050D2
          0x17E66D2B8D788C0C
          0xF9756B04ABA2140A 0x9C8C9F7FE9506204 0x9BBCE8488D957CD9
          0x8C11B426417EE934 0x3CE3F9CC7B05A7FC 0x8831B0F3BB2056EB
          0x1CB419F8806EE62E)).
    (* gamma2 = xi^{2(p-1)/3} for BN446 in Montgomery form (full Fp2) *)
    Definition bn446_load_gamma2 : function_t :=
      ("bn446_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x45E78B4FE63EE181 0xC4B27D3AF0DF7AE3 0xEE74A57CA979AB51
          0x7C90D7115B12CFA9 0xF9EF862CFF8602AD 0x0DA75398389DC684
          0x01454DB433D5A0C2
          0xC14D0635840B43D9 0xDAF080662FD4E161 0x6A0B5079634CD7FB
          0x85F6C9E09A3EBF87 0xEDA90A144A7C855A 0x4F66FFAE21471A09
          0x0F6E4C6307FA68AE)).
    (* w_frob_c1 = xi^{(p-1)/6} for BN446 in Montgomery form (full Fp2) *)
    Definition bn446_load_w_frob_c1 : function_t :=
      ("bn446_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x4F42FB173240CACF 0x41A6624C14E770DB 0x4CE482DDAEF1E09C
          0xACFB794D0EA9EB70 0x8E6475845F69F02F 0xD188D14E6F71BE65
          0x0CA5E41A2878689A
          0x0B8C0C1CBA0162A2 0x039CE6E5C8948976 0xD48AB015DA2F897B
          0xFD77AA8DDC863E6C 0x25EAA23E38AC4FA8 0x3BBF3C8AC583EA9D
          0x1A2B7CB0A28128C2)).
    (* ============================================================== *)
    (* Final exponentiation hard part (DSD decomposition)             *)
    (* ============================================================== *)

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p constants *)
        cmd.call [] "bn446_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bn446_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bn446_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* === Phase 1: Powers of u === *)
        (* t0 = f^u *)
        cmd.call [] "bn446_Fp12_pow_u"
          [expr.var "t0"; expr.var "f"];
        (* t1 = f^(u^2) *)
        cmd.call [] "bn446_Fp12_pow_u"
          [expr.var "t1"; expr.var "t0"];
        (* t2 = f^(u^3) *)
        cmd.call [] "bn446_Fp12_pow_u"
          [expr.var "t2"; expr.var "t1"];

        (* === Phase 2: y6 = conj(f^(u^3) * f^(u^3*p)) === *)
        (* t3 = frobenius(t2) = f^(u^3*p) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t2 = t2 * t3 = f^(u^3 + u^3*p) *)
        cmd.call [] fp12_mul_name
          [expr.var "t2"; expr.var "t2"; expr.var "t3"];
        (* t2 = conj(t2) = y6 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t2"; expr.var "t2"];

        (* === Phase 3: T01 = y6^2 * y4 * y5 === *)
        (* out = y6^2 *)
        cmd.call [] fp12_sqr_name
          [expr.var "out"; expr.var "t2"];
        (* t3 = frobenius(t1) = f^(u^2*p)  [saved for Phase 5] *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t1";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t2 = t0 * t3 = f^(u + u^2*p) *)
        cmd.call [] fp12_mul_name
          [expr.var "t2"; expr.var "t0"; expr.var "t3"];
        (* t2 = conj(t2) = y4 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t2"; expr.var "t2"];
        (* out = out * t2 = y6^2 * y4 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t2"];
        (* t1 = conj(t1) = y5 = f^(-u^2) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];
        (* out = out * t1 = T01 = y6^2 * y4 * y5 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t1"];

        (* === Phase 4: T11 = T01 * y3 * y5 === *)
        (* t2 = frobenius(t0) = f^(u*p) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t0";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t2 = conj(t2) = y3 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t2"; expr.var "t2"];
        (* t0 = out * t2 = T01 * y3 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "out"; expr.var "t2"];
        (* t0 = t0 * t1 = T11 = T01 * y3 * y5 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];

        (* === Phase 5: T02 = T01 * y2 === *)
        (* t1 = frobenius(t3) = f^(u^2*p^2) = y2 *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "t3";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* out = out * t1 = T02 = T01 * y2 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t1"];

        (* === Phase 6: T13 = (T11^2 * T02)^2 === *)
        (* t1 = T11^2 *)
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t0"];
        (* t1 = t1 * out = T12 = T11^2 * T02 *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "out"];
        (* t1 = T12^2 = T13 *)
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t1"];

        (* === Phase 7: y0 = f^p * f^(p^2) * f^(p^3) === *)
        (* t0 = frobenius(f) = f^p *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t0"; expr.var "f";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t2 = frobenius(t0) = f^(p^2) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t0";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t3 = frobenius(t2) = f^(p^3) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t0 = t0 * t2 = f^(p + p^2) *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t2"];
        (* t0 = t0 * t3 = y0 = f^(p + p^2 + p^3) *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t3"];

        (* === Phase 8: Final assembly === *)
        (* t2 = T13 * y0 = T14 *)
        cmd.call [] fp12_mul_name
          [expr.var "t2"; expr.var "t1"; expr.var "t0"];
        (* t0 = conj(f) = y1 = f^(-1) [cyclotomic: conj = inv] *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t0"; expr.var "f"];
        (* t0 = T13 * y1 = T03 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t1"; expr.var "t0"];
        (* t0 = T03^2 *)
        cmd.call [] fp12_sqr_name
          [expr.var "t0"; expr.var "t0"];
        (* out = T03^2 * T14 = RESULT *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "t0"; expr.var "t2"]
      ].

    Definition bn446_final_exp_hard_dsd : function_t :=
      ("bn446_final_exp_hard_dsd",
       (["out"; "f"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t3;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_c1;
          coq:(final_exp_hard_dsd_body)
        ))).
    (* ============================================================== *)
    (* DSD final exponentiation (easy part + DSD hard part)           *)
    (* ============================================================== *)

    Local Definition final_exp_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] fp12_conjugate_name
          [expr.var "result"; expr.var "f"];
        cmd.call [] fp12_inv_name
          [expr.var "tmp"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "result"; expr.var "tmp"];
        cmd.call [] fp12_frobenius_p2_name
          [expr.var "tmp"; expr.var "result";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "tmp"; expr.var "result"];
        cmd.call [] "bn446_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result"]
      ].

    Definition bn446_final_exp_dsd : function_t :=
      ("bn446_final_exp_dsd",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          coq:(final_exp_dsd_body)
        ))).
    (* ============================================================== *)
    (* Top-level pairing                                               *)
    (* ============================================================== *)

    Local Definition pairing_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] "bn446_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bn446_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bn446_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        cmd.call [] "bn446_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        cmd.call [] "bn446_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bn446_pairing_dsd : function_t :=
      ("bn446_pairing_dsd",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_dsd_body)
        ))).
    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bn446_all_pairing_funcs : list function_t :=
      bn446_Fp6_funcs ++
      bn446_Fp12_funcs ++
      bn446_pairing_ops ++
      [ bn446_Fp2_mul_fp;
        bn446_make_line;
        bn446_load_gamma1_p2;
        bn446_load_gamma2_p2;
        bn446_load_w_frob_p2_c1;
        bn446_load_gamma1;
        bn446_load_gamma2;
        bn446_load_w_frob_c1;
        bn446_Fp12_pow_u;
        bn446_final_exp_hard_dsd;
        bn446_final_exp_dsd;
        bn446_miller_loop;
        bn446_pairing_dsd ].

End BN446_Pairing.
