(** * BN256 Pairing -- bedrock2 compilation top-level.

    Instantiates the full field tower (Fp -> Fp2 -> Fp6 -> Fp12) for
    BN256 and defines bedrock2 function bodies for the optimal
    Ate pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 65 bits of the 6u+2 parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (DSD decomposition -- placeholder, BN-specific formula TBD)
    - Top-level pairing chaining Miller loop + final exponentiation

    BN256 differences from BN254:
    - xi = (3, 1) (not (9, 1)): mul_xi uses multiply-by-3
    - u = 0x5A76AE9AEC588301 (63 bits)
    - |6u+2| = 0x21EC817A18A131208 (66 bits, needs 2 words on stack)
    - Different Frobenius constants
    - u is POSITIVE => NO conjugation after Miller loop

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
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn256_felem_copy.
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
   are in the companion files: BN256_PairingHelpers.v, BN256_MillerLoop.v,
   BN256_PowU.v, BN256_FinalExpHardDSD.v, BN256_FinalExpDSD.v,
   BN256_PairingTop.v. *)

Section BN256_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BN256 prime parameters                                          *)
    (* ============================================================== *)

    Let bn256_M_pos : positive := Eval vm_compute in (Z.to_pos bn256_prime.m).

    Instance bn256_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn256_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn256_mul";
      PrimeField.add := "bn256_add";
      PrimeField.sub := "bn256_sub";
      PrimeField.opp := "bn256_opp";
      PrimeField.square := "bn256_square";
      PrimeField.scmula24 := "bn256_scmula24";
      PrimeField.inv := "bn256_inv";
      PrimeField.from_bytes := "bn256_from_bytes";
      PrimeField.to_bytes := "bn256_to_bytes";
      PrimeField.select_znz := "bn256_select_znz";
      PrimeField.felem_copy := "bn256_felem_copy";
      PrimeField.from_word := "bn256_from_word";
      PrimeField.from_list := "bn256_from_list";
    |}.

    Instance bn256_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn256. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bn256_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn256_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn256_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn256_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn256_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn256_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn256_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn256_frep |}.

    Instance bn256_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn256_fp_rep] in *.
      cbv [Field.bounded_by bn256_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* beta = -1 for BN256 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn256_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (3, 1) for BN256 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn256_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.
    Let bn256_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bn256_beta_nz : bn256_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bn256_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bn256_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* BN256: p = 3 mod 4, so -1 is a QNR.
       Euler criterion: (-1)^((p-1)/2) = -1 /= 1. *)
    Lemma bn256_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bn256_beta).
    Proof.
      intro H.
      assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
        by exact prime_bn256.
      assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bn256_M_big.
      apply (proj2 (@F.euler_criterion _ Hprime Hbig bn256_beta bn256_beta_nz)) in H.
      assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bn256_beta
        (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
      { vm_cast_no_check (eq_refl false). }
      apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
      rewrite Z.eqb_refl in Hcheck. discriminate.
    Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bn256_Fp2_".
    Let fp6_prefix := "bn256_Fp6_".
    Let fp12_prefix := "bn256_Fp12_".

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

    Instance bn256_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn256_beta "bn256_") in exact v).
    Instance bn256_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn256_beta "bn256_") in exact v).
    Instance bn256_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bn256_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bn256_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bn256_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bn256_".

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
    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Let fp2_mul_fp_name : string := "bn256_Fp2_mul_fp".
    Let make_line_name : string := "bn256_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by xi = (3, 1)                *)
    (*   (a0 + a1*u) * (3 + u) = (3*a0 - a1) + (a0 + 3*a1)*u        *)
    (*   where beta = -1, so a1*u*u = -a1                              *)
    (*   Multiply-by-3: x -> 2x -> 2x+x = 3x  (2 adds)               *)
    (* ============================================================== *)

    Definition bn256_Fp2_mul_xi : function_t :=
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
         (* out.re = 3a - b *)
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp_a3"; expr_fp_snd (expr.var "x")]);
         (* out.im = a + 3b *)
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "x"; expr.var "tmp_b3"])
       ))).

    Lemma bn256_Fp2_mul_xi_name_eq : fst bn256_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bn256_Fp6_funcs : list function_t :=
      Fp6_funcs bn256_beta bn256_xi_re bn256_xi_im fp6_prefix fp2_prefix bn256_Fp2_mul_xi.

    Definition bn256_Fp12_funcs : list function_t :=
      Fp12_funcs bn256_beta bn256_xi_re bn256_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bn256_pairing_ops : list function_t :=
      PairingOps_funcs bn256_beta bn256_xi_re bn256_xi_im fp12_prefix fp6_prefix fp2_prefix.

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

    Definition bn256_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).
    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (*   c0 = (lambda*x_T - y_T, -(lambda*x_P), 0)                   *)
    (*   c1 = (0, (y_P, 0), 0)                                        *)
    (* ============================================================== *)

    Definition bn256_make_line : function_t :=
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
    (* ============================================================== *)
    (* Frobenius constant loaders for BN256                            *)
    (*                                                                  *)
    (* p^2-Frobenius constants (imaginary parts are zero):              *)
    (*   gamma1_p2 = xi^{(p^2-1)/3}                                    *)
    (*   gamma2_p2 = xi^{2(p^2-1)/3}                                   *)
    (*   w_frob_p2_c1 = xi^{(p^2-1)/6}                                 *)
    (* ============================================================== *)

    (* Helper: store an Fp2 constant = (real, 0) where real is 4 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal l0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal l1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal l2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal l3);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0)
      ].

    (* Helper: store a full Fp2 constant (real + imaginary, 8 limbs) *)
    Local Definition store_fp2_full (v : string)
      (r0 r1 r2 r3 i0 i1 i2 i3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal r0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal r1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal r2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal r3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal i0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal i1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal i2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal i3)
      ].

    (* gamma1_p2 = xi^{(p^2-1)/3} for BN256 in Montgomery form *)
    Definition bn256_load_gamma1_p2 : function_t :=
      ("bn256_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x12d3cef5e1ada57d 0xe2eca1463753babb 0x0ca41e40ddccf750 0x551337060397e04c)).
    (* gamma2_p2 = xi^{2(p^2-1)/3} for BN256 in Montgomery form *)
    Definition bn256_load_gamma2_p2 : function_t :=
      ("bn256_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x3642364f386c1db8 0xe825f92d2acd661f 0xf2aba7e846c19d14 0x5a0bcea3dc52b7a0)).
    (* w_frob_p2_c1 = xi^{(p^2-1)/6} for BN256 in Montgomery form *)
    Definition bn256_load_w_frob_p2_c1 : function_t :=
      ("bn256_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xe21a761d259c78af 0x06358fa3f5e84f7e 0xb7c444d01ac33f0d 0x35a9333f6e50d058)).
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
    (* Miller loop (real body -- processes 65 bits of |6u+2|)          *)
    (* ============================================================== *)

    (* BN256 parameter u = 0x5A76AE9AEC588301 (positive) *)
    Let bn256_x : Z := 0x5A76AE9AEC588301.

    (* |6u+2| = 39111536946472751624 = 0x21EC817A18A131208, 66 bits.
       Needs two 64-bit words on the stack:
         lo = 0x1EC817A18A131208 (low 64 bits)
         hi = 0x2              (high 2 bits: bits 65-64)
       The leading bit (bit 65) initializes T=Q. We then iterate bits
       64 down to 0, reading from hi (bit 64) then lo (bits 63..0).
       Bit extraction uses two words: for i >= 64, read from hi;
       for i < 64, read from lo. *)

    Definition bn256_6u2_lo : Z := 0x1EC817A18A131208.
    Definition bn256_6u2_hi : Z := 0x2.

    (* Store the two 6u+2 limbs on the stack *)
    Local Definition store_6u2_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var "u6p2") (expr.literal bn256_6u2_lo);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "u6p2") (expr.literal 8))
          (expr.literal bn256_6u2_hi)
      ].

    (* One iteration of the Miller loop:
       - Decrement i
       - Extract bit i from the two-word 6u+2:
         if i >= 64, read from hi word (offset 8), shift by i-64
         if i < 64, read from lo word (offset 0), shift by i
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of 6u+2 is set *)
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
       Processes bits 64 down to 0 of |6u+2| (bit 65 = MSB initializes T = Q).
       BN256 has positive u, so NO conjugation after the loop. *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 65);
        cmd.while (expr.var "i") miller_loop_iteration;
        (* No conjugation needed: BN256 has positive u *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bn256_miller_loop : function_t :=
      ("bn256_miller_loop",
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
    (* Final exponentiation                                            *)
    (*   f^{(p^12-1)/r} = f^{(p^6-1)(p^2+1)*h3}                     *)
    (*   Easy part: conjugate + inv + mul + frobenius_p2 + mul         *)
    (*   Hard part: BN-specific DSD formula (placeholder for now)      *)
    (* ============================================================== *)

    (* ============================================================== *)
    (* Fp12_pow_u: raise Fp12 element to the BN parameter u            *)
    (*   Uses left-to-right binary square-and-multiply on              *)
    (*   u = 0x5A76AE9AEC588301 (63-bit, top bit always set)          *)
    (*   u is POSITIVE for BN256, so NO conjugation after.             *)
    (* ============================================================== *)

    Local Definition pow_u_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.call [] fp12_sqr_name
          [expr.var "result"; expr.var "result"];
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x5A76AE9AEC588301) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bn256_Fp12_pow_u : function_t :=
      ("bn256_Fp12_pow_u",
       (["out"; "base"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          coq:(cmd_seq_list [
            cmd.call [] fp12_copy_name
              [expr.var "result"; expr.var "base"];
            cmd.set "i" (expr.literal 62);
            cmd.while (expr.var "i") pow_u_loop_body;
            cmd.call [] fp12_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).
    (* ============================================================== *)
    (* Frobenius p constant loaders (for DSD final exponentiation)    *)
    (* Constants: gamma1 = xi^{(p-1)/3}, gamma2 = xi^{2(p-1)/3},     *)
    (*   w_frob_c1 = xi^{(p-1)/6} for BN256 in Montgomery form       *)
    (* All imaginary parts are zero.                                   *)
    (* ============================================================== *)

    (* gamma1 = xi^{(p-1)/3} for BN256 in Montgomery form *)
    Definition bn256_load_gamma1 : function_t :=
      ("bn256_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0xf8606916d3816f2c 0x1e5c0d7926de927e 0xbc45f3946d81185e 0x80752a25aa738091
          0x4f59e37c01832e57 0xae6be39ac2bbbfe4 0xe04ea1bb697512f8 0x3097caa8fc40e10e)).
    (* gamma2 = xi^{2(p-1)/3} for BN256 in Montgomery form *)
    Definition bn256_load_gamma2 : function_t :=
      ("bn256_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x4d2ea218872f3d2c 0x2fcb27fc4abe7b69 0xd31d972f0e88ced9 0x53adc04a00a73b15
          0x51678e7469b3c52a 0x4fb98f8b13319fc9 0x29b2254db3f1df75 0x1c044935a3d22fb2)).
    (* w_frob_c1 = xi^{(p-1)/6} for BN256 in Montgomery form *)
    Definition bn256_load_w_frob_c1 : function_t :=
      ("bn256_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x7407634dd9cca958 0x36d5bd6c7afb8f26 0xf4b1c32cebd880fa 0x06aa7869306f455f
          0x25af52988477cdb7 0x3d81a455ddced86a 0x227d012e872c2431 0x0179198d3ea65d05)).
    (* ============================================================== *)
    (* Final exponentiation hard part (Fuentes-Castaneda algorithm)   *)
    (*   BN-specific formula from "Faster Final Exponentiation on     *)
    (*   Ate Pairing" (Fuentes-Castaneda, Knapp, Rodriguez-Henriquez) *)
    (*                                                                  *)
    (*   Registers: t0, t1, t2, t3, out (used as temp in phases)      *)
    (*   3 pow_u calls, 3 sqr, 10 mul, 7 frobenius, 3 conjugate      *)
    (*   BN256 has POSITIVE u, so NO conjugation after pow_u.          *)
    (* ============================================================== *)

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p^1 constants *)
        cmd.call [] "bn256_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bn256_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bn256_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* Phase 1: Powers of u *)
        (* t0 = f^u *)
        cmd.call [] "bn256_Fp12_pow_u"
          [expr.var "t0"; expr.var "f"];
        (* t1 = f^{u^2} *)
        cmd.call [] "bn256_Fp12_pow_u"
          [expr.var "t1"; expr.var "t0"];
        (* t2 = f^{u^3} *)
        cmd.call [] "bn256_Fp12_pow_u"
          [expr.var "t2"; expr.var "t1"];

        (* Phase 2: y6 = conj(f^{u^3} * frobenius(f^{u^3})) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_mul_name
          [expr.var "t2"; expr.var "t2"; expr.var "t3"];
        cmd.call [] fp12_conjugate_name
          [expr.var "t2"; expr.var "t2"];
        (* t2 = y6 *)

        (* Phase 3: out = y6^2 * y4 * y5 *)
        (* out = y6^2 *)
        cmd.call [] fp12_sqr_name
          [expr.var "out"; expr.var "t2"];
        (* t2 = frobenius(f^{u^2}) = f^{u^2 * p} -- save for Phase 5 *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t1";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t3 = f^{u + u^2*p} *)
        cmd.call [] fp12_mul_name
          [expr.var "t3"; expr.var "t0"; expr.var "t2"];
        (* t3 = conj => y4 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t3"; expr.var "t3"];
        (* out = y6^2 * y4 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t3"];
        (* t3 = conj(f^{u^2}) = y5 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t3"; expr.var "t1"];
        (* out = y6^2 * y4 * y5 = T01 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t3"];

        (* Phase 4: t0 = T01 * y3 * y5 = T11 *)
        (* t1 = frobenius(f^u) = f^{u*p} *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "t0";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* t1 = conj => y3 *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];
        (* t0 = T01 * y3 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "out"; expr.var "t1"];
        (* t0 = T01 * y3 * y5 = T11 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t3"];

        (* Phase 5: out = T01 * y2 = T02 *)
        (* t1 = frobenius(t2) = f^{u^2*p^2} = y2 (reuses saved t2) *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        (* out = T01 * y2 = T02 *)
        cmd.call [] fp12_mul_name
          [expr.var "out"; expr.var "out"; expr.var "t1"];

        (* Phase 6: t1 = (T11^2 * T02)^2 = T13 *)
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t0"];
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "out"];
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t1"];
        (* t1 = T13 *)

        (* Phase 7: y0 = f^p * f^{p^2} * f^{p^3} *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t0"; expr.var "f";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t0";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t2"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t3"];
        (* t0 = y0 *)

        (* Phase 8: Final = T13 * y0 combined with T13 * y1 *)
        (* t2 = T13 * y0 = T14 *)
        cmd.call [] fp12_mul_name
          [expr.var "t2"; expr.var "t1"; expr.var "t0"];
        (* t0 = conj(f) = y1 *)
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

    Definition bn256_final_exp_hard_dsd : function_t :=
      ("bn256_final_exp_hard_dsd",
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
    (*   Easy part: same as BLS12 (conjugate/inv/frobenius_p2)         *)
    (*   Hard part: DSD decomposition (placeholder -- BN-specific TBD) *)
    (* ============================================================== *)

    Local Definition final_exp_dsd_body : Syntax.cmd.cmd :=
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
        (* Hard part: DSD decomposition *)
        cmd.call [] "bn256_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result"]
      ].

    Definition bn256_final_exp_dsd : function_t :=
      ("bn256_final_exp_dsd",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          coq:(final_exp_dsd_body)
        ))).
    (* ============================================================== *)
    (* Top-level pairing using DSD final exponentiation                *)
    (* ============================================================== *)

    Local Definition pairing_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p^2 constants *)
        cmd.call [] "bn256_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bn256_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bn256_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bn256_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation (DSD) *)
        cmd.call [] "bn256_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bn256_pairing_dsd : function_t :=
      ("bn256_pairing_dsd",
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

    Definition bn256_all_pairing_funcs : list function_t :=
      bn256_Fp6_funcs ++
      bn256_Fp12_funcs ++
      bn256_pairing_ops ++
      [ bn256_Fp2_mul_fp;
        bn256_make_line;
        bn256_load_gamma1_p2;
        bn256_load_gamma2_p2;
        bn256_load_w_frob_p2_c1;
        bn256_load_gamma1;
        bn256_load_gamma2;
        bn256_load_w_frob_c1;
        bn256_Fp12_pow_u;
        bn256_final_exp_hard_dsd;
        bn256_final_exp_dsd;
        bn256_miller_loop;
        bn256_pairing_dsd ].

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bn256_pairing_dsd" on G1 point P = (p_x,    *)
    (* p_y) and G2 point Q = (q_x, q_y) produces the optimal Ate      *)
    (* pairing e(P, Q) as an Fp12 element.                             *)
    (* ============================================================== *)

End BN256_Pairing.
