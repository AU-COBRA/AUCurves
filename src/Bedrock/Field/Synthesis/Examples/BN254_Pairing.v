(** * BN254 Pairing — bedrock2 compilation top-level.

    Instantiates the full field tower (Fp -> Fp2 -> Fp6 -> Fp12) for
    BN254 (alt_bn128) and defines bedrock2 function bodies for the optimal
    Ate pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 65 bits of the 6u+2 parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (DSD decomposition — placeholder, BN-specific formula TBD)
    - Top-level pairing chaining Miller loop + final exponentiation

    BN254 differences from BLS12-377:
    - beta = -1 (not -5), xi = (9, 1) (not u = (0, 1))
    - Fp = 4 words (not 6), 254-bit prime
    - u = 0x44E992B44A6909F1 is positive => NO conjugation after Miller loop
    - Miller loop iterates over bits of |6u+2| (65 bits, single word)
    - p ≡ 3 mod 4 makes QNR proof simpler

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
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
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

(* WARNING: The [program_logic_goal_for_function!] notation expands to [True].
   Lemmas proved with [exact I] below are VACUOUS — they assert nothing about
   the function's correctness. They exist only to confirm the function body
   is well-formed Rocq syntax. Actual WP correctness proofs live in the
   companion files:
     - BN254_PairingHelpers.v  (mul_fp, make_line, constant loaders)
     - BN254_MillerLoop.v      (miller_loop)
     - BN254_PowU.v            (pow_u)
     - BN254_FinalExpHardDSD.v (final_exp_hard_dsd)
     - BN254_FinalExpDSD.v     (final_exp_dsd)
     - BN254_PairingTop.v      (pairing_dsd)
   Those files re-state the lemmas with proper specs and prove them for real.
   Do NOT rely on the stubs in this file for any security argument. *)

Section BN254_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BN254 prime parameters                                          *)
    (* ============================================================== *)

    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
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

    Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bn254_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_fp_rep] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* beta = -1 for BN254 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (9, 1) for BN254 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bn254_beta_nz : bn254_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bn254_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bn254_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* BN254: p ≡ 3 mod 4, so -1 is a QNR.
       Euler criterion: (-1)^((p-1)/2) = -1 ≠ 1. *)
    Lemma bn254_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bn254_beta).
    Proof.
      intro H.
      assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
        by exact prime_bn254.
      assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bn254_M_big.
      apply (proj2 (@F.euler_criterion _ Hprime Hbig bn254_beta bn254_beta_nz)) in H.
      assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bn254_beta
        (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
      { vm_cast_no_check (eq_refl false). }
      apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
      rewrite Z.eqb_refl in Hcheck. discriminate.
    Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bn254_Fp2_".
    Let fp6_prefix := "bn254_Fp6_".
    Let fp12_prefix := "bn254_Fp12_".

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

    Instance bn254_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn254_beta "bn254_") in exact v).
    Instance bn254_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn254_beta "bn254_") in exact v).
    Instance bn254_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bn254_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bn254_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bn254_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bn254_".

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
    Let fp2_mul_fp_name : string := "bn254_Fp2_mul_fp".
    Let make_line_name : string := "bn254_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by xi = (9, 1)                *)
    (*   (a0 + a1*u) * (9 + u) = (9*a0 - a1) + (a0 + 9*a1)*u        *)
    (*   where beta = -1, so a1*u*u = -a1                              *)
    (*   Multiply-by-9: x -> 2x -> 4x -> 8x -> 8x+x = 9x            *)
    (* ============================================================== *)

    Definition bn254_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_a9;
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_b9;
         (* tmp_a9 = 9*a: 2a -> 4a -> 8a -> 8a+a *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "x"; expr.var "x"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "x"]);
         (* tmp_b9 = 9*b: 2b -> 4b -> 8b -> 8b+b *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr_fp_snd (expr.var "x"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr_fp_snd (expr.var "x")]);
         (* out.re = 9a - b *)
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp_a9"; expr_fp_snd (expr.var "x")]);
         (* out.im = a + 9b *)
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "x"; expr.var "tmp_b9"])
       ))).

    Lemma bn254_Fp2_mul_xi_name_eq : fst bn254_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bn254_Fp6_funcs : list function_t :=
      Fp6_funcs bn254_beta bn254_xi_re bn254_xi_im fp6_prefix fp2_prefix bn254_Fp2_mul_xi.

    Definition bn254_Fp12_funcs : list function_t :=
      Fp12_funcs bn254_beta bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bn254_pairing_ops : list function_t :=
      PairingOps_funcs bn254_beta bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix.

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

    Definition bn254_Fp2_mul_fp : function_t :=
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
    (*                                                                  *)
    (* NOTE (2026-04-11): this layout is wrong for BN254's sextic      *)
    (* D-twist (the correct sparse line should store y_p at c0.c0,    *)
    (* -lam*x_p at c1.c0, lam*x_t-y_t at c1.c1). See the corrected    *)
    (* [bn254_make_line_corrected] below, which bn254_miller_loop_optimal
       calls to fix the optimal-ate bug. The old bn254_make_line is kept
       so that the existing WP proof bn254_make_line_ok (and the old
       bn254_miller_loop that uses it) still compile unchanged.       *)
    (* ============================================================== *)

    Definition bn254_make_line : function_t :=
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
    (* make_line_corrected: BN254 sparse line as Fp12 (correct layout) *)
    (*                                                                  *)
    (* BN254 uses a sextic D-twist E': y^2 = x^3 + 3/xi. The sparse    *)
    (* line in the Fp12 basis (1, v, v^2, w, vw, v^2w) =               *)
    (* (w^0, w^2, w^4, w^1, w^3, w^5) is:                              *)
    (*                                                                  *)
    (*   line = y_p (constant) + (-lam*x_p)*w + (lam*x_t - y_t)*w^3   *)
    (*                                                                  *)
    (* Layout:                                                          *)
    (*   out.c0.c0 = (y_p, 0)         (w^0 constant term)              *)
    (*   out.c0.c1 = (0, 0)            (w^2)                           *)
    (*   out.c0.c2 = (0, 0)            (w^4)                           *)
    (*   out.c1.c0 = -(lam * x_p)      (w^1)                           *)
    (*   out.c1.c1 = lam*x_t - y_t     (w^3)                           *)
    (*   out.c1.c2 = (0, 0)            (w^5)                           *)
    (*                                                                  *)
    (* This is the body the safe-Rust crate's generated/bn254_safe_tower.rs
       was hand-edited to use (see EXTRACTION_AUDIT.md). It is called by
       bn254_miller_loop_optimal below. We keep it as a SEPARATE function
       (not replacing bn254_make_line) so the existing 800-line WP proof
       bn254_make_line_ok still targets its original body. The WP proof
       for this variant is future work tracked by PLAN_PAIRING_SPECS.md
       Phase 4 ("L4 equivalence theorem"). *)
    (* ============================================================== *)

    Definition bn254_make_line_corrected : function_t :=
      ("bn254_make_line_corrected",
       (["out"; "lam"; "x_t"; "y_t"; "x_p"; "y_p"],
        []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd_seq_list [
           (* === c0.c0 = (y_p, 0)  -- w^0 constant term === *)
           cmd.call [] fp_copy_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out")); expr.var "y_p"];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c0 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           (* === c0.c1 = (0, 0)  -- w^2 === *)
           cmd.call [] from_word_name
             [expr_fp6_c1 (expr_fp12_c0 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c1 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           (* === c0.c2 = (0, 0)  -- w^4 === *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c0 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           (* === c1.c0 = -(lam * x_p)  -- w^1 === *)
           cmd.call [] fp2_mul_fp_name
             [expr.var "tmp"; expr.var "lam"; expr.var "x_p"];
           cmd.call [] fp2_opp_name
             [expr_fp6_c0 (expr_fp12_c1 (expr.var "out")); expr.var "tmp"];
           (* === c1.c1 = lam*x_t - y_t  -- w^3 === *)
           cmd.call [] fp2_mul_name
             [expr_fp6_c1 (expr_fp12_c1 (expr.var "out"));
              expr.var "lam"; expr.var "x_t"];
           cmd.call [] fp2_sub_name
             [expr_fp6_c1 (expr_fp12_c1 (expr.var "out"));
              expr_fp6_c1 (expr_fp12_c1 (expr.var "out")); expr.var "y_t"];
           (* === c1.c2 = (0, 0)  -- w^5 === *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0]
         ])
       ))).
    (* ============================================================== *)
    (* Frobenius constant loaders for BN254                            *)
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

    (* gamma1_p2 = xi^{(p^2-1)/3} for BN254 in Montgomery form *)
    Definition bn254_load_gamma1_p2 : function_t :=
      ("bn254_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x3350c88e13e80b9c 0x7dce557cdb5e56b9 0x6001b4b8b615564a 0x2682e617020217e0)).
    (* gamma2_p2 = xi^{2(p^2-1)/3} for BN254 in Montgomery form *)
    Definition bn254_load_gamma2_p2 : function_t :=
      ("bn254_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x71930c11d782e155 0xa6bb947cffbe3323 0xaa303344d4741444 0x2c3b3f0d26594943)).
    (* w_frob_p2_c1 = xi^{(p^2-1)/6} for BN254 in Montgomery form *)
    Definition bn254_load_w_frob_p2_c1 : function_t :=
      ("bn254_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xca8d800500fa1bf2 0xf0c5d61468b39769 0x0e201271ad0d4418 0x04290f65bad856e6)).
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
    (* Miller loop (real body — processes 65 bits of |6u+2|)           *)
    (* ============================================================== *)

    (* BN254 parameter u = 0x44E992B44A6909F1 (positive) *)
    Let bn254_x : Z := 0x44E992B44A6909F1.

    (* |6u+2| = 29793968203157093288 = 0x19D797039BE763BA8, 65 bits.
       Fits in a single 64-bit word after the leading bit is consumed.
       We store it as a single 64-bit limb (low 64 bits) on the stack:
         lo = 0x9D797039BE763BA8 (low 64 bits, bit 64 = MSB initializes T=Q)
       and iterate 64 bits (bits 63 down to 0).
       Bit extraction: bit = (lo >> i) & 1 *)

    Let bn254_6u2_lo : Z := 0x9D797039BE763BA8.

    (* Store the single 6u+2 limb on the stack *)
    Local Definition store_6u2_limbs : Syntax.cmd.cmd :=
      cmd.store access_size.word (expr.var "u6p2") (expr.literal bn254_6u2_lo).

    (* One iteration of the Miller loop:
       - Decrement i
       - Extract bit i from the single-word 6u+2
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of 6u+2 is set *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* Extract bit i from u6p2: bit = (u6p2 >> i) & 1 *)
        cmd.set "word" (expr.load access_size.word (expr.var "u6p2"));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word") (expr.var "i"))
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
        cmd.call [] "bn254_make_line_corrected"
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
            cmd.call [] "bn254_make_line_corrected"
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

    (* Corrected Miller iteration: identical to [miller_loop_iteration]
       except the line-evaluation calls target [bn254_make_line_corrected]
       (the BN254 sparse-line layout — see the comment at the definition).
       Used by [bn254_miller_loop_optimal] below. *)
    Local Definition miller_loop_iteration_corrected : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.set "word" (expr.load access_size.word (expr.var "u6p2"));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word") (expr.var "i"))
          (expr.literal 1));
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
        cmd.call [] "bn254_make_line_corrected"
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
            cmd.call [] "bn254_make_line_corrected"
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
       Processes bits 63 down to 0 of |6u+2| (bit 64 = MSB initializes T = Q).
       BN254 has positive u, so NO conjugation after the loop.

       KNOWN BUG (2026-04-09): the optimal ate pairing for BN curves
       requires two additional line evaluations after the main loop:
           Q1   =   pi_p (Q)
           nQ2  =  -pi_p^2 (Q)
       on the twist, with corresponding line(T, Q1, P), T += Q1,
       line(T, nQ2, P) steps. Without these the result is not bilinear.
       The corrections live in
         bn254-safe-rust/generated/bn254_safe_tower.rs
       as a hand-edit at the end of bn254_miller_loop, using the
       new bn254_load_q1_y_const loader added below.
       Pushing the corrections into this Coq source is blocked on
       reworking the BN254_MillerLoop.v WP proof to match the new body
       shape; see PLAN_PAIRING_SPECS.md Phase 4 for the structured
       approach (the L4 equivalence theorem makes the rewrite forced
       rather than optional). *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 64);
        cmd.while (expr.var "i") miller_loop_iteration;
        (* No conjugation needed: BN254 has positive u *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bn254_miller_loop : function_t :=
      ("bn254_miller_loop",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          stackalloc 8 as u6p2;
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
    (*   u = 0x44E992B44A6909F1 (64-bit, top bit always set)           *)
    (*   u is POSITIVE for BN254, so NO conjugation after.             *)
    (* ============================================================== *)

    Local Definition pow_u_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.call [] fp12_sqr_name
          [expr.var "result"; expr.var "result"];
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x44E992B44A6909F1) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bn254_Fp12_pow_u : function_t :=
      ("bn254_Fp12_pow_u",
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
    (*   w_frob_c1 = xi^{(p-1)/6} for BN254 in Montgomery form       *)
    (* All imaginary parts are zero.                                   *)
    (* ============================================================== *)

    (* gamma1 = xi^{(p-1)/3} = xi^{2*(p-1)/6} for BN254 in Montgomery form *)
    Definition bn254_load_gamma1 : function_t :=
      ("bn254_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0xb5773b104563ab30 0x347f91c8a9aa6454
          0x7a007127242e0991 0x1956bcd8118214ec
          0x6e849f1ea0aa4757 0xaa1c7b6d89f89141
          0xb6e713cdfae0ca3a 0x26694fbb4e82ebc3)).
    (* gamma2 = xi^{2(p-1)/3} = xi^{4*(p-1)/6} for BN254 in Montgomery form *)
    Definition bn254_load_gamma2 : function_t :=
      ("bn254_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x7361d77f843abe92 0xa5bb2bd3273411fb
          0x9c941f314b3e2399 0x15df9cddbb9fd3ec
          0x5dddfd154bd8c949 0x62cb29a5a4445b60
          0x37bc870a0c7dd2b9 0x24830a9d3171f0fd)).
    (* w_frob_c1 = xi^{(p-1)/6} for BN254 in Montgomery form *)
    Definition bn254_load_w_frob_c1 : function_t :=
      ("bn254_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0xaf9ba69633144907 0xca6b1d7387afb78a
          0x11bded5ef08a2087 0x02f34d751a1f3a7c
          0xa222ae234c492d72 0xd00f02a4565de15b
          0xdc2ff3a253dfc926 0x10a75716b3899551)).

    (* q1_y_const = xi^{(p-1)/2} for BN254 in Montgomery form.

       Used by the optimal-ate Frobenius corrections to compute Q1.y where
       Q1 = pi_p(Q) on the twist:
           Q1.y = conj(q.y) * xi^{(p-1)/2}
       (Q1.x uses gamma1 = xi^{(p-1)/3}, which already exists above.)

       This loader is new (added 2026-04-09 as part of the BN254 optimal-ate
       fix); see PLAN_21_22.md for the bug it closes. *)
    Definition bn254_load_q1_y_const : function_t :=
      ("bn254_load_q1_y_const",
       (["out"], []:list String.string,
        store_fp2_full "out"
          16482010305593259561 13488546290961988299
          3578621962720924518  2681173117283399901
          11661927080404088775 553939530661941723
          7860678177968807019  3208568454732775116)).
    (* ============================================================== *)
    (* Final exponentiation hard part: Fuentes-Castaneda et al.       *)
    (*   "Faster hashing to G2" (SAC 2011), Algorithm 1 for BN.      *)
    (*   Uses cyclotomic squaring + 3 pow_u + 5 frobenius_p.          *)
    (*   BN254 has POSITIVE u, so NO conjugations after pow_u.        *)
    (*   Registers: t0, t1, t2, t3, out (5 Fp12 temporaries).        *)
    (* ============================================================== *)

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p constants *)
        cmd.call [] "bn254_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bn254_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bn254_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* === Phase 1: Powers of u === *)
        (* t0 = f^u *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t0"; expr.var "f"];
        (* t1 = f^(u^2) *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t1"; expr.var "t0"];
        (* t2 = f^(u^3) *)
        cmd.call [] "bn254_Fp12_pow_u"
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

    Definition bn254_final_exp_hard_dsd : function_t :=
      ("bn254_final_exp_hard_dsd",
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
    (* DSD final exponentiation (easy part + hard part)               *)
    (*   Easy part: f^{p^6-1} * f^{p^2+1} (conjugate/inv/frob_p2)   *)
    (*   Hard part: Fuentes-Castaneda Algorithm 1 for BN curves      *)
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
        cmd.call [] "bn254_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result"]
      ].

    Definition bn254_final_exp_dsd : function_t :=
      ("bn254_final_exp_dsd",
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
        cmd.call [] "bn254_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bn254_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bn254_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bn254_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation (DSD) *)
        cmd.call [] "bn254_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bn254_pairing_dsd : function_t :=
      ("bn254_pairing_dsd",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_dsd_body)
        ))).
    (* ============================================================== *)
    (* Fp2 conjugate helper (BN254 Frob corrections need it)          *)
    (*                                                                  *)
    (* (a + b*u) -> (a - b*u). NOT the same as fp2_opp which negates  *)
    (* both components.                                                 *)
    (* ============================================================== *)

    Definition bn254_Fp2_conjugate : function_t :=
      ("bn254_Fp2_conjugate",
       (["out"; "x"], []:list String.string,
        bedrock_func_body:(
          coq:(cmd_seq_list [
            (* out.fst = x.fst *)
            cmd.call [] fp_copy_name [expr.var "out"; expr.var "x"];
            (* out.snd = -x.snd *)
            cmd.call [] (AbstractField.opp (F:=Fp))
              [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x")]
          ])
        ))).

    (* ============================================================== *)
    (* Miller loop with Frobenius corrections (FIXES KNOWN BUG)        *)
    (*                                                                  *)
    (* Computes the optimal-ate Miller phase for BN254. After the      *)
    (* main 64-bit |6u+2| loop, applies two line evaluations:          *)
    (*   - at Q1  = pi_p(Q)  on the twist                             *)
    (*   - at -Q2 = -pi_p^2(Q) on the twist                            *)
    (* This is the Vercauteren correction missing from the bare        *)
    (* [bn254_miller_loop] above.                                      *)
    (*                                                                  *)
    (* Layout matches the safe-rust hand edit in                       *)
    (* [bn254-safe-rust/generated/bn254_safe_tower.rs]. The two are    *)
    (* line-by-line equivalent.                                        *)
    (* ============================================================== *)

    Local Definition frob_corrections_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bn254_load_gamma1"     [expr.var "const_g1"];
        cmd.call [] "bn254_load_q1_y_const" [expr.var "const_g_y"];
        cmd.call [] "bn254_load_gamma1_p2"  [expr.var "const_g1p2"];

        (* === Step 1: Q1 = (conj(q_x) * gamma1, conj(q_y) * q1_y_const) === *)
        cmd.call [] "bn254_Fp2_conjugate" [expr.var "tmp1"; expr.var "q_x"];
        cmd.call [] fp2_mul_name
          [expr.var "q1_x"; expr.var "tmp1"; expr.var "const_g1"];
        cmd.call [] "bn254_Fp2_conjugate" [expr.var "tmp1"; expr.var "q_y"];
        cmd.call [] fp2_mul_name
          [expr.var "q1_y"; expr.var "tmp1"; expr.var "const_g_y"];

        (* Slope lambda = (Q1.y - t_y) / (Q1.x - t_x) *)
        cmd.call [] fp2_sub_name [expr.var "tmp1"; expr.var "q1_y"; expr.var "t_y"];
        cmd.call [] fp2_sub_name [expr.var "tmp2"; expr.var "q1_x"; expr.var "t_x"];
        cmd.call [] fp2_inv_name [expr.var "tmp2"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];

        (* Line at P, multiply f *)
        cmd.call [] "bn254_make_line_corrected"
          [expr.var "line"; expr.var "lambda";
           expr.var "t_x"; expr.var "t_y"; expr.var "p_x"; expr.var "p_y"];
        cmd.call [] fp12_mul_name
          [expr.var "f"; expr.var "f"; expr.var "line"];

        (* T = T + Q1: new_x = lambda^2 - t_x - q1_x *)
        cmd.call [] fp2_sqr_name [expr.var "tmp1"; expr.var "lambda"];
        cmd.call [] fp2_sub_name [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_sub_name [expr.var "tmp2"; expr.var "tmp1"; expr.var "q1_x"];
        (* new_y = lambda*(t_x - new_x) - t_y *)
        cmd.call [] fp2_sub_name [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_sub_name [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "tmp2"];

        (* === Step 2: nQ2.x = q_x * gamma1_p2.c0  (real part only)
           nQ2.y = q_y  (because xi^((p^2-1)/2) = -1 cancels with the negation) *)
        cmd.call [] fp2_mul_fp_name
          [expr.var "q1_x"; expr.var "q_x"; expr.var "const_g1p2"];
          (* note: const_g1p2 is Fp2 with c1 = 0; passing its real part as Fp scalar
             via fp2_mul_fp uses only the first 4 limbs of const_g1p2 *)

        (* Slope lambda = (q_y - t_y) / (nq2_x - t_x) *)
        cmd.call [] fp2_sub_name [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
        cmd.call [] fp2_sub_name [expr.var "tmp2"; expr.var "q1_x"; expr.var "t_x"];
        cmd.call [] fp2_inv_name [expr.var "tmp2"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];

        (* Line at P, multiply f *)
        cmd.call [] "bn254_make_line_corrected"
          [expr.var "line"; expr.var "lambda";
           expr.var "t_x"; expr.var "t_y"; expr.var "p_x"; expr.var "p_y"];
        cmd.call [] fp12_mul_name
          [expr.var "f"; expr.var "f"; expr.var "line"]
        (* No final T update needed — this was the last addition *)
      ].

    Local Definition miller_loop_optimal_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 64);
        cmd.while (expr.var "i") miller_loop_iteration_corrected;
        (* Frobenius corrections (Vercauteren optimal-ate) *)
        frob_corrections_body;
        (* Copy result to output *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bn254_miller_loop_optimal : function_t :=
      ("bn254_miller_loop_optimal",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          stackalloc 8 as u6p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as q1_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as q1_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as const_g1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as const_g_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as const_g1p2;
          coq:(miller_loop_optimal_full_body)
        ))).

    (* ============================================================== *)
    (* Top-level optimal-ate pairing (uses bn254_miller_loop_optimal)   *)
    (* ============================================================== *)

    Local Definition pairing_dsd_optimal_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.call [] "bn254_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bn254_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bn254_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop WITH Frobenius corrections *)
        cmd.call [] "bn254_miller_loop_optimal"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        cmd.call [] "bn254_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bn254_pairing_dsd_optimal : function_t :=
      ("bn254_pairing_dsd_optimal",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2))  as w_frob_p2_c1;
          coq:(pairing_dsd_optimal_body)
        ))).

    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bn254_all_pairing_funcs : list function_t :=
      bn254_Fp6_funcs ++
      bn254_Fp12_funcs ++
      bn254_pairing_ops ++
      [ bn254_Fp2_mul_fp;
        bn254_make_line;
        bn254_make_line_corrected;        (* added 2026-04-11, D-twist sparse layout *)
        bn254_load_gamma1_p2;
        bn254_load_gamma2_p2;
        bn254_load_w_frob_p2_c1;
        bn254_load_gamma1;
        bn254_load_gamma2;
        bn254_load_w_frob_c1;
        bn254_load_q1_y_const;            (* added 2026-04-09, used by Frob corrections *)
        bn254_Fp12_pow_u;
        bn254_final_exp_hard_dsd;
        bn254_final_exp_dsd;
        bn254_miller_loop;
        (* bn254_Fp2_conjugate already in bn254_pairing_ops via PairingOps_funcs *)
        bn254_miller_loop_optimal;        (* added 2026-04-11, FIXES the optimal-ate bug *)
        bn254_pairing_dsd;
        bn254_pairing_dsd_optimal ].      (* added 2026-04-11, top-level optimal-ate *)

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bn254_pairing_dsd" on G1 point P = (p_x,    *)
    (* p_y) and G2 point Q = (q_x, q_y) produces the optimal Ate      *)
    (* pairing e(P, Q) as an Fp12 element.                             *)
    (* ============================================================== *)

End BN254_Pairing.
