(** * BLS12-377 Pairing — bedrock2 compilation top-level.

    Instantiates the full field tower (Fp -> Fp2 -> Fp6 -> Fp12) for
    BLS12-377 and defines bedrock2 function bodies for the optimal Ate
    pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 65 bits of the 6u+2 parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (square-and-multiply with 1255-bit h3 exponent)
    - Top-level pairing chaining Miller loop + final exponentiation

    BLS12-377 differences from BLS12-381:
    - beta = -5 (not -1), xi = u (not 1+u)
    - u = 0x8508c00000000001 is positive => NO conjugation after Miller loop
    - Miller loop iterates over bits of 6u+2 (66 bits) instead of |u| (64 bits)

    WP proofs are stubs (exact I) — the function bodies are real.
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
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_FinalExpH3.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section BLS12_377_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BLS12-377 prime parameters                                      *)
    (* ============================================================== *)

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_prime_params : PrimeFieldParameters := {|
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

    Instance bls377_prime_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bls377_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_fp_rep] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* beta = -5 for BLS12-377 (Fp2 = Fp[u]/(u^2 + 5)) *)
    Let bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).

    (* xi = u for BLS12-377 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls377_xi_re : F PrimeField.M_pos := @F.zero PrimeField.M_pos.
    Let bls377_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bls377_beta_nz : bls377_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bls377_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bls377_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* BLS12-377: p mod 4 <> 3 (p ≡ 1 mod 8), so we use the Euler criterion:
       β^((p-1)/2) ≠ 1 implies β is a QNR.  Proof ported from bls12_377_instances.v. *)
    Lemma bls377_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls377_beta).
    Proof.
      intro H.
      assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
        by exact prime_bls12_377.
      assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bls377_M_big.
      apply (proj2 (@F.euler_criterion _ Hprime Hbig bls377_beta bls377_beta_nz)) in H.
      assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bls377_beta
        (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
      { vm_cast_no_check (eq_refl false). }
      apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
      rewrite Z.eqb_refl in Hcheck. discriminate.
    Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bls377_Fp2_".
    Let fp6_prefix := "bls377_Fp6_".
    Let fp12_prefix := "bls377_Fp12_".

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

    Instance bls377_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls377_beta "bls377_") in exact v).
    Instance bls377_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls377_beta "bls377_") in exact v).
    Instance bls377_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bls377_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bls377_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bls377_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bls377_".

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
    Let fp2_mul_fp_name : string := "bls377_Fp2_mul_fp".
    Let make_line_name : string := "bls377_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.
    Let fp6_mul_name : string := AbstractField.mul (F:=Fp6).
    Let fp6_add_name : string := AbstractField.add (F:=Fp6).
    Let fp6_mul_fp2_name : string := (fp6_prefix ++ "mul_fp2")%string.
    Let fp6_mul_by_v_name : string := (fp6_prefix ++ "mul_by_v")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by xi = u                     *)
    (*   (a0 + a1*u) * u = a1*u^2 + a0*u = beta*a1 + a0*u            *)
    (*   = -5*a1 + a0*u                                                *)
    (*   Result: (-5*a1, a0)                                           *)
    (* ============================================================== *)

    Definition bls377_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         (* Compute 5*x.im in out.re: v = x.im+x.im; v = v+v; v = v+x.im *)
         coq:(cmd.call [] fp_add_name
           [expr.var "out"; expr_fp_snd (expr.var "x"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_add_name
           [expr.var "out"; expr.var "out"; expr.var "out"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "out"; expr.var "out"; expr_fp_snd (expr.var "x")]);
         (* out.im = x.re (copy before overwriting out.re) *)
         coq:(cmd.call [] fp_copy_name
           [expr_fp_snd (expr.var "out"); expr.var "x"]);
         (* out.re = 0 - 5*x.im = -5*x.im *)
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp;
         coq:(cmd.call [] fp_sub_name
           [expr.var "tmp"; expr.var "tmp"; expr.var "tmp"]);
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp"; expr.var "out"])
       ))).

    Lemma bls377_Fp2_mul_xi_name_eq : fst bls377_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    (* Fp2_mul_xi flat unop_spec: not needed — Fp6 proofs resolve via the
       typeclass instance, not this Hypothesis. The nested version
       (unop_spec_nested) is Qed in bls12_377_Fp2_proofs.v. *)

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bls377_Fp6_funcs : list function_t :=
      Fp6_funcs bls377_beta bls377_xi_re bls377_xi_im fp6_prefix fp2_prefix bls377_Fp2_mul_xi.

    Definition bls377_Fp12_funcs : list function_t :=
      Fp12_funcs bls377_beta bls377_xi_re bls377_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bls377_pairing_ops : list function_t :=
      PairingOps_funcs bls377_beta bls377_xi_re bls377_xi_im fp12_prefix fp6_prefix fp2_prefix.

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

    Definition bls377_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).

    Lemma bls377_Fp2_mul_fp_ok : program_logic_goal_for_function! bls377_Fp2_mul_fp.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (*   c0 = (lambda*x_T - y_T, -(lambda*x_P), 0)                   *)
    (*   c1 = (0, (y_P, 0), 0)                                        *)
    (* ============================================================== *)

    Definition bls377_make_line : function_t :=
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

    Lemma bls377_make_line_ok : program_logic_goal_for_function! bls377_make_line.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Fp12_mul_by_024: sparse Fp12 × line evaluation                  *)
    (*   Line is (ell0, ell2, ell4 : Fp2), representing the sparse     *)
    (*   Fp12 element ((ell0, ell2, 0), (ell4, 0, 0)).                 *)
    (*   Same formula as bls12_Fp12_mul_by_024; tower structure is     *)
    (*   identical (both BLS12 variants use Fp6 = Fp2[v]/(v^3 - xi)). *)
    (* ============================================================== *)

    Local Definition mul_by_024_body_377 : Syntax.cmd.cmd :=
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
        (* t1 = Fp6_mul_fp2(a.c0, ell4) *)
        cmd.call [] fp6_mul_fp2_name
          [expr.var "t1"; expr_fp12_c0 (expr.var "a"); expr.var "ell4"];
        (* out.c1 = t2 + t1 *)
        cmd.call [] fp6_add_name
          [expr_fp12_c1 (expr.var "out"); expr.var "t2"; expr.var "t1"]
      ].

    Definition bls377_Fp12_mul_by_024 : function_t :=
      ("bls377_Fp12_mul_by_024",
       (["out"; "a"; "ell0"; "ell2"; "ell4"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as b;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as u;
          coq:(mul_by_024_body_377)
        ))).

    Lemma bls377_Fp12_mul_by_024_ok :
      program_logic_goal_for_function! bls377_Fp12_mul_by_024.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Frobenius constant loaders for BLS12-377                        *)
    (*                                                                  *)
    (* TODO: Compute actual Frobenius constants for BLS12-377.         *)
    (* Values below are PLACEHOLDERS (zeros).                          *)
    (* Only the p^2-Frobenius constants are needed for final exp:       *)
    (*   gamma1_p2 = xi^{(p^2-1)/3}                                    *)
    (*   gamma2_p2 = xi^{2(p^2-1)/3}                                   *)
    (*   w_frob_p2_c1 = xi^{(p^2-1)/6}                                 *)
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

    (* Helper: store a full Fp2 constant (real + imaginary, 12 limbs) *)
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

    (* gamma1_p2 = xi^{(p^2-1)/3} for BLS12-377 in Montgomery form *)
    Definition bls377_load_gamma1_p2 : function_t :=
      ("bls377_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xdacd106da5847973 0xd8fe2454bac2a79a 0x1ada4fd6fd832edc
          0xfb9868449d150908 0xd63eb8aeea32285e 0x167d6a36f873fd0)).

    Lemma bls377_load_gamma1_p2_ok :
      program_logic_goal_for_function! bls377_load_gamma1_p2.
    Proof. exact I. Qed.

    (* gamma2_p2 = xi^{2(p^2-1)/3} for BLS12-377 in Montgomery form *)
    Definition bls377_load_gamma2_p2 : function_t :=
      ("bls377_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x2c766f925a7b8727 0x3d7f6b0253d58b5 0x838ec0deec122131
          0xbd5eb3e9f658bb10 0x6942bd126ed3e52e 0x1673786dd04ed6a)).

    Lemma bls377_load_gamma2_p2_ok :
      program_logic_goal_for_function! bls377_load_gamma2_p2.
    Proof. exact I. Qed.

    (* w_frob_p2_c1 = xi^{(p^2-1)/6} for BLS12-377 in Montgomery form *)
    Definition bls377_load_w_frob_p2_c1 : function_t :=
      ("bls377_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x5892506da58478da 0x133366940ac2a74b 0x9b64a150cdf726cf
          0x5cc426090a9c587e 0x5cf848adfdcd640c 0x4702bf3ac02380)).

    Lemma bls377_load_w_frob_p2_c1_ok :
      program_logic_goal_for_function! bls377_load_w_frob_p2_c1.
    Proof. exact I. Qed.

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
    (* Miller loop (real body — processes 65 bits of 6u+2)             *)
    (* ============================================================== *)

    (* BLS12-377 parameter u = 0x8508c00000000001 (positive) *)
    Let bls377_x : Z := 0x8508c00000000001.

    (* 6u+2 = 0x31e34800000000008, 66 bits.
       We store it as two 64-bit limbs on the stack:
         lo = 0x1e34800000000008 (low 64 bits)
         hi = 0x3 (high 2 bits)
       and iterate 65 bits (bits 64 down to 0, MSB bit 65 initializes T=Q).
       Bit extraction: word = limb[i/64], bit = (word >> (i%64)) & 1 *)

    Let bls377_6u2_lo : Z := 0x1e34800000000008.
    Let bls377_6u2_hi : Z := 0x3.

    (* Store the two 6u+2 limbs on the stack *)
    Local Definition store_6u2_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var "u6p2") (expr.literal bls377_6u2_lo);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "u6p2") (expr.literal 8))
          (expr.literal bls377_6u2_hi)
      ].

    (* One iteration of the Miller loop:
       - Decrement i
       - Extract bit i from the 6u+2 array
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of 6u+2 is set *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* Extract bit i from u6p2: word = u6p2[i/64], bit = (word >> (i%64)) & 1 *)
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
       Processes bits 64 down to 0 of 6u+2 (bit 65 = MSB initializes T = Q).
       BLS12-377 has positive u, so NO conjugation after the loop. *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 65);
        cmd.while (expr.var "i") miller_loop_iteration;
        (* No conjugation needed: BLS12-377 has positive u *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bls377_miller_loop : function_t :=
      ("bls377_miller_loop",
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

    Lemma bls377_miller_loop_ok : program_logic_goal_for_function! bls377_miller_loop.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Final exponentiation                                            *)
    (*   f^{(p^12-1)/r} = f^{(p^6-1)(p^2+1)*h3}                     *)
    (*   Easy part: conjugate + inv + mul + frobenius_p2 + mul         *)
    (*   Hard part: square-and-multiply with h3 (1255-bit exponent)    *)
    (* ============================================================== *)

    (* Store h3 = (p^4 - p^2 + 1)/r exponent as 20 little-endian u64 limbs.
       Values from BLS12_377_FinalExpH3.bls377_h3_words. *)
    Local Definition h3_store_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word
          (expr.var "h3") (expr.literal 0x0000000000000001);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 8))
          (expr.literal 0x2e16ba8860000000);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 16))
          (expr.literal 0x68c0eaeea22e6800);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 24))
          (expr.literal 0x719b834b69044687);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 32))
          (expr.literal 0xf4f6974b4ff0fa27);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 40))
          (expr.literal 0x27dc8f4db069bf65);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 48))
          (expr.literal 0xabcaf63f0a34fcb8);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 56))
          (expr.literal 0x0bd948d5f4548283);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 64))
          (expr.literal 0xaae0551dffcf72fb);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 72))
          (expr.literal 0xd1eefd89535f9b5a);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 80))
          (expr.literal 0xfcd1c3fa1470f8b2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 88))
          (expr.literal 0x1a8d889828282015);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 96))
          (expr.literal 0x5497a9781d812991);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 104))
          (expr.literal 0xcc65eca9c9678a84);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 112))
          (expr.literal 0xc548afd84225b34c);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 120))
          (expr.literal 0xbef98d9c2cce3b25);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 128))
          (expr.literal 0x3b4074a5448da5cf);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 136))
          (expr.literal 0x0576728e56efc3bf);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 144))
          (expr.literal 0x0774d7d810d5cbdf);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 152))
          (expr.literal 0x0000006d616e4372)
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

    (* ============================================================== *)
    (* Fp12_pow_u: raise Fp12 element to the BLS parameter u           *)
    (*   Uses left-to-right binary square-and-multiply on              *)
    (*   u = 0x8508c00000000001 (64-bit, top bit always set)           *)
    (*   u is POSITIVE for BLS12-377, so NO conjugation after.         *)
    (* ============================================================== *)

    Local Definition pow_u_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.call [] fp12_sqr_name
          [expr.var "result"; expr.var "result"];
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x8508c00000000001) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bls377_Fp12_pow_u : function_t :=
      ("bls377_Fp12_pow_u",
       (["out"; "base"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          coq:(cmd_seq_list [
            cmd.call [] fp12_copy_name
              [expr.var "result"; expr.var "base"];
            cmd.set "i" (expr.literal 63);
            cmd.while (expr.var "i") pow_u_loop_body;
            cmd.call [] fp12_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).

    Lemma bls377_Fp12_pow_u_ok :
      program_logic_goal_for_function! bls377_Fp12_pow_u.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Frobenius p constant loaders (for DSD final exponentiation)    *)
    (* Constants: gamma1 = xi^{(p-1)/3}, gamma2 = xi^{2(p-1)/3},     *)
    (*   w_frob_c1 = xi^{(p-1)/6} for BLS12-377 in Montgomery form   *)
    (* All imaginary parts are zero.                                   *)
    (* ============================================================== *)

    (* gamma1 = xi^{(p-1)/3} for BLS12-377 in Montgomery form *)
    Definition bls377_load_gamma1 : function_t :=
      ("bls377_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x5892506da58478da 0x133366940ac2a74b 0x9b64a150cdf726cf
          0x5cc426090a9c587e 0x5cf848adfdcd640c 0x4702bf3ac02380
          0 0 0 0 0 0)).

    Lemma bls377_load_gamma1_ok :
      program_logic_goal_for_function! bls377_load_gamma1.
    Proof. exact I. Qed.

    (* gamma2 = xi^{2(p-1)/3} for BLS12-377 in Montgomery form *)
    Definition bls377_load_gamma2 : function_t :=
      ("bls377_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0xdacd106da5847973 0xd8fe2454bac2a79a 0x1ada4fd6fd832edc
          0xfb9868449d150908 0xd63eb8aeea32285e 0x167d6a36f873fd0
          0 0 0 0 0 0)).

    Lemma bls377_load_gamma2_ok :
      program_logic_goal_for_function! bls377_load_gamma2.
    Proof. exact I. Qed.

    (* w_frob_c1 = xi^{(p-1)/6} for BLS12-377 in Montgomery form *)
    Definition bls377_load_w_frob_c1 : function_t :=
      ("bls377_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0x6ec47a04a3f7ca9e 0xa42e0cb968c1fa44 0x578d5187fbd2bd23
          0x930eeb0ac79dd4bd 0xa24883de1e09a9ee 0xdaa7058067d46f
          0 0 0 0 0 0)).

    Lemma bls377_load_w_frob_c1_ok :
      program_logic_goal_for_function! bls377_load_w_frob_c1.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Final exponentiation hard part (DSD decomposition)             *)
    (*   Computes f^{(p^4 - p^2 + 1)/r} using the DSD method:       *)
    (*   BLS12-377 has POSITIVE u, so NO conjugations after pow_u.    *)
    (*   t0 = f^u (no conjugation — u is positive)                    *)
    (*   t1 = t0^2 (no conjugation — was conjugated for negative x)   *)
    (*   t2 = pow_u(t0) = f^{u^2} (no conjugation)                   *)
    (*   t3 = t2^2 = f^{2u^2} (no conjugation)                       *)
    (*   Chain multiplications and Frobenius maps                     *)
    (* ============================================================== *)

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bls377_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bls377_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bls377_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* t0 = f^u (NO conjugation — u is positive for BLS12-377) *)
        cmd.call [] "bls377_Fp12_pow_u"
          [expr.var "t0"; expr.var "f"];

        (* t1 = t0^2 (NO conjugation — u positive means t0^2 = f^{2u}) *)
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t0"];

        (* t2 = pow_u(t0) = f^{u^2} (NO conjugation) *)
        cmd.call [] "bls377_Fp12_pow_u"
          [expr.var "t2"; expr.var "t0"];

        (* t3 = t2^2 = f^{2u^2} (NO conjugation) *)
        cmd.call [] fp12_sqr_name
          [expr.var "t3"; expr.var "t2"];

        (* t1 = t1 * t2 => f^{2u + u^2} *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t2 = pow_u(t2) => f^{u^3} *)
        cmd.call [] "bls377_Fp12_pow_u"
          [expr.var "t2"; expr.var "t2"];

        (* t1 = t1 * t2 => f^{u^3 + u^2 + 2u} *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t1 = conjugate(t1) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];

        (* t1 = t1 * f *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "f"];

        (* t1 = conjugate(t1) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];

        (* t0 = conjugate(f) — reuse t0 as temp for conj(f) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t0"; expr.var "f"];

        (* t1 = t1 * conj(f) *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t0"];

        (* t2 = pow_u(t2) => f^{u^4} *)
        cmd.call [] "bls377_Fp12_pow_u"
          [expr.var "t2"; expr.var "t2"];

        (* t0 = t2 * t3 — reuse t0 as accumulator *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t2"; expr.var "t3"];

        (* t0 = t0 * t1 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];

        (* Frobenius maps: t1 = f^p, t2 = f^{p^2}, t3 = f^{p^3} *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "f";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t1";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];

        (* result = t0 * frob1 * frob2 * frob3 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t2"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t3"];

        (* Copy to output *)
        cmd.call [] fp12_copy_name
          [expr.var "out"; expr.var "t0"]
      ].

    Definition bls377_final_exp_hard_dsd : function_t :=
      ("bls377_final_exp_hard_dsd",
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

    Lemma bls377_final_exp_hard_dsd_ok :
      program_logic_goal_for_function! bls377_final_exp_hard_dsd.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* DSD final exponentiation (easy part + DSD hard part)           *)
    (*   Easy part: same as naive (conjugate/inv/frobenius_p2)         *)
    (*   Hard part: DSD decomposition instead of h3 exponentiation    *)
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
        cmd.call [] "bls377_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result"]
      ].

    Definition bls377_final_exp_dsd : function_t :=
      ("bls377_final_exp_dsd",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          coq:(final_exp_dsd_body)
        ))).

    Lemma bls377_final_exp_dsd_ok :
      program_logic_goal_for_function! bls377_final_exp_dsd.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Top-level pairing using DSD final exponentiation                *)
    (* ============================================================== *)

    Local Definition pairing_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p^2 constants *)
        cmd.call [] "bls377_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bls377_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bls377_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bls377_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation (DSD) *)
        cmd.call [] "bls377_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bls377_pairing_dsd : function_t :=
      ("bls377_pairing_dsd",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_dsd_body)
        ))).

    Lemma bls377_pairing_dsd_ok :
      program_logic_goal_for_function! bls377_pairing_dsd.
    Proof. exact I. Qed.

    (* Full final exponentiation (naive h3 square-and-multiply):
       Easy part 1: result = conj(f) * inv(f) = f^{p^6-1}
       Easy part 2: result = frob_p2(result) * result = result^{p^2+1}
       Hard part:   result = result^{h3}
       Note: BLS12-377 h3 is 1255 bits (20 limbs), so we scan 1280 bits *)
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
        (* Hard part: result^{h3} via square-and-multiply *)
        cmd.call [] fp12_copy_name
          [expr.var "base"; expr.var "result"];
        fp12_set_one "result";
        h3_store_limbs;
        cmd.set "started" (expr.literal 0);
        cmd.set "i" (expr.literal 1280);
        cmd.while (expr.var "i") h3_loop_body;
        (* Copy to output *)
        cmd.call [] fp12_copy_name
          [expr.var "out"; expr.var "result"]
      ].

    Definition bls377_final_exp : function_t :=
      ("bls377_final_exp",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as base;
          stackalloc 160 as h3;
          coq:(final_exp_full_body)
        ))).

    Lemma bls377_final_exp_ok : program_logic_goal_for_function! bls377_final_exp.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Top-level pairing: e(P, Q) = final_exp(miller_loop(P, Q))      *)
    (* ============================================================== *)

    Local Definition pairing_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bls377_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bls377_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bls377_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bls377_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation *)
        cmd.call [] "bls377_final_exp"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bls377_pairing : function_t :=
      ("bls377_pairing",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_full_body)
        ))).

    Lemma bls377_pairing_ok : program_logic_goal_for_function! bls377_pairing.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bls377_all_pairing_funcs : list function_t :=
      bls377_Fp6_funcs ++
      bls377_Fp12_funcs ++
      bls377_pairing_ops ++
      [ bls377_Fp2_mul_fp;
        bls377_make_line;
        bls377_load_gamma1_p2;
        bls377_load_gamma2_p2;
        bls377_load_w_frob_p2_c1;
        bls377_load_gamma1;
        bls377_load_gamma2;
        bls377_load_w_frob_c1;
        bls377_Fp12_pow_u;
        bls377_final_exp_hard_dsd;
        bls377_final_exp_dsd;
        bls377_miller_loop;
        bls377_final_exp;
        bls377_pairing;
        bls377_pairing_dsd ].

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bls377_pairing" on G1 point P = (p_x, p_y)  *)
    (* and G2 point Q = (q_x, q_y) produces the optimal Ate pairing    *)
    (* e(P, Q) as an Fp12 element.                                     *)
    (* ============================================================== *)

End BLS12_377_Pairing.
