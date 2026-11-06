(** * Miller loop body fragments with feval tracking.

    The body of the while loop of [bls12_miller_loop] is [BLS12_Pairing.miller_loop_iteration]
    = cmd_seq_list [set i; D1 .. D16; set bit; cond bit (cmd_seq_list [A1 .. A13]) skip].
    [miller_iteration_split] restates it, by conversion, as
      cmd.seq (set i) (cmd_seq_k miller_doubling_calls (cmd.seq (set bit) (cond ...)))
    so the doubling calls D1 .. D16 are a command prefix in continuation form, and the
    addition step is the closed command [miller_addition_cmd].  The bedrock2 code is not changed.

    [miller_doubling_ok] and [miller_addition_ok] are the WP lemmas of the two fragments: they
    track feval of f, T = (t_x, t_y), lambda and line and state that the results are the
    feval models [dbl_model] / [add_model], which [dbl_model_eq] / [add_model_eq] identify with
    the components of [BLS12_Fp12Feval.bedrock2_miller_step] (bit false / bit true).
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
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2Feval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MakeLineFunctional.
Require Theory.BLS12Pairing.Fp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp12Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import bedrock2.Loops.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_MillerStepFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-381 prime parameters *)
    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_pf_params : PrimeFieldParameters := {|
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

    Instance bls12_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bls12_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_Fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bls12_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bls12_beta "bls12_".
    Instance bls12_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bls12_beta "bls12_".
    Instance bls12_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bls12_beta bls12_xi_re bls12_xi_im "bls12_".
    Instance bls12_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_".
    Instance bls12_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bls12_beta bls12_xi_re bls12_xi_im "bls12_".
    Instance bls12_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_".

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_add.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.un_square.

    Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.un_inv.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bls12_Fp2_rep').

    (* Fp12 operations *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.bin_mul.

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.un_square.

    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bls12_Fp12_rep').

    (* Fp operations needed by make_line *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls12_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bls12_Fp_rep).

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls12_Fp_rep).

    (* ============================================================ *)
    (* The loop body as a command prefix                             *)
    (* ============================================================ *)

    Fixpoint cmd_seq_k (cs : list Syntax.cmd.cmd) (k : Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cs with
      | [] => k
      | c :: rest => cmd.seq c (cmd_seq_k rest k)
      end.

    Definition miller_iteration_cmds : list Syntax.cmd.cmd :=
      ltac:(let v := eval cbv delta [BLS12_Pairing.miller_loop_iteration] in
                      BLS12_Pairing.miller_loop_iteration in
            let w := eval cbv beta zeta in v in
            lazymatch w with
            | BLS12_Pairing.cmd_seq_list ?L => exact L
            end).

    Definition miller_doubling_calls : list Syntax.cmd.cmd :=
      ltac:(let v := eval cbv [miller_iteration_cmds firstn skipn] in
                      (firstn 16 (skipn 1 miller_iteration_cmds)) in exact v).

    Definition miller_bit_cmd : Syntax.cmd.cmd :=
      ltac:(let v := eval cbv [miller_iteration_cmds nth] in
                      (nth 17 miller_iteration_cmds cmd.skip) in exact v).

    Definition miller_cond_cmd : Syntax.cmd.cmd :=
      ltac:(let v := eval cbv [miller_iteration_cmds nth] in
                      (nth 18 miller_iteration_cmds cmd.skip) in exact v).

    Definition miller_addition_calls : list Syntax.cmd.cmd :=
      ltac:(lazymatch eval cbv [miller_cond_cmd] in miller_cond_cmd with
            | cmd.cond _ (BLS12_Pairing.cmd_seq_list ?L) cmd.skip => exact L
            end).

    Definition miller_addition_cmd : Syntax.cmd.cmd :=
      BLS12_Pairing.cmd_seq_list miller_addition_calls.

    Lemma miller_iteration_split :
      BLS12_Pairing.miller_loop_iteration =
      cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
        (cmd_seq_k miller_doubling_calls (cmd.seq miller_bit_cmd miller_cond_cmd)).
    Proof. reflexivity. Qed.

    Lemma miller_cond_cmd_eq :
      miller_cond_cmd = cmd.cond (expr.var "bit") miller_addition_cmd cmd.skip.
    Proof. reflexivity. Qed.

    (* ============================================================ *)
    (* Feval models of the two fragments                             *)
    (* ============================================================ *)

    Local Notation F2mul := (@AbstractField.Fmul _ bls12_Fp2_params').
    Local Notation F2add := (@AbstractField.Fadd _ bls12_Fp2_params').
    Local Notation F2sub := (@AbstractField.Fsub _ bls12_Fp2_params').
    Local Notation F2inv := (@AbstractField.Finv _ bls12_Fp2_params').
    Local Notation F12mul := (@AbstractField.Fmul _ bls12_Fp12_params').

    (** Doubling: D1..D6 compute lambda, D7 the line, D8/D9 f, D10..D16 the point. *)
    Definition dbl_lambda (tx ty : Fp2) : Fp2 :=
      let t1 := F2mul tx tx in
      F2mul (F2add (F2add t1 t1) t1) (F2inv (F2add ty ty)).

    Definition dbl_point (tx ty lam : Fp2) : Fp2 * Fp2 :=
      let x' := F2sub (F2sub (F2mul lam lam) tx) tx in
      (x', F2sub (F2mul lam (F2sub tx x')) ty).

    Definition dbl_model (f : Fp12) (tx ty : Fp2) (xp yp : Fp) : Fp12 * (Fp2 * Fp2) :=
      let lam := dbl_lambda tx ty in
      (F12mul (F12mul f f) (make_line_feval_model lam tx ty xp yp), dbl_point tx ty lam).

    (** Addition: A1..A4 lambda, A5 line, A6 f, A7..A13 the point. *)
    Definition add_lambda (tx ty qx qy : Fp2) : Fp2 :=
      F2mul (F2sub qy ty) (F2inv (F2sub qx tx)).

    Definition add_point (tx ty qx lam : Fp2) : Fp2 * Fp2 :=
      let x' := F2sub (F2sub (F2mul lam lam) tx) qx in
      (x', F2sub (F2mul lam (F2sub tx x')) ty).

    Definition add_model (f : Fp12) (tx ty qx qy : Fp2) (xp yp : Fp) : Fp12 * (Fp2 * Fp2) :=
      let lam := add_lambda tx ty qx qy in
      (F12mul f (make_line_feval_model lam tx ty xp yp), add_point tx ty qx lam).

    (** One iteration (bit = false: doubling only; bit = true: doubling then addition). *)
    Definition step_model (qx qy : Fp2) (xp yp : Fp) (st : Fp12 * (Fp2 * Fp2)) (bit : bool)
      : Fp12 * (Fp2 * Fp2) :=
      let '(f, (tx, ty)) := st in
      let '(f', (tx', ty')) := dbl_model f tx ty xp yp in
      if bit then add_model f' tx' ty' qx qy xp yp else (f', (tx', ty')).

    (* ============================================================ *)
    (* Bridge to BLS12_Fp12Feval.bedrock2_miller_step                *)
    (* ============================================================ *)

    Local Opaque Pairing.fp2_mul Pairing.fp2_sqr Pairing.fp2_inv Pairing.fp2_add Pairing.fp2_sub
      Pairing.make_line Fp12.fp12_mul.

    (** The Fp2 inverse of the bedrock2 model is [QuadraticExtensions.invp2]; its equality with
        [Pairing.fp2_inv] for BLS12-381 is taken as a hypothesis here (as the Fp6 bridges are
        in BLS12_Fp12Feval.v). *)
    Lemma step_model_eq
      (Hinv : forall a : Fp2, F2inv a = Pairing.fp2_inv PrimeField.M_pos a) :
      forall qx qy xp yp st bit,
        step_model qx qy xp yp st bit =
        BLS12_Fp12Feval.bedrock2_miller_step PrimeField.M_pos qx qy xp yp st bit.
    Proof.
      intros qx qy xp yp [f [tx ty]] bit.
      unfold step_model, dbl_model, dbl_lambda, dbl_point, add_model, add_lambda, add_point,
        BLS12_Fp12Feval.bedrock2_miller_step, Pairing.ec2_double_with_lambda,
        Pairing.ec2_add_with_lambda.
      rewrite !Hinv.
      change (@AbstractField.Fmul _ bls12_Fp2_params')
        with (QuadraticExtensions.mulp2 PrimeField.M_pos (F.of_Z PrimeField.M_pos (-1))).
      change (@AbstractField.Fadd _ bls12_Fp2_params')
        with (QuadraticExtensions.addp2 PrimeField.M_pos).
      change (@AbstractField.Fsub _ bls12_Fp2_params')
        with (QuadraticExtensions.subp2 PrimeField.M_pos).
      rewrite !BLS12_Fp2Feval.sqrp2_eq_fp2_sqr, !BLS12_Fp2Feval.mulp2_eq_fp2_mul.
      rewrite !BLS12_Fp2Feval.addp2_eq_fp2_add, !BLS12_Fp2Feval.subp2_eq_fp2_sub.
      rewrite !make_line_feval_model_eq.
      destruct bit; reflexivity.
    Qed.

    Local Transparent Pairing.fp2_mul Pairing.fp2_sqr Pairing.fp2_inv Pairing.fp2_add Pairing.fp2_sub
      Pairing.make_line Fp12.fp12_mul.

    (* ============================================================ *)
    (* Feval chains (pure): per-call equations -> models             *)
    (* ============================================================ *)

    Lemma dbl_chain (vf vf1 vf2 vln : Fp12)
      (vtx vty v1 v2 v3 v4 v5 v6 v10 v11 v12 v13 v14 v15 : Fp2) (vxp vyp : Fp) :
      v1 = F2mul vtx vtx -> v2 = F2add v1 v1 -> v3 = F2add v2 v1 ->
      v4 = F2add vty vty -> v5 = F2inv v4 -> v6 = F2mul v3 v5 ->
      vln = make_line_feval_model v6 vtx vty vxp vyp ->
      vf1 = F12mul vf vf -> vf2 = F12mul vf1 vln ->
      v10 = F2mul v6 v6 -> v11 = F2sub v10 vtx -> v12 = F2sub v11 vtx ->
      v13 = F2sub vtx v12 -> v14 = F2mul v6 v13 -> v15 = F2sub v14 vty ->
      vf2 = fst (dbl_model vf vtx vty vxp vyp) /\
      v12 = fst (snd (dbl_model vf vtx vty vxp vyp)) /\
      v15 = snd (snd (dbl_model vf vtx vty vxp vyp)) /\
      v6 = dbl_lambda vtx vty /\
      vln = make_line_feval_model (dbl_lambda vtx vty) vtx vty vxp vyp.
    Proof.
      intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
      subst. repeat split.
    Qed.

    Lemma add_chain (vf vf1 vln : Fp12)
      (vtx vty vqx vqy v1 v2 v3 v4 v7 v8 v9 v10 v11 v12 : Fp2) (vxp vyp : Fp) :
      v1 = F2sub vqy vty -> v2 = F2sub vqx vtx -> v3 = F2inv v2 -> v4 = F2mul v1 v3 ->
      vln = make_line_feval_model v4 vtx vty vxp vyp ->
      vf1 = F12mul vf vln ->
      v7 = F2mul v4 v4 -> v8 = F2sub v7 vtx -> v9 = F2sub v8 vqx ->
      v10 = F2sub vtx v9 -> v11 = F2mul v4 v10 -> v12 = F2sub v11 vty ->
      vf1 = fst (add_model vf vtx vty vqx vqy vxp vyp) /\
      v9 = fst (snd (add_model vf vtx vty vqx vqy vxp vyp)) /\
      v12 = snd (snd (add_model vf vtx vty vqx vqy vxp vyp)) /\
      v4 = add_lambda vtx vty vqx vqy /\
      vln = make_line_feval_model (add_lambda vtx vty vqx vqy) vtx vty vxp vyp.
    Proof.
      intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
      subst. repeat split.
    Qed.


    (* ============================================================ *)
    (* make_line with feval (from BLS12_MakeLineFunctional.v)        *)
    (* ============================================================ *)

    Definition spec_of_make_line_f : spec_of "bls12_make_line" :=
      fnspec! "bls12_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp12_felem) (lam xt yt : Fp2_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight lam /\
          Fp2_bounded Fp2_tight xt /\
          Fp2_bounded Fp2_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp2 plam lam ⋆
            (FElem_Fp2 pxt xt ⋆
             (FElem_Fp2 pyt yt ⋆
              (FElem_Fp pxp xp ⋆
               (FElem_Fp pyp yp ⋆ Rr)))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_feval out =
              make_line_feval_model (Fp2_feval lam) (Fp2_feval xt) (Fp2_feval yt)
                (Fp_feval xp) (Fp_feval yp) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp2 plam lam ⋆
              (FElem_Fp2 pxt xt ⋆
               (FElem_Fp2 pyt yt ⋆
                (FElem_Fp pxp xp ⋆
                 (FElem_Fp pyp yp ⋆ Rr)))))) mem' }.

    Lemma make_line_f_ok :
      forall functions
        (HMakeLine : map.get functions "bls12_make_line" = Some (snd bls12_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfpEnv : map.get functions "bls12_Fp2_mul_fp" = Some (snd bls12_Fp2_mul_fp))
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      spec_of_make_line_f functions.
    Proof.
      intros. unfold spec_of_make_line_f.
      intros pout' plam' pxt' pyt' pxp' pyp' old_out' lam' xt' yt' xp' yp' Rr' tr' mem'
        [Hblam' [Hbxt' [Hbyt' [Hbxp' [Hbyp' Hsep']]]]].
      eapply Semantics.weaken_call.
      { eapply (bls12_make_line_functional_ok functions HMakeLine
                 HFp2mul HFp2sub HFp2opp
                 (bls12_Fp2_mul_fp_ok functions HFp2mulfpEnv HFpmul)
                 HFpcopy HFfromword).
        split; [exact Hblam' |].
        split; [exact Hbxt' |].
        split; [exact Hbyt' |].
        split; [exact Hbxp' |].
        split; [exact Hbyp' |].
        exact Hsep'. }
      cbv beta. intros t' m' rets [Hrets [Htr' [out' [Hf' [Hb' Hs']]]]].
      subst. exact (conj eq_refl (conj eq_refl (ex_intro _ out' (conj Hf' (conj Hb' Hs'))))).
    Qed.

    (* ============================================================ *)
    (* Tactics (from BLS12_MillerLoop.v, keeping the feval facts)    *)
    (* ============================================================ *)

    Local Ltac resolve_map_get := BLS12_MillerGeneric.miller_resolve_map_get.
    Local Ltac miller_straightline := BLS12_MillerGeneric.miller_straightline.
    Local Ltac eval_dexprs_abstract := BLS12_MillerGeneric.miller_eval_dexprs_abstract.
    Local Ltac solve_miller_bounds := BLS12_MillerGeneric.miller_solve_bounds.

    Local Ltac solve_mapget :=
      match goal with
      | |- map.get _ _ = Some _ =>
        first
        [ exact eq_refl
        | assumption
        | match goal with
          | H : map.get _ ?k = Some _ |- map.get _ ?k = Some _ => exact H
          end ]
      end.

    Local Ltac solve_leaf :=
      first
      [ eexists; ecancel_assumption_with_copy
      | ecancel_assumption_with_copy
      | solve_miller_bounds
      | solve_mapget ].

    Local Ltac solve_precond :=
      match goal with
      | |- _ /\ _ => split; [| solve_precond]; solve_leaf
      | _ => solve_leaf
      end.

    (* Feval facts are kept behind an inductive wrapper so that the bound and
       separation solvers (eassumption, exact H) do not try them. *)
    Record hidden (P : Prop) : Prop := hide { unhide : P }.

    (* one call; keeps the output name [vo] and its feval fact [hf] (hidden) *)
    Local Ltac mcallf spec vo hf :=
      try miller_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ eapply spec; solve_precond
      | cbv beta; intros ? ? ? [? [? ?]]; subst;
        cbv [map.putmany_of_list_zip];
        eexists; split; [exact eq_refl |] ];
      match goal with
      | Hrem : exists _, _ /\ _ /\ _ |- _ => destruct Hrem as [vo [hf [?Hb ?Hs]]];
                                             apply (@hide _) in hf
      end.

    Local Ltac mcopy spec :=
      try miller_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ eapply spec; solve_precond
      | cbv beta; intros ? ? ? [? [? ?]]; subst;
        cbv [map.putmany_of_list_zip];
        eexists; split; [exact eq_refl |] ].

    Local Ltac norm_feval H :=
      destruct H as [H];
      cbv [AbstractField.un_model AbstractField.bin_model AbstractField.un_square
           AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub
           AbstractField.un_inv AbstractField.Fsquare] in H.

    (* ============================================================ *)
    (* Doubling fragment                                             *)
    (* ============================================================ *)

    Local Notation dbl_sep a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
        f tx ty lam tmp1 tmp2 line xp yp R :=
      (FElem_Fp12 a_f f ⋆
       (FElem_Fp2 a_tx tx ⋆
        (FElem_Fp2 a_ty ty ⋆
         (FElem_Fp2 a_lam lam ⋆
          (FElem_Fp2 a_tmp1 tmp1 ⋆
           (FElem_Fp2 a_tmp2 tmp2 ⋆
            (FElem_Fp12 a_line line ⋆
             (FElem_Fp p_px xp ⋆
              (FElem_Fp p_py yp ⋆ R))))))))) (only parsing).

    Lemma miller_doubling_ok :
      forall functions
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2add : spec_of_Fp2_add functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HML : spec_of_make_line_f functions)
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py : word)
        (f : Fp12_felem) (tx ty lam tmp1 tmp2 : Fp2_felem) (line : Fp12_felem)
        (xp yp : Fp_felem) (R : mem -> Prop)
        (rest : Syntax.cmd.cmd) tr m l post,
        Fp12_bounded Fp12_tight f ->
        Fp2_bounded Fp2_tight tx -> Fp2_bounded Fp2_tight ty ->
        Fp_bounded Fp_loose xp -> Fp_bounded Fp_loose yp ->
        dbl_sep a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
          f tx ty lam tmp1 tmp2 line xp yp R m ->
        map.get l "f" = Some a_f -> map.get l "t_x" = Some a_tx ->
        map.get l "t_y" = Some a_ty -> map.get l "lambda" = Some a_lam ->
        map.get l "tmp1" = Some a_tmp1 -> map.get l "tmp2" = Some a_tmp2 ->
        map.get l "line" = Some a_line ->
        map.get l "p_x" = Some p_px -> map.get l "p_y" = Some p_py ->
        (forall m' (f' : Fp12_felem) (tx' ty' lam' tmp1' tmp2' : Fp2_felem) (line' : Fp12_felem),
           Fp12_feval f' =
             fst (dbl_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty) (Fp_feval xp) (Fp_feval yp)) ->
           Fp2_feval tx' =
             fst (snd (dbl_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty) (Fp_feval xp) (Fp_feval yp))) ->
           Fp2_feval ty' =
             snd (snd (dbl_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty) (Fp_feval xp) (Fp_feval yp))) ->
           Fp2_feval lam' = dbl_lambda (Fp2_feval tx) (Fp2_feval ty) ->
           Fp12_feval line' =
             make_line_feval_model (dbl_lambda (Fp2_feval tx) (Fp2_feval ty))
               (Fp2_feval tx) (Fp2_feval ty) (Fp_feval xp) (Fp_feval yp) ->
           Fp12_bounded Fp12_tight f' ->
           Fp2_bounded Fp2_tight tx' -> Fp2_bounded Fp2_tight ty' ->
           dbl_sep a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
             f' tx' ty' lam' tmp1' tmp2' line' xp yp R m' ->
           WeakestPrecondition.cmd functions rest tr m' l post) ->
        WeakestPrecondition.cmd functions (cmd_seq_k miller_doubling_calls rest) tr m l post.
    Proof.
      intros functions HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2copy HFp12mul HFp12sqr HML
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py f tx ty lam tmp1 tmp2 line xp yp R
        rest tr m l post Hbf Hbtx Hbty Hbxp Hbyp Hsep
        Hlf Hltx Hlty Hllam Hltmp1 Hltmp2 Hlline Hlpx Hlpy Hk.
      cbv [cmd_seq_k miller_doubling_calls].
      mcallf HFp2sqr v1 E1.
      mcallf HFp2add v2 E2.
      mcallf HFp2add v3 E3.
      mcallf HFp2add v4 E4.
      mcallf HFp2inv v5 E5.
      mcallf HFp2mul v6 E6.
      mcallf HML vln E7.
      mcallf HFp12sqr vf1 E8.
      mcallf HFp12mul vf2 E9.
      mcallf HFp2sqr v10 E10.
      mcallf HFp2sub v11 E11.
      mcallf HFp2sub v12 E12.
      mcallf HFp2sub v13 E13.
      mcallf HFp2mul v14 E14.
      mcallf HFp2sub v15 E15.
      mcopy HFp2copy.
      destruct E7 as [E7]. norm_feval E1. norm_feval E2. norm_feval E3. norm_feval E4. norm_feval E5.
      norm_feval E6. norm_feval E8. norm_feval E9. norm_feval E10. norm_feval E11.
      norm_feval E12. norm_feval E13. norm_feval E14. norm_feval E15.
      destruct (dbl_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15)
      as [Hf' [Htx' [Hty' [Hlam' Hline']]]].
      clear E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
      eapply Hk; [ exact Hf' | exact Htx' | exact Hty' | exact Hlam' | exact Hline' | solve_miller_bounds | solve_miller_bounds | solve_miller_bounds | ecancel_assumption ].
    Qed.

    (* ============================================================ *)
    (* Addition fragment                                             *)
    (* ============================================================ *)

    Lemma miller_addition_ok :
      forall functions
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HML : spec_of_make_line_f functions)
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py p_qx p_qy : word)
        (f : Fp12_felem) (tx ty lam tmp1 tmp2 : Fp2_felem) (line : Fp12_felem)
        (xp yp : Fp_felem) (qx qy : Fp2_felem) (R : mem -> Prop)
        tr m l (post : Semantics.trace -> mem -> locals -> Prop),
        Fp12_bounded Fp12_tight f ->
        Fp2_bounded Fp2_tight tx -> Fp2_bounded Fp2_tight ty ->
        Fp_bounded Fp_loose xp -> Fp_bounded Fp_loose yp ->
        Fp2_bounded Fp2_tight qx -> Fp2_bounded Fp2_tight qy ->
        dbl_sep a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
          f tx ty lam tmp1 tmp2 line xp yp
          (FElem_Fp2 p_qx qx ⋆ (FElem_Fp2 p_qy qy ⋆ R)) m ->
        map.get l "f" = Some a_f -> map.get l "t_x" = Some a_tx ->
        map.get l "t_y" = Some a_ty -> map.get l "lambda" = Some a_lam ->
        map.get l "tmp1" = Some a_tmp1 -> map.get l "tmp2" = Some a_tmp2 ->
        map.get l "line" = Some a_line ->
        map.get l "p_x" = Some p_px -> map.get l "p_y" = Some p_py ->
        map.get l "q_x" = Some p_qx -> map.get l "q_y" = Some p_qy ->
        (forall m' (f' : Fp12_felem) (tx' ty' lam' tmp1' tmp2' : Fp2_felem) (line' : Fp12_felem),
           Fp12_feval f' =
             fst (add_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty)
                    (Fp2_feval qx) (Fp2_feval qy) (Fp_feval xp) (Fp_feval yp)) ->
           Fp2_feval tx' =
             fst (snd (add_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty)
                         (Fp2_feval qx) (Fp2_feval qy) (Fp_feval xp) (Fp_feval yp))) ->
           Fp2_feval ty' =
             snd (snd (add_model (Fp12_feval f) (Fp2_feval tx) (Fp2_feval ty)
                         (Fp2_feval qx) (Fp2_feval qy) (Fp_feval xp) (Fp_feval yp))) ->
           Fp2_feval lam' = add_lambda (Fp2_feval tx) (Fp2_feval ty) (Fp2_feval qx) (Fp2_feval qy) ->
           Fp12_feval line' =
             make_line_feval_model
               (add_lambda (Fp2_feval tx) (Fp2_feval ty) (Fp2_feval qx) (Fp2_feval qy))
               (Fp2_feval tx) (Fp2_feval ty) (Fp_feval xp) (Fp_feval yp) ->
           Fp12_bounded Fp12_tight f' ->
           Fp2_bounded Fp2_tight tx' -> Fp2_bounded Fp2_tight ty' ->
           dbl_sep a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py
             f' tx' ty' lam' tmp1' tmp2' line' xp yp
             (FElem_Fp2 p_qx qx ⋆ (FElem_Fp2 p_qy qy ⋆ R)) m' ->
           post tr m' l) ->
        WeakestPrecondition.cmd functions miller_addition_cmd tr m l post.
    Proof.
      intros functions HFp2mul HFp2sub HFp2sqr HFp2inv HFp2copy HFp12mul HML
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line p_px p_py p_qx p_qy
        f tx ty lam tmp1 tmp2 line xp yp qx qy R tr m l post
        Hbf Hbtx Hbty Hbxp Hbyp Hbqx Hbqy Hsep
        Hlf Hltx Hlty Hllam Hltmp1 Hltmp2 Hlline Hlpx Hlpy Hlqx Hlqy Hk.
      cbv [miller_addition_cmd miller_addition_calls BLS12_Pairing.cmd_seq_list].
      mcallf HFp2sub v1 E1.     (* A1: tmp1 = q_y - t_y *)
      mcallf HFp2sub v2 E2.     (* A2: tmp2 = q_x - t_x *)
      mcallf HFp2inv v3 E3.     (* A3: tmp2 = tmp2^-1 *)
      mcallf HFp2mul v4 E4.     (* A4: lambda = tmp1 * tmp2 *)
      mcallf HML vln E5.        (* A5: line = make_line(lambda, t_x, t_y, p_x, p_y) *)
      mcallf HFp12mul vf1 E6.   (* A6: f = f * line *)
      mcallf HFp2sqr v7 E7.     (* A7: tmp1 = lambda^2 *)
      mcallf HFp2sub v8 E8.     (* A8: tmp1 = tmp1 - t_x *)
      mcallf HFp2sub v9 E9.     (* A9: tmp2 = tmp1 - q_x *)
      mcallf HFp2sub v10 E10.   (* A10: tmp1 = t_x - tmp2 *)
      mcallf HFp2mul v11 E11.   (* A11: tmp1 = lambda * tmp1 *)
      mcallf HFp2sub v12 E12.   (* A12: t_y = tmp1 - t_y *)
      mcopy HFp2copy.           (* A13: t_x = tmp2 *)
      destruct E5 as [E5].
      norm_feval E1. norm_feval E2. norm_feval E3. norm_feval E4. norm_feval E6.
      norm_feval E7. norm_feval E8. norm_feval E9. norm_feval E10. norm_feval E11.
      norm_feval E12.
      destruct (add_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12)
        as [Hf' [Htx' [Hty' [Hlam' Hline']]]].
      clear E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
      eapply Hk; [ exact Hf' | exact Htx' | exact Hty' | exact Hlam' | exact Hline'
                 | solve_miller_bounds | solve_miller_bounds | solve_miller_bounds
                 | ecancel_assumption ].
    Qed.

End BLS12_MillerStepFunctional.
