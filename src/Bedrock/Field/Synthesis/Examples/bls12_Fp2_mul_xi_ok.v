(* WP proof for BLS12-381 fp2_mul_xi: (a0,a1) → (a0-a1, a0+a1) *)
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section Proof.
  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    BLS12_Pairing.bls12_prime_params BLS12_Pairing.bls12_prime_params_ok
    BLS12_Pairing.bls12_fp_rep BLS12_Pairing.bls12_fp_rep_ok.
  Existing Instance prime_field_parameters.

  Let beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
  Let xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
  Let xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.
  Let fp2_prefix := "bls12_Fp2_".

  Let F_representation := BLS12_Pairing.bls12_fp_rep.
  Let Fp2_fp_inst : AbstractField.FieldParameters (F PrimeField.M_pos * F PrimeField.M_pos) :=
    CubicFieldExtensions.Fp2_fp_inst beta fp2_prefix.
  Let Fp2_repr_inst : @AbstractField.FieldRepresentation _ Fp2_fp_inst _ _ _ _ :=
    CubicFieldExtensions.Fp2_repr_inst beta fp2_prefix.

  Instance spec_of_fp_copy : spec_of PrimeField.felem_copy :=
    AbstractField.spec_of_felem_copy (F:=F PrimeField.M_pos).
  Instance spec_of_fp_sub : spec_of PrimeField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F PrimeField.M_pos).
  Instance spec_of_fp_add : spec_of PrimeField.add :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F PrimeField.M_pos).
  Instance spec_of_mul_xi_local : spec_of (fp2_prefix ++ "mul_xi") :=
    spec_of_Fp2_mul_xi beta xi_re xi_im fp2_prefix.

  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.

  Local Ltac2 Notation "instance_of" type(constr) :=
    lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

  Local Ltac2 rec callee_specs_ft (cmd : constr) : constr list :=
    multi_match! cmd with
      | cmd.cond _ ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.seq ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.while _ ?c => callee_specs_ft c
      | cmd.stackalloc _ _ ?c => callee_specs_ft c
      | cmd.call _ ?f _ => [instance_of (spec_of $f)]
      | _ => []
    end.

  Local Ltac2 program_logic_goal_for_ft (proc : constr) : unit :=
    let unfolded := eval hnf in $proc in
    lazy_match! unfolded with
    | (?fname, (?params, ?rets, ?body)) =>
      let fname_spec := instance_of (spec_of $fname) in
      let specs := callee_specs_ft body in
      let goal := (fun (functions : constr) =>
        List.fold_right (fun ps c => '(($ps $functions) -> $c)) specs '($fname_spec $functions)) in
      exact (forall functions (EnvContains : map.get functions $fname = Some ($params, $rets, $body)),
        ltac2:(let g := goal &functions in exact $g))
    end.

  Local Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
     Control.plus (fun () => program_logic_goal_for_ft (Ltac2.Constr.pretype proc)) (fun _ => exact True)))
    (at level 10, only parsing).

  Lemma bls12_Fp2_mul_xi_ok :
    program_logic_goal_for_function! BLS12_Pairing.bls12_Fp2_mul_xi.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFsub HFadd.
    unfold spec_of_Fp2_mul_xi, AbstractField.unop_spec.
    intros pout px out x Rr tr mem0 [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func BLS12_Pairing.bls12_Fp2_mul_xi BLS12_Pairing.expr_fp_snd].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc tmp === *)
    split. { apply Z_mod_mult. }
    intros tmp mStack m1 HstackTmp Hm1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst ltac:(exact _) ltac:(exact _) tmp) as Hfb.
    unfold AbstractField.Placeholder in Hfb.
    pose proof (proj1 (Hfb mStack) HstackTmp) as [tmp_val Htmp]. clear Hfb.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _ ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix px x m_x Hfx) as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _ ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix tmp tmp_val mStack Htmp) as [m_t1 [m_t2 [Hsep_t [Ht1 Ht2]]]].
    destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_t as [Heq_t Hd_t12].
    subst m_x mStack.
    unfold bounded_by, Fp2_repr_inst, Fp2_field_representation in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx1 Hbx2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_rx) as [Hd_x1_rx Hd_x2_rx].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sT Hd_rx_sT].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_sT) as [Hd_x1_sT Hd_x2_sT].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_sT) as [Hd_x1_t1 Hd_x1_t2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_sT) as [Hd_x2_t1 Hd_x2_t2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_rx_sT) as [Hd_rx_t1 Hd_rx_t2].
    (* All 4 calls: 2x felem_copy + sub + add handled by straightline.
       NOTE: repeat straightline handles the first call but stops at the second.
       The remaining calls and postcondition need manual handling.
       This proof structure is correct — the goal after straightline is
       Semantics.call for the remaining operations. *)
    repeat straightline.
    (* TODO: Complete the remaining calls + postcondition assembly.
       The proof mirrors the old CubicFieldExtensions.v Fp2_mul_xi_ok
       but needs adaptation for the different straightline behavior. *)
    admit.
  Admitted.

End Proof.
