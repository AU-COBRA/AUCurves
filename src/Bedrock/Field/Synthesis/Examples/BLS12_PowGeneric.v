(** * Generic Power-by-parameter WP Proof
    Parameterized proof for square-and-multiply exponentiation f^{|param|}
    where param is a BLS12-family curve parameter (x or u).
    Instantiated by BLS12_PowX.v (381) and BLS12_377_PowU.v (377).
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
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section PowGeneric.

    (* === Fp-level instances (provided by caller) === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Context {pf_params : PrimeFieldParameters}.
    Existing Instance pf_params.
    Context {pf_params_ok : PrimeFieldParameters_ok}.
    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Context {Fp_rep : AbstractField.FieldRepresentation (F:=Fp)}.
    Context {Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

    (* Extension field constants *)
    Variable beta : F PrimeField.M_pos.
    Variable xi_re xi_im : F PrimeField.M_pos.
    Variable func_prefix : string.

    Let fp2_prefix := (func_prefix ++ "Fp2_")%string.
    Let fp6_prefix := (func_prefix ++ "Fp6_")%string.
    Let fp12_prefix := (func_prefix ++ "Fp12_")%string.

    (* Extension field instances from the factory *)
    Instance gen_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params beta func_prefix.
    Instance gen_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep beta func_prefix.
    Instance gen_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params beta xi_re xi_im func_prefix.
    Instance gen_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep beta xi_re xi_im func_prefix.
    Instance gen_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params beta xi_re xi_im func_prefix.
    Instance gen_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep beta xi_re xi_im func_prefix.

    (* === Abbreviations === *)
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_feval := (@AbstractField.feval _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).

    Local Typeclasses Opaque gen_Fp12_params.
    Local Typeclasses Opaque gen_Fp6_params.
    Local Typeclasses Opaque gen_Fp2_params.

    (* === Operation specs (needed for weaken_call) === *)
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=gen_Fp12_rep) AbstractField.un_square.
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=gen_Fp12_rep) AbstractField.bin_mul.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=gen_Fp12_rep).

    (* === Pow-specific parameters === *)
    Variable pow_func_name : string.
    Variable bls_param : Z.
    Variable bls_param_bits : Z.  (* number of bits minus 1, e.g. 63 *)
    Hypothesis bls_param_bits_nonneg : (0 <= bls_param_bits)%Z.

    (* Derived Let definitions: transparent, unfoldable within this section *)
    Let fp12_sqr_name := AbstractField.square (F:=Fp12).
    Let fp12_mul_name := AbstractField.mul (F:=Fp12).
    Let fp12_copy_name := AbstractField.felem_copy (F:=Fp12).

    Let pow_loop_body : Syntax.cmd.cmd :=
      cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
        (cmd.seq (cmd.call [] fp12_sqr_name
                    [expr.var "result"; expr.var "result"])
          (cmd.seq (cmd.set "bit" (expr.op bopname.and
                      (expr.op bopname.sru (expr.literal bls_param) (expr.var "i"))
                      (expr.literal 1)))
            (cmd.cond (expr.var "bit")
              (cmd.call [] fp12_mul_name
                [expr.var "result"; expr.var "result"; expr.var "base"])
              cmd.skip))).

    Let pow_func_impl : list string * list string * Syntax.cmd.cmd :=
      (["out"; "base"], []:list String.string,
       cmd.stackalloc "result" felem_size_in_bytes (
         cmd.seq (cmd.call [] fp12_copy_name
                    [expr.var "result"; expr.var "base"])
           (cmd.seq (cmd.set "i" (expr.literal bls_param_bits))
             (cmd.seq (cmd.while (expr.var "i") pow_loop_body)
               (cmd.call [] fp12_copy_name
                  [expr.var "out"; expr.var "result"]))))).

    (* ==================================================================== *)
    (* Loop invariant                                                       *)
    (* ==================================================================== *)

    Definition pow_inv
      (a_result a_base a_out : word)
      (base_val : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= Z.to_nat bls_param_bits)%nat /\
      exists (result_val : Fp12_felem),
        Fp12_bounded Fp12_tight result_val /\
        (FElem_Fp12 a_result result_val ⋆
         (FElem_Fp12 a_base base_val ⋆ Rr)) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "result" = Some a_result /\
        map.get l "base" = Some a_base /\
        map.get l "out" = Some a_out.

    (* ==================================================================== *)
    (* Spec                                                                 *)
    (* ==================================================================== *)

    Instance spec_of_pow : spec_of pow_func_name :=
      fnspec! pow_func_name (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆
           (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Local Instance gen_Fp12_rep_ok :
      @AbstractField.FieldRepresentation_ok _ gen_Fp12_params _ _ _ _ gen_Fp12_rep :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok beta xi_re xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    (* ==================================================================== *)
    (* Main WP theorem                                                      *)
    (* ==================================================================== *)

    Lemma pow_ok :
      forall functions
        (EnvContains : map.get functions pow_func_name =
          Some pow_func_impl)
        (HFsqr : spec_of_Fp12_sqr functions)
        (HFmul : spec_of_Fp12_mul functions)
        (HFcopy : spec_of_Fp12_felem_copy functions),
      spec_of_pow functions.
    Proof.
      intros functions EnvContains HFsqr HFmul HFcopy.
      unfold spec_of_pow.
      intros pout pbase tr mem0 old_out base_val Rr [Hbbase Hsep].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv match beta delta [WeakestPrecondition.func pow_func_impl].
      eexists. split. { exact eq_refl. }
      (* Process stackalloc manually *)
      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      (* Convert anybytes to FElem *)
      assert (Hri_ex : exists ri, FElem_Fp12 a_result ri mSr).
      { pose proof (@AbstractField.FElem_from_bytes _ gen_Fp12_params _ _ _ _ gen_Fp12_rep) as Hconv.
        cbv [Lift1Prop.iff1 Placeholder] in Hconv.
        apply Hconv; [typeclasses eauto | typeclasses eauto | exact HaSr]. }
      destruct Hri_ex as [ri Hri].
      assert (Hsep_all : ((FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out)) ⋆ FElem_Fp12 a_result ri) mCr).
      { exists Rr, mSr. exact (conj HmSr (conj Hsep Hri)). }
      clear Hsep HaSr HmSr Hri.
      repeat straightline.
      (* First call: Fp12_copy(result, base) *)
      eapply Semantics.weaken_call.
      1: { eapply HFcopy. split. { ecancel_assumption. } ecancel_assumption. }
      intros ? ? ? [? [? Hsep_copy]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
      repeat straightline.
      (* Now at while loop. Apply Loops.while_localsmap *)
      eapply Loops.while_localsmap
        with (v0 := Z.to_nat bls_param_bits) (lt := Nat.lt)
             (invariant := fun v t m l =>
                pow_inv a_result pbase pout mem0 (FElem_Fp12 pout tr ⋆ old_out) t' v t m l).
      { exact lt_wf. }
      { (* Initial invariant *)
        unfold pow_inv. split. { reflexivity. } split. { lia. }
        exists mem0. split. { exact Hbbase. }
        split. { exact Hsep_copy. }
        subst l0 l i.
        repeat split;
          try (rewrite map.get_put_same; reflexivity);
          try (repeat (rewrite map.get_put_diff by congruence);
               rewrite map.get_put_same; reflexivity).
        (* "i" conjunct: word.of_Z bls_param_bits = word.of_Z (Z.of_nat (Z.to_nat bls_param_bits)) *)
        rewrite map.get_put_same. f_equal. f_equal.
        rewrite Z2Nat.id; [reflexivity | exact bls_param_bits_nonneg]. }
      { (* Loop body + exit *)
        intros v t_v m_v l_v Hinv.
        unfold pow_inv in Hinv.
        destruct Hinv as [Ht [Hv_le [result_v [Hbr [Hsep_v [Hget_i [Hget_result [Hget_base Hget_out]]]]]]]].
        subst.
        exists (word.of_Z (Z.of_nat v)). cbv [Markers.split].
        split. { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
                 eexists. split; [exact Hget_i | reflexivity]. }
        split.
        { (* TRUE branch: v <> 0, process loop body *)
          intro Hne.
          unfold pow_loop_body.
          (* i = i - 1 *)
          eexists. split.
          { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          (* sqr(result, result) *)
          eexists. split. { solve [eval_dexprs_fast]. }
          unfold spec_of_Fp12_sqr, AbstractField.unop_spec in HFsqr.
          eapply Semantics.weaken_call.
          1: { eapply (HFsqr a_result a_result result_v result_v
                 (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out))).
               split. { apply AbstractField.relax_bounds. exact Hbr. }
               split. { eexists. ecancel_assumption. }
               ecancel_assumption. }
          cbv beta.
          intros ? ? ? [? [? [sqr_out [Hfeval_sqr [Hb_sqr Hsep_sqr]]]]]. subst.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          (* bit = (bls_param >> i) & 1 *)
          repeat straightline.
          (* Bit extraction DEXPR *)
          eexists. split.
          { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          cbv beta delta [dlet.dlet Semantics.interp_binop].
          cbv beta iota delta [Semantics.interp_binop].
          set (bit_val := word.and (word.sru (word.of_Z bls_param)
            (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1))) (word.of_Z 1)).
          set (new_i := word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)).
          set (l_new := map.put (map.put l_v "i" new_i) "bit" bit_val).
          repeat straightline.
          (* Conditional: if bit { mul } else { skip } *)
          unfold1_cmd_goal. cbv beta match delta [cmd_body].
          exists bit_val. split.
          { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
            eexists. split. { subst l_new. rewrite map.get_put_same. reflexivity. }
            reflexivity. }
          split.
          { (* bit <> 0: mul(result, result, base) *)
            intro Hbit_ne.
            repeat straightline.
            unfold spec_of_Fp12_mul, AbstractField.binop_spec in HFmul.
            eexists. split.
            { unfold dexprs, list_map, list_map_body.
              cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
              repeat (eexists; split; [| try reflexivity]).
              all: subst l_new.
              all: repeat (first [rewrite map.get_put_same; reflexivity
                                 | rewrite map.get_put_diff by congruence]).
              all: exact Hget_result || exact Hget_base. }
            eapply Semantics.weaken_call.
            1: { eapply (HFmul a_result a_result pbase sqr_out sqr_out mem0
                   (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out))).
                 split. { apply AbstractField.relax_bounds. exact Hb_sqr. }
                 split. { apply AbstractField.relax_bounds. exact Hbbase. }
                 split. { exists (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out)).
                          exact Hsep_sqr. }
                 split. { exists (FElem_Fp12 a_result sqr_out ⋆ (FElem_Fp12 pout tr ⋆ old_out)).
                          ecancel_assumption. }
                 ecancel_assumption. }
            cbv beta. intros ? ? ? [? [? [mul_out [Hfeval_mul [Hb_mul Hsep_mul]]]]]. subst.
            cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
            exists (v - 1)%nat. split.
            { unfold pow_inv. split. { reflexivity. } split. { lia. }
              exists mul_out. split. { exact Hb_mul. }
              split. { exact Hsep_mul. }
              subst l_new new_i bit_val.
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_same. f_equal. ZnWords. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_result. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_base. }
              rewrite map.get_put_diff by congruence.
              rewrite map.get_put_diff by congruence. exact Hget_out. }
            assert (Hv_pos : (0 < v)%nat) by
              (destruct v; [exfalso; apply Hne; vm_compute; reflexivity | lia]).
            lia. }
          { (* bit = 0: skip, re-establish invariant with sqr_out *)
            intro Hbit_zero. repeat straightline.
            exists (v - 1)%nat. split.
            { unfold pow_inv. split. { reflexivity. } split. { lia. }
              exists sqr_out. split. { exact Hb_sqr. }
              split. { exact Hsep_sqr. }
              subst l_new new_i bit_val.
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_same. f_equal. ZnWords. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_result. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_base. }
              rewrite map.get_put_diff by congruence.
              rewrite map.get_put_diff by congruence. exact Hget_out. }
            assert (Hv_pos : (0 < v)%nat) by
              (destruct v; [exfalso; apply Hne; vm_compute; reflexivity | lia]).
            lia. } }
        { (* FALSE branch: v = 0, exit loop *)
          intro Heq.
          repeat straightline.
          exists [pout; a_result]. split.
          { unfold dexprs, list_map, list_map_body.
            cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
            repeat (eexists; split; [| try reflexivity]).
            all: first [exact Hget_out | exact Hget_result]. }
          eapply Semantics.weaken_call.
          1: { eapply HFcopy. split. { ecancel_assumption. } ecancel_assumption. }
          cbv beta. intros ? ? ? [Hrets [Htr_eq Hsep_out]]. symmetry in Htr_eq. subst.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          destruct Hsep_out as [m_out [m_rest [Hsp_out [Hf_out Hrest]]]].
          destruct Hrest as [m_ares [m_frame [Hsp_rest [Hf_ares Hf_frame]]]].
          assert (Hanybytes : Memory.anybytes a_result felem_size_in_bytes m_ares).
          { pose proof (@AbstractField.FElem_from_bytes _ gen_Fp12_params _ _ _ _ gen_Fp12_rep) as Hconv.
            apply Hconv; [typeclasses eauto | typeclasses eauto |].
            exists result_v. exact Hf_ares. }
          exists (map.putmany m_out m_frame), m_ares.
          split. { exact Hanybytes. }
          split. { (* map.split *)
            unfold map.split in *.
            destruct Hsp_out as [He_out Hd_out]. destruct Hsp_rest as [He_rest Hd_rest]. subst.
            assert (Hd_oa : map.disjoint m_out m_ares) by
              (eapply (proj1 (@map.disjoint_putmany_r _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) _ _ _) Hd_out)).
            assert (Hd_fa : map.disjoint m_frame m_ares) by
              (apply map.disjoint_comm; exact Hd_rest).
            split.
            { rewrite (@map.putmany_comm _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_ares m_frame Hd_rest).
              rewrite <- (@map.putmany_assoc _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_frame m_ares).
              reflexivity. }
            eapply (proj2 (@map.disjoint_putmany_l _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_frame m_ares)).
            exact (conj Hd_oa Hd_fa). }
          cbv [list_map list_map_body get].
          refine (conj eq_refl (conj eq_refl (ex_intro _ result_v (conj (AbstractField.relax_bounds _ Hbr) _)))).
          exists m_out, m_frame.
          unfold map.split in *.
          destruct Hsp_out as [He_out Hd_out]. destruct Hsp_rest as [He_rest Hd_rest]. subst.
          refine (conj (conj eq_refl _) (conj Hf_out Hf_frame)).
          eapply (proj1 (@map.disjoint_putmany_r _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_ares m_frame) Hd_out). } }
    Qed.

End PowGeneric.
