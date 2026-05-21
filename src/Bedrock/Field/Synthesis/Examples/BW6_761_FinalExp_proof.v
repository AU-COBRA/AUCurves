(** * BW6-761 Final Exponentiation WP Proof
    Standalone WP correctness proofs for the BW6-761 final
    exponentiation functions defined in BW6_761_FinalExp.v.

    Mirrors the proof structure of BLS24_509_FinalExp_proof.v:
      1. bw6_fp6_pow_abs_u_ok  — square-and-multiply loop for u
      2. bw6_final_exp_easy_ok — easy part: 2 stackallocs + 5 calls
      3. bw6_final_exp_hard_ok — hard part: 4 stackallocs + chain
      4. bw6_final_exp_ok      — combines easy + hard

    Differences from the BLS24 template:
      - Fp6 (not Fp24); base field is Fp.
      - Tower is Fp -> Fp3 -> Fp6 (quadratic top).
      - Seed u = 0x8508c00000000001 is 64 bits (vs BLS24's 52 bits).
      - Hard part uses 4 stack slots (a, b, c, d) instead of 5.
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
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FinalExp.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BW6_FinalExpProof.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Existing Instances
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok.

  Local Notation FElem_Fp6 :=
    (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_bounded :=
    (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_tight :=
    (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_loose :=
    (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_felem :=
    (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation FElem_Fp3 :=
    (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_bounded :=
    (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_tight :=
    (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_loose :=
    (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_felem :=
    (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).

  Local Typeclasses Opaque bw6_Fp6_params.
  Local Typeclasses Opaque bw6_Fp3_params.

  (* ============================================================ *)
  (* Callee spec instances                                         *)
  (* ============================================================ *)

  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec (F:=Fp6) (field_representation:=bw6_Fp6_repr)
      AbstractField.bin_mul.
  Instance spec_of_Fp6_sqr : spec_of (AbstractField.square (F:=Fp6)) :=
    AbstractField.unop_spec (F:=Fp6) (field_representation:=bw6_Fp6_repr)
      AbstractField.un_square.
  Instance spec_of_Fp6_inv : spec_of (AbstractField.inv (F:=Fp6)) :=
    AbstractField.unop_spec (F:=Fp6) (field_representation:=bw6_Fp6_repr)
      AbstractField.un_inv.
  Instance spec_of_Fp6_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6) (field_representation:=bw6_Fp6_repr).

  (* ============================================================ *)
  (* Loop invariant for pow_abs_u                                  *)
  (* ============================================================ *)

  Definition pow_abs_u_inv
    (a_result a_base pout px : word)
    (x_val : Fp6_felem)
    (old_out : Fp6_felem)
    (Rr : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 63)%nat /\
    exists result_v : Fp6_felem,
      Fp6_bounded Fp6_tight result_v /\
      (FElem_Fp6 a_result result_v *
       (FElem_Fp6 a_base x_val *
        (FElem_Fp6 pout old_out *
         (FElem_Fp6 px x_val * Rr))))%sep m /\
      map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
      map.get l "result" = Some a_result /\
      map.get l "base" = Some a_base /\
      map.get l "out" = Some pout.

  Lemma bw6_fp6_pow_abs_u_ok :
    forall functions
      (EnvContains : map.get functions "bw6_fp6_pow_abs_u" =
        Some (snd BW6_761_FinalExp.bw6_fp6_pow_abs_u))
      (HFp6mul : spec_of_Fp6_mul functions)
      (HFp6sqr : spec_of_Fp6_sqr functions)
      (HFp6copy : spec_of_Fp6_felem_copy functions),
    spec_of_bw6_fp6_pow_abs_u functions.
  Proof.
    intros functions EnvContains HFp6mul HFp6sqr HFp6copy.
    unfold spec_of_bw6_fp6_pow_abs_u.
    intros pout px old_out x_val Rr tr mem0 [Hbx Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_fp6_pow_abs_u. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* Stackalloc 1: result (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_result mSr mCr HaSr HmSr.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr _ _ a_result mSr) HaSr) as [ri Hri].

    (* Stackalloc 2: base (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_base mSb mCb HaSb HmSb.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr _ _ a_base mSb) HaSb) as [bi Hbi].

    pose proof (proj1 (map.split_comm mCr mem0 mSr) HmSr) as HmSr'.
    assert (Hsep1 :
      (FElem_Fp6 a_result ri *
       (FElem_Fp6 pout old_out *
        (FElem_Fp6 px x_val * Rr)))%sep mCr).
    { exists mSr, mem0. exact (conj HmSr' (conj Hri Hsep)). }

    pose proof (proj1 (map.split_comm mCb mCr mSb) HmSb) as HmSb'.
    assert (Hsep_all :
      (FElem_Fp6 a_base bi *
       (FElem_Fp6 a_result ri *
        (FElem_Fp6 pout old_out *
         (FElem_Fp6 px x_val * Rr))))%sep mCb).
    { exists mSb, mCr. exact (conj HmSb' (conj Hbi Hsep1)). }

    clear Hsep Hsep1 HaSr HmSr Hri HaSb HmSb Hbi HmSr' HmSb'.

    cbv [BW6_761_FinalExp.cmd_seq_list].

    repeat straightline.

    (* Call 1: copy(base, x) — base := x_val *)
    eapply Semantics.weaken_call.
    1: { eapply HFp6copy.
         split. { ecancel_assumption. }
         ecancel_assumption. }
    intros t_c1 ? rets1 [Hrets1 [Htr1 Hsep_copy1]].
    subst rets1. rewrite <- Htr1 in *. clear t_c1 Htr1.
    cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
    repeat straightline.

    (* Call 2: copy(result, base) — result := x_val *)
    eapply Semantics.weaken_call.
    1: { eapply HFp6copy.
         split. { ecancel_assumption. }
         ecancel_assumption. }
    intros t_c2 ? rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2. rewrite <- Htr2 in *. clear t_c2 Htr2.
    cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
    repeat straightline.

    (* While loop: 63 iterations *)
    eapply Loops.while_localsmap
      with (v0 := 63%nat) (lt := Nat.lt)
           (invariant := fun v t m l =>
              pow_abs_u_inv a_result a_base pout px x_val old_out Rr tr v t m l).
    { exact lt_wf. }
    { (* Initial invariant *)
      unfold pow_abs_u_inv. split. { reflexivity. } split. { lia. }
      exists x_val. split. { exact Hbx. }
      split. { exact Hsep_copy2. }
      subst.
      repeat split;
        try (rewrite map.get_put_same; reflexivity);
        try (repeat (rewrite map.get_put_diff by congruence);
             rewrite map.get_put_same; reflexivity). }
    { (* Loop body + exit condition *)
      intros v t_v m_v l_v Hinv.
      unfold pow_abs_u_inv in Hinv.
      destruct Hinv as [Ht [Hv_le [result_v [Hbr [Hsep_v [Hget_i [Hget_result [Hget_base Hget_out]]]]]]]].
      subst.
      exists (word.of_Z (Z.of_nat v)). cbv [Markers.split].
      split. { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
               eexists. split; [exact Hget_i | reflexivity]. }
      split.
      { (* TRUE branch *)
        intro Hne.
        unfold BW6_761_FinalExp.pow_abs_u_loop.
        cbv [BW6_761_FinalExp.cmd_seq_list].
        eexists. split.
        { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
        eexists. split. { solve [eval_dexprs_fast]. }
        unfold spec_of_Fp6_sqr, AbstractField.unop_spec in HFp6sqr.
        eapply Semantics.weaken_call.
        1: { eapply (HFp6sqr a_result a_result result_v result_v
               (FElem_Fp6 a_base x_val *
                (FElem_Fp6 pout old_out *
                 (FElem_Fp6 px x_val * Rr)))%sep).
             split. { apply AbstractField.relax_bounds. exact Hbr. }
             split. { eexists. ecancel_assumption. }
             ecancel_assumption. }
        cbv beta.
        intros t_sqr ? rets_sqr [Hrets_sqr [Htr_sqr [sqr_out [Hfeval_sqr [Hb_sqr Hsep_sqr]]]]].
        subst rets_sqr. rewrite <- Htr_sqr in *. clear t_sqr Htr_sqr.
        cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
        repeat straightline.
        eexists. split.
        { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
        cbv beta iota delta [Semantics.interp_binop].
        set (new_i := word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)).
        set (bit_val := word.and
          (word.sru (word.of_Z 0x8508c00000000001) new_i)
          (word.of_Z 1)).
        set (l_new := map.put (map.put l_v "i" new_i) "bit" bit_val).
        repeat straightline.
        unfold1_cmd_goal. cbv beta match delta [cmd_body].
        exists bit_val. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
          eexists. split. { subst l_new. rewrite map.get_put_same. reflexivity. }
          reflexivity. }
        split.
        { (* bit <> 0 *)
          intro Hbit_ne.
          repeat straightline.
          unfold spec_of_Fp6_mul, AbstractField.binop_spec in HFp6mul.
          eexists. split.
          { cbv [dexprs list_map list_map_body WeakestPrecondition.expr
                 WeakestPrecondition.expr_body WeakestPrecondition.get
                 WeakestPrecondition.literal dlet.dlet].
            repeat (eexists; split; [| try reflexivity]).
            all: subst l_new.
            all: repeat (first [rewrite map.get_put_same; reflexivity
                               | rewrite map.get_put_diff by congruence]).
            all: first [exact Hget_result | exact Hget_base]. }
          eapply Semantics.weaken_call.
          1: { eapply (HFp6mul a_result a_result a_base sqr_out sqr_out x_val
                 (FElem_Fp6 a_base x_val *
                  (FElem_Fp6 pout old_out *
                   (FElem_Fp6 px x_val * Rr)))%sep).
               split. { apply AbstractField.relax_bounds. exact Hb_sqr. }
               split. { apply AbstractField.relax_bounds. exact Hbx. }
               split. { exists (FElem_Fp6 a_base x_val *
                                (FElem_Fp6 pout old_out *
                                 (FElem_Fp6 px x_val * Rr)))%sep.
                        exact Hsep_sqr. }
               split. { exists (FElem_Fp6 a_result sqr_out *
                                (FElem_Fp6 pout old_out *
                                 (FElem_Fp6 px x_val * Rr)))%sep.
                        ecancel_assumption. }
               ecancel_assumption. }
          intros t_mul ? rets_mul [Hrets_mul [Htr_mul [mul_out [Hfeval_mul [Hb_mul Hsep_mul]]]]].
          subst rets_mul. rewrite <- Htr_mul in *. clear t_mul Htr_mul.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          exists (v - 1)%nat. split.
          { unfold pow_abs_u_inv. split. { reflexivity. } split. { lia. }
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
        { (* bit = 0 *)
          intro Hbit_zero. repeat straightline.
          exists (v - 1)%nat. split.
          { unfold pow_abs_u_inv. split. { reflexivity. } split. { lia. }
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
        (* copy(out, result) *)
        exists [pout; a_result]. split.
        { cbv [dexprs list_map list_map_body WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.get
               WeakestPrecondition.literal dlet.dlet].
          repeat (eexists; split; [| try reflexivity]).
          all: first [exact Hget_out | exact Hget_result]. }
        eapply Semantics.weaken_call.
        1: { eapply HFp6copy.
             split. { ecancel_assumption. }
             ecancel_assumption. }
        intros t_out m_out rets_out [Hrets_out [Htr_out Hsep_out]].
        subst rets_out. rewrite <- Htr_out in *. clear t_out Htr_out.
        cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }

        (* Dealloc base then result *)
        assert (Hsep_base_front :
          (FElem_Fp6 a_base x_val *
           (FElem_Fp6 a_result result_v *
            (FElem_Fp6 pout result_v *
             (FElem_Fp6 px x_val * Rr))))%sep m_out).
        { ecancel_assumption. }
        destruct Hsep_base_front as [mStack_base [m_after_base [Hsp_base [Hfe_base Hrest_base]]]].
        assert (Hab_base : Memory.anybytes a_base
            (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_base).
        { exact (AbstractField.FElem_to_bytes (field_representation:=bw6_Fp6_repr)
                   a_base x_val mStack_base Hfe_base). }
        exists m_after_base, mStack_base.
        split. { exact Hab_base. }
        split. { apply map.split_comm. exact Hsp_base. }

        assert (Hsep_result_front :
          (FElem_Fp6 a_result result_v *
           (FElem_Fp6 pout result_v *
            (FElem_Fp6 px x_val * Rr)))%sep m_after_base).
        { ecancel_assumption. }
        clear Hrest_base.
        destruct Hsep_result_front as [mStack_result [m_final [Hsp_result [Hfe_result Hrest_final]]]].
        assert (Hab_result : Memory.anybytes a_result
            (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_result).
        { exact (AbstractField.FElem_to_bytes (field_representation:=bw6_Fp6_repr)
                   a_result result_v mStack_result Hfe_result). }
        exists m_final, mStack_result.
        split. { exact Hab_result. }
        split. { apply map.split_comm. exact Hsp_result. }

        cbv [list_map list_map_body WeakestPrecondition.get].
        split. { reflexivity. }
        split. { reflexivity. }
        exists result_v.
        split. { apply AbstractField.relax_bounds. exact Hbr. }
        exact Hrest_final. } }
  Qed.

  (* ============================================================ *)
  (* Lemma: bw6_fp6_pow_u_ok                                       *)
  (* Just wraps pow_abs_u.                                          *)
  (* ============================================================ *)

  Lemma bw6_fp6_pow_u_ok :
    forall functions
      (EnvContains : map.get functions "bw6_fp6_pow_u" =
        Some (snd BW6_761_FinalExp.bw6_fp6_pow_u))
      (HFpowabsu : spec_of_bw6_fp6_pow_abs_u functions),
    spec_of_bw6_fp6_pow_u functions.
  Proof.
    intros functions EnvContains HFpowabsu.
    unfold spec_of_bw6_fp6_pow_u.
    intros pout px old_out x_val Rr tr mem0 [Hbx Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_fp6_pow_u. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }
    cbv [BW6_761_FinalExp.cmd_seq_list].
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFpowabsu. split; [exact Hbx | ecancel_assumption]. }
    intros t_c ? rets_c [Hrets_c [Htr_c [out_v [Hb_out Hsep_out]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists out_v. split. { exact Hb_out. }
    ecancel_assumption.
  Qed.

  (* ============================================================ *)
  (* Lemma: bw6_final_exp_easy_ok                                  *)
  (* Body: 2 stackallocs + 5 calls + 2 deallocs.                  *)
  (* ============================================================ *)

  Lemma bw6_final_exp_easy_ok :
    forall functions
      (EnvContains : map.get functions "bw6_final_exp_easy" =
        Some (snd BW6_761_FinalExp.bw6_final_exp_easy))
      (HFp6mul   : spec_of_Fp6_mul functions)
      (HFp6inv   : spec_of_Fp6_inv functions)
      (HFp6conj  : spec_of_bw6_fp6_conjugate functions)
      (HFp6frob  : spec_of_bw6_fp6_frob functions),
    spec_of_bw6_final_exp_easy functions.
  Proof.
    intros functions EnvContains HFp6mul HFp6inv HFp6conj HFp6frob.
    unfold spec_of_bw6_final_exp_easy.
    intros pout pf p_gfp3 p_gfp6 old_out f gfp3 gfp6 Rr tr mem0
      [Hbf [Hbg3 [Hbg6 Hsep]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_final_exp_easy. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* Stackalloc 1: t0 (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t0 mSt0 mCt0 HaSt0 HmSt0.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr _ _ a_t0 mSt0) HaSt0) as [t0i Ht0i].

    (* Stackalloc 2: t1 (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t1 mSt1 mCt1 HaSt1 HmSt1.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr _ _ a_t1 mSt1) HaSt1) as [t1i Ht1i].

    (* Build master sep from 2 stackalloc layers + original *)
    pose proof (proj1 (map.split_comm mCt0 mem0 mSt0) HmSt0) as HmSt0'.
    assert (Hsep1 :
      (FElem_Fp6 a_t0 t0i *
       (FElem_Fp6 pf f *
        (FElem_Fp6 pout old_out *
         (FElem_Fp3 p_gfp3 gfp3 *
          (FElem_Fp3 p_gfp6 gfp6 * Rr)))))%sep mCt0).
    { exists mSt0, mem0. exact (conj HmSt0' (conj Ht0i Hsep)). }

    pose proof (proj1 (map.split_comm mCt1 mCt0 mSt1) HmSt1) as HmSt1'.
    assert (Hsep_all :
      (FElem_Fp6 a_t1 t1i *
       (FElem_Fp6 a_t0 t0i *
        (FElem_Fp6 pf f *
         (FElem_Fp6 pout old_out *
          (FElem_Fp3 p_gfp3 gfp3 *
           (FElem_Fp3 p_gfp6 gfp6 * Rr))))))%sep mCt1).
    { exists mSt1, mCt0. exact (conj HmSt1' (conj Ht1i Hsep1)). }

    clear Hsep Hsep1 HaSt0 HmSt0 Ht0i HaSt1 HmSt1 Ht1i HmSt0' HmSt1'.
    cbv [BW6_761_FinalExp.final_exp_easy_body BW6_761_FinalExp.cmd_seq_list].

    (* Call 1: conjugate(t0, f) — tight -> loose *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6conj.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [conj_v [Hb_conj Hsep_conj]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 2: inv(t1, f) — tight -> loose (unop_spec) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6inv.
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [inv_v [Hfeval_inv [Hb_inv Hsep_inv]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 3: mul(t0, t0, t1) — binop, loose*loose -> tight *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_conj |].
         split; [exact Hb_inv |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [mul1_v [Hfeval_mul1 [Hb_mul1 Hsep_mul1]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 4: frob(t1, t0, gfp3, gfp6) — tight -> loose *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6frob.
         split; [exact Hb_mul1 |].
         split; [exact Hbg3 |].
         split; [exact Hbg6 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [frob_v [Hb_frob [Hfeval_frob Hsep_frob]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 5: mul(out, t1, t0) — binop, loose*tight -> tight *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_frob |].
         split; [exact Hb_mul1 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [mul2_v [Hfeval_mul2 [Hb_mul2 Hsep_mul2]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Stack deallocation: t1 then t0 (innermost first) *)
    match goal with Hc : (_ * _)%sep ?m |- _ =>
      assert (Hsep_t1_front :
        (FElem_Fp6 a_t1 frob_v *
         (FElem_Fp6 pout mul2_v *
          (FElem_Fp6 a_t0 mul1_v *
           (FElem_Fp6 pf f *
            (FElem_Fp3 p_gfp3 gfp3 *
             (FElem_Fp3 p_gfp6 gfp6 * Rr))))))%sep m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_t1_front as [mStack_t1 [m_at1 [Hsp_t1 [Hfe_t1 Hrest_t1]]]].
    assert (Hab_t1 : Memory.anybytes a_t1
        (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_t1).
    { exact (AbstractField.FElem_to_bytes (field_representation:=bw6_Fp6_repr)
               a_t1 frob_v mStack_t1 Hfe_t1). }
    exists m_at1, mStack_t1.
    split. { exact Hab_t1. }
    split. { apply map.split_comm. exact Hsp_t1. }

    (* Dealloc t0 *)
    assert (Hsep_t0_front :
      (FElem_Fp6 a_t0 mul1_v *
       (FElem_Fp6 pout mul2_v *
        (FElem_Fp6 pf f *
         (FElem_Fp3 p_gfp3 gfp3 *
          (FElem_Fp3 p_gfp6 gfp6 * Rr)))))%sep m_at1).
    { ecancel_assumption. }
    clear Hrest_t1.
    destruct Hsep_t0_front as [mStack_t0 [m_final [Hsp_t0 [Hfe_t0 Hrest_final]]]].
    assert (Hab_t0 : Memory.anybytes a_t0
        (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_t0).
    { exact (AbstractField.FElem_to_bytes (field_representation:=bw6_Fp6_repr)
               a_t0 mul1_v mStack_t0 Hfe_t0). }
    exists m_final, mStack_t0.
    split. { exact Hab_t0. }
    split. { apply map.split_comm. exact Hsp_t0. }

    (* Final postcondition *)
    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists mul2_v.
    split. { apply AbstractField.relax_bounds. exact Hb_mul2. }
    exact Hrest_final.
  Qed.

  (* ============================================================ *)
  (* Lemma: bw6_final_exp_hard_ok                                  *)
  (* Body: 4 stackallocs (a, b, c, d) + 16-step chain.            *)
  (* Steps: pow_u(x4), conj(x1), frob(x1), frob_p2(x1),           *)
  (*        frob_p3(x1), mul(x7), sqr(x1).                        *)
  (* ============================================================ *)

  Lemma bw6_final_exp_hard_ok :
    forall functions
      (EnvContains : map.get functions "bw6_final_exp_hard" =
        Some (snd BW6_761_FinalExp.bw6_final_exp_hard))
      (HFp6mul     : spec_of_Fp6_mul functions)
      (HFp6sqr     : spec_of_Fp6_sqr functions)
      (HFp6conj    : spec_of_bw6_fp6_conjugate functions)
      (HFp6frob    : spec_of_bw6_fp6_frob functions)
      (HFp6frob_p2 : spec_of_bw6_fp6_frob_p2 functions)
      (HFp6frob_p3 : spec_of_bw6_fp6_frob_p3 functions)
      (HFp6powu    : spec_of_bw6_fp6_pow_u functions)
      (HFp6powu_ip : spec_of_bw6_fp6_pow_u_inplace functions),
    spec_of_bw6_final_exp_hard functions.
    intros. unfold spec_of_bw6_final_exp_hard.
    (* TODO(BW6 Frobenius spec strengthening, Phase 5):
       Spec now requires Fp6_feval out = frobenius_fp6_gallina ... over the
       2 (easy) / 5 (hard) / 5 (full) FElem_Fp3 sep hypotheses.  Remaining
       work is purely WP threading (mirror bw6_fp6_pow_abs_u_ok) plus
       one feval-equation chaining at each frob/conjugate/mul call, since
       each callee's strengthened spec now exposes
         feval result = (Gallina op) (feval inputs).
       No new algebraic content; CHAIN.  See BW6_761_FrobModel.v for the
       per-component algebra. *)
  Admitted.

  (* ============================================================ *)
  (* Lemma: bw6_final_exp_ok                                       *)
  (* Body: 1 stackalloc (easy_result) + 2 calls + 1 dealloc.      *)
  (* ============================================================ *)

  Lemma bw6_final_exp_ok :
    forall functions
      (EnvContains : map.get functions "bw6_final_exp" =
        Some (snd BW6_761_FinalExp.bw6_final_exp))
      (HFeasy : spec_of_bw6_final_exp_easy functions)
      (HFhard : spec_of_bw6_final_exp_hard functions),
    spec_of_bw6_final_exp functions.
    intros. unfold spec_of_bw6_final_exp.
    (* TODO(BW6 Frobenius spec strengthening, Phase 5 — composition gap):
       Spec composition needs:
         1. final_exp_easy_ok handed back Fp6_tight (currently delivers loose).
            Without this, hard_ok's tight precondition can't be discharged.
            Mirror BLS24_509_FinalExp_proof.v's tighten step.
         2. WP threading via stackalloc-then-2-calls (template:
            bw6_fp6_pow_abs_u_ok, which has the same 2-stackalloc + N-call
            pattern + dealloc cascade).
       No new algebraic content.  See BW6_761_FrobModel.v for the
       per-component Frobenius algebra. *)
  Admitted.

End BW6_FinalExpProof.
