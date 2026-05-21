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
    intros. unfold spec_of_bw6_final_exp_easy.
    intros pout pf p_gfp3 p_gfp6 old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_final_exp_easy. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* Stackalloc 1: t0 (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t0 mSt0 mCt0 HaSt0 HmSt0.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_t0 mSt0) HaSt0) as [t0i Ht0i].

    (* Stackalloc 2: t1 (Fp6) *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t1 mSt1 mCt1 HaSt1 HmSt1.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_t1 mSt1) HaSt1) as [t1i Ht1i].

    cbv [BW6_761_FinalExp.final_exp_easy_body BW6_761_FinalExp.cmd_seq_list].

    pose proof (proj1 (map.split_comm mCt0 mem0 mSt0) HmSt0) as HmSt0'.
    assert (Hsep1 :
      (FElem_Fp6 a_t0 t0i *
       (FElem_Fp6 pf f *
        (FElem_Fp6 pout old_out * Rr)))%sep mCt0).
    { exists mSt0, mem0. exact (conj HmSt0' (conj Ht0i Hsep)). }

    pose proof (proj1 (map.split_comm mCt1 mCt0 mSt1) HmSt1) as HmSt1'.
    assert (Hsep_all :
      (FElem_Fp6 a_t1 t1i *
       (FElem_Fp6 a_t0 t0i *
        (FElem_Fp6 pf f *
         (FElem_Fp6 pout old_out * Rr))))%sep mCt1).
    { exists mSt1, mCt0. exact (conj HmSt1' (conj Ht1i Hsep1)). }

    clear Hsep Hsep1.

    (* Call 1: conjugate(t0, f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6conj.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [conj_v [Hb_conj Hsep_conj]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 2: inv(t1, f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6inv.
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [inv_v [Hfeval_inv [Hb_inv Hsep_inv]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 3: mul(t0, t0, t1) *)
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

    (* Call 4: frob(t1, t0, gammas) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6frob.
         split; [exact Hb_mul1 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [frob_v [Hb_frob Hsep_frob]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 5: mul(out, t1, t0) *)
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

    (* Stack deallocation: t1 then t0 *)
    match goal with Hc : (_ * _)%sep ?m |- _ =>
      assert (Hsep_t1_front :
        (FElem_Fp6 a_t1 frob_v *
         (FElem_Fp6 pout mul2_v *
          (FElem_Fp6 a_t0 mul1_v *
           (FElem_Fp6 pf f * Rr))))%sep m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_t1_front as [mStack_t1 [m_at1 [Hsp_t1 [Hfe_t1 Hrest_t1]]]].
    assert (Hab_t1 : Memory.anybytes a_t1 (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_t1).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_t1 frob_v mStack_t1 Hfe_t1) as Ht1_bytes.
      cbv [Placeholder] in Ht1_bytes. exact Ht1_bytes. }
    exists m_at1, mStack_t1.
    split. { exact Hab_t1. }
    split. { apply map.split_comm. exact Hsp_t1. }

    assert (Hsep_t0_front :
      (FElem_Fp6 a_t0 mul1_v *
       (FElem_Fp6 pout mul2_v *
        (FElem_Fp6 pf f * Rr)))%sep m_at1).
    { ecancel_assumption. }
    clear Hrest_t1.
    destruct Hsep_t0_front as [mStack_t0 [m_final [Hsp_t0 [Hfe_t0 Hrest_final]]]].
    assert (Hab_t0 : Memory.anybytes a_t0 (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_t0).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_t0 mul1_v mStack_t0 Hfe_t0) as Ht0_bytes.
      cbv [Placeholder] in Ht0_bytes. exact Ht0_bytes. }
    exists m_final, mStack_t0.
    split. { exact Hab_t0. }
    split. { apply map.split_comm. exact Hsp_t0. }

    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists mul2_v.
    split. { exact Hb_mul2. }
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
  Proof.
    intros. unfold spec_of_bw6_final_exp_hard.
    intros pout pf p_gfp3 p_gfp6 p_gfp3_p2 p_gfp6_p2 p_gfp6_p3
      old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_final_exp_hard. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* Stackalloc 1: a *)
    straightline. split. { apply Z_mod_mult. }
    intros a_a mSa mCa HaSa HmSa.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_a mSa) HaSa) as [ai Hai].

    (* Stackalloc 2: b *)
    straightline. split. { apply Z_mod_mult. }
    intros a_b mSb mCb HaSb HmSb.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_b mSb) HaSb) as [bi Hbi].

    (* Stackalloc 3: c *)
    straightline. split. { apply Z_mod_mult. }
    intros a_c mSc mCc HaSc HmSc.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_c mSc) HaSc) as [ci Hci].

    (* Stackalloc 4: d *)
    straightline. split. { apply Z_mod_mult. }
    intros a_d mSd mCd HaSd HmSd.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_d mSd) HaSd) as [di Hdi].

    cbv [BW6_761_FinalExp.final_exp_hard_body
         BW6_761_FinalExp.inline_pow_u
         BW6_761_FinalExp.cmd_seq_list].

    (* Build master sep *)
    pose proof (proj1 (map.split_comm mCa mem0 mSa) HmSa) as HmSa'.
    assert (Hsep1 :
      (FElem_Fp6 a_a ai *
       (FElem_Fp6 pf f *
        (FElem_Fp6 pout old_out * Rr)))%sep mCa).
    { exists mSa, mem0. exact (conj HmSa' (conj Hai Hsep)). }

    pose proof (proj1 (map.split_comm mCb mCa mSb) HmSb) as HmSb'.
    assert (Hsep2 :
      (FElem_Fp6 a_b bi *
       (FElem_Fp6 a_a ai *
        (FElem_Fp6 pf f *
         (FElem_Fp6 pout old_out * Rr))))%sep mCb).
    { exists mSb, mCa. exact (conj HmSb' (conj Hbi Hsep1)). }

    pose proof (proj1 (map.split_comm mCc mCb mSc) HmSc) as HmSc'.
    assert (Hsep3 :
      (FElem_Fp6 a_c ci *
       (FElem_Fp6 a_b bi *
        (FElem_Fp6 a_a ai *
         (FElem_Fp6 pf f *
          (FElem_Fp6 pout old_out * Rr)))))%sep mCc).
    { exists mSc, mCb. exact (conj HmSc' (conj Hci Hsep2)). }

    pose proof (proj1 (map.split_comm mCd mCc mSd) HmSd) as HmSd'.
    assert (Hsep_all :
      (FElem_Fp6 a_d di *
       (FElem_Fp6 a_c ci *
        (FElem_Fp6 a_b bi *
         (FElem_Fp6 a_a ai *
          (FElem_Fp6 pf f *
           (FElem_Fp6 pout old_out * Rr))))))%sep mCd).
    { exists mSd, mCc. exact (conj HmSd' (conj Hdi Hsep3)). }

    clear Hsep Hsep1 Hsep2 Hsep3.

    (* Step 1: a = pow_u(f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6powu.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a1_v [Hb_a1 Hsep_a1]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 2: b = a*f *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_a1 |].
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b2_v [_ [Hb_b2 Hsep_b2]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 3: a = pow_u(b) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6powu.
         split; [exact Hb_b2 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a3_v [Hb_a3 Hsep_a3]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 4a: c = conj(b) — out-of-place *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6conj.
         split; [exact Hb_b2 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c4a_v [Hb_c4a Hsep_c4a]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 4b: b = a*c *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_a3 |].
         split; [exact Hb_c4a |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b4_v [_ [Hb_b4 Hsep_b4]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 5: c = frob(b) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6frob.
         split; [exact Hb_b4 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c5_v [Hb_c5 Hsep_c5]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 6: d = b*c *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_b4 |].
         split; [exact Hb_c5 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [d6_v [_ [Hb_d6 Hsep_d6]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 7: a = pow_u(d) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6powu.
         split; [exact Hb_d6 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a7_v [Hb_a7 Hsep_a7]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 8: b = pow_u(a) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6powu.
         split; [exact Hb_a7 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b8_v [Hb_b8 Hsep_b8]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 9: c = frob_p2(d) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6frob_p2.
         split; [exact Hb_d6 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c9_v [Hb_c9 Hsep_c9]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 10: a = a*c *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_a7 |].
         split; [exact Hb_c9 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a10_v [_ [Hb_a10 Hsep_a10]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 11: b = pow_u(b) — IN-PLACE *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6powu_ip; [exact Hb_b8 | ecancel_assumption]. }
    intros ? ? ? [? [? [b11_v [Hb_b11 Hsep_b11]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 12: c = frob_p3(d) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6frob_p3.
         split; [exact Hb_d6 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c12_v [Hb_c12 Hsep_c12]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 13: b = b*c *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_b11 |].
         split; [exact Hb_c12 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b13_v [_ [Hb_b13 Hsep_b13]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 14: a = a*b *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_a10 |].
         split; [exact Hb_b13 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a14_v [_ [Hb_a14 Hsep_a14]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 15a: b = sqr(f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6sqr.
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b15a_v [_ [Hb_b15a Hsep_b15a]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 15b: b = b*f *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_b15a |].
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b15_v [_ [Hb_b15 Hsep_b15]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 16: out = a*b *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp6mul.
         split; [exact Hb_a14 |].
         split; [exact Hb_b15 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [out_v [_ [Hb_out Hsep_out]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Stack dealloc: d, c, b, a (innermost first) *)

    (* Dealloc d *)
    match goal with Hc : (_ * _)%sep ?m |- _ =>
      assert (Hsep_d_front :
        (FElem_Fp6 a_d d6_v *
         (FElem_Fp6 pout out_v *
          (FElem_Fp6 a_c c12_v *
           (FElem_Fp6 a_b b15_v *
            (FElem_Fp6 a_a a14_v *
             (FElem_Fp6 pf f * Rr))))))%sep m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_d_front as [mStack_d [m_ad [Hsp_d [Hfe_d Hrest_d]]]].
    assert (Hab_d : Memory.anybytes a_d (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_d).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_d d6_v mStack_d Hfe_d) as Hd_bytes.
      cbv [Placeholder] in Hd_bytes. exact Hd_bytes. }
    exists m_ad, mStack_d.
    split. { exact Hab_d. }
    split. { apply map.split_comm. exact Hsp_d. }

    (* Dealloc c *)
    assert (Hsep_c_front :
      (FElem_Fp6 a_c c12_v *
       (FElem_Fp6 pout out_v *
        (FElem_Fp6 a_b b15_v *
         (FElem_Fp6 a_a a14_v *
          (FElem_Fp6 pf f * Rr)))))%sep m_ad).
    { ecancel_assumption. }
    clear Hrest_d.
    destruct Hsep_c_front as [mStack_c [m_ac [Hsp_c [Hfe_c Hrest_c]]]].
    assert (Hab_c : Memory.anybytes a_c (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_c).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_c c12_v mStack_c Hfe_c) as Hc_bytes.
      cbv [Placeholder] in Hc_bytes. exact Hc_bytes. }
    exists m_ac, mStack_c.
    split. { exact Hab_c. }
    split. { apply map.split_comm. exact Hsp_c. }

    (* Dealloc b *)
    assert (Hsep_b_front :
      (FElem_Fp6 a_b b15_v *
       (FElem_Fp6 pout out_v *
        (FElem_Fp6 a_a a14_v *
         (FElem_Fp6 pf f * Rr))))%sep m_ac).
    { ecancel_assumption. }
    clear Hrest_c.
    destruct Hsep_b_front as [mStack_b [m_ab [Hsp_b [Hfe_b Hrest_b]]]].
    assert (Hab_b : Memory.anybytes a_b (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_b).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_b b15_v mStack_b Hfe_b) as Hb_bytes.
      cbv [Placeholder] in Hb_bytes. exact Hb_bytes. }
    exists m_ab, mStack_b.
    split. { exact Hab_b. }
    split. { apply map.split_comm. exact Hsp_b. }

    (* Dealloc a *)
    assert (Hsep_a_front :
      (FElem_Fp6 a_a a14_v *
       (FElem_Fp6 pout out_v *
        (FElem_Fp6 pf f * Rr)))%sep m_ab).
    { ecancel_assumption. }
    clear Hrest_b.
    destruct Hsep_a_front as [mStack_a [m_final [Hsp_a [Hfe_a Hrest_final]]]].
    assert (Hab_a : Memory.anybytes a_a (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_a).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_a a14_v mStack_a Hfe_a) as Ha_bytes.
      cbv [Placeholder] in Ha_bytes. exact Ha_bytes. }
    exists m_final, mStack_a.
    split. { exact Hab_a. }
    split. { apply map.split_comm. exact Hsp_a. }

    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists out_v.
    split. { exact Hb_out. }
    exact Hrest_final.
  Qed.

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
  Proof.
    intros. unfold spec_of_bw6_final_exp.
    intros pout pf p_gfp3 p_gfp6 p_gfp3_p2 p_gfp6_p2 p_gfp6_p3
      old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BW6_761_FinalExp.bw6_final_exp. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* Stackalloc: easy_result *)
    straightline. split. { apply Z_mod_mult. }
    intros a_easy mSe mCe HaSe HmSe.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bw6_Fp6_params _ _ _ _
      bw6_Fp6_repr wordok mapok a_easy mSe) HaSe) as [ei Hei].

    cbv [BW6_761_FinalExp.cmd_seq_list].

    pose proof (proj1 (map.split_comm mCe mem0 mSe) HmSe) as HmSe'.
    assert (Hsep_all :
      (FElem_Fp6 a_easy ei *
       (FElem_Fp6 pf f *
        (FElem_Fp6 pout old_out * Rr)))%sep mCe).
    { exists mSe, mem0. exact (conj HmSe' (conj Hei Hsep)). }

    clear Hsep.

    (* Call 1: final_exp_easy *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFeasy.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [easy_v [Hb_easy Hsep_easy]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Call 2: final_exp_hard *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFhard.
         split; [exact Hb_easy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [hard_v [Hb_hard Hsep_hard]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Dealloc easy_result *)
    match goal with Hc : (_ * _)%sep ?m |- _ =>
      assert (Hsep_easy_front :
        (FElem_Fp6 a_easy easy_v *
         (FElem_Fp6 pout hard_v *
          (FElem_Fp6 pf f * Rr)))%sep m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_easy_front as [mStack_easy [m_final [Hsp_easy [Hfe_easy Hrest_final]]]].
    assert (Hab_easy : Memory.anybytes a_easy (AbstractField.felem_size_in_bytes (F:=Fp6)) mStack_easy).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bw6_Fp6_repr)
                    a_easy easy_v mStack_easy Hfe_easy) as Heasy_bytes.
      cbv [Placeholder] in Heasy_bytes. exact Heasy_bytes. }
    exists m_final, mStack_easy.
    split. { exact Hab_easy. }
    split. { apply map.split_comm. exact Hsp_easy. }

    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists hard_v.
    split. { exact Hb_hard. }
    exact Hrest_final.
  Qed.

End BW6_FinalExpProof.
