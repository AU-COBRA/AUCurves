(** * BLS24-509 Final Exponentiation WP Proof
    Standalone WP correctness proofs for the BLS24-509 final exponentiation
    functions defined in BLS24_509_FinalExp.v.

    Four lemmas:
    1. bls24_fp24_pow_abs_z_ok  — square-and-multiply loop for |z| (Admitted)
    2. bls24_final_exp_easy_ok  — easy part: 2 stackallocs + 5 calls (partially proven)
    3. bls24_final_exp_hard_ok  — hard part: 5 stackallocs + 20-step chain (partially proven)
    4. bls24_final_exp_ok       — combines easy + hard (fully proven)

    Status: lemmas 1-3 have Admitted subgoals for the frob/loop steps.
    Lemma 4 is fully proven assuming lemmas 2-3.
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
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_FinalExp.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS24_FinalExpProof.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (* BLS24-509 prime parameters *)
  Existing Instances
    bls24_prime_params
    bls24_prime_params_ok
    prime_field_parameters
    bls24_Fp_repr
    bls24_Fp_repr_ok.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.
  Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

  (* Extension field instances *)
  Existing Instances
    bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
    bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
    bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
    bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok.

  (* ============================================================ *)
  (* Local FElem notations                                         *)
  (* ============================================================ *)

  Local Notation FElem_Fp24 := (@AbstractField.FElem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
  Local Notation Fp24_bounded := (@AbstractField.bounded_by _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
  Local Notation Fp24_tight := (@AbstractField.tight_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
  Local Notation Fp24_loose := (@AbstractField.loose_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
  Local Notation Fp24_felem := (@AbstractField.felem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).

  Local Typeclasses Opaque bls24_Fp24_params.
  Local Typeclasses Opaque bls24_Fp8_params.
  Local Typeclasses Opaque bls24_Fp4_params.
  Local Typeclasses Opaque bls24_Fp2_params.

  (* ============================================================ *)
  (* Callee spec instances                                         *)
  (* ============================================================ *)

  Instance spec_of_Fp24_mul : spec_of (AbstractField.mul (F:=Fp24)) :=
    AbstractField.binop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.bin_mul.
  Instance spec_of_Fp24_sqr : spec_of (AbstractField.square (F:=Fp24)) :=
    AbstractField.unop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.un_square.
  Instance spec_of_Fp24_inv : spec_of (AbstractField.inv (F:=Fp24)) :=
    AbstractField.unop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.un_inv.
  Instance spec_of_Fp24_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp24)) :=
    AbstractField.spec_of_felem_copy (F:=Fp24) (field_representation:=bls24_Fp24_repr).

  (* ============================================================ *)
  (* Specs for BLS24-specific higher-level functions               *)
  (* Frob functions take 6 word args. Gamma FElems live in Rr     *)
  (* and are not tracked explicitly in the sep.                    *)
  (* ============================================================ *)

  (* spec for bls24_fp24_frob *)
  Instance spec_of_bls24_fp24_frob : spec_of "bls24_fp24_frob" :=
    fnspec! "bls24_fp24_frob"
      (pout px p_gfp4 p_gfp8 p_gfp24_1 p_gfp24_2 : word)
      / (old_out x : Fp24_felem) Rr,
    { requires tr mem :=
        Fp24_bounded Fp24_tight x /\
        (FElem_Fp24 pout old_out ⋆
         (FElem_Fp24 px x ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out ⋆
           (FElem_Fp24 px x ⋆ Rr)) mem' }.

  (* spec for bls24_fp24_frob_p2 *)
  Instance spec_of_bls24_fp24_frob_p2 : spec_of "bls24_fp24_frob_p2" :=
    fnspec! "bls24_fp24_frob_p2"
      (pout px p_gfp4_p2 p_gfp8_p2 p_gfp24_p2_1 p_gfp24_p2_2 : word)
      / (old_out x : Fp24_felem) Rr,
    { requires tr mem :=
        Fp24_bounded Fp24_tight x /\
        (FElem_Fp24 pout old_out ⋆
         (FElem_Fp24 px x ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out ⋆
           (FElem_Fp24 px x ⋆ Rr)) mem' }.

  (* spec for bls24_fp24_frob_p4 *)
  Instance spec_of_bls24_fp24_frob_p4 : spec_of "bls24_fp24_frob_p4" :=
    fnspec! "bls24_fp24_frob_p4"
      (pout px p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2 : word)
      / (old_out x : Fp24_felem) Rr,
    { requires tr mem :=
        Fp24_bounded Fp24_tight x /\
        (FElem_Fp24 pout old_out ⋆
         (FElem_Fp24 px x ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out ⋆
           (FElem_Fp24 px x ⋆ Rr)) mem' }.

  (* spec for bls24_final_exp_easy *)
  Instance spec_of_bls24_final_exp_easy : spec_of "bls24_final_exp_easy" :=
    fnspec! "bls24_final_exp_easy"
      (pout pf p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2 : word)
      / (old_out f : Fp24_felem) Rr,
    { requires tr mem :=
        Fp24_bounded Fp24_tight f /\
        (FElem_Fp24 pf f ⋆
         (FElem_Fp24 pout old_out ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out ⋆
           (FElem_Fp24 pf f ⋆ Rr)) mem' }.

  (* spec for bls24_final_exp_hard *)
  Instance spec_of_bls24_final_exp_hard : spec_of "bls24_final_exp_hard" :=
    fnspec! "bls24_final_exp_hard"
      (pout pf
       p_gfp4 p_gfp8 p_gfp24_1 p_gfp24_2
       p_gfp4_p2 p_gfp8_p2 p_gfp24_p2_1 p_gfp24_p2_2
       p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2 : word)
      / (old_out f : Fp24_felem) Rr,
    { requires tr mem :=
        Fp24_bounded Fp24_tight f /\
        (FElem_Fp24 pf f ⋆
         (FElem_Fp24 pout old_out ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out ⋆
           (FElem_Fp24 pf f ⋆ Rr)) mem' }.

  (* In-place pow_z spec: pout = px.  The function overwrites its input.
     This cannot be expressed with the standard fnspec! nested sep since
     it requires two disjoint FElem cells at the same address.
     Instead we state it as a direct WeakestPrecondition.call prop. *)
  Definition spec_of_bls24_fp24_pow_z_inplace
    (functions : @map.rep String.string
      (list String.string * list String.string * Syntax.cmd.cmd) _) : Prop :=
    forall p_x (x : Fp24_felem) Rr tr mem,
      Fp24_bounded Fp24_tight x ->
      (FElem_Fp24 p_x x ⋆ Rr) mem ->
      WeakestPrecondition.call functions "bls24_fp24_pow_z"
        tr mem [p_x; p_x]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\ exists out,
             Fp24_bounded Fp24_loose out /\
             (FElem_Fp24 p_x out ⋆ Rr) mem').

  (* ============================================================ *)
  (* Lemma 1: bls24_fp24_pow_abs_z_ok                              *)
  (* The function has a while loop: 2 stackallocs, loop 51 times. *)
  (* Admitted — needs Loops.while_localsmap.                       *)
  (* ============================================================ *)

  (* Loop invariant for bls24_fp24_pow_abs_z:
     v is the remaining number of loop iterations (v = i, counting from 51 to 0).
     We track result (changes each iteration), base (= x_val, constant),
     the original out cell (pout, old_out), and the original x cell (px, x_val). *)
  Definition pow_abs_z_inv
    (a_result a_base pout px : word)
    (x_val : Fp24_felem)
    (old_out : Fp24_felem)
    (Rr : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 51)%nat /\
    exists result_v : Fp24_felem,
      Fp24_bounded Fp24_tight result_v /\
      (FElem_Fp24 a_result result_v ⋆
       (FElem_Fp24 a_base x_val ⋆
        (FElem_Fp24 pout old_out ⋆
         (FElem_Fp24 px x_val ⋆ Rr)))) m /\
      map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
      map.get l "result" = Some a_result /\
      map.get l "base" = Some a_base /\
      map.get l "out" = Some pout.

  Lemma bls24_fp24_pow_abs_z_ok :
    forall functions
      (EnvContains : map.get functions "bls24_fp24_pow_abs_z" =
        Some (snd BLS24_509_FinalExp.bls24_fp24_pow_abs_z))
      (HFp24mul : spec_of_Fp24_mul functions)
      (HFp24sqr : spec_of_Fp24_sqr functions)
      (HFp24copy : spec_of_Fp24_felem_copy functions),
    spec_of_bls24_fp24_pow_abs_z functions.
  Proof.
    intros functions EnvContains HFp24mul HFp24sqr HFp24copy.
    unfold spec_of_bls24_fp24_pow_abs_z.
    intros pout px old_out x_val Rr tr mem0 [Hbx Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BLS24_509_FinalExp.bls24_fp24_pow_abs_z. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stackalloc 1: result (Fp24)                                       *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_result mSr mCr HaSr HmSr.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr _ _ a_result mSr) HaSr) as [ri Hri].

    (* ================================================================ *)
    (* Stackalloc 2: base (Fp24)                                         *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_base mSb mCb HaSb HmSb.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr _ _ a_base mSb) HaSb) as [bi Hbi].

    (* Build the master sep for the combined memory mCb *)
    pose proof (proj1 (map.split_comm mCr mem0 mSr) HmSr) as HmSr'.
    assert (Hsep1 :
      (FElem_Fp24 a_result ri ⋆
       (FElem_Fp24 pout old_out ⋆
        (FElem_Fp24 px x_val ⋆ Rr))) mCr).
    { exists mSr, mem0. exact (conj HmSr' (conj Hri Hsep)). }

    pose proof (proj1 (map.split_comm mCb mCr mSb) HmSb) as HmSb'.
    assert (Hsep_all :
      (FElem_Fp24 a_base bi ⋆
       (FElem_Fp24 a_result ri ⋆
        (FElem_Fp24 pout old_out ⋆
         (FElem_Fp24 px x_val ⋆ Rr)))) mCb).
    { exists mSb, mCr. exact (conj HmSb' (conj Hbi Hsep1)). }

    clear Hsep Hsep1 HaSr HmSr Hri HaSb HmSb Hbi HmSr' HmSb'.

    (* Unfold cmd_seq_list to expose the sequence of commands *)
    cbv [BLS24_509_FinalExp.cmd_seq_list].

    repeat straightline.

    (* ================================================================ *)
    (* Call 1: copy(base, x) — base := x_val                           *)
    (* ================================================================ *)
    eapply Semantics.weaken_call.
    1: { eapply HFp24copy.
         split. { ecancel_assumption. }
         ecancel_assumption. }
    intros t_c1 ? rets1 [Hrets1 [Htr1 Hsep_copy1]].
    subst rets1. rewrite <- Htr1 in *. clear t_c1 Htr1.
    cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
    repeat straightline.

    (* ================================================================ *)
    (* Call 2: copy(result, base) — result := x_val                    *)
    (* ================================================================ *)
    eapply Semantics.weaken_call.
    1: { eapply HFp24copy.
         split. { ecancel_assumption. }
         ecancel_assumption. }
    intros t_c2 ? rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2. rewrite <- Htr2 in *. clear t_c2 Htr2.
    cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
    repeat straightline.

    (* ================================================================ *)
    (* While loop: Loops.while_localsmap with 51 iterations             *)
    (* ================================================================ *)
    eapply Loops.while_localsmap
      with (v0 := 51%nat) (lt := Nat.lt)
           (invariant := fun v t m l =>
              pow_abs_z_inv a_result a_base pout px x_val old_out Rr tr v t m l).
    { exact lt_wf. }
    { (* Initial invariant: i = 51, result = x_val (tight) *)
      unfold pow_abs_z_inv. split. { reflexivity. } split. { lia. }
      exists x_val. split. { exact Hbx. }
      split. { exact Hsep_copy2. }
      subst.
      repeat split;
        try (rewrite map.get_put_same; reflexivity);
        try (repeat (rewrite map.get_put_diff by congruence);
             rewrite map.get_put_same; reflexivity). }
    { (* Loop body + exit condition *)
      intros v t_v m_v l_v Hinv.
      unfold pow_abs_z_inv in Hinv.
      destruct Hinv as [Ht [Hv_le [result_v [Hbr [Hsep_v [Hget_i [Hget_result [Hget_base Hget_out]]]]]]]].
      subst.
      exists (word.of_Z (Z.of_nat v)). cbv [Markers.split].
      split. { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
               eexists. split; [exact Hget_i | reflexivity]. }
      split.
      { (* TRUE branch: v <> 0, process loop body *)
        intro Hne.
        unfold BLS24_509_FinalExp.pow_abs_z_loop.
        cbv [BLS24_509_FinalExp.cmd_seq_list].
        (* i = i - 1 *)
        eexists. split.
        { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
        (* sqr(result, result) *)
        eexists. split. { solve [eval_dexprs_fast]. }
        unfold spec_of_Fp24_sqr, AbstractField.unop_spec in HFp24sqr.
        eapply Semantics.weaken_call.
        1: { eapply (HFp24sqr a_result a_result result_v result_v
               (FElem_Fp24 a_base x_val ⋆
                (FElem_Fp24 pout old_out ⋆
                 (FElem_Fp24 px x_val ⋆ Rr)))).
             split. { apply AbstractField.relax_bounds. exact Hbr. }
             split. { eexists. ecancel_assumption. }
             ecancel_assumption. }
        cbv beta.
        intros t_sqr ? rets_sqr [Hrets_sqr [Htr_sqr [sqr_out [Hfeval_sqr [Hb_sqr Hsep_sqr]]]]].
        subst rets_sqr. rewrite <- Htr_sqr in *. clear t_sqr Htr_sqr.
        cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
        (* bit = (bls24_z_abs >> i) & 1 *)
        repeat straightline.
        (* bit expression evaluation *)
        eexists. split.
        { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
        cbv beta iota delta [Semantics.interp_binop].
        set (new_i := word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)).
        set (bit_val := word.and
          (word.sru (word.of_Z 0x800000ffff801) new_i)
          (word.of_Z 1)).
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
          unfold spec_of_Fp24_mul, AbstractField.binop_spec in HFp24mul.
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
          1: { eapply (HFp24mul a_result a_result a_base sqr_out sqr_out x_val
                 (FElem_Fp24 a_base x_val ⋆
                  (FElem_Fp24 pout old_out ⋆
                   (FElem_Fp24 px x_val ⋆ Rr)))).
               split. { apply AbstractField.relax_bounds. exact Hb_sqr. }
               split. { apply AbstractField.relax_bounds. exact Hbx. }
               split. { exists (FElem_Fp24 a_base x_val ⋆
                                (FElem_Fp24 pout old_out ⋆
                                 (FElem_Fp24 px x_val ⋆ Rr))).
                        exact Hsep_sqr. }
               split. { exists (FElem_Fp24 a_result sqr_out ⋆
                                (FElem_Fp24 pout old_out ⋆
                                 (FElem_Fp24 px x_val ⋆ Rr))).
                        ecancel_assumption. }
               ecancel_assumption. }
          intros t_mul ? rets_mul [Hrets_mul [Htr_mul [mul_out [Hfeval_mul [Hb_mul Hsep_mul]]]]].
          subst rets_mul. rewrite <- Htr_mul in *. clear t_mul Htr_mul.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          exists (v - 1)%nat. split.
          { unfold pow_abs_z_inv. split. { reflexivity. } split. { lia. }
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
          { unfold pow_abs_z_inv. split. { reflexivity. } split. { lia. }
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
        1: { eapply HFp24copy.
             split. { ecancel_assumption. }
             ecancel_assumption. }
        intros t_out m_out rets_out [Hrets_out [Htr_out Hsep_out]].
        subst rets_out. rewrite <- Htr_out in *. clear t_out Htr_out.
        cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }

        (* Stack deallocation: base then result (innermost first) *)
        (* The post-loop sep contains: result_v, base=x_val, pout=result_v, px=x_val *)
        (* After copy(out, result_v), Hsep_out says (FElem pout result_v * ...) *)
        (* We need to deallocate a_base, then a_result *)

        (* Rearrange to put a_base at front for dealloc *)
        assert (Hsep_base_front :
          (FElem_Fp24 a_base x_val ⋆
           (FElem_Fp24 a_result result_v ⋆
            (FElem_Fp24 pout result_v ⋆
             (FElem_Fp24 px x_val ⋆ Rr)))) m_out).
        { ecancel_assumption. }
        destruct Hsep_base_front as [mStack_base [m_after_base [Hsp_base [Hfe_base Hrest_base]]]].
        assert (Hab_base : Memory.anybytes a_base
            (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_base).
        { exact (AbstractField.FElem_to_bytes (field_representation:=bls24_Fp24_repr)
                   a_base x_val mStack_base Hfe_base). }
        exists m_after_base, mStack_base.
        split. { exact Hab_base. }
        split. { apply map.split_comm. exact Hsp_base. }

        (* Dealloc a_result *)
        assert (Hsep_result_front :
          (FElem_Fp24 a_result result_v ⋆
           (FElem_Fp24 pout result_v ⋆
            (FElem_Fp24 px x_val ⋆ Rr))) m_after_base).
        { ecancel_assumption. }
        clear Hrest_base.
        destruct Hsep_result_front as [mStack_result [m_final [Hsp_result [Hfe_result Hrest_final]]]].
        assert (Hab_result : Memory.anybytes a_result
            (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_result).
        { exact (AbstractField.FElem_to_bytes (field_representation:=bls24_Fp24_repr)
                   a_result result_v mStack_result Hfe_result). }
        exists m_final, mStack_result.
        split. { exact Hab_result. }
        split. { apply map.split_comm. exact Hsp_result. }

        (* Final postcondition *)
        cbv [list_map list_map_body WeakestPrecondition.get].
        split. { reflexivity. }
        split. { reflexivity. }
        exists result_v.
        split. { apply AbstractField.relax_bounds. exact Hbr. }
        exact Hrest_final. } }
  Qed.

  (* ============================================================ *)
  (* Lemma 2: bls24_final_exp_easy_ok                              *)
  (* Body: 2 stackallocs (t0, t1) + 5 calls + 2 deallocs.         *)
  (* Calls: conjugate(t0,f), inv(t1,f), mul(t0,t0,t1),            *)
  (*        frob_p4(t1,t0,gammas), mul(out,t1,t0)                 *)
  (* ============================================================ *)

  Lemma bls24_final_exp_easy_ok :
    forall functions
      (EnvContains : map.get functions "bls24_final_exp_easy" =
        Some (snd BLS24_509_FinalExp.bls24_final_exp_easy))
      (HFp24mul     : spec_of_Fp24_mul functions)
      (HFp24inv     : spec_of_Fp24_inv functions)
      (HFp24conj    : spec_of_bls24_fp24_conjugate functions)
      (HFp24frob_p4 : spec_of_bls24_fp24_frob_p4 functions),
    spec_of_bls24_final_exp_easy functions.
  Proof.
    intros. unfold spec_of_bls24_final_exp_easy.
    intros pout pf p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2
      old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BLS24_509_FinalExp.bls24_final_exp_easy. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stackalloc 1: t0 (Fp24)                                          *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t0 mSt0 mCt0 HaSt0 HmSt0.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_t0 mSt0) HaSt0) as [t0i Ht0i].

    (* ================================================================ *)
    (* Stackalloc 2: t1 (Fp24)                                          *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_t1 mSt1 mCt1 HaSt1 HmSt1.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_t1 mSt1) HaSt1) as [t1i Ht1i].

    cbv [BLS24_509_FinalExp.final_exp_easy_body BLS24_509_FinalExp.cmd_seq_list].

    (* ================================================================ *)
    (* Build master sep from 2 stackalloc layers + original             *)
    (* ================================================================ *)
    pose proof (proj1 (map.split_comm mCt0 mem0 mSt0) HmSt0) as HmSt0'.
    assert (Hsep1 :
      (FElem_Fp24 a_t0 t0i ⋆
       (FElem_Fp24 pf f ⋆
        (FElem_Fp24 pout old_out ⋆ Rr))) mCt0).
    { exists mSt0, mem0. exact (conj HmSt0' (conj Ht0i Hsep)). }

    pose proof (proj1 (map.split_comm mCt1 mCt0 mSt1) HmSt1) as HmSt1'.
    assert (Hsep_all :
      (FElem_Fp24 a_t1 t1i ⋆
       (FElem_Fp24 a_t0 t0i ⋆
        (FElem_Fp24 pf f ⋆
         (FElem_Fp24 pout old_out ⋆ Rr)))) mCt1).
    { exists mSt1, mCt0. exact (conj HmSt1' (conj Ht1i Hsep1)). }

    clear Hsep Hsep1.

    (* ================================================================ *)
    (* Call 1: conjugate(t0, f) — tight -> loose                       *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24conj.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [conj_v [Hb_conj Hsep_conj]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Call 2: inv(t1, f) — tight -> loose (unop_spec format)          *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24inv.
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [inv_v [Hfeval_inv [Hb_inv Hsep_inv]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Call 3: mul(t0, t0, t1) — binop, loose*loose->tight             *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_conj |].
         split; [exact Hb_inv |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [mul1_v [Hfeval_mul1 [Hb_mul1 Hsep_mul1]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Call 4: frob_p4(t1, t0, gammas) — tight -> loose                *)
    (* TODO: The frob_p4 spec has 6 word args. After repeat straightline *)
    (* the local variable lookups for gamma args may leave open goals.  *)
    (* Full proof requires showing those lookups succeed.               *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24frob_p4.
         split; [exact Hb_mul1 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [frob_v [Hb_frob Hsep_frob]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Call 5: mul(out, t1, t0) — binop, loose*tight->tight            *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_frob |].
         split; [exact Hb_mul1 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [mul2_v [Hfeval_mul2 [Hb_mul2 Hsep_mul2]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stack deallocation: t1 then t0 (innermost first)                 *)
    (* ================================================================ *)

    (* Dealloc t1 *)
    match goal with Hc : (_ ⋆ _)%sep ?m |- _ =>
      assert (Hsep_t1_front :
        (FElem_Fp24 a_t1 frob_v ⋆
         (FElem_Fp24 pout mul2_v ⋆
          (FElem_Fp24 a_t0 mul1_v ⋆
           (FElem_Fp24 pf f ⋆ Rr)))) m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_t1_front as [mStack_t1 [m_at1 [Hsp_t1 [Hfe_t1 Hrest_t1]]]].
    assert (Hab_t1 : Memory.anybytes a_t1 (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_t1).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_t1 frob_v mStack_t1 Hfe_t1) as Ht1_bytes.
      cbv [Placeholder] in Ht1_bytes. exact Ht1_bytes. }
    exists m_at1, mStack_t1.
    split. { exact Hab_t1. }
    split. { apply map.split_comm. exact Hsp_t1. }

    (* Dealloc t0 *)
    assert (Hsep_t0_front :
      (FElem_Fp24 a_t0 mul1_v ⋆
       (FElem_Fp24 pout mul2_v ⋆
        (FElem_Fp24 pf f ⋆ Rr))) m_at1).
    { ecancel_assumption. }
    clear Hrest_t1.
    destruct Hsep_t0_front as [mStack_t0 [m_final [Hsp_t0 [Hfe_t0 Hrest_final]]]].
    assert (Hab_t0 : Memory.anybytes a_t0 (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_t0).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_t0 mul1_v mStack_t0 Hfe_t0) as Ht0_bytes.
      cbv [Placeholder] in Ht0_bytes. exact Ht0_bytes. }
    exists m_final, mStack_t0.
    split. { exact Hab_t0. }
    split. { apply map.split_comm. exact Hsp_t0. }

    (* Final postcondition *)
    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists mul2_v.
    split. { exact Hb_mul2. }
    exact Hrest_final.
  Qed.

  (* ============================================================ *)
  (* Lemma 3: bls24_final_exp_hard_ok                              *)
  (* Body: 5 stackallocs (a,b,c,d,e) + 20-step chain + 5 deallocs *)
  (* The 20 steps use: pow_z(×8), frob(×1), frob_p2(×1),         *)
  (*   frob_p4(×1), mul(×6), sqr(×1), conjugate(×2)              *)
  (* ============================================================ *)

  Lemma bls24_final_exp_hard_ok :
    forall functions
      (EnvContains : map.get functions "bls24_final_exp_hard" =
        Some (snd BLS24_509_FinalExp.bls24_final_exp_hard))
      (HFp24mul     : spec_of_Fp24_mul functions)
      (HFp24sqr     : spec_of_Fp24_sqr functions)
      (HFp24conj    : spec_of_bls24_fp24_conjugate functions)
      (HFp24frob    : spec_of_bls24_fp24_frob functions)
      (HFp24frob_p2 : spec_of_bls24_fp24_frob_p2 functions)
      (HFp24frob_p4 : spec_of_bls24_fp24_frob_p4 functions)
      (HFp24powz    : spec_of_bls24_fp24_pow_z functions)
      (HFp24powz_ip : spec_of_bls24_fp24_pow_z_inplace functions),
    spec_of_bls24_final_exp_hard functions.
  Proof.
    intros. unfold spec_of_bls24_final_exp_hard.
    intros pout pf
      p_gfp4 p_gfp8 p_gfp24_1 p_gfp24_2
      p_gfp4_p2 p_gfp8_p2 p_gfp24_p2_1 p_gfp24_p2_2
      p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2
      old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BLS24_509_FinalExp.bls24_final_exp_hard. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stackalloc 1: a (Fp24)                                           *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_a mSa mCa HaSa HmSa.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_a mSa) HaSa) as [ai Hai].

    (* ================================================================ *)
    (* Stackalloc 2: b (Fp24)                                           *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_b mSb mCb HaSb HmSb.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_b mSb) HaSb) as [bi Hbi].

    (* ================================================================ *)
    (* Stackalloc 3: c (Fp24)                                           *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_c mSc mCc HaSc HmSc.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_c mSc) HaSc) as [ci Hci].

    (* ================================================================ *)
    (* Stackalloc 4: d (Fp24)                                           *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_d mSd mCd HaSd HmSd.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_d mSd) HaSd) as [di Hdi].

    (* ================================================================ *)
    (* Stackalloc 5: e (Fp24)                                           *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_e mSe mCe HaSe HmSe.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_e mSe) HaSe) as [ei Hei].

    cbv [BLS24_509_FinalExp.final_exp_hard_body
         BLS24_509_FinalExp.inline_pow_z
         BLS24_509_FinalExp.cmd_seq_list].

    (* ================================================================ *)
    (* Build master sep from 5 stackalloc layers                        *)
    (* ================================================================ *)
    pose proof (proj1 (map.split_comm mCa mem0 mSa) HmSa) as HmSa'.
    assert (Hsep1 :
      (FElem_Fp24 a_a ai ⋆
       (FElem_Fp24 pf f ⋆
        (FElem_Fp24 pout old_out ⋆ Rr))) mCa).
    { exists mSa, mem0. exact (conj HmSa' (conj Hai Hsep)). }

    pose proof (proj1 (map.split_comm mCb mCa mSb) HmSb) as HmSb'.
    assert (Hsep2 :
      (FElem_Fp24 a_b bi ⋆
       (FElem_Fp24 a_a ai ⋆
        (FElem_Fp24 pf f ⋆
         (FElem_Fp24 pout old_out ⋆ Rr)))) mCb).
    { exists mSb, mCa. exact (conj HmSb' (conj Hbi Hsep1)). }

    pose proof (proj1 (map.split_comm mCc mCb mSc) HmSc) as HmSc'.
    assert (Hsep3 :
      (FElem_Fp24 a_c ci ⋆
       (FElem_Fp24 a_b bi ⋆
        (FElem_Fp24 a_a ai ⋆
         (FElem_Fp24 pf f ⋆
          (FElem_Fp24 pout old_out ⋆ Rr))))) mCc).
    { exists mSc, mCb. exact (conj HmSc' (conj Hci Hsep2)). }

    pose proof (proj1 (map.split_comm mCd mCc mSd) HmSd) as HmSd'.
    assert (Hsep4 :
      (FElem_Fp24 a_d di ⋆
       (FElem_Fp24 a_c ci ⋆
        (FElem_Fp24 a_b bi ⋆
         (FElem_Fp24 a_a ai ⋆
          (FElem_Fp24 pf f ⋆
           (FElem_Fp24 pout old_out ⋆ Rr)))))) mCd).
    { exists mSd, mCc. exact (conj HmSd' (conj Hdi Hsep3)). }

    pose proof (proj1 (map.split_comm mCe mCd mSe) HmSe) as HmSe'.
    assert (Hsep_all :
      (FElem_Fp24 a_e ei ⋆
       (FElem_Fp24 a_d di ⋆
        (FElem_Fp24 a_c ci ⋆
         (FElem_Fp24 a_b bi ⋆
          (FElem_Fp24 a_a ai ⋆
           (FElem_Fp24 pf f ⋆
            (FElem_Fp24 pout old_out ⋆ Rr))))))) mCe).
    { exists mSe, mCd. exact (conj HmSe' (conj Hei Hsep4)). }

    clear Hsep Hsep1 Hsep2 Hsep3 Hsep4.

    (* ================================================================ *)
    (* 20-step addition chain                                            *)
    (* Steps 1-21 (including the two f^3 sub-steps):                   *)
    (*  1.  a = pow_z(f)                                                *)
    (*  2.  b = conj(f); b = a*b = f^{u-1}                             *)
    (*  3.  a = pow_z(b)                                                *)
    (*  4.  c = conj(b); c = a*c = f^{(u-1)^2}                         *)
    (*  5.  a = pow_z(c)                                                *)
    (*  6.  b = frob(c)                                                 *)
    (*  7.  d = a*b                                                     *)
    (*  8.  a = pow_z(d)                                                *)
    (*  9.  a = pow_z(a)                                                *)
    (* 10.  b = frob_p2(d)                                              *)
    (* 11.  e = a*b                                                     *)
    (* 12-15. a = e^{u^4} (4 pow_z)                                    *)
    (* 16.  b = frob_p4(e)                                              *)
    (* 17.  a = a*b                                                     *)
    (* 18.  c = conj(e)                                                 *)
    (* 19.  a = a*c                                                     *)
    (* 20a. b = sqr(f)                                                  *)
    (* 20b. b = b*f = f^3                                               *)
    (* 21.  out = a*b                                                   *)
    (* ================================================================ *)

    (* Step 1: a = pow_z(f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a1_v [Hb_a1 Hsep_a1]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 2a: b = conj(f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24conj.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b2a_v [Hb_b2a Hsep_b2a]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 2b: b = a*b = f^{u-1} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a1 |].
         split; [exact Hb_b2a |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b2_v [_ [Hb_b2 Hsep_b2]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 3: a = pow_z(b) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz.
         split; [exact Hb_b2 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a3_v [Hb_a3 Hsep_a3]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 4a: c = conj(b) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24conj.
         split; [exact Hb_b2 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c4a_v [Hb_c4a Hsep_c4a]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 4b: c = a*c = f^{(u-1)^2} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a3 |].
         split; [exact Hb_c4a |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c4_v [_ [Hb_c4 Hsep_c4]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 5: a = pow_z(c) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz.
         split; [exact Hb_c4 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a5_v [Hb_a5 Hsep_a5]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 6: b = frob(c) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24frob.
         split; [exact Hb_c4 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b6_v [Hb_b6 Hsep_b6]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 7: d = a*b = f^{(u+p)(u-1)^2} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a5 |].
         split; [exact Hb_b6 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [d7_v [_ [Hb_d7 Hsep_d7]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 8: a = pow_z(d) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz.
         split; [exact Hb_d7 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a8_v [Hb_a8 Hsep_a8]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 9: a = pow_z(a) — IN-PLACE (pout = px = a_a) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz_ip; [exact Hb_a8 | ecancel_assumption]. }
    intros ? ? ? [? [? [a9_v [Hb_a9 Hsep_a9]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 10: b = frob_p2(d) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24frob_p2.
         split; [exact Hb_d7 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b10_v [Hb_b10 Hsep_b10]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 11: e = a*b = f^{(u^2+p^2)(u+p)(u-1)^2} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a9 |].
         split; [exact Hb_b10 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [e11_v [_ [Hb_e11 Hsep_e11]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Steps 12-15: a = e^{u^4} (4 successive pow_z) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz.
         split; [exact Hb_e11 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a12_v [Hb_a12 Hsep_a12]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 13: a = pow_z(a) — IN-PLACE *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz_ip; [exact Hb_a12 | ecancel_assumption]. }
    intros ? ? ? [? [? [a13_v [Hb_a13 Hsep_a13]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 14: a = pow_z(a) — IN-PLACE *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz_ip; [exact Hb_a13 | ecancel_assumption]. }
    intros ? ? ? [? [? [a14_v [Hb_a14 Hsep_a14]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 15: a = pow_z(a) — IN-PLACE *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24powz_ip; [exact Hb_a14 | ecancel_assumption]. }
    intros ? ? ? [? [? [a15_v [Hb_a15 Hsep_a15]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 16: b = frob_p4(e) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24frob_p4.
         split; [exact Hb_e11 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b16_v [Hb_b16 Hsep_b16]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 17: a = a*b = f^{(u^4+p^4)...} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a15 |].
         split; [exact Hb_b16 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a17_v [_ [Hb_a17 Hsep_a17]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 18: c = conj(e) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24conj.
         split; [exact Hb_e11 |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [c18_v [Hb_c18 Hsep_c18]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 19: a = a*c = f^{(u^4+p^4-1)...} *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a17 |].
         split; [exact Hb_c18 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [a19_v [_ [Hb_a19 Hsep_a19]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 20a: b = sqr(f) *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24sqr.
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b20_v [_ [Hb_b20 Hsep_b20]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 20b: b = b*f = f^3 *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_b20 |].
         split; [exact Hbf |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [b21_v [_ [Hb_b21 Hsep_b21]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* Step 21: out = a*b = full hard part result *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFp24mul.
         split; [exact Hb_a19 |].
         split; [exact Hb_b21 |].
         split; [eexists; ecancel_assumption_with_copy |].
         split; [eexists; ecancel_assumption_with_copy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [out_v [_ [Hb_out Hsep_out]]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stack deallocation: e, d, c, b, a (innermost first)              *)
    (* Use match goal to extract the current memory name.               *)
    (* ================================================================ *)

    (* Dealloc e — extract current sep hypothesis *)
    match goal with Hc : (_ ⋆ _)%sep ?m |- _ =>
      assert (Hsep_e_front :
        (FElem_Fp24 a_e e11_v ⋆
         (FElem_Fp24 pout out_v ⋆
          (FElem_Fp24 a_d d7_v ⋆
           (FElem_Fp24 a_c c18_v ⋆
            (FElem_Fp24 a_b b21_v ⋆
             (FElem_Fp24 a_a a19_v ⋆
              (FElem_Fp24 pf f ⋆ Rr))))))) m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_e_front as [mStack_e [m_ae [Hsp_e [Hfe_e Hrest_e]]]].
    assert (Hab_e : Memory.anybytes a_e (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_e).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_e e11_v mStack_e Hfe_e) as He_bytes.
      cbv [Placeholder] in He_bytes. exact He_bytes. }
    exists m_ae, mStack_e.
    split. { exact Hab_e. }
    split. { apply map.split_comm. exact Hsp_e. }

    (* Dealloc d *)
    assert (Hsep_d_front :
      (FElem_Fp24 a_d d7_v ⋆
       (FElem_Fp24 pout out_v ⋆
        (FElem_Fp24 a_c c18_v ⋆
         (FElem_Fp24 a_b b21_v ⋆
          (FElem_Fp24 a_a a19_v ⋆
           (FElem_Fp24 pf f ⋆ Rr)))))) m_ae).
    { ecancel_assumption. }
    clear Hrest_e.
    destruct Hsep_d_front as [mStack_d [m_ad [Hsp_d [Hfe_d Hrest_d]]]].
    assert (Hab_d : Memory.anybytes a_d (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_d).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_d d7_v mStack_d Hfe_d) as Hd_bytes.
      cbv [Placeholder] in Hd_bytes. exact Hd_bytes. }
    exists m_ad, mStack_d.
    split. { exact Hab_d. }
    split. { apply map.split_comm. exact Hsp_d. }

    (* Dealloc c *)
    assert (Hsep_c_front :
      (FElem_Fp24 a_c c18_v ⋆
       (FElem_Fp24 pout out_v ⋆
        (FElem_Fp24 a_b b21_v ⋆
         (FElem_Fp24 a_a a19_v ⋆
          (FElem_Fp24 pf f ⋆ Rr))))) m_ad).
    { ecancel_assumption. }
    clear Hrest_d.
    destruct Hsep_c_front as [mStack_c [m_ac [Hsp_c [Hfe_c Hrest_c]]]].
    assert (Hab_c : Memory.anybytes a_c (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_c).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_c c18_v mStack_c Hfe_c) as Hc_bytes.
      cbv [Placeholder] in Hc_bytes. exact Hc_bytes. }
    exists m_ac, mStack_c.
    split. { exact Hab_c. }
    split. { apply map.split_comm. exact Hsp_c. }

    (* Dealloc b *)
    assert (Hsep_b_front :
      (FElem_Fp24 a_b b21_v ⋆
       (FElem_Fp24 pout out_v ⋆
        (FElem_Fp24 a_a a19_v ⋆
         (FElem_Fp24 pf f ⋆ Rr)))) m_ac).
    { ecancel_assumption. }
    clear Hrest_c.
    destruct Hsep_b_front as [mStack_b [m_ab [Hsp_b [Hfe_b Hrest_b]]]].
    assert (Hab_b : Memory.anybytes a_b (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_b).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_b b21_v mStack_b Hfe_b) as Hb_bytes.
      cbv [Placeholder] in Hb_bytes. exact Hb_bytes. }
    exists m_ab, mStack_b.
    split. { exact Hab_b. }
    split. { apply map.split_comm. exact Hsp_b. }

    (* Dealloc a *)
    assert (Hsep_a_front :
      (FElem_Fp24 a_a a19_v ⋆
       (FElem_Fp24 pout out_v ⋆
        (FElem_Fp24 pf f ⋆ Rr))) m_ab).
    { ecancel_assumption. }
    clear Hrest_b.
    destruct Hsep_a_front as [mStack_a [m_final [Hsp_a [Hfe_a Hrest_final]]]].
    assert (Hab_a : Memory.anybytes a_a (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_a).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_a a19_v mStack_a Hfe_a) as Ha_bytes.
      cbv [Placeholder] in Ha_bytes. exact Ha_bytes. }
    exists m_final, mStack_a.
    split. { exact Hab_a. }
    split. { apply map.split_comm. exact Hsp_a. }

    (* Final postcondition *)
    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists out_v.
    split. { exact Hb_out. }
    exact Hrest_final.
  Qed.

  (* ============================================================ *)
  (* Lemma 4: bls24_final_exp_ok                                   *)
  (* Body: 1 stackalloc (easy_result) + 2 calls + 1 dealloc.     *)
  (* Fully proven assuming easy and hard lemmas.                   *)
  (* ============================================================ *)

  Lemma bls24_final_exp_ok :
    forall functions
      (EnvContains : map.get functions "bls24_final_exp" =
        Some (snd BLS24_509_FinalExp.bls24_final_exp))
      (HFeasy : spec_of_bls24_final_exp_easy functions)
      (HFhard : spec_of_bls24_final_exp_hard functions),
    spec_of_bls24_final_exp functions.
  Proof.
    intros. unfold spec_of_bls24_final_exp.
    intros pout pf
      p_gamma_fp4 p_gamma_fp8 p_gamma_fp24_1 p_gamma_fp24_2
      p_gamma_fp4_p2 p_gamma_fp8_p2 p_gamma_fp24_p2_1 p_gamma_fp24_p2_2
      p_gamma_fp4_p4 p_gamma_fp8_p4 p_gamma_fp24_p4_1 p_gamma_fp24_p4_2
      old_out f Rr tr mem0 [Hbf Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold BLS24_509_FinalExp.bls24_final_exp. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stackalloc: easy_result (Fp24)                                   *)
    (* ================================================================ *)
    straightline. split. { apply Z_mod_mult. }
    intros a_easy mSe mCe HaSe HmSe.
    pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _
      bls24_Fp24_repr wordok mapok a_easy mSe) HaSe) as [ei Hei].

    cbv [BLS24_509_FinalExp.cmd_seq_list].

    (* Build master sep *)
    pose proof (proj1 (map.split_comm mCe mem0 mSe) HmSe) as HmSe'.
    assert (Hsep_all :
      (FElem_Fp24 a_easy ei ⋆
       (FElem_Fp24 pf f ⋆
        (FElem_Fp24 pout old_out ⋆ Rr))) mCe).
    { exists mSe, mem0. exact (conj HmSe' (conj Hei Hsep)). }

    clear Hsep.

    (* ================================================================ *)
    (* Call 1: final_exp_easy(easy_result, f, gammas_p4)                *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFeasy.
         split; [exact Hbf |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [easy_v [Hb_easy Hsep_easy]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Call 2: final_exp_hard(out, easy_result, all_gammas)             *)
    (* ================================================================ *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HFhard.
         split; [exact Hb_easy |].
         ecancel_assumption_with_copy. }
    intros ? ? ? [? [? [hard_v [Hb_hard Hsep_hard]]]]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* ================================================================ *)
    (* Stack deallocation: easy_result                                  *)
    (* ================================================================ *)
    match goal with Hc : (_ ⋆ _)%sep ?m |- _ =>
      assert (Hsep_easy_front :
        (FElem_Fp24 a_easy easy_v ⋆
         (FElem_Fp24 pout hard_v ⋆
          (FElem_Fp24 pf f ⋆ Rr))) m);
      [ecancel_assumption | clear Hc]
    end.
    destruct Hsep_easy_front as [mStack_easy [m_final [Hsp_easy [Hfe_easy Hrest_final]]]].
    assert (Hab_easy : Memory.anybytes a_easy (AbstractField.felem_size_in_bytes (F:=Fp24)) mStack_easy).
    { pose proof (AbstractField.FElem_to_bytes
                    (field_representation:=bls24_Fp24_repr)
                    a_easy easy_v mStack_easy Hfe_easy) as Heasy_bytes.
      cbv [Placeholder] in Heasy_bytes. exact Heasy_bytes. }
    exists m_final, mStack_easy.
    split. { exact Hab_easy. }
    split. { apply map.split_comm. exact Hsp_easy. }

    (* Final postcondition *)
    cbv [list_map list_map_body WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    exists hard_v.
    split. { exact Hb_hard. }
    exact Hrest_final.
  Qed.

  (* ============================================================ *)
  (* Strengthened frob body-correctness lemmas                     *)
  (*                                                                *)
  (* Each strong-spec lemma closes the algebraic Frobenius           *)
  (* equation [Fp24_feval out = FrobModelFp24 ... (Fp24_feval x) ...] *)
  (* via a library bridge analogous to BLS12-377's                   *)
  (* [spec_of_Fp12_frobenius_p2_strong_ok] (commit a6f5044).         *)
  (*                                                                *)
  (* Pattern: take the library-shape spec                            *)
  (*   [BLS24_509_FinalExp.spec_of_bls24_fp24_frob_lib functions]    *)
  (* as a hypothesis (Hlib).  The lib spec carries the same algebraic *)
  (* clause and bounds, but uses a different sep-ordering convention *)
  (* (px first, then gammas in call-arg order, then pout last with   *)
  (* Rr) — matching PairingFieldOps.spec_of_Fp12_frobenius_p2.       *)
  (*                                                                *)
  (* The bridge proof uses [Semantics.weaken_call] +                 *)
  (* [ecancel_assumption] to translate from the strong sep shape     *)
  (* (pout first, then px, then gammas, then Rr) to the lib shape.   *)
  (*                                                                *)
  (* The body-correctness of the library spec itself is deferred to  *)
  (* a future Fp24 extension of PairingFieldOps.v (BLS24-509's       *)
  (* quadratic-first tower has no current library coverage; BLS12's  *)
  (* cubic-then-quadratic Fp12 lemmas don't directly apply).         *)
  (* ============================================================ *)

  Lemma bls24_fp24_frob_strong_ok :
    forall functions
      (Hlib : BLS24_509_FinalExp.spec_of_bls24_fp24_frob_lib functions),
    BLS24_509_FinalExp.spec_of_bls24_fp24_frob_strong functions.
  Proof.
    intros functions Hlib.
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_strong.
    intros pout px p_gfp4 p_gfp8 p_gfp24_1 p_gfp24_2.
    intros old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem.
    intros [Hbx [Hbg4 [Hbg8 [Hbg24_1 [Hbg24_2 Hmem]]]]].
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_lib in Hlib.
    specialize (Hlib pout px p_gfp4 p_gfp8 p_gfp24_1 p_gfp24_2
                     old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem).
    eapply Semantics.weaken_call.
    1:{ eapply Hlib. clear Hlib.
        split; [exact Hbx|].
        split; [exact Hbg4|].
        split; [exact Hbg8|].
        split; [exact Hbg24_1|].
        split; [exact Hbg24_2|].
        ecancel_assumption. }
    intros tr' mem' rets [Hrets [Htreq [out [Hbounded [Hfeval Hmem']]]]].
    subst tr' rets.
    split; [reflexivity|].
    split; [reflexivity|].
    exists out.
    split; [exact Hbounded|].
    split; [exact Hfeval|].
    ecancel_assumption.
  Qed.

  Lemma bls24_fp24_frob_p2_strong_ok :
    forall functions
      (Hlib : BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p2_lib functions),
    BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p2_strong functions.
  Proof.
    intros functions Hlib.
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p2_strong.
    intros pout px p_gfp4_p2 p_gfp8_p2 p_gfp24_p2_1 p_gfp24_p2_2.
    intros old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem.
    intros [Hbx [Hbg4 [Hbg8 [Hbg24_1 [Hbg24_2 Hmem]]]]].
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p2_lib in Hlib.
    specialize (Hlib pout px p_gfp4_p2 p_gfp8_p2 p_gfp24_p2_1 p_gfp24_p2_2
                     old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem).
    eapply Semantics.weaken_call.
    1:{ eapply Hlib. clear Hlib.
        split; [exact Hbx|].
        split; [exact Hbg4|].
        split; [exact Hbg8|].
        split; [exact Hbg24_1|].
        split; [exact Hbg24_2|].
        ecancel_assumption. }
    intros tr' mem' rets [Hrets [Htreq [out [Hbounded [Hfeval Hmem']]]]].
    subst tr' rets.
    split; [reflexivity|].
    split; [reflexivity|].
    exists out.
    split; [exact Hbounded|].
    split; [exact Hfeval|].
    ecancel_assumption.
  Qed.

  Lemma bls24_fp24_frob_p4_strong_ok :
    forall functions
      (Hlib : BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p4_lib functions),
    BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p4_strong functions.
  Proof.
    intros functions Hlib.
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p4_strong.
    intros pout px p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2.
    intros old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem.
    intros [Hbx [Hbg4 [Hbg8 [Hbg24_1 [Hbg24_2 Hmem]]]]].
    unfold BLS24_509_FinalExp.spec_of_bls24_fp24_frob_p4_lib in Hlib.
    specialize (Hlib pout px p_gfp4_p4 p_gfp8_p4 p_gfp24_p4_1 p_gfp24_p4_2
                     old_out x gfp4 gfp8 gfp24_1 gfp24_2 Rr tr mem).
    eapply Semantics.weaken_call.
    1:{ eapply Hlib. clear Hlib.
        split; [exact Hbx|].
        split; [exact Hbg4|].
        split; [exact Hbg8|].
        split; [exact Hbg24_1|].
        split; [exact Hbg24_2|].
        ecancel_assumption. }
    intros tr' mem' rets [Hrets [Htreq [out [Hbounded [Hfeval Hmem']]]]].
    subst tr' rets.
    split; [reflexivity|].
    split; [reflexivity|].
    exists out.
    split; [exact Hbounded|].
    split; [exact Hfeval|].
    ecancel_assumption.
  Qed.

End BLS24_FinalExpProof.
