(** * Single-scalar wNAF ��� WP proof with abstracted loop body.

    The bedrock2 loop iterates MSB-first (iter = num_iters down to 0).
    At each step: iter--, double acc, process d[iter].

    Invariant: accumulator is on the curve and is [pt_eq] to
    scmul(weighted_sum(skipn vi dk)) P.

    Generic over field_parameters — works for BN254, BN256, P-256, etc.

    ** G6 **  The point-level part of the invariant is stated up to the
    Section-parametric equivalence [pt_eq] and carries an [oncurve]
    conjunct; the sep-logic part stays Leibniz.  Instantiating
    [pt_eq := eq], [oncurve := fun _ => True] recovers the previous
    interface.

    ** G5 **  The aliased negation is called at the Section-parametric
    name [opp_name], not the [FieldParameters] field [opp]. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import bedrock2.Loops.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section WNAF_Single.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word} {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters} {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok} {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z := (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name opp_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  (** *** G6: the point-level equivalence and the on-curve predicate.

      The four group laws used to be declared here; [wnaf_single_ok]
      never used them (all algebra is inside [HLoopBody]), so only what
      the invariant and the initialisation need is kept. *)
  Context (pt_eq : F * F * F -> F * F * F -> Prop).
  Context (pt_eq_equiv : Equivalence pt_eq).
  Context (oncurve : F * F * F -> Prop).
  Context (oncurve_id : oncurve (Fzero,Fone,Fzero)).
  Let scmul_s := scmul Fzero Fone curve_add.

  Local Lemma pt_refl : forall P, pt_eq P P.
  Proof. destruct pt_eq_equiv as [Hr _ _]. exact Hr. Qed.

  (** Loop invariant for MSB-first downward loop.
      At top of loop with iter = vi, the accumulator is on the curve and
        acc ~ scmul(weighted_sum(skipn vi dk)) P
      Initially (vi=num_iters): skipn num_iters dk = [], ws = 0, acc = identity.
      Finally (vi=0): skipn 0 dk = dk, ws = wsum dk = k, acc ~ k*P. *)
  Definition wnaf_single_inv
    (pOx pOy pOz pAx pAy pAz pT pDK : word)
    (Px Py Pz : F) (dk : list Z) (num_iters : nat)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    exists (Ox Oy Oz Ax Ay Az : F) (iw : word),
    (oncurve (Ox, Oy, Oz)
     /\ pt_eq (Ox, Oy, Oz) (scmul_s (Z.to_nat (weighted_sum (skipn v dk) 0)) (Px,Py,Pz)))
    /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
        ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R) m
    /\ map.get l "outx" = Some pOx /\ map.get l "outy" = Some pOy
    /\ map.get l "outz" = Some pOz /\ map.get l "auxx" = Some pAx
    /\ map.get l "auxy" = Some pAy /\ map.get l "auxz" = Some pAz
    /\ map.get l "table_P" = Some pT
    /\ map.get l "digits_k" = Some pDK
    /\ map.get l "iter" = Some iw
    /\ word.unsigned iw = Z.of_nat v
    /\ (v <= num_iters)%nat
    /\ tr = t.

  Theorem wnaf_single_ok :
    forall functions
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      dk Px Py Pz k num_iters
      (Hlen : length dk = num_iters)
      (Hk : wsum dk = k)
      (Hknn : 0 <= k)
      (Hnbound : Z.of_nat num_iters < 2 ^ width)
      (R : mem -> Prop)
      pT pDK
      (HLoopBody : forall (n : nat) pOx pOy pOz pAx pAy pAz
         (Ox Oy Oz Ax Ay Az : F) tr0 m0 l0,
         (n < num_iters)%nat ->
         oncurve (Ox,Oy,Oz) ->
         pt_eq (Ox,Oy,Oz) (scmul_s (Z.to_nat (weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz)) ->
         (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
          ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R) m0 ->
         map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
         map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
         map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
         map.get l0 "table_P" = Some pT ->
         map.get l0 "digits_k" = Some pDK ->
         map.get l0 "iter" = Some (word.of_Z (Z.of_nat (S n))) ->
         WeakestPrecondition.cmd functions
           (wnaf_single_loop_body curve_add_name curve_double_name
              felem_copy opp_name felem_size_in_bytes
              "digits_k" "table_P")
           tr0 m0 l0
           (fun t' m' l' =>
             exists Ox' Oy' Oz' Ax' Ay' Az',
             oncurve (Ox',Oy',Oz')
             /\ pt_eq (Ox',Oy',Oz') (scmul_s (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))
             /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
                 ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R) m'
             /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
             /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
             /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
             /\ map.get l' "table_P" = Some pT
             /\ map.get l' "digits_k" = Some pDK
             /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
             /\ tr0 = t')),
    forall pOx pOy pOz pAx pAy pAz
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F) tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    map.get l "table_P" = Some pT ->
    map.get l "digits_k" = Some pDK ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R) m ->
    WeakestPrecondition.cmd functions
      (wnaf_single_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp_name (Z.of_nat num_iters) felem_size_in_bytes
         "digits_k" "table_P")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        oncurve (Rx,Ry,Rz)
        /\ pt_eq (Rx,Ry,Rz) (scmul_s (Z.to_nat k) (Px,Py,Pz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R) m').
  Proof.
    intros.
    unfold wnaf_single_func_body.

    (* store_zero *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [dexprs list_map list_map_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
      eexists; split; [exact H|]. eexists; split; [exact H0|].
      eexists; split; [exact H1|]. exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply HStoreZero. ecancel_assumption_impl. }
    intros t0 m0 rets0 [Hrets0 [Htr0 Hsep0]].
    subst rets0. symmetry in Htr0. subst t0.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* set iter = num_iters *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal dlet.dlet]. exact eq_refl. }

    (* while loop *)
    eapply Loops.while_localsmap
      with (v0 := num_iters) (lt := Nat.lt)
           (invariant := wnaf_single_inv pOx pOy pOz pAx pAy pAz pT pDK
              Px Py Pz dk num_iters R tr).
    { exact lt_wf. }

    (* Initial invariant *)
    { unfold wnaf_single_inv.
      rewrite skipn_all2 by lia.
      simpl weighted_sum.
      exists Fzero, Fone, Fzero, Ax0, Ay0, Az0, (word.of_Z (Z.of_nat num_iters)).
      split.
      - split.
        + exact oncurve_id.
        + simpl Z.to_nat. unfold scmul_s. simpl scmul.
          apply pt_refl.
      - change CompilationAbstract.FElem with Compilation2.FElem in Hsep0.
        repeat split; try ecancel_assumption_impl;
        try (rewrite map.get_put_same; exact eq_refl);
        try (rewrite map.get_put_diff by congruence; assumption);
        try lia.
        + rewrite word.unsigned_of_Z; apply Z.mod_small;
          pose proof (Nat2Z.is_nonneg num_iters); lia. }

    (* Loop body + post-loop *)
    { intros vi t1 m1 l1 Hinv.
      destruct Hinv as (Oxi & Oyi & Ozi & Axi & Ayi & Azi & iwi &
        (Hoc_i & Hout_i) & Hsep_i & Hl_ox' & Hl_oy' & Hl_oz' &
        Hl_ax' & Hl_ay' & Hl_az' &
        Hl_t' & Hl_dk' &
        Hl_iter' & Hiw_val & Hv_le & Htr_eq).
      subst t1.

      (* Branch condition: 0 < iter *)
      exists (Semantics.interp_binop bopname.ltu (word.of_Z 0) iwi).
      unfold Markers.split. split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        eexists. split; [exact Hl_iter'|]. exact eq_refl. }
      split.

      - (* TRUE branch: vi > 0 *)
        intro Hne.
        assert (Hvi_gt0 : (vi > 0)%nat).
        { cbv [Semantics.interp_binop] in Hne.
          destruct (word.ltu (word.of_Z 0) iwi) eqn:Eb;
            [|exfalso; apply Hne; rewrite word.unsigned_of_Z_0; reflexivity].
          pose proof (@word.unsigned_ltu _ _ word_ok (word.of_Z 0) iwi) as Hltu.
          rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_lt in Hltu.
          rewrite word.unsigned_of_Z_0, Hiw_val in Hltu. lia. }
        clear Hne.
        destruct vi as [|n]; [lia|].
        assert (Hn_lt : (n < num_iters)%nat) by lia.
        assert (Hiwi_eq : iwi = word.of_Z (Z.of_nat (S n)))
          by (rewrite <- (word.of_Z_unsigned iwi); rewrite Hiw_val; reflexivity).
        subst iwi.

        (* Apply HLoopBody *)
        specialize (HLoopBody n pOx pOy pOz pAx pAy pAz
          Oxi Oyi Ozi Axi Ayi Azi tr m1 l1
          Hn_lt Hoc_i Hout_i Hsep_i Hl_ox' Hl_oy' Hl_oz' Hl_ax' Hl_ay' Hl_az'
          Hl_t' Hl_dk' Hl_iter').

        eapply WeakestPreconditionProperties.Proper_cmd; [|exact HLoopBody].
        intros t' m' l' (Ox' & Oy' & Oz' & Ax' & Ay' & Az' &
          Hoc' & Hout' & Hsep' & Hlox'' & Hloy'' & Hloz'' &
          Hlax'' & Hlay'' & Hlaz'' &
          Hlt'' & Hldk'' &
          Hliter'' & Htr').
        subst t'.

        exists n. unfold Markers.split. split.
        + unfold wnaf_single_inv.
          exists Ox', Oy', Oz', Ax', Ay', Az', (word.of_Z (Z.of_nat n)).
          repeat split; try assumption; try lia.
          * rewrite word.unsigned_of_Z; apply Z.mod_small;
            pose proof (Nat2Z.is_nonneg n); lia.
        + lia.

      - (* FALSE branch: vi = 0 *)
        intro Hcond.
        assert (Hvi0 : vi = 0%nat).
        { cbv [Semantics.interp_binop] in Hcond.
          destruct (word.ltu (word.of_Z 0) iwi) eqn:Eb.
          - exfalso. rewrite word.unsigned_of_Z_1 in Hcond. lia.
          - pose proof (@word.unsigned_ltu _ _ word_ok (word.of_Z 0) iwi) as Hltu.
            rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_ge in Hltu.
            rewrite word.unsigned_of_Z_0, Hiw_val in Hltu. lia. }
        subst vi. simpl skipn in Hout_i.
        unfold wsum in Hk. rewrite Hk in Hout_i.
        exists Oxi, Oyi, Ozi, Axi, Ayi, Azi.
        split; [exact Hoc_i|].
        split; [exact Hout_i|]. ecancel_assumption. }
  Qed.

End WNAF_Single.
