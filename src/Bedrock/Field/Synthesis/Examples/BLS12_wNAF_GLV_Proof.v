(** * BLS12 wNAF GLV — WP proof with abstracted loop body.

    The bedrock2 loop iterates MSB-first (iter = 129 down to 0).
    At each step: iter--, double acc, process d1[iter], process d2[iter].

    Invariant: accumulator = Horner partial evaluation of digits vi..128,
    i.e., weighted_sum (skipn vi dk) 0 for each scalar component. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import bedrock2.Loops.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section WNAF_GLV.
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

  Context (curve_add_name curve_double_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).
  Let scmul_glv := scmul Fzero Fone curve_add.

  (** Loop invariant for the MSB-first downward loop.

      At the top of the loop with iter = vi, the accumulator holds
      the Horner evaluation of digits vi..128:

        acc = curve_add (scmul (ws(skipn vi dk1)) P) (scmul (ws(skipn vi dk2)) Phi)

      Here ws = weighted_sum with starting position 0.

      Initially (vi=129): skipn 129 dk = [], ws([]) = 0, acc = identity.
      Finally (vi=0): skipn 0 dk = dk, ws(dk) = wsum dk = k, acc = k*P + k2*Phi. *)

  Definition wnaf_inv
    (pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2 : word)
    (Px Py Pz Phix Phiy Phiz : F) (dk1 dk2 : list Z)
    (R : word -> word -> word -> word -> mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    exists (Ox Oy Oz Ax Ay Az : F) (iw : word),
    (Ox, Oy, Oz) =
      curve_add (scmul_glv (Z.to_nat (weighted_sum (skipn v dk1) 0)) (Px,Py,Pz))
                (scmul_glv (Z.to_nat (weighted_sum (skipn v dk2) 0)) (Phix,Phiy,Phiz))
    /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
        ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R pTP pTPhi pDK1 pDK2) m
    /\ map.get l "outx" = Some pOx /\ map.get l "outy" = Some pOy
    /\ map.get l "outz" = Some pOz /\ map.get l "auxx" = Some pAx
    /\ map.get l "auxy" = Some pAy /\ map.get l "auxz" = Some pAz
    /\ map.get l "table_P" = Some pTP /\ map.get l "table_Phi" = Some pTPhi
    /\ map.get l "digits_k1" = Some pDK1 /\ map.get l "digits_k2" = Some pDK2
    /\ map.get l "iter" = Some iw
    /\ word.unsigned iw = Z.of_nat v
    /\ (v <= 129)%nat
    /\ tr = t.

  Theorem wnaf_glv_ok :
    forall functions
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      dk1 dk2 Px Py Pz Phix Phiy Phiz k1 k2
      (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat)
      (Hk1 : wsum dk1 = k1) (Hk2 : wsum dk2 = k2)
      (Hk1nn : 0 <= k1) (Hk2nn : 0 <= k2)
      (R : word -> word -> word -> word -> mem -> Prop)
      (** Loop body hypothesis: given iter = S n and the invariant
          at S n, the body (iter--, double, process d1[n], process d2[n])
          establishes the invariant at n.
          The postcondition directly states the Horner partial evaluation,
          which correctly models both positive digits (add scmul)
          and negative digits (add negated scmul via opp). *)
      (HLoopBody : forall (n : nat) pOx pOy pOz pAx pAy pAz
         pTP pTPhi pDK1 pDK2
         (Ox Oy Oz Ax Ay Az : F) tr0 m0 l0,
         (n < 129)%nat ->
         (Ox,Oy,Oz) = curve_add
           (scmul_glv (Z.to_nat (weighted_sum (skipn (S n) dk1) 0)) (Px,Py,Pz))
           (scmul_glv (Z.to_nat (weighted_sum (skipn (S n) dk2) 0)) (Phix,Phiy,Phiz)) ->
         (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
          ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R pTP pTPhi pDK1 pDK2) m0 ->
         map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
         map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
         map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
         map.get l0 "table_P" = Some pTP -> map.get l0 "table_Phi" = Some pTPhi ->
         map.get l0 "digits_k1" = Some pDK1 -> map.get l0 "digits_k2" = Some pDK2 ->
         map.get l0 "iter" = Some (word.of_Z (Z.of_nat (S n))) ->
         WeakestPrecondition.cmd functions
           (wnaf_loop_body curve_add_name curve_double_name
              felem_copy opp felem_size_in_bytes
              "digits_k1" "digits_k2" "table_P" "table_Phi")
           tr0 m0 l0
           (fun t' m' l' =>
             exists Ox' Oy' Oz' Ax' Ay' Az',
             (Ox',Oy',Oz') =
               curve_add
                 (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
                 (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
             /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
                 ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R pTP pTPhi pDK1 pDK2) m'
             /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
             /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
             /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
             /\ map.get l' "table_P" = Some pTP /\ map.get l' "table_Phi" = Some pTPhi
             /\ map.get l' "digits_k1" = Some pDK1 /\ map.get l' "digits_k2" = Some pDK2
             /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
             /\ tr0 = t')),
    forall pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F) tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    map.get l "table_P" = Some pTP -> map.get l "table_Phi" = Some pTPhi ->
    map.get l "digits_k1" = Some pDK1 -> map.get l "digits_k2" = Some pDK2 ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R pTP pTPhi pDK1 pDK2) m ->
    WeakestPrecondition.cmd functions
      (wnaf_glv_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp 129 felem_size_in_bytes
         "digits_k1" "digits_k2" "table_P" "table_Phi")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        (Rx,Ry,Rz) = curve_add (scmul_glv (Z.to_nat k1) (Px,Py,Pz))
                                (scmul_glv (Z.to_nat k2) (Phix,Phiy,Phiz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R pTP pTPhi pDK1 pDK2) m').
  Proof.
    intros.
    unfold wnaf_glv_func_body.

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

    (* set iter = 129 *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal dlet.dlet]. exact eq_refl. }

    (* while loop — variant is iter value, decreasing from 129 to 0 *)
    eapply Loops.while_localsmap
      with (v0 := 129%nat) (lt := Nat.lt)
           (invariant := wnaf_inv pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
              Px Py Pz Phix Phiy Phiz dk1 dk2 R tr).
    { exact lt_wf. }

    (* Initial invariant: iter = 129, skipn 129 dk = [], acc = identity *)
    { unfold wnaf_inv.
      rewrite skipn_all2 by lia. rewrite skipn_all2 by lia.
      simpl weighted_sum.
      exists Fzero, Fone, Fzero, Ax0, Ay0, Az0, (word.of_Z 129).
      split.
      - simpl Z.to_nat. unfold scmul_glv. simpl scmul.
        rewrite curve_add_id_l. reflexivity.
      - change CompilationAbstract.FElem with Compilation2.FElem in Hsep0.
        repeat split; try ecancel_assumption_impl;
        try (rewrite map.get_put_same; exact eq_refl);
        try (rewrite map.get_put_diff by congruence; assumption);
        try lia.
        + rewrite word.unsigned_of_Z. unfold word.wrap.
          destruct width_cases as [Hw|Hw]; rewrite Hw;
          (change (129 mod 2 ^ 32) with 129 || change (129 mod 2 ^ 64) with 129);
          reflexivity. }

    (* Loop body + post-loop *)
    { intros vi t1 m1 l1 Hinv.
      destruct Hinv as (Oxi & Oyi & Ozi & Axi & Ayi & Azi & iwi &
        Hout_i & Hsep_i & Hl_ox' & Hl_oy' & Hl_oz' &
        Hl_ax' & Hl_ay' & Hl_az' &
        Hl_tp' & Hl_tphi' & Hl_dk1' & Hl_dk2' &
        Hl_iter' & Hiw_val & Hv_le & Htr_eq).
      subst t1.

      (* Branch condition: 0 < iter *)
      exists (Semantics.interp_binop bopname.ltu (word.of_Z 0) iwi).
      unfold Markers.split. split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        eexists. split; [exact Hl_iter'|]. exact eq_refl. }
      split.

      - (* TRUE branch: vi > 0, iter > 0 *)
        intro Hne.
        assert (Hvi_gt0 : (vi > 0)%nat).
        { cbv [Semantics.interp_binop] in Hne.
          destruct (word.ltu (word.of_Z 0) iwi) eqn:Eb;
            [|exfalso; apply Hne; rewrite word.unsigned_of_Z_0; reflexivity].
          pose proof (@word.unsigned_ltu _ _ word_ok (word.of_Z 0) iwi) as Hltu.
          rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_lt in Hltu.
          rewrite word.unsigned_of_Z_0, Hiw_val in Hltu. lia. }
        clear Hne.

        (* vi = S n for some n < 129 *)
        destruct vi as [|n]; [lia|].
        assert (Hn_lt : (n < 129)%nat) by lia.

        (* Replace iwi with word.of_Z (S n) *)
        assert (Hiwi_eq : iwi = word.of_Z (Z.of_nat (S n)))
          by (rewrite <- (word.of_Z_unsigned iwi); rewrite Hiw_val; reflexivity).
        subst iwi.

        (* Apply HLoopBody *)
        specialize (HLoopBody n pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
          Oxi Oyi Ozi Axi Ayi Azi tr m1 l1
          Hn_lt Hout_i Hsep_i Hl_ox' Hl_oy' Hl_oz' Hl_ax' Hl_ay' Hl_az'
          Hl_tp' Hl_tphi' Hl_dk1' Hl_dk2' Hl_iter').

        eapply WeakestPreconditionProperties.Proper_cmd; [|exact HLoopBody].
        intros t' m' l' (Ox' & Oy' & Oz' & Ax' & Ay' & Az' &
          Hout' & Hsep' & Hlox'' & Hloy'' & Hloz'' &
          Hlax'' & Hlay'' & Hlaz'' &
          Hltp'' & Hltphi'' & Hldk1'' & Hldk2'' &
          Hliter'' & Htr').
        subst t'.

        exists n. unfold Markers.split. split.
        + (* Invariant at n *)
          unfold wnaf_inv.
          exists Ox', Oy', Oz', Ax', Ay', Az', (word.of_Z (Z.of_nat n)).
          repeat split; try assumption; try lia.
          * rewrite word.unsigned_of_Z. unfold word.wrap.
            destruct width_cases as [Hw|Hw]; rewrite Hw;
            rewrite Z.mod_small; lia.
        + lia.

      - (* FALSE branch: vi = 0, iter = 0 *)
        intro Hcond.
        assert (Hvi0 : vi = 0%nat).
        { cbv [Semantics.interp_binop] in Hcond.
          destruct (word.ltu (word.of_Z 0) iwi) eqn:Eb.
          - exfalso. rewrite word.unsigned_of_Z_1 in Hcond. lia.
          - pose proof (@word.unsigned_ltu _ _ word_ok (word.of_Z 0) iwi) as Hltu.
            rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_ge in Hltu.
            rewrite word.unsigned_of_Z_0, Hiw_val in Hltu. lia. }
        subst vi. simpl skipn in Hout_i.
        unfold wsum in Hk1, Hk2. rewrite Hk1, Hk2 in Hout_i.
        exists Oxi, Oyi, Ozi, Axi, Ayi, Azi.
        split; [exact Hout_i|]. ecancel_assumption. }
  Qed.

End WNAF_GLV.
