(** * The MSM's addition with a mixed-addition fast path (BLS12-381 G1).

    [msm_curve_add_mixed] is the new body of ["msm_curve_add"], the addition that
    [BLS12_MSM.msm_bls12] calls for every bucket update, running sum and window sum
    ([BLS12_G1ArenaRust.msm_curve_add]).  Its arguments are those of the former copy-out
    wrapper, X1 X2 Y1 Y2 Z1 Z2 Xout Yout Zout:

      e = 1; e = e & (load(Z2 + 8 i) == ONE[i])   for i = 0 .. 5
      if (e) { RCB 2015 Algorithm 8 on (X1 : Y1 : Z1) and (X2, Y2), into Xout Yout Zout }
      else   { the former body: stackalloc tx ty tz; curve_add(.., tx, ty, tz); copy into Xout .. }

    ONE is the word list of 1 in the Montgomery representation of BLS12-381 ([one_mont]).  The
    input points of an MSM are affine (Z = 1: [group::g1_msm] on [G1Projective::from_affine]),
    so every bucket update takes the first branch (11 multiplications and 2 by 3b instead of
    12 and 2, 13 additions instead of 19, and no copy); the buckets and running sums have
    arbitrary Z and take the second.

    [msm_curve_add_mixed_ok]: the body satisfies [BLS12_MSM.CurveAddAliasedOK] for
    [g1_add_spec = ladderstep_triple tb], the contract the former wrapper had
    ([BLS12_MSM_Wrappers.copy_out_add_ok]); so [BLS12_MSM_Closed.msm_bls12_closed] keeps its
    statement.  If the six words of Z2 are those of 1, then Z2 = feval ONE = 1 (no canonicity of
    the representation is needed: equal words have equal values), and Algorithm 8 at Z2 = 1 is
    Algorithm 7 coordinate for coordinate ([MixedAddA0.madd_a0_triple_eq]; at the Gallina level
    [madd_a0_is_cadd]: Algorithm 8 is [RcbProjectiveLaws.cadd] with Z2 = 1).

    Everything is Qed; no Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.RcbAnyOut.
Require Import Bedrock.Group.CurveAdd.MixedAddA0.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Wrappers.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.BLS12_MSM_Functional.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * Gallina level: Algorithm 8 is the complete RCB addition with Z2 = 1

    [RcbProjectiveLaws.cadd 0 tb] is fiat-crypto's [Projective.add] on on-curve inputs
    ([RcbProjectiveLaws.cadd_is_Padd]); [BLS12_MSM_Functional.ladderstep_triple_is_cadd]
    identifies it with Algorithm 7. *)
Section MixedIsCadd.
  Context {field_parameters : FieldParameters}.
  Local Notation F := (F M_pos).

  Lemma madd_a0_is_cadd (three_b_val : F) (P : F * F * F) (X2 Y2 : F) :
    madd_a0_triple three_b_val P (X2, Y2)
    = RcbProjectiveLaws.cadd 0%F three_b_val P (X2, Y2, 1%F).
  Proof. rewrite madd_a0_triple_eq. apply ladderstep_triple_is_cadd. Qed.
End MixedIsCadd.

Section MixedAdd.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).

  (** 1 in the Montgomery representation: 2^384 mod p, little-endian 64-bit words. *)
  Definition one_mont : list Z :=
    [0x760900000002fffd; 0xebf4000bc40c0002; 0x5f48985753c758ba;
     0x77ce585370525745; 0x5c071a97a256ec6d; 0x15f65ec3fa80e493].

  Lemma feval_one_mont :
    feval (List.map (@word.of_Z 64 BasicC64Semantics.word) one_mont) = 1%F.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (** e := e & (load(Z2 + off) == c) *)
  Definition z2_step (off c : Z) : cmd :=
    cmd.set "e"
      (expr.op bopname.and (expr.var "e")
         (expr.op bopname.eq
            (expr.load access_size.word
               (expr.op bopname.add (expr.var "Z2") (expr.literal off)))
            (expr.literal c))).

  Definition z2_is_one : cmd :=
    cmd.seq (cmd.set "e" (expr.literal 1))
    (cmd.seq (z2_step 0  (nth 0 one_mont 0))
    (cmd.seq (z2_step 8  (nth 1 one_mont 0))
    (cmd.seq (z2_step 16 (nth 2 one_mont 0))
    (cmd.seq (z2_step 24 (nth 3 one_mont 0))
    (cmd.seq (z2_step 32 (nth 4 one_mont 0))
             (z2_step 40 (nth 5 one_mont 0))))))).

  Definition madd_cmd_bls : cmd :=
    @madd_a0_cmd 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem _ _
      bls12_field_parameters bls12_frep bls12_frep_ok "bls12_three_b".

  Definition msm_curve_add_mixed_body : cmd :=
    cmd.seq z2_is_one
      (cmd.cond (expr.var "e") madd_cmd_bls (copy_out_body "curve_add" add_ins outs3)).

  Definition msm_curve_add_mixed : string * Syntax.func :=
    ("msm_curve_add", ((add_ins ++ outs3)%list, @nil string, msm_curve_add_mixed_body)).

  Local Notation tb := (feval (proj1_sig three_b_felem)).

  (** ** Proof tools (as in [BLS12_MSM_Wrappers], whose tactics are local) *)

  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | (rewrite !map.get_put_diff by congruence;
             first [ apply map.get_put_same | eassumption | reflexivity ])
          | eassumption
          | reflexivity ].

  Local Ltac eval_call_args :=
    repeat match goal with
           | x := _ : @Interface.map.rep _ _ _ |- _ => subst x
           end;
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | (eexists; split; [ solve [ solve_mapget ] | ])
      | (eexists; split; [ exact eq_refl | ]) ]).

  Local Ltac wp_expose_call :=
    repeat (lazymatch goal with
            | |- WeakestPrecondition.cmd _ _ _ _ _ _ =>
                unfold1_cmd_goal;
                cbv beta match delta [WeakestPrecondition.cmd_body]
            end).

  Local Ltac stackalloc3 Hsep :=
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let atx := fresh "atx" in let mSx := fresh "mSx" in let mCx := fresh "mCx" in
    let Hanyx := fresh "Hanyx" in let Hsplitx := fresh "Hsplitx" in
    let xtx := fresh "xtx" in let Hax := fresh "Hax" in
    intros atx mSx mCx Hanyx Hsplitx;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyx Hsplitx Hsep) as (xtx & Hax);
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let aty := fresh "aty" in let mSy := fresh "mSy" in let mCy := fresh "mCy" in
    let Hanyy := fresh "Hanyy" in let Hsplity := fresh "Hsplity" in
    let xty := fresh "xty" in let Hay := fresh "Hay" in
    intros aty mSy mCy Hanyy Hsplity;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyy Hsplity Hax) as (xty & Hay);
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let atz := fresh "atz" in let mSz := fresh "mSz" in let mCz := fresh "mCz" in
    let Hanyz := fresh "Hanyz" in let Hsplitz := fresh "Hsplitz" in
    let xtz := fresh "xtz" in let Haz := fresh "Haz" in
    intros atz mSz mCz Hanyz Hsplitz;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyz Hsplitz Hay) as (xtz & Haz);
    clear Hsep Hax Hay.

  Lemma bls12_bounds_eq_ma : @loose_bounds _ _ _ _ _ bls12_frep = tight_bounds.
  Proof. reflexivity. Qed.

  (** One step of the test. *)
  Lemma wp_z2_step (fns : Semantics.env) tr (m : BasicC64Semantics.mem)
        (l : BasicC64Semantics.locals)
        (post : Semantics.trace -> BasicC64Semantics.mem -> BasicC64Semantics.locals -> Prop)
        (e0 pz w : BasicC64Semantics.word) (off c : Z) :
    map.get l "e" = Some e0 -> map.get l "Z2" = Some pz ->
    Memory.load access_size.word m (word.add pz (word.of_Z off)) = Some w ->
    post tr m (map.put l "e"
      (word.and e0 (if word.eqb w (word.of_Z c) then word.of_Z 1 else word.of_Z 0))) ->
    WeakestPrecondition.cmd fns (z2_step off c) tr m l post.
  Proof.
    intros He Hz Hl Hp. cbv [z2_step].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eexists; split; [ | exact Hp ].
    cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal WeakestPrecondition.load dlet.dlet].
    eexists; split; [ exact He | ].
    eexists; split; [ exact Hz | ].
    eexists; split; [ exact Hl | ].
    reflexivity.
  Qed.

  Lemma and_eqb_ne0 (e0 w c : BasicC64Semantics.word) :
    word.unsigned (word.and e0 (if word.eqb w c then word.of_Z 1 else word.of_Z 0)) <> 0 ->
    word.unsigned e0 <> 0 /\ w = c.
  Proof.
    rewrite word.unsigned_and_nowrap.
    destruct (word.eqb w c) eqn:E.
    - apply word.eqb_true in E. intros H. split; [ | exact E ].
      intros H0. apply H. rewrite H0. reflexivity.
    - intros H. exfalso. apply H. rewrite word.unsigned_of_Z_0. apply Z.land_0_r.
  Qed.

  Lemma put8_back (L : BasicC64Semantics.locals) (a1 a2 a3 a4 a5 a6 a7 a8 : BasicC64Semantics.word) :
    map.get L "Xout" = Some a1 -> map.get L "Yout" = Some a2 -> map.get L "Zout" = Some a3 ->
    map.get L "X1" = Some a4 -> map.get L "Y1" = Some a5 -> map.get L "Z1" = Some a6 ->
    map.get L "X2" = Some a7 -> map.get L "Y2" = Some a8 ->
    map.put (map.put (map.put (map.put (map.put (map.put (map.put (map.put L
      "Xout" a1) "Yout" a2) "Zout" a3) "X1" a4) "Y1" a5) "Z1" a6) "X2" a7) "Y2" a8 = L.
  Proof.
    intros H1 H2 H3 H4 H5 H6 H7 H8.
    rewrite (map.put_idemp L _ _ H1), (map.put_idemp L _ _ H2), (map.put_idemp L _ _ H3),
      (map.put_idemp L _ _ H4), (map.put_idemp L _ _ H5), (map.put_idemp L _ _ H6),
      (map.put_idemp L _ _ H7), (map.put_idemp L _ _ H8).
    reflexivity.
  Qed.

  (** ** The contract *)

  Theorem msm_curve_add_mixed_ok (functions : Semantics.env) :
    map.get functions "msm_curve_add" = Some (snd msm_curve_add_mixed) ->
    spec_of_ladderstep_anyout three_b_felem functions ->
    spec_of_felem_copy functions ->
    spec_of_BinOp bin_mul functions ->
    spec_of_BinOp bin_add functions ->
    spec_of_BinOp bin_sub functions ->
    spec_of_three_b_loader_madd three_b_felem "bls12_three_b" functions ->
    CurveAddAliasedOK "msm_curve_add" (ladderstep_triple tb) functions.
  Proof.
    intros Henv Hadd Hcopy Hmul Hadd2 Hsub H3b.
    cbv [spec_of_ladderstep_anyout] in Hadd.
    change CompilationAbstract.FElem with Compilation2.FElem in Hadd.
    cbv [CurveAddAliasedOK]. change CompilationAbstract.FElem with Compilation2.FElem.
    intros pb1 pp1 pb2 pp2 pb3 pp3 B1 P1 B2 P2 B3 P3 R0 tr0 m0 Hsep.
    (* The six words of Z2 and their loads. *)
    assert (Hz : (FElem (Some tight_bounds) pp3 P3
                  * (FElem (Some tight_bounds) pb1 B1 * FElem (Some tight_bounds) pp1 P1
                     * FElem (Some tight_bounds) pb2 B2 * FElem (Some tight_bounds) pp2 P2
                     * FElem (Some tight_bounds) pb3 B3 * R0))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ Hz) as ([zl Hzl] & Hzfe & _ & Hzsep).
    clear Hz. cbn [proj1_sig] in *.
    change felem_size_in_words with 6%nat in Hzl.
    destruct zl as [| z0 [| z1 [| z2 [| z3 [| z4 [| z5 []]]]]]]; try discriminate.
    cbv [Field.FElem proj1_sig] in Hzsep. cbn [array] in Hzsep.
    change (Memory.bytes_per_word 64) with 8 in Hzsep.
    repeat match type of Hzsep with
    | context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
      let c := eval cbv in (a + b)%Z in
      replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
        with (word.add base (word.of_Z c)) in Hzsep by ring
    end.
    assert (L0 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 0)) = Some z0).
    { replace (word.add pp3 (word.of_Z 0)) with pp3 by ring.
      eapply Scalars.load_word_of_sep. ecancel_assumption. }
    assert (L1 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 8)) = Some z1)
      by (eapply Scalars.load_word_of_sep; ecancel_assumption).
    assert (L2 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 16)) = Some z2)
      by (eapply Scalars.load_word_of_sep; ecancel_assumption).
    assert (L3 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 24)) = Some z3)
      by (eapply Scalars.load_word_of_sep; ecancel_assumption).
    assert (L4 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 32)) = Some z4)
      by (eapply Scalars.load_word_of_sep; ecancel_assumption).
    assert (L5 : Memory.load access_size.word m0 (word.add pp3 (word.of_Z 40)) = Some z5)
      by (eapply Scalars.load_word_of_sep; ecancel_assumption).
    clear Hzsep.
    (* Enter the function. *)
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func msm_curve_add_mixed snd
                          msm_curve_add_mixed_body z2_is_one add_ins outs3 List.app].
    eexists. split. { reflexivity. }
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    (* e = 1 *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eexists; split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal dlet.dlet]. reflexivity. }
    cbv [dlet.dlet].
    (* the six comparisons *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L0 | ]; cbv beta.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L1 | ]; cbv beta.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L2 | ]; cbv beta.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L3 | ]; cbv beta.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L4 | ]; cbv beta.
    eapply wp_z2_step; [ solve_mapget | solve_mapget | exact L5 | ]; cbv beta.
    (* if (e) *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eexists; split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get].
      eexists; split; [ solve_mapget | reflexivity ]. }
    split.
    - (* Z2's words are those of 1: Algorithm 8, in place. *)
      intros Hne.
      destruct (and_eqb_ne0 _ _ _ Hne) as [Hne4 E5]; clear Hne.
      destruct (and_eqb_ne0 _ _ _ Hne4) as [Hne3 E4]; clear Hne4.
      destruct (and_eqb_ne0 _ _ _ Hne3) as [Hne2 E3]; clear Hne3.
      destruct (and_eqb_ne0 _ _ _ Hne2) as [Hne1 E2]; clear Hne2.
      destruct (and_eqb_ne0 _ _ _ Hne1) as [Hne0 E1]; clear Hne1.
      destruct (and_eqb_ne0 _ _ _ Hne0) as [_ E0]; clear Hne0.
      subst z0 z1 z2 z3 z4 z5.
      assert (HP3 : P3 = 1%F) by (rewrite <- Hzfe; exact feval_one_mont).
      clear Hzfe. subst P3.
      lazymatch goal with
      | |- WeakestPrecondition.cmd _ _ _ _ ?L _ =>
          rewrite <- (put8_back L pb1 pb2 pb3 pb1 pb2 pb3 pp1 pp2) by solve_mapget
      end.
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ | eapply (@madd_a0_cmd_ok 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem
                      BasicC64Semantics.locals BasicC64Semantics.ext_spec _ _ _ _
                      bls12_field_parameters bls12_frep bls12_frep_ok
                      bls12_bounds_eq_ma three_b_felem
                      "bls12_three_b" functions Hmul Hadd2 Hsub H3b
                      pb1 pb2 pb3 pp1 pp2 B1 B2 B3 P1 P2
                      (FElem (Some tight_bounds) pp3 1%F * R0)%sep);
            change CompilationAbstract.FElem with Compilation2.FElem;
            ecancel_assumption ].
      intros t m l Hpred.
      cbv [madd_a0_pred wp_bind_retvars] in Hpred.
      destruct Hpred as (rets & _ & -> & <- & ? & ? & ? & _ & X3 & Y3 & Z3 & Hgal & Hm).
      change CompilationAbstract.FElem with Compilation2.FElem in Hm.
      assert (Htrip : ladderstep_triple tb (B1, B2, B3) (P1, P2, 1%F) = (X3, Y3, Z3)).
      { rewrite <- madd_a0_triple_eq. cbv [madd_a0_triple].
        exact (f_equal (fun p => let '\<x, y, z\> := p in (x, y, z)) Hgal). }
      cbv beta match fix delta [list_map list_map_body].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      rewrite Htrip. cbv beta iota.
      ecancel_assumption.
    - (* otherwise: the former copy-out body *)
      intros _.
      cbv beta match delta [copy_out_body List.app List.map nth].
      stackalloc3 Hsep.
      wp_expose_call.
      eexists. split. { solve [ eval_call_args ]. }
      assert (Hpre : (FElem None atx (feval xtx) * FElem None aty (feval xty)
                      * FElem None atz (feval xtz)
                      * (FElem (Some tight_bounds) pb1 B1 * FElem (Some tight_bounds) pp1 P1
                         * FElem (Some tight_bounds) pb2 B2 * FElem (Some tight_bounds) pp2 P2
                         * FElem (Some tight_bounds) pb3 B3 * FElem (Some tight_bounds) pp3 P3
                         * R0))%sep mCz).
      { apply FElem_none_intro3. ecancel_assumption. }
      specialize (Hadd pb1 pp1 pb2 pp2 pb3 pp3 atx aty atz
                    B1 P1 B2 P2 B3 P3 (feval xtx) (feval xty) (feval xtz) R0 tr0 mCz).
      eapply Semantics.weaken_call.
      1: { apply Hadd; ecancel_assumption. }
      intros tr4 m4 rets4 Hp4. cbv beta in Hp4.
      destruct Hp4 as (Hr4 & Ht4 & outx & outy & outz & Hgal & Hm4).
      subst rets4. subst tr4. clear Haz Hpre.
      eexists. split. { exact eq_refl. }
      wp_expose_call.
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr5 m5 rets5 Hp5. cbv beta in Hp5.
      destruct Hp5 as (Hr5 & Ht5 & Hm5). subst rets5. subst tr5. clear Hm4.
      eexists. split. { exact eq_refl. }
      wp_expose_call.
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr6 m6 rets6 Hp6. cbv beta in Hp6.
      destruct Hp6 as (Hr6 & Ht6 & Hm6). subst rets6. subst tr6. clear Hm5.
      eexists. split. { exact eq_refl. }
      wp_expose_call.
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr7 m7 rets7 Hp7. cbv beta in Hp7.
      destruct Hp7 as (Hr7 & Ht7 & Hm7). subst rets7. subst tr7. clear Hm6.
      eexists. split. { exact eq_refl. }
      cbv beta.
      assert (Hdz : (FElem (Some tight_bounds) atz outz
                     * (FElem (Some tight_bounds) aty outy
                        * (FElem (Some tight_bounds) atx outx
                           * (FElem (Some tight_bounds) pb1 outx
                              * FElem (Some tight_bounds) pp1 P1
                              * FElem (Some tight_bounds) pb2 outy
                              * FElem (Some tight_bounds) pp2 P2
                              * FElem (Some tight_bounds) pb3 outz
                              * FElem (Some tight_bounds) pp3 P3
                              * R0))))%sep m7)
        by ecancel_assumption.
      clear Hm7.
      destruct (FElem2_dealloc _ _ _ _ _ Hdz) as (mz & mSz2 & Habz & Hspz & Hpz).
      exists mz, mSz2. split; [ exact Habz | ]. split; [ exact Hspz | ]. cbv beta.
      destruct (FElem2_dealloc _ _ _ _ _ Hpz) as (my & mSy2 & Haby & Hspy & Hpy).
      exists my, mSy2. split; [ exact Haby | ]. split; [ exact Hspy | ]. cbv beta.
      destruct (FElem2_dealloc _ _ _ _ _ Hpy) as (mx & mSx2 & Habx & Hspx & Hpx).
      exists mx, mSx2. split; [ exact Habx | ]. split; [ exact Hspx | ].
      cbv beta match fix delta [list_map list_map_body].
      split; [ reflexivity | ]. split; [ reflexivity | ].
      rewrite (ladderstep_triple_of_gallina _ _ _ _ _ _ _ _ _ _ Hgal). cbv beta iota.
      exact Hpx.
  Qed.
End MixedAdd.
