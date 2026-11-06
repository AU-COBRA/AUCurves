(** * BLS12-381: the Fp2 leaf specs of the functional pairing theorem.

    [bls12_Fp2_{add,sub,mul,felem_copy}] are the tower library's
    [QuadraticFieldExtensions.Fp2_*] at the instances of [BLS12_MillerStepFunctional]
    (beta = -1, prefix "bls12_Fp2_"); their correctness lemmas take the base-field specs,
    discharged in [BLS12_PairingLeavesFp].  [bls12_Fp2_square], [bls12_Fp2_opp] and
    [bls12_Fp2_inv] are new bodies with WP proofs here; [bls12_Fp2_inv] assumes the
    AbstractField spec of the base-field inverse [bls12_inv].
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
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsMul.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2InvBridge.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.

Local Open Scope string_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation env := (Interface.map.rep (map:=Semantics.env)).
Local Notation Fp := (F (@PrimeField.M_pos MS.bls12_pf_params)).

Definition bls12_beta : Fp := F.of_Z _ (-1).
Definition fp2_prefix : string := "bls12_Fp2_".

Local Notation pp := MS.bls12_pf_params.
Local Notation frep := MS.bls12_Fp_rep.

Definition bls12_Fp2_felem_copy :=
  Fp2_felem_copy (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix.
Definition bls12_Fp2_add :=
  Fp2_add (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix.
Definition bls12_Fp2_sub :=
  Fp2_sub (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix.
Definition bls12_Fp2_mul :=
  Fp2_mul (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix.

(** [bls12_Fp2_square]: [x^2 = x * x], by one call of [bls12_Fp2_mul] (which allows its output
    to alias its inputs). *)
Definition bls12_Fp2_square : string * Syntax.func :=
  ("bls12_Fp2_square", (["out"; "x"], (nil : list string), bedrock_func_body:(
    coq:(cmd.call [] "bls12_Fp2_mul" [expr.var "out"; expr.var "x"; expr.var "x"])
  ))).

(** [bls12_Fp2_opp]: the input is first copied to the stack (so that the output may alias it),
    then each component is negated by [bls12_opp]. *)
Definition bls12_Fp2_opp : string * Syntax.func :=
  ("bls12_Fp2_opp", (["out"; "x"], (nil : list string), bedrock_func_body:(
    stackalloc 96 as t;
    coq:(cmd.call [] "bls12_Fp2_felem_copy" [expr.var "t"; expr.var "x"]);
    coq:(cmd.call [] "bls12_opp" [expr.var "out"; expr.var "t"]);
    coq:(cmd.call [] "bls12_opp"
           [expr.op bopname.add (expr.var "out") (expr.literal 48);
            expr.op bopname.add (expr.var "t") (expr.literal 48)])
  ))).

(** [bls12_Fp2_inv]: [(a0 + a1 u)^-1 = (a0 * n^-1, (-a1) * n^-1)] with [n = a0^2 + a1^2]
    (beta = -1).  The input is copied to the stack first; [s] holds [a0^2], [a1^2], then
    [n] and [n^-1], then [-a1]. *)
Definition bls12_Fp2_inv : string * Syntax.func :=
  ("bls12_Fp2_inv", (["out"; "x"], (nil : list string), bedrock_func_body:(
    stackalloc 96 as t;
    stackalloc 96 as s;
    coq:(cmd.call [] "bls12_Fp2_felem_copy" [expr.var "t"; expr.var "x"]);
    coq:(cmd.call [] "bls12_square" [expr.var "s"; expr.var "t"]);
    coq:(cmd.call [] "bls12_square"
           [expr.op bopname.add (expr.var "s") (expr.literal 48);
            expr.op bopname.add (expr.var "t") (expr.literal 48)]);
    coq:(cmd.call [] "bls12_add"
           [expr.var "s"; expr.var "s"; expr.op bopname.add (expr.var "s") (expr.literal 48)]);
    coq:(cmd.call [] "bls12_inv"
           [expr.op bopname.add (expr.var "s") (expr.literal 48); expr.var "s"]);
    coq:(cmd.call [] "bls12_mul"
           [expr.var "out"; expr.var "t"; expr.op bopname.add (expr.var "s") (expr.literal 48)]);
    coq:(cmd.call [] "bls12_opp" [expr.var "s"; expr.op bopname.add (expr.var "t") (expr.literal 48)]);
    coq:(cmd.call [] "bls12_mul"
           [expr.op bopname.add (expr.var "out") (expr.literal 48); expr.var "s";
            expr.op bopname.add (expr.var "s") (expr.literal 48)])
  ))).

Local Notation FElem1 := (@AbstractField.FElem _ _ _ _ _ _ frep).
Local Notation FElem2 := (@AbstractField.FElem _ MS.bls12_Fp2_params' _ _ _ _ MS.bls12_Fp2_rep').
Local Notation fst_felem := (fst_felem (prime_parameters:=pp) (field_representation:=frep)).
Local Notation snd_felem := (snd_felem (prime_parameters:=pp) (field_representation:=frep)).

Lemma Fp2_split48 p v m :
  FElem2 p v m ->
  (FElem1 p (fst_felem v) * FElem1 (word.add p (word.of_Z 48)) (snd_felem v))%sep m.
Proof.
  intros H.
  exact (Fp2_raw_FElem_split (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix
           p v m H).
Qed.

Lemma sep_eq_l {key value} {mp : map.map key value} (P Q : @map.rep _ _ mp -> Prop) (m1 m : @map.rep _ _ mp) :
  P m1 -> (eq m1 * Q)%sep m -> (P * Q)%sep m.
Proof. intros HP (ma & mb & Hs & E & HQ). subst ma. exists m1, mb. auto. Qed.

Lemma sep_impl_l {key value} {mp : map.map key value} (P P' Q : @map.rep _ _ mp -> Prop) m :
  (forall m', P m' -> P' m') -> (P * Q)%sep m -> (P' * Q)%sep m.
Proof. intros HPP (ma & mb & Hs & HP & HQ). exists ma, mb. auto. Qed.

Lemma FElem1_length p v m R : (FElem1 p v * R)%sep m -> length v = 6%nat.
Proof.
  intros H. cbv [AbstractField.FElem Bignum.Bignum] in H.
  eapply sep_assoc in H. eapply sep_emp_l in H. exact (proj1 H).
Qed.

Lemma Fp2_join48 p v1 v2 m :
  (FElem1 p v1 * FElem1 (word.add p (word.of_Z 48)) v2)%sep m ->
  FElem2 p (v1 ++ v2) m.
Proof.
  intros H.
  pose proof (FElem1_length _ _ _ _ H) as L1.
  pose proof (FElem1_length _ _ _ _ (proj1 (sep_comm _ _ _) H)) as L2.
  exact (Fp2_raw_FElem_join (prime_parameters:=pp) (F_representation:=frep) bls12_beta fp2_prefix
           p v1 v2 m L1 L2 H).
Qed.

Local Ltac unop_call H pout px out x bx :=
  eapply WeakestPreconditionProperties.Proper_call;
  [ | refine (H pout px out x _ _ _ (conj bx (conj _ _)));
      [ eexists; ecancel_assumption | ecancel_assumption ] ].
Local Ltac binop_call H pout px py out x y bx byy :=
  eapply WeakestPreconditionProperties.Proper_call;
  [ | refine (H pout px py out x y _ _ _ (conj bx (conj byy (conj _ (conj _ _)))));
      [ eexists; ecancel_assumption | eexists; ecancel_assumption | ecancel_assumption ] ].
Local Ltac post_call Hold o Hv Hbo Hm :=
  let tr' := fresh "tr" in let m' := fresh "m" in let rets := fresh "rets" in
  let Hrets := fresh "Hrets" in let Htr := fresh "Htr" in
  intros tr' m' rets (Hrets & Htr & o & Hv & Hbo & Hm); subst rets tr';
  eexists; split; [reflexivity|]; clear Hold.

Section Leaves.
  Add Ring bls12_Fp_ring : (@F.ring_theory (@PrimeField.M_pos pp)).
  Variable functions : env.
  Hypothesis E_copy : map.get functions "bls12_felem_copy" = Some bls12_felem_copy.
  Hypothesis E_add : map.get functions "bls12_add" = Some (snd bls12_add).
  Hypothesis E_sub : map.get functions "bls12_sub" = Some (snd bls12_sub).
  Hypothesis E_mul : map.get functions "bls12_mul" = Some (snd bls12_mul).
  Hypothesis E_Fp2_copy :
    map.get functions "bls12_Fp2_felem_copy" = Some (snd bls12_Fp2_felem_copy).

  Lemma bls12_Fp2_felem_copy_spec : MS.spec_of_Fp2_felem_copy functions.
  Proof.
    pose proof (bls12_Fp_felem_copy_leaf functions E_copy) as Hc.
    exact (Fp2_felem_copy_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta fp2_prefix functions E_Fp2_copy Hc Hc).
  Qed.

  Lemma bls12_Fp2_add_spec :
    map.get functions "bls12_Fp2_add" = Some (snd bls12_Fp2_add) ->
    MS.spec_of_Fp2_add functions.
  Proof.
    intros E.
    pose proof bls12_Fp2_felem_copy_spec as Hc2.
    pose proof (bls12_Fp_add_leaf_MS functions E_add) as Ha.
    exact (Fp2_add_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta fp2_prefix functions E Hc2 Hc2 Ha Ha).
  Qed.

  Lemma bls12_Fp2_sub_spec :
    map.get functions "bls12_Fp2_sub" = Some (snd bls12_Fp2_sub) ->
    MS.spec_of_Fp2_sub functions.
  Proof.
    intros E.
    pose proof bls12_Fp2_felem_copy_spec as Hc2.
    pose proof (bls12_Fp_sub_leaf functions E_sub) as Hs.
    exact (Fp2_sub_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta fp2_prefix functions E Hc2 Hc2 Hs Hs).
  Qed.

  Lemma bls12_mul_neg_1 : forall x y : Fp, F.sub x y = F.add x (F.mul bls12_beta y).
  Proof.
    intros x y. cbv [bls12_beta].
    change (F.of_Z (@PrimeField.M_pos pp) (-1)) with (F.opp (@F.one (@PrimeField.M_pos pp))).
    ring.
  Qed.

  Lemma bls12_Fp_bounds_equiv :
    forall x, @AbstractField.bounded_by _ _ _ _ _ _ frep (@AbstractField.loose_bounds _ _ _ _ _ _ frep) x ->
      @AbstractField.bounded_by _ _ _ _ _ _ frep (@AbstractField.tight_bounds _ _ _ _ _ _ frep) x.
  Proof. intros x H; exact H. Qed.

  Lemma bls12_Fp2_mul_spec :
    map.get functions "bls12_Fp2_mul" = Some (snd bls12_Fp2_mul) ->
    MS.spec_of_Fp2_mul functions.
  Proof.
    intros E.
    pose proof (bls12_Fp_mul_leaf functions E_mul) as Hm.
    pose proof (bls12_Fp_add_leaf_MS functions E_add) as Ha.
    pose proof (bls12_Fp_sub_leaf functions E_sub) as Hs.
    exact (Fp2_mul_ok (prime_parameters:=pp) (prime_parameters_ok:=MS.bls12_pf_params_ok) (F_representation:=frep)
             (bounds_equiv:=bls12_Fp_bounds_equiv)
             bls12_beta fp2_prefix bls12_mul_neg_1 functions E Hm Hm Ha Ha Hm Hs Hs Hs).
  Qed.

  Lemma bls12_Fp2_square_spec :
    map.get functions "bls12_Fp2_square" = Some (snd bls12_Fp2_square) ->
    MS.spec_of_Fp2_mul functions ->
    MS.spec_of_Fp2_sqr functions.
  Proof.
    intros E Hmul.
    cbv [MS.spec_of_Fp2_sqr AbstractField.unop_spec].
    intros pout px out x Rr tr m (Hb & HX & HO).
    pose proof (Hmul pout px px out x x Rr tr m (conj Hb (conj Hb (conj HX (conj HX HO)))))
      as Hcall.
    clear Hmul Hb HX HO.
    eapply start_func; [exact E | clear E].
    cbv match beta delta [WeakestPrecondition.func bls12_Fp2_square snd].
    eexists; split; [exact eq_refl|].
    repeat straightline.
    eapply WeakestPreconditionProperties.Proper_call; [ | exact Hcall ].
    intros tr' m' rets (Hrets & Htr & out' & Hv & Hb' & Hs). subst rets.
    eexists; split; [reflexivity|].
    cbn [list_map]. split; [reflexivity|]. split; [exact Htr|].
    exists out'. split; [exact Hv|]. split; [exact Hb'|exact Hs].
  Qed.

  Lemma bls12_Fp2_opp_spec :
    map.get functions "bls12_Fp2_opp" = Some (snd bls12_Fp2_opp) ->
    map.get functions "bls12_opp" = Some (snd bls12_opp) ->
    MS.spec_of_Fp2_opp functions.
  Proof.
    intros E Eopp.
    pose proof bls12_Fp2_felem_copy_spec as Hcp.
    pose proof (bls12_Fp_opp_leaf functions Eopp) as Hop.
    clear E_copy E_add E_sub E_mul E_Fp2_copy.
    cbv [MS.spec_of_Fp2_opp AbstractField.unop_spec].
    intros pout px out x Rr tr m (Hb & [Ra HX] & HO).
    eapply start_func; [exact E | clear E].
    cbv match beta delta [WeakestPrecondition.func bls12_Fp2_opp snd].
    eexists; split; [exact eq_refl|].
    repeat straightline.
    clear HX HO H1 H2 length_stack length_stack0 stack stack0.
    rename HX0 into HX, HO0 into HO.
    destruct (proj1 (AbstractField.FElem_from_bytes (field_representation:=MS.bls12_Fp2_rep') a mStack) H)
      as [old Hold].
    assert (Hm0 : (eq m1 * FElem2 a old)%sep m0) by (exists m1, mStack; auto).
    clear H H0.
    pose proof (sep_eq_l _ _ _ _ HX Hm0) as HXm.
    pose proof (sep_eq_l _ _ _ _ HO Hm0) as HOm.
    subst args.
    eapply WeakestPreconditionProperties.Proper_call;
      [ | refine (Hcp a px old x Ra (eq m1) tr m0 (conj _ _)); ecancel_assumption ].
    intros tr2 m2 rets (Hrets & Htr2 & Hm2). subst rets tr2.
    eexists; split; [reflexivity|].
    pose proof (sep_eq_l _ _ _ _ HO (proj1 (sep_comm _ _ _) Hm2)) as H2.
    clear HXm HOm Hm0 Hold HX HO Hm2.
    assert (H3 : (FElem2 pout out * (FElem2 a x * Rr))%sep m2) by ecancel_assumption.
    clear H2.
    apply (sep_impl_l _ _ _ _ (Fp2_split48 pout out)) in H3.
    assert (H4 : (FElem2 a x * (FElem1 pout (fst_felem out)
                   * FElem1 (word.add pout (word.of_Z 48)) (snd_felem out) * Rr))%sep m2)
      by ecancel_assumption.
    clear H3.
    apply (sep_impl_l _ _ _ _ (Fp2_split48 a x)) in H4.
    destruct Hb as [Hb1 Hb2].
    repeat straightline.
    subst args.
    eapply WeakestPreconditionProperties.Proper_call;
      [ | refine (Hop pout a (fst_felem out) (fst_felem x) _ tr m2 (conj Hb1 (conj _ _)));
          [ eexists; ecancel_assumption | ecancel_assumption ] ].
    intros tr3 m3 rets (Hrets & Htr3 & o1 & Hv1 & Hbo1 & Hm3). subst rets tr3.
    eexists; split; [reflexivity|].
    clear H4.
    repeat straightline.
    subst args.
    eapply WeakestPreconditionProperties.Proper_call;
      [ | refine (Hop (word.add pout (word.of_Z 48)) (word.add a (word.of_Z 48))
                    (snd_felem out) (snd_felem x) _ tr m3 (conj Hb2 (conj _ _)));
          [ eexists; ecancel_assumption | ecancel_assumption ] ].
    intros tr4 m4 rets (Hrets & Htr4 & o2 & Hv2 & Hbo2 & Hm4). subst rets tr4.
    eexists; split; [reflexivity|].
    clear Hm3.
    assert (L1 : length o1 = 6%nat).
    { eapply (FElem1_length pout o1 m4
               (FElem1 (word.add pout (word.of_Z 48)) o2 * FElem1 a (fst_felem x)
                * FElem1 (word.add a (word.of_Z 48)) (snd_felem x) * Rr)%sep).
      ecancel_assumption. }
    pose proof (FElem1_length _ _ _ _ Hm4) as L2.
    assert (H5 : ((FElem1 a (fst_felem x) * FElem1 (word.add a (word.of_Z 48)) (snd_felem x))
                  * ((FElem1 pout o1 * FElem1 (word.add pout (word.of_Z 48)) o2) * Rr))%sep m4)
      by ecancel_assumption.
    clear Hm4.
    apply (sep_impl_l _ _ _ _ (Fp2_join48 a _ _)) in H5.
    apply sep_comm in H5.
    apply (sep_impl_l _ _ _ _ (fun m' H => sep_impl_l _ _ _ m' (Fp2_join48 pout o1 o2) H)) in H5.
    apply sep_comm in H5.
    rewrite (Fp2_list_decomp (prime_parameters:=pp) (F_representation:=frep)) in H5.
    apply (sep_impl_l _ _ _ _ (AbstractField.FElem_to_bytes a x)) in H5.
    destruct H5 as (mS & mR & Hs & HS & HR).
    exists mR, mS. split; [exact HS|]. split; [apply map.split_comm; exact Hs|].
    cbn [list_map]. split; [reflexivity|]. split; [reflexivity|].
    assert (Ef : fst_felem (o1 ++ o2)%list = o1) by (apply firstn_app'; exact L1).
    assert (Es : snd_felem (o1 ++ o2)%list = o2) by (apply skipn_app; exact L1).
    exists (o1 ++ o2)%list. split; [|split; [|exact HR]].
    - assert (Hfe : @AbstractField.feval _ _ _ _ _ _ MS.bls12_Fp2_rep' (o1 ++ o2)%list
                    = (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem (o1 ++ o2)%list),
                       @AbstractField.feval _ _ _ _ _ _ frep (snd_felem (o1 ++ o2)%list)))
        by reflexivity.
      rewrite Ef, Es in Hfe. rewrite Hfe, Hv1, Hv2. reflexivity.
    - refine (conj _ _).
      + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                  (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (fst_felem (o1 ++ o2)%list)).
        rewrite Ef. exact Hbo1.
      + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                  (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (snd_felem (o1 ++ o2)%list)).
        rewrite Es. exact Hbo2.
Qed.

  Lemma bls12_Fp2_inv_spec :
    map.get functions "bls12_Fp2_inv" = Some (snd bls12_Fp2_inv) ->
    map.get functions "bls12_opp" = Some (snd bls12_opp) ->
    map.get functions "bls12_square" = Some (snd bls12_square) ->
    AbstractField.unop_spec (F:=Fp) (field_representation:=frep) AbstractField.un_inv functions ->
    MS.spec_of_Fp2_inv functions.
  Proof.
    intros E Eopp Esq Hinv.
    pose proof bls12_Fp2_felem_copy_spec as Hcp.
    pose proof (bls12_Fp_opp_leaf functions Eopp) as Hop.
    pose proof (bls12_Fp_square_leaf functions Esq) as Hsq.
    pose proof (bls12_Fp_mul_leaf functions E_mul) as Hmul.
    pose proof (bls12_Fp_add_leaf_MS functions E_add) as Hadd.
    clear E_copy E_add E_sub E_mul E_Fp2_copy Eopp Esq.
    cbv [MS.spec_of_Fp2_inv AbstractField.unop_spec].
    intros pout px out x Rr tr m (Hb & [Ra HX] & HO).
    eapply start_func; [exact E | clear E].
    cbv match beta delta [WeakestPrecondition.func bls12_Fp2_inv snd].
    eexists; split; [exact eq_refl|].
    repeat straightline.
    clear HX HO HX1 HO1 H3 H4 H5 H6 length_stack length_stack0 length_stack1 length_stack2
          stack stack0 stack1 stack2.
    rename HX0 into HX, HO0 into HO.
    destruct (proj1 (AbstractField.FElem_from_bytes (field_representation:=MS.bls12_Fp2_rep') a mStack) H)
      as [oldt Holdt].
    destruct (proj1 (AbstractField.FElem_from_bytes (field_representation:=MS.bls12_Fp2_rep') a0 mStack0) H1)
      as [olds Holds].
    assert (Hm1 : (eq m2 * FElem2 a oldt)%sep m1) by (exists m2, mStack; auto).
    assert (Hm0 : (eq m1 * FElem2 a0 olds)%sep m0) by (exists m1, mStack0; auto).
    clear H H0 H1 H2 Holdt Holds.
    pose proof (sep_eq_l _ _ _ _ (sep_eq_l _ _ _ _ HX Hm1) Hm0) as HXm.
    pose proof (sep_eq_l _ _ _ _ (proj1 (sep_comm _ _ _) Hm1) Hm0) as HAm.
    clear Hm0 Hm1 HX.
    subst args.
    eapply WeakestPreconditionProperties.Proper_call;
      [ | refine (Hcp a px oldt x _ _ tr m0 (conj _ _)); ecancel_assumption ].
    intros tr3 m3 rets (Hrets & Htr3 & Hm3). subst rets tr3.
    eexists; split; [reflexivity|].
    clear HXm HAm.
    assert (Hm3' : (eq m2 * (FElem2 a x * FElem2 a0 olds))%sep m3) by ecancel_assumption.
    clear Hm3.
    pose proof (sep_eq_l _ _ _ _ HO Hm3') as H3. clear Hm3' HO.
    assert (H4 : (FElem2 a x * (FElem2 a0 olds * (FElem2 pout out * Rr)))%sep m3)
      by ecancel_assumption.
    clear H3.
    apply (sep_impl_l _ _ _ _ (Fp2_split48 a x)) in H4.
    assert (H5 : (FElem2 a0 olds * (FElem1 a (fst_felem x)
                   * FElem1 (word.add a (word.of_Z 48)) (snd_felem x) * (FElem2 pout out * Rr)))%sep m3)
      by ecancel_assumption.
    clear H4.
    apply (sep_impl_l _ _ _ _ (Fp2_split48 a0 olds)) in H5.
    assert (H6 : (FElem2 pout out * (FElem1 a0 (fst_felem olds)
                   * FElem1 (word.add a0 (word.of_Z 48)) (snd_felem olds)
                   * FElem1 a (fst_felem x)
                   * FElem1 (word.add a (word.of_Z 48)) (snd_felem x) * Rr))%sep m3)
      by ecancel_assumption.
    clear H5.
    apply (sep_impl_l _ _ _ _ (Fp2_split48 pout out)) in H6.
    destruct Hb as [Hb1 Hb2].
    (* s <- t.re^2 *)
    repeat straightline. subst args.
    unop_call Hsq a0 a (fst_felem olds) (fst_felem x) Hb1.
    post_call H6 q0 Hq0 Hbq0 H7.
    (* s+48 <- t.im^2 *)
    repeat straightline. subst args.
    unop_call Hsq (word.add a0 (word.of_Z 48)) (word.add a (word.of_Z 48)) (snd_felem olds) (snd_felem x) Hb2.
    post_call H7 q1 Hq1 Hbq1 H8.
    (* s <- s + (s+48) *)
    repeat straightline. subst args.
    binop_call Hadd a0 a0 (word.add a0 (word.of_Z 48)) q0 q0 q1 Hbq0 Hbq1.
    post_call H8 nn Hnn Hbnn H9.
    (* s+48 <- inv s *)
    repeat straightline. subst args.
    unop_call Hinv (word.add a0 (word.of_Z 48)) a0 q1 nn Hbnn.
    post_call H9 ni Hni Hbni H10.
    (* out <- t.re * (s+48) *)
    repeat straightline. subst args.
    binop_call Hmul pout a (word.add a0 (word.of_Z 48)) (fst_felem out) (fst_felem x) ni Hb1 Hbni.
    post_call H10 r0 Hr0 Hbr0 H11.
    (* s <- - t.im *)
    repeat straightline. subst args.
    unop_call Hop a0 (word.add a (word.of_Z 48)) nn (snd_felem x) Hb2.
    post_call H11 na1 Hna1 Hbna1 H12.
    (* out+48 <- s * (s+48) *)
    repeat straightline. subst args.
    binop_call Hmul (word.add pout (word.of_Z 48)) a0 (word.add a0 (word.of_Z 48)) (snd_felem out) na1 ni Hbna1 Hbni.
    post_call H12 r1 Hr1 Hbr1 H13.
    assert (L1 : length r0 = 6%nat).
    { eapply (FElem1_length pout r0 m
               (FElem1 (word.add pout (word.of_Z 48)) r1 * FElem1 a0 na1
                * FElem1 (word.add a0 (word.of_Z 48)) ni * FElem1 a (fst_felem x)
                * FElem1 (word.add a (word.of_Z 48)) (snd_felem x) * Rr)%sep).
      ecancel_assumption. }
    assert (H14 : ((FElem1 a0 na1 * FElem1 (word.add a0 (word.of_Z 48)) ni)
                   * ((FElem1 a (fst_felem x) * FElem1 (word.add a (word.of_Z 48)) (snd_felem x))
                      * ((FElem1 pout r0 * FElem1 (word.add pout (word.of_Z 48)) r1) * Rr)))%sep m)
      by ecancel_assumption.
    clear H13.
    apply (sep_impl_l _ _ _ _ (Fp2_join48 a0 _ _)) in H14.
    apply (sep_impl_l _ _ _ _ (AbstractField.FElem_to_bytes a0 _)) in H14.
    destruct H14 as (mS & mR & Hs & HS & HR).
    exists mR, mS. split; [exact HS|]. split; [apply map.split_comm; exact Hs|].
    apply (sep_impl_l _ _ _ _ (Fp2_join48 a _ _)) in HR.
    rewrite (Fp2_list_decomp (prime_parameters:=pp) (F_representation:=frep)) in HR.
    apply (sep_impl_l _ _ _ _ (AbstractField.FElem_to_bytes a x)) in HR.
    destruct HR as (mS' & mR' & Hs' & HS' & HR').
    exists mR', mS'. split; [exact HS'|]. split; [apply map.split_comm; exact Hs'|].
    apply (sep_impl_l _ _ _ _ (Fp2_join48 pout _ _)) in HR'.
    cbn [list_map]. split; [reflexivity|]. split; [reflexivity|].
    assert (Ef : fst_felem (r0 ++ r1)%list = r0) by (apply firstn_app'; exact L1).
    assert (Es : snd_felem (r0 ++ r1)%list = r1) by (apply skipn_app; exact L1).
    exists (r0 ++ r1)%list. split; [|split; [|exact HR']].
    - assert (Hfe : @AbstractField.feval _ _ _ _ _ _ MS.bls12_Fp2_rep' (r0 ++ r1)%list
                    = (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem (r0 ++ r1)%list),
                       @AbstractField.feval _ _ _ _ _ _ frep (snd_felem (r0 ++ r1)%list)))
        by reflexivity.
      rewrite Ef, Es in Hfe. rewrite Hfe.
      transitivity (Pairing.fp2_inv BLS12_Fp2InvBridge.bls12_381_M_pos
                      (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem x),
                       @AbstractField.feval _ _ _ _ _ _ frep (snd_felem x))).
      + rewrite Hr0, Hr1, Hni, Hna1, Hnn, Hq0, Hq1. reflexivity.
      + symmetry. exact (BLS12_Fp2InvBridge.bls12_381_invp2_eq_fp2_inv _).
    - refine (conj _ _).
      + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                  (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (fst_felem (r0 ++ r1)%list)).
        rewrite Ef. exact Hbr0.
      + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                  (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (snd_felem (r0 ++ r1)%list)).
        rewrite Es. exact Hbr1.
Qed.
End Leaves.
