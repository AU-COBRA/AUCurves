(** * BLS12_G2_ScalarMul — G2 scalar multiplication as a proved bedrock2 program.

    [g2_scalar_mul] multiplies a point of E'(Fp2) by a 256-bit scalar (four
    little-endian 64-bit limbs), most significant bit first:

      outx := px - px; outz := px - px; outy := 3b'      (the identity (0 : 3b' : 0))
      for i = 255 down to 0:
        out := double(out)                       ("g2_curve_double_ip", in place)
        if bit i of the scalar is set: out := out + P   ("g2_curve_add_ip", in place)

    The loop is [BLS12_G1_ScalarMul.g1_scalar_mul]'s, over Fp2; the callees
    are the in-place Rupicola derivations of [CurveAddAF.v] (no copy-out
    wrappers and no constant-store leaves: the identity is built from
    ["bls12_Fp2_sub"] and the proved 3b' loader).

    - [g2_scalar_mul_ok]: the program returns [dadd_from cadd cdbl s P 256 init]
      on raw Fp2 triples, from the callee contracts;
    - [g2_smul_correct]: on an on-curve P that is [pt_eq] to [k P] (repeated
      [RcbLawsAF.cadd] from (0 : 1 : 0)), [k] the 256 bits read;
    - [g2_scalar_mul_closed]: the closed BLS12-381 statement, with only the
      Fp2 leaf contracts as premises.

    Variable time (branches on the scalar bits).  No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require bedrock2.Loops.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Crypto.Algebra.Ring.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Bedrock.Group.CurveAdd.CurveAddAF.
Require Import Bedrock.Group.CurveAdd.RcbLawsAF.
Require Import Bedrock.BLS12_G2_ThreeB.
Require Import Bedrock.BLS12_G2_Closed.
Require Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Bedrock.BLS12_MSM_Closed.
Import Syntax BinInt String List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Notation Fp := (F PrimeField.M_pos).
Local Notation Fp2 := (Fp * Fp)%type.
Local Notation AFElem := Compilation2_Fp2.AFElem.

(* ================================================================== *)
(** ** 1. Algebra: double-and-add over the Fp2 RCB formulas              *)
(* ================================================================== *)

Section Algebra.
  Existing Instances Bitwidth64.BW64 bls12_prime_parameters bls12_Fp2_field_parameters.
  Existing Instance prime_field_parameters.

  Local Notation cadd := (@RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation cdbl := (@RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation pt_eq := (@RcbLawsAF.pt_eq Fp2 bls12_Fp2_field_parameters g2_dec).
  Local Notation id_pt := (@RcbLawsAF.id_pt Fp2 bls12_Fp2_field_parameters).

  #[local] Existing Instances g2_fld g2_dec g2_char_ge_3 g2_char_ge_12 g2_char_ge_21.

  Local Notation Lcadd_Proper :=
    (RcbLawsAF.cadd_Proper g2_b g2_tb g2_Hthree_b g2_Hdisc g2_Hexcept).
  Local Notation Lcadd_assoc :=
    (RcbLawsAF.cadd_assoc g2_b g2_tb g2_Hthree_b g2_Hdisc g2_Hexcept).
  Local Notation Lcadd_comm :=
    (RcbLawsAF.cadd_comm g2_b g2_tb g2_Hthree_b g2_Hdisc g2_Hexcept).
  Local Notation Lcadd_id_l :=
    (RcbLawsAF.cadd_id_l g2_b g2_tb g2_Hthree_b g2_Hdisc g2_Hexcept).

  Lemma g2_pt_eq_Equivalence : Equivalence pt_eq.
  Proof. exact (RcbLawsAF.pt_eq_Equivalence g2_b g2_tb g2_Hthree_b). Qed.

  Lemma g2_oncurve_cadd p q : g2_oncurve p -> g2_oncurve q -> g2_oncurve (cadd p q).
  Proof. intros Hp Hq. rewrite (g2_cadd_padd p q Hp Hq). exact (proj2_sig _). Qed.

  Lemma g2_oncurve_id : g2_oncurve id_pt.
  Proof. exact (RcbLawsAF.oncurve_id g2_b g2_tb g2_Hthree_b). Qed.

  Lemma g2_cdbl_cadd p : g2_oncurve p -> cdbl p = cadd p p.
  Proof. exact (RcbLawsAF.cdbl_is_cadd g2_b g2_tb g2_Hthree_b p). Qed.

  Definition Gs : Type := { p : Fp2 * Fp2 * Fp2 | g2_oncurve p }.
  Definition ids : Gs := exist _ id_pt g2_oncurve_id.
  Definition adds (x y : Gs) : Gs :=
    exist _ (cadd (proj1_sig x) (proj1_sig y))
      (g2_oncurve_cadd _ _ (proj2_sig x) (proj2_sig y)).
  Definition dbls (x : Gs) : Gs :=
    exist _ (cdbl (proj1_sig x))
      (eq_ind_r g2_oncurve (g2_oncurve_cadd _ _ (proj2_sig x) (proj2_sig x))
         (g2_cdbl_cadd _ (proj2_sig x))).
  Definition eqs (x y : Gs) : Prop := pt_eq (proj1_sig x) (proj1_sig y).

  #[local] Instance eqs_Equivalence : Equivalence eqs.
  Proof.
    pose proof g2_pt_eq_Equivalence as E.
    split; unfold eqs.
    - intros x. reflexivity.
    - intros x y H. symmetry. exact H.
    - intros x y z H1 H2. etransitivity; eassumption.
  Qed.

  #[local] Instance adds_Proper : Proper (eqs ==> eqs ==> eqs) adds.
  Proof.
    intros [x Hx] [x' Hx'] Ex [y Hy] [y' Hy'] Ey. unfold eqs, adds in *; cbn [proj1_sig] in *.
    exact (Lcadd_Proper x x' y y' Hx Hx' Hy Hy' Ex Ey).
  Qed.

  Lemma adds_assoc a b c : eqs (adds (adds a b) c) (adds a (adds b c)).
  Proof.
    destruct a as [x Hx], b as [y Hy], c as [z Hz]. unfold eqs, adds; cbn [proj1_sig].
    pose proof g2_pt_eq_Equivalence as E. symmetry.
    exact (Lcadd_assoc x y z Hx Hy Hz).
  Qed.

  Lemma adds_comm a b : eqs (adds a b) (adds b a).
  Proof.
    destruct a as [x Hx], b as [y Hy]. unfold eqs, adds; cbn [proj1_sig].
    exact (Lcadd_comm x y Hx Hy).
  Qed.

  Lemma adds_id_l a : eqs (adds ids a) a.
  Proof.
    destruct a as [x Hx]. unfold eqs, adds, ids; cbn [proj1_sig].
    exact (Lcadd_id_l x Hx).
  Qed.

  Lemma dbls_add a : eqs (dbls a) (adds a a).
  Proof.
    destruct a as [x Hx]. unfold eqs, adds, dbls; cbn [proj1_sig].
    rewrite (g2_cdbl_cadd x Hx). pose proof g2_pt_eq_Equivalence as E. reflexivity.
  Qed.

  (** Double-and-add from any on-curve accumulator [pt_eq] to the identity. *)
  Lemma g2_dadd_correct (n : nat) (s : list Z) (P acc : Fp2 * Fp2 * Fp2) :
    g2_oncurve P -> g2_oncurve acc -> pt_eq acc id_pt ->
    pt_eq (dadd_from cadd cdbl s P n acc) (smul id_pt cadd (low_bits s n) P).
  Proof.
    intros HP Hacc Eacc.
    pose proof (dadd_from_smul eqs ids adds dbls adds_assoc adds_comm adds_id_l dbls_add
                  s (exist _ P HP) n 0) as H.
    rewrite Nat.mul_0_r, Nat.add_0_l in H.
    assert (Ea : eqs (exist _ acc Hacc) (smul ids adds 0 (exist _ P HP))) by exact Eacc.
    pose proof (dadd_from_Proper eqs adds dbls dbls_add s (exist _ P HP) n _ _ Ea) as H'.
    pose proof (transitivity H' H) as H2.
    unfold eqs in H2.
    rewrite (f_dadd_from adds dbls cadd cdbl (@proj1_sig _ _)
               (fun _ _ => eq_refl) (fun _ => eq_refl)) in H2.
    rewrite (f_smul ids adds id_pt cadd (@proj1_sig _ _)
               eq_refl (fun _ _ => eq_refl) (low_bits s n)) in H2.
    exact H2.
  Qed.
End Algebra.

(* ================================================================== *)
(** ** 2. The bedrock2 program                                          *)
(* ================================================================== *)

Definition g2_curve_add_ip_name : string := "g2_curve_add_ip".
Definition g2_curve_double_ip_name : string := "g2_curve_double_ip".
Definition g2_sub_name : string := "bls12_Fp2_sub".

(** Loop body: [i := i - 1; out := 2 out (in place);
    a := scalar + ((i >> 6) << 3); bit := (load(a) >> (i & 63)) & 1;
    if bit { out := out + P (in place) }]. *)
Definition g2_scalar_mul_loop_body : Syntax.cmd :=
  cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
  (cmd.seq (cmd.call [] g2_curve_double_ip_name
              [expr.var "outx"; expr.var "outy"; expr.var "outz"])
  (cmd.seq (cmd.set "a"
              (expr.op bopname.add (expr.var "scalar")
                 (expr.op bopname.slu
                    (expr.op bopname.sru (expr.var "i") (expr.literal 6))
                    (expr.literal 3))))
  (cmd.seq (cmd.set "bit"
              (expr.op bopname.and
                 (expr.op bopname.sru
                    (expr.load access_size.word (expr.var "a"))
                    (expr.op bopname.and (expr.var "i") (expr.literal 63)))
                 (expr.literal 1)))
     (cmd.cond (expr.var "bit")
        (cmd.call [] g2_curve_add_ip_name
           [expr.var "outx"; expr.var "px";
            expr.var "outy"; expr.var "py";
            expr.var "outz"; expr.var "pz"])
        cmd.skip)))).

(** out := (px - px, 3b', px - px) = (0 : 3b' : 0), then the loop. *)
Definition g2_scalar_mul_body : Syntax.cmd :=
  cmd.seq (cmd.call [] g2_sub_name [expr.var "outx"; expr.var "px"; expr.var "px"])
  (cmd.seq (cmd.call [] g2_sub_name [expr.var "outz"; expr.var "px"; expr.var "px"])
  (cmd.seq (cmd.call [] g2_three_b_name [expr.var "outy"])
  (cmd.seq (cmd.set "i" (expr.literal 256))
     (cmd.while (expr.var "i") g2_scalar_mul_loop_body)))).

Definition g2_scalar_mul_func : Syntax.func :=
  (["outx"; "outy"; "outz"; "scalar"; "px"; "py"; "pz"], [], g2_scalar_mul_body).

Definition g2_add_ip_body : Syntax.func :=
  @af_curve_add_ip_body 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem _ _ Fp2
    bls12_Fp2_field_parameters bls12_Fp2_field_representation g2_three_b_name.

Definition g2_double_ip_body : Syntax.func :=
  @af_curve_double_ip_body 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem _ _ Fp2
    bls12_Fp2_field_parameters bls12_Fp2_field_representation g2_three_b_name.

(* ================================================================== *)
(** ** 3. The program computes [dadd_from cadd cdbl] on raw triples     *)
(* ================================================================== *)

Section Proof.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation
    bls12_prime_parameters_ok bls12_field_representation_ok.
  Existing Instance prime_field_parameters.
  Existing Instances bls12_field_parameters bls12_frep bls12_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation mem := BasicC64Semantics.mem.
  Local Notation locals := BasicC64Semantics.locals.
  Local Notation cadd := (@RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation cdbl := (@RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation tight := (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation).
  Local Notation FElemT := (AFElem (Some tight)).
  Local Notation Fsub := (@AbstractField.Fsub Fp2 bls12_Fp2_field_parameters).

  Definition g2_init (P : Fp2 * Fp2 * Fp2) : Fp2 * Fp2 * Fp2 :=
    let '(X, _, _) := P in (Fsub X X, g2_tb, Fsub X X).

  Definition g2_smul_target (s : list word) (P : Fp2 * Fp2 * Fp2) : Fp2 * Fp2 * Fp2 :=
    smul_prog cadd cdbl (g2_init P) (List.map word.unsigned s) P.

  Lemma afelem_of (p : word) (ws : list word) (v : Fp2) bnd :
    AbstractField.feval (F:=Fp2) ws = v -> AbstractField.bounded_by (F:=Fp2) bnd ws ->
    Lift1Prop.impl1 (AbstractField.FElem (F:=Fp2) p ws) (AFElem (Some bnd) p v).
  Proof.
    intros Hv Hb m0 Hm0. unfold AFElem. exists ws.
    apply sep_emp_l. split; [ split; assumption | exact Hm0 ].
  Qed.

  Lemma g2_sub_self_call (functions : Semantics.env) :
    spec_of_af_sub (F:=Fp2) functions ->
    forall (pout px : word) (X o : Fp2) (R : mem -> Prop) tr m,
      (AFElem None pout o * FElemT px X * R)%sep m ->
      Semantics.call functions g2_sub_name tr m [pout; px; px]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\ (FElemT pout (Fsub X X) * FElemT px X * R)%sep m').
  Proof.
    intros Hsub pout px X o R tr m Hm.
    unfold AFElem in Hm. sepsimpl.
    cbv [spec_of_af_sub AbstractField.binop_spec] in Hsub.
    rename x into wo, x0 into wx, H3 into Hb.
    subst X o.
    eapply Semantics.weaken_call.
    { eapply (Hsub pout px px wo wx wx (AbstractField.FElem (F:=Fp2) px wx * R)%sep tr m).
      split; [ exact Hb | ]. split; [ exact Hb | ].
      split; [ eexists; ecancel_assumption | ].
      split; [ eexists; ecancel_assumption | ].
      ecancel_assumption. }
    cbv beta. intros tr' m' rets (Hr & Htr & out & Hfe & Hbd & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    cbv [AbstractField.bin_sub AbstractField.bin_model AbstractField.bin_outbounds] in Hfe, Hbd.
    rewrite g2_bounds_eq in Hbd.
    eapply Proper_sep_impl1;
      [ eapply Proper_sep_impl1; [ exact (afelem_of pout out _ _ Hfe Hbd)
                                 | exact (afelem_of px wx _ _ eq_refl Hb) ]
      | reflexivity
      | ecancel_assumption ].
  Qed.
  Ltac solve_get :=
    repeat (rewrite map.get_put_diff by congruence);
    first [ rewrite map.get_put_same; reflexivity | eassumption ].

  Ltac peel :=
    cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
    fold WeakestPrecondition.cmd.

  Ltac eval_dexprs :=
    cbv [WeakestPrecondition.dexprs WeakestPrecondition.dexpr list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.literal WeakestPrecondition.get dlet.dlet];
    repeat (eexists; split; [solve_get|]);
    try reflexivity.

  Lemma unsigned_small (v : Z) :
    0 <= v < 2 ^ 64 -> word.unsigned (word.of_Z v : word) = v.
  Proof. intros. apply word.unsigned_of_Z_nowrap. lia. Qed.

  Lemma word_i_and_63 (v : Z) :
    0 <= v < 256 ->
    word.unsigned (word.and (word.of_Z v) (word.of_Z 63) : word) = v mod 64.
  Proof.
    intros Hv. rewrite word.unsigned_and_nowrap, !unsigned_small by lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma word_limb_addr (sp : word) (v : Z) :
    0 <= v < 256 ->
    word.add sp (word.slu (word.sru (word.of_Z v) (word.of_Z 6)) (word.of_Z 3))
    = word.add sp (word.of_Z (Z.of_nat 0 * 32 + Z.of_nat (Z.to_nat (v / 64)) * 8)).
  Proof.
    intros Hv. f_equal. apply word.unsigned_inj.
    assert (Hq : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite word.unsigned_slu by (rewrite unsigned_small by lia; lia).
    rewrite word.unsigned_sru_nowrap by (rewrite unsigned_small by lia; lia).
    rewrite !unsigned_small by lia.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    rewrite ?Z2Nat.id by lia.
    unfold word.wrap. rewrite Z.mod_small by lia.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
  Qed.

  Lemma word_bit (x : word) (k : word) :
    0 <= word.unsigned k < 64 ->
    word.unsigned (word.and (word.sru x k) (word.of_Z 1) : word)
    = Z.b2z (Z.testbit (word.unsigned x) (word.unsigned k)).
  Proof.
    intros Hk. rewrite word.unsigned_and_nowrap.
    rewrite word.unsigned_sru_nowrap by lia.
    rewrite unsigned_small by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    rewrite Z.testbit_spec' by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma word_sub_1 (v : nat) :
    (0 < v <= 256)%nat ->
    word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) = (word.of_Z (Z.of_nat (v - 1)) : word).
  Proof.
    intros Hv. apply word.unsigned_inj.
    rewrite word.unsigned_sub, !unsigned_small by lia.
    unfold word.wrap. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma word_of_nat_zero (v : nat) :
    (v <= 256)%nat -> word.unsigned (word.of_Z (Z.of_nat v) : word) = Z.of_nat v.
  Proof. intros. apply unsigned_small. lia. Qed.

  Lemma scalar_bit_word (s : list word) (v : nat) :
    (v < 256)%nat ->
    scalar_bit (List.map word.unsigned s) v
    = Z.testbit (word.unsigned (nth (Z.to_nat (Z.of_nat v / 64)) s (word.of_Z 0)))
                (Z.of_nat v mod 64).
  Proof.
    intros Hv. unfold scalar_bit.
    replace (Z.to_nat (Z.of_nat v / 64)) with (Nat.div v 64)
      by (rewrite <- (Nat2Z.id (Nat.div v 64)), Nat2Z.inj_div; reflexivity).
    replace (Z.of_nat v mod 64) with (Z.of_nat (Nat.modulo v 64))
      by (rewrite Nat2Z.inj_mod; reflexivity).
    f_equal.
    replace 0 with (word.unsigned (word.of_Z 0 : word)) at 1
      by apply word.unsigned_of_Z_0.
    apply map_nth.
  Qed.

  (** The callee contracts, behind a record so that they stay folded. *)
  Record Callees (functions : Semantics.env) : Prop := mkCallees {
    c_add : spec_of_af_curve_add_ip (F:=Fp2) g2_tb functions;
    c_dbl : spec_of_af_curve_double_ip (F:=Fp2) g2_tb functions;
    c_sub : spec_of_af_sub (F:=Fp2) functions;
    c_tb : spec_of_af_three_b (F:=Fp2) g2_tb g2_three_b_name functions }.

  Lemma add_ip_triple X1 X2 Y1 Y2 Z1 Z2 Xo Yo Zo :
    af_add_ip_gallina (three_b_val:=g2_tb) X1 X2 Y1 Y2 Z1 Z2 = \<Xo, Yo, Zo\> ->
    cadd (X1, Y1, Z1) (X2, Y2, Z2) = (Xo, Yo, Zo).
  Proof. intros H. cbv [RcbLawsAF.cadd]. rewrite <- af_add_ip_eq, H. reflexivity. Qed.

  Lemma double_ip_triple X Y Z Xo Yo Zo :
    af_double_ip_gallina (three_b_val:=g2_tb) X Y Z = \<Xo, Yo, Zo\> ->
    cdbl (X, Y, Z) = (Xo, Yo, Zo).
  Proof. intros H. cbv [RcbLawsAF.cdbl]. rewrite <- af_double_ip_eq, H. reflexivity. Qed.

  Definition loop_inv (functions : Semantics.env) (tr : Semantics.trace)
      (outx outy outz sp px py pz : word) (s : list word) (X Y Z : Fp2)
      (R : mem -> Prop) (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 256)%nat /\
    map.get l "outx" = Some outx /\ map.get l "outy" = Some outy /\
    map.get l "outz" = Some outz /\ map.get l "scalar" = Some sp /\
    map.get l "px" = Some px /\ map.get l "py" = Some py /\
    map.get l "pz" = Some pz /\
    map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
    exists ax ay az,
      dadd_from cadd cdbl (List.map word.unsigned s) (X, Y, Z) v (ax, ay, az)
      = g2_smul_target s (X, Y, Z) /\
      (FElemT outx ax * FElemT outy ay * FElemT outz az
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m.

  Lemma g2_scalar_mul_body_wp functions (HC : Callees functions)
      (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : Fp2)
      (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals) :
    length s = 4%nat ->
    (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
     * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
    map.get l "outx" = Some outx -> map.get l "outy" = Some outy ->
    map.get l "outz" = Some outz -> map.get l "scalar" = Some sp ->
    map.get l "px" = Some px -> map.get l "py" = Some py -> map.get l "pz" = Some pz ->
    WeakestPrecondition.cmd functions g2_scalar_mul_body tr m l
      (fun tr' m' l' =>
         tr' = tr /\
         exists ox oy oz,
           (ox, oy, oz) = g2_smul_target s (X, Y, Z) /\
           (FElemT outx ox * FElemT outy oy * FElemT outz oz
            * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').
  Proof.
    intros Hlen Hm Hox Hoy Hoz Hsp Hpx Hpy Hpz.
    cbv [g2_scalar_mul_body].
    (* outx := px - px *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (g2_sub_self_call functions (c_sub _ HC) outx px X ox0
                (AFElem None outy oy0 * AFElem None outz oz0
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT py Y * FElemT pz Z * R)%sep tr m).
      ecancel_assumption. }
    cbv beta. intros tr1 m1 rets (-> & <- & Hm1).
    eexists; split; [reflexivity|].
    (* outz := px - px *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (g2_sub_self_call functions (c_sub _ HC) outz px X oz0
                (FElemT outx (Fsub X X) * AFElem None outy oy0
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT py Y * FElemT pz Z * R)%sep tr m1).
      ecancel_assumption. }
    cbv beta. intros tr2 m2 rets (-> & <- & Hm2).
    eexists; split; [reflexivity|].
    (* outy := 3b' *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply ((c_tb _ HC) outy oy0
                (FElemT outx (Fsub X X) * FElemT outz (Fsub X X)
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep
                tr m2).
      ecancel_assumption. }
    cbv beta. intros tr3 m3 rets (-> & <- & Hm3).
    rewrite g2_bounds_eq in Hm3.
    eexists; split; [reflexivity|].
    (* i := 256 *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    cbv [dlet.dlet].
    eapply (Loops.while_localsmap (measure := nat)
              (loop_inv functions tr outx outy outz sp px py pz s X Y Z R)
              Wf_nat.lt_wf 256%nat).
    { cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
      do 8 (split; [solve_get|]).
      exists (Fsub X X), g2_tb, (Fsub X X). split.
      - unfold g2_smul_target, smul_prog, g2_init. reflexivity.
      - ecancel_assumption. }
    intros v t mv lv Hinv.
    destruct Hinv as (-> & Hv & Hlx & Hly & Hlz & Hls & Hlpx & Hlpy & Hlpz & Hli
                      & ax & ay & az & Hacc & Hmv).
    exists (word.of_Z (Z.of_nat v)). split.
    { eval_dexprs. }
    split.
    - intros Hne.
      assert (Hv0 : (0 < v)%nat).
      { destruct v; [|lia]. exfalso. apply Hne. apply word.unsigned_of_Z_0. }
      set (v' := (v - 1)%nat).
      cbv [g2_scalar_mul_loop_body].
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      cbv [Semantics.interp_binop].
      rewrite word_sub_1 by lia. fold v'.
      (* out := double(out) in place *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply ((c_dbl _ HC) outx outy outz ax ay az
                  (BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep
                  tr mv).
        ecancel_assumption. }
      cbv beta. intros t2 md rets (-> & <- & dx & dy & dz & Hdg & Hmd).
      pose proof (double_ip_triple _ _ _ _ _ _ Hdg) as Hd. clear Hdg.
      eexists; split; [reflexivity|].
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      assert (Hv'256 : (v' < 256)%nat) by lia.
      set (limb := Z.to_nat (Z.of_nat v' / 64)).
      assert (Hlimb : (limb < 4)%nat).
      { unfold limb. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        apply Z.div_lt_upper_bound; lia. }
      pose proof (BLS12_MSM.ScalarsArray_load_limb (field_parameters := bls12_field_parameters)
                    (field_representation := bls12_frep)
                    eq_refl (fun p _ => p) (fun p => p) (F.zero, F.zero, F.zero)
                    sp [s] 0 limb
                    (FElemT outx dx * FElemT outy dy * FElemT outz dz
                     * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep md
                    ltac:(cbn; lia) Hlimb) as Hload.
      cbn [nth] in Hload.
      peel. peel.
      eexists; split.
      { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
             WeakestPrecondition.expr_body WeakestPrecondition.literal
             WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
        eexists; split; [solve_get|].
        eexists; split.
        { cbv [Semantics.interp_binop].
          rewrite word_limb_addr by lia. apply Hload. ecancel_assumption. }
        eexists; split; [solve_get|].
        reflexivity. }
      cbv [dlet.dlet Semantics.interp_binop].
      set (bitw := word.and
                     (word.sru (nth limb s (word.of_Z 0))
                        (word.and (word.of_Z (Z.of_nat v')) (word.of_Z 63)))
                     (word.of_Z 1) : word).
      assert (Hbit : word.unsigned bitw
                     = Z.b2z (scalar_bit (List.map word.unsigned s) v')).
      { unfold bitw. rewrite word_bit by (rewrite word_i_and_63 by lia;
                                         pose proof (Z.mod_pos_bound (Z.of_nat v') 64); lia).
        rewrite word_i_and_63 by lia. rewrite scalar_bit_word by lia. reflexivity. }
      peel.
      eexists; split; [eval_dexprs|].
      replace v with (S v') in Hacc by lia.
      cbn [dadd_from] in Hacc. rewrite Hd in Hacc.
      split.
      + intros Hb.
        assert (Hsb : scalar_bit (List.map word.unsigned s) v' = true).
        { destruct (scalar_bit (List.map word.unsigned s) v'); [reflexivity|].
          rewrite Hbit in Hb. cbn in Hb. congruence. }
        rewrite Hsb in Hacc.
        peel.
        eexists; split; [eval_dexprs|].
        eapply Semantics.weaken_call.
        { eapply ((c_add _ HC) outx px outy py outz pz dx X dy Y dz Z
                    (BLS12_MSM.ScalarsArray sp [s] * R)%sep tr md).
          ecancel_assumption. }
        cbv beta. intros t3 ma rets (-> & <- & sx & sy & sz & Hsg & Hma).
        pose proof (add_ip_triple _ _ _ _ _ _ _ _ _ Hsg) as Hs. clear Hsg.
        rewrite Hs in Hacc.
        eexists; split; [reflexivity|].
        exists v'. split; [|lia].
        cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
        do 8 (split; [solve_get|]).
        exists sx, sy, sz. split; [exact Hacc|]. ecancel_assumption.
      + intros Hb.
        assert (Hsb : scalar_bit (List.map word.unsigned s) v' = false).
        { destruct (scalar_bit (List.map word.unsigned s) v'); [|reflexivity].
          rewrite Hbit in Hb. cbn in Hb. congruence. }
        rewrite Hsb in Hacc.
        peel.
        exists v'. split; [|lia].
        cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
        do 8 (split; [solve_get|]).
        exists dx, dy, dz. split; [exact Hacc|]. ecancel_assumption.
    - intros Hz.
      rewrite word_of_nat_zero in Hz by exact Hv.
      assert (v = 0%nat) as -> by lia.
      cbn [dadd_from] in Hacc.
      split; [reflexivity|].
      exists ax, ay, az. split; [exact Hacc|exact Hmv].
  Qed.
  Definition spec_of_g2_scalar_mul (functions : Semantics.env) : Prop :=
    forall (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : Fp2)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g2_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz,
             (ox, oy, oz) = g2_smul_target s (X, Y, Z) /\
             (FElemT outx ox * FElemT outy oy * FElemT outz oz
              * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').

  Theorem g2_scalar_mul_ok functions :
    map.get functions "g2_scalar_mul" = Some g2_scalar_mul_func ->
    Callees functions ->
    spec_of_g2_scalar_mul functions.
  Proof.
    intros Henv HC outx outy outz sp px py pz ox0 oy0 oz0 X Y Z s R tr m Hlen Hm.
    unfold Semantics.call.
    do 3 eexists. split; [exact Henv|].
    destruct (map.of_list_zip ["outx"; "outy"; "outz"; "scalar"; "px"; "py"; "pz"]
                [outx; outy; outz; sp; px; py; pz]) as [l0|] eqn:Hzip.
    2: { exfalso. cbn in Hzip. discriminate Hzip. }
    exists l0. split; [reflexivity|].
    cbn in Hzip. injection Hzip as <-.
    eapply Semantics.exec.weaken.
    { eapply WeakestPreconditionProperties.sound_cmd.
      eapply (g2_scalar_mul_body_wp functions HC outx outy outz sp px py pz
                ox0 oy0 oz0 X Y Z s R tr m); try exact Hlen; try exact Hm;
        reflexivity. }
    intros tr' m' l' (-> & ox & oy & oz & Hres & Hm').
    exists []. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    exists ox, oy, oz. split; [exact Hres|exact Hm'].
  Qed.
End Proof.

(* ================================================================== *)
(** ** 4. k P on E'(Fp2), and the closed statement                      *)
(* ================================================================== *)

Section Closed.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation
    bls12_prime_parameters_ok bls12_field_representation_ok.
  Existing Instance prime_field_parameters.
  #[local] Existing Instances g2_fld g2_dec g2_char_ge_3 g2_char_ge_12 g2_char_ge_21.

  #[local] Instance prime_M_sm : Znumtheory.prime (Z.pos PrimeField.M_pos) :=
    bls12_prime_certif.prime_bls12_381.

  Add Ring Fp_ring_sm : (F.ring_theory PrimeField.M_pos)
    (morphism (F.ring_morph PrimeField.M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory PrimeField.M_pos),
     power_tac (F.power_theory PrimeField.M_pos) [F.is_pow_constant]).

  Local Notation word := BasicC64Semantics.word.
  Local Notation mem := BasicC64Semantics.mem.
  Local Notation cadd := (@RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation cdbl := (@RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation pt_eq := (@RcbLawsAF.pt_eq Fp2 bls12_Fp2_field_parameters g2_dec).
  Local Notation id_pt := (@RcbLawsAF.id_pt Fp2 bls12_Fp2_field_parameters).
  Local Notation Fzero := (@AbstractField.Fzero Fp2 bls12_Fp2_field_parameters).
  Local Notation Fone2 := (@AbstractField.Fone Fp2 bls12_Fp2_field_parameters).
  Local Notation Fopp2 := (@AbstractField.Fopp Fp2 bls12_Fp2_field_parameters).
  Local Notation Fadd2 := (@AbstractField.Fadd Fp2 bls12_Fp2_field_parameters).
  Local Notation Fsub2 := (@AbstractField.Fsub Fp2 bls12_Fp2_field_parameters).
  Local Notation Fmul2 := (@AbstractField.Fmul Fp2 bls12_Fp2_field_parameters).

  Add Ring Fp2_ring_sm :
    (@Ring.ring_theory_for_stdlib_tactic Fp2 (@eq Fp2) Fzero Fone2 Fopp2 Fadd2 Fsub2 Fmul2 _).
  Local Notation tight := (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation).
  Local Notation FElemT := (AFElem (Some tight)).

  Lemma g2_init_eq X Y Z : g2_init (X, Y, Z) = (Fzero, g2_tb, Fzero).
  Proof.
    destruct X as [a b]. cbv [g2_init].
    cbv [AbstractField.Fsub AbstractField.Fzero bls12_Fp2_field_parameters Fp2_field_parameters
         subp2 zerop2 fst snd].
    f_equal; f_equal; f_equal; ring.
  Qed.

  Lemma g2_tb_nz : g2_tb <> Fzero.
  Proof.
    intros H. apply (f_equal (fun x => F.to_Z (fst x))) in H. vm_compute in H. discriminate H.
  Qed.

  Lemma g2_init_oncurve P : g2_oncurve (g2_init P).
  Proof.
    destruct P as [[X Y] Z]. rewrite g2_init_eq.
    cbv [g2_oncurve RcbLawsAF.oncurve]. split.
    - ring.
    - intros _. exact g2_tb_nz.
  Qed.

  Lemma g2_init_id P : pt_eq (g2_init P) id_pt.
  Proof.
    destruct P as [[X Y] Z]. rewrite g2_init_eq.
    cbv [RcbLawsAF.pt_eq RcbLawsAF.id_pt].
    match goal with |- context [@Crypto.Util.Decidable.dec ?P ?i] =>
      destruct (@Crypto.Util.Decidable.dec P i) as [_|n] end;
      [ reflexivity | exfalso; apply n; reflexivity ].
  Qed.

  (** Double-and-add over the Fp2 RCB formulas from (0 : 3b' : 0), on an
      on-curve point, is [pt_eq] to [k P], [k] the 256-bit limb integer. *)
  Theorem g2_smul_correct (s : list word) (P : Fp2 * Fp2 * Fp2) :
    length s = 4%nat -> g2_oncurve P ->
    pt_eq (g2_smul_target s P)
          (smul id_pt cadd (BLS12_MSM_Closed.scalar_value s) P).
  Proof.
    intros Hlen HP. unfold g2_smul_target. rewrite smul_prog_eq.
    rewrite (BLS12_MSM_Closed.scalar_value_bits s Hlen).
    exact (g2_dadd_correct 256 (List.map word.unsigned s) P (g2_init P) HP
             (g2_init_oncurve P) (g2_init_id P)).
  Qed.
  #[local] Instance g2_rep_ok_sm :
    @AbstractField.FieldRepresentation_ok Fp2 _ _ _ _ _ bls12_Fp2_field_representation :=
    Fp2_field_representation_ok _ _.

  (** The closed statement: in an environment holding the printed bodies,
      with only the Fp2 leaf contracts as premises, [g2_scalar_mul] returns
      a tight triple projectively equal to [k P] for every point P of
      E'(Fp2) with tight coordinates, [k] the 256-bit integer of the limbs. *)
  Theorem g2_scalar_mul_closed (functions : Semantics.env) :
    map.get functions "g2_scalar_mul" = Some g2_scalar_mul_func ->
    map.get functions g2_curve_add_ip_name = Some g2_add_ip_body ->
    map.get functions g2_curve_double_ip_name = Some g2_double_ip_body ->
    map.get functions g2_three_b_name = Some g2_three_b_body ->
    spec_of_af_mul (F:=Fp2) functions ->
    spec_of_af_add (F:=Fp2) functions ->
    spec_of_af_sub (F:=Fp2) functions ->
    forall (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : Fp2)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      g2_oncurve (X, Y, Z) ->
      (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g2_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : Fp2,
             pt_eq (ox, oy, oz) (smul id_pt cadd (BLS12_MSM_Closed.scalar_value s) (X, Y, Z))
             /\ (FElemT outx ox * FElemT outy oy * FElemT outz oz
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z
                 * R)%sep m').
  Proof.
    intros Hsm Hai Hdi Htb Hmul Hadd Hsub.
    assert (HC : Callees functions).
    { pose proof (g2_three_b_ok functions Htb) as Hload.
      constructor.
      - exact (@af_curve_add_ip_correct 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem
                 _ _ _ _ _ _ Fp2 bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                 g2_bounds_eq g2_tb g2_three_b_name I functions Hai Hmul Hadd Hsub Hload).
      - exact (@af_curve_double_ip_correct 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem
                 _ _ _ _ _ _ Fp2 bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                 g2_bounds_eq g2_tb g2_three_b_name I functions Hdi Hmul Hadd Hsub Hload).
      - exact Hsub.
      - exact Hload. }
    pose proof (g2_scalar_mul_ok functions Hsm HC) as Hspec.
    intros outx outy outz sp px py pz ox0 oy0 oz0 X Y Z s R tr m Hlen Hon Hm.
    eapply Semantics.weaken_call.
    { exact (Hspec outx outy outz sp px py pz ox0 oy0 oz0 X Y Z s R tr m Hlen Hm). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Hres & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz. split; [ | exact Hm' ].
    rewrite Hres. exact (g2_smul_correct s (X, Y, Z) Hlen Hon).
  Qed.
End Closed.
