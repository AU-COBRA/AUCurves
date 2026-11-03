(** * [Ristretto255_BOrderBridge] — bridge [ℓ·B = E.zero] from XYZT to the affine
      Edwards group, and discharge the [2]-surjectivity content used by
      [Ristretto255_Inj.main_subgroup_doubling_nontrivial].

    Strategy (see the file header of [Curve25519_B_Order.v]):

      - [Curve25519_B_Order.lB_is_xyzt_identity] (Qed, native_decide) establishes
        that [ℓ·B] in raw XYZT projective coords is the identity [(0, c, c, 0)].
      - This file connects the raw XYZT scalar mult [Edwards_xyzt_smult_pos] to
        fiat-crypto's verified extended-coordinate group ([Crypto.Curves.Edwards.XYZT.Basic])
        via a representation predicate [repr], reusing fiat's [to_affine_m1add]
        homomorphism (NO re-proof of the Hisil–Carter–Dawson–Wong formulas).
      - Induction on [positive] lifts the per-add homomorphism to a full scalar-mult
        homomorphism into the affine [scalarmult_ref] over the Edwards commutative group.
      - [lB_is_xyzt_identity] then yields [ℓ·B = E.zero] in the affine group, hence
        [nB ℓ = E.zero].
      - [2]-surjectivity (every nonzero element of an odd-prime-order group is a
        double) + a torsion-exclusion computation discharge the residual axiom. *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Group.
Require Import Crypto.Algebra.ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.Curve25519_B_Order.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_RoundTrip.

Local Open Scope F_scope.
Local Notation FF := (F p).

(** Native-compiled decision (faster than [vm_cast]); mirrors [Curve25519_B_Order]. *)
Local Ltac native_decide_eq :=
  apply Decidable.dec_bool; native_cast_no_check (eq_refl true).

(** ** The affine Edwards group over Curve25519, as concrete instances. *)
Definition Eopp := (@AffineProofs.E.opp (F p) (@eq (F p)) F.zero F.one (@F.opp p) (@F.add p) (@F.sub p)
     (@F.mul p) (@F.inv p) (@F.div p) Curve25519.field (@F.eq_dec p) E.a E.d E.nonzero_a).

Definition Egroup : @group Curve25519.E.point E.eq Curve25519.E.add Curve25519.E.zero Eopp :=
  commutative_group_group
    (AffineProofs.E.edwards_curve_commutative_group
      (field:=Curve25519.field) (char_ge_3:=Curve25519.char_ge_3) (Feq_dec:=F.eq_dec)
      (a:=E.a) (d:=E.d) (nonzero_a:=E.nonzero_a) (square_a:=E.square_a) (nonsquare_d:=E.nonsquare_d)).
Existing Instance Egroup.

Definition Escalar : Z -> Curve25519.E.point -> Curve25519.E.point :=
  @scalarmult_ref Curve25519.E.point Curve25519.E.add Curve25519.E.zero Eopp.
Definition Escalar_is : @ScalarMult.is_scalarmult Curve25519.E.point E.eq Curve25519.E.add Curve25519.E.zero Eopp Escalar :=
  @ScalarMult.scalarmult_ref_is_scalarmult Curve25519.E.point E.eq Curve25519.E.add Curve25519.E.zero Eopp Egroup.
Existing Instance Escalar_is.

(** ** fiat-crypto extended-coordinate point and operations at Curve25519 params. *)
Notation Ext_point := (@Extended.point (F p) (@eq (F p)) F.zero (@F.add p) (@F.mul p) E.a E.d).
Notation Eext_eq := (@Extended.eq (F p) (@eq (F p)) F.zero (@F.add p) (@F.mul p) E.a E.d).

Definition Eto_affine : Ext_point -> Curve25519.E.point :=
  @Extended.to_affine (F p) (@eq (F p)) F.zero F.one (@F.opp p) (@F.add p) (@F.sub p) (@F.mul p) (@F.inv p) (@F.div p) Curve25519.field (@F.eq_dec p) E.a E.d E.nonzero_a.
Definition Efrom_affine : Curve25519.E.point -> Ext_point :=
  @Extended.from_affine (F p) (@eq (F p)) F.zero F.one (@F.opp p) (@F.add p) (@F.sub p) (@F.mul p) (@F.inv p) (@F.div p) Curve25519.field (@F.eq_dec p) E.a E.d E.nonzero_a.

Lemma Ea_eq_minus1 : E.a = F.opp F.one. Proof. reflexivity. Qed.

Lemma twice_d_eq : (F.of_Z p 2 * E.d)%F = (E.d + E.d)%F.
Proof.
  assert (Hchar : (F.of_Z p 2 : F p) = (F.one + F.one)%F).
  { apply ModularArithmeticTheorems.F.eq_to_Z_iff. reflexivity. }
  rewrite Hchar. ring.
Qed.

(** [a = -1] and [twice_d = d + d] instantiate fiat's [m1add]. *)
Definition Em1add : Ext_point -> Ext_point -> Ext_point :=
  @Extended.m1add (F p) (@eq (F p)) F.zero F.one (@F.opp p) (@F.add p) (@F.sub p) (@F.mul p) (@F.inv p) (@F.div p)
    Curve25519.field Curve25519.char_ge_3 (@F.eq_dec p) E.a E.d E.nonzero_a E.square_a E.nonsquare_d
    Ea_eq_minus1 (F.of_Z p 2 * E.d) twice_d_eq.

(** ** Representation predicate: a raw 4-tuple [(X,Y,Z,T)] represents an extended
       point [(X,Y,Z,Ta,Tb)] iff [T = Ta*Tb] (the extended T-coordinate factorisation).
       The raw add stores [T] as a single product; fiat keeps [Ta], [Tb] separate. *)
Definition to_affine_raw (r : FF * FF * FF * FF) : FF * FF :=
  let X := fst (fst (fst r)) in let Y := snd (fst (fst r)) in let Z := snd (fst r) in
  ((X * F.inv Z)%F, (Y * F.inv Z)%F).

Definition repr (r : FF * FF * FF * FF) (Q : Ext_point) : Prop :=
  let '(X, Y, Z, Ta, Tb) := proj1_sig Q in r = (X, Y, Z, (Ta * Tb)%F).

Lemma Eto_affine_coords (Q : Ext_point) :
  proj1_sig (Eto_affine Q) = (let '(X, Y, Z, _, _) := proj1_sig Q in ((X * F.inv Z)%F, (Y * F.inv Z)%F)).
Proof.
  unfold Eto_affine, Extended.to_affine. cbn [proj1_sig].
  destruct Q as [ [ [ [ [X Y] Z] Ta] Tb] HQ]. reflexivity.
Qed.

(** (B1) Per-add homomorphism: the raw XYZT add agrees with fiat's [m1add] under [repr].
        Both formulas are identical up to the single-vs-split T factorisation and [2d = d+d]. *)
Lemma repr_add (r1 r2 : FF * FF * FF * FF) (Q1 Q2 : Ext_point) :
  repr r1 Q1 -> repr r2 Q2 -> repr (edwards_xyzt_add25519 r1 r2) (Em1add Q1 Q2).
Proof.
  unfold repr, Em1add, Extended.m1add, edwards_xyzt_add25519.
  destruct Q1 as [ [ [ [ [X1 Y1] Z1] Ta1] Tb1] HQ1].
  destruct Q2 as [ [ [ [ [X2 Y2] Z2] Ta2] Tb2] HQ2].
  cbn [proj1_sig]. intros H1 H2. subst r1 r2. cbn [fst snd].
  assert (Hchar : (F.of_Z p 2 : F p) = (F.one + F.one)%F).
  { apply ModularArithmeticTheorems.F.eq_to_Z_iff. reflexivity. }
  rewrite !Hchar.
  apply pair_equal_spec; split;
    [apply pair_equal_spec; split; [apply pair_equal_spec; split|]|]; ring.
Qed.

Lemma to_affine_raw_repr (r : FF * FF * FF * FF) (Q : Ext_point) :
  repr r Q -> to_affine_raw r = proj1_sig (Eto_affine Q).
Proof.
  unfold repr, to_affine_raw. rewrite Eto_affine_coords.
  destruct Q as [ [ [ [ [X Y] Z] Ta] Tb] HQ]. cbn [proj1_sig].
  intros ->. cbn [fst snd]. reflexivity.
Qed.

Lemma Eto_affine_m1add (P Q : Ext_point) :
  E.eq (Eto_affine (Em1add P Q)) (Curve25519.E.add (Eto_affine P) (Eto_affine Q)).
Proof.
  exact (@Extended.to_affine_m1add (F p) (@eq (F p)) F.zero F.one (@F.opp p) (@F.add p) (@F.sub p) (@F.mul p) (@F.inv p) (@F.div p)
    Curve25519.field Curve25519.char_ge_3 (@F.eq_dec p) E.a E.d E.nonzero_a E.square_a E.nonsquare_d
    Ea_eq_minus1 (F.of_Z p 2 * E.d) twice_d_eq P Q).
Qed.

(** (B2) Scalar-mult homomorphism: the raw binary scalar mult lands in the same affine
        point as [scalarmult_ref], maintaining the [repr] invariant. *)
Lemma smult_pos_repr_affine :
  forall (n : positive) (r : FF * FF * FF * FF) (Q : Ext_point),
    repr r Q ->
    exists Q' : Ext_point,
      repr (Edwards_xyzt_smult_pos n r) Q' /\
      E.eq (Eto_affine Q') (Escalar (Z.pos n) (Eto_affine Q)).
Proof.
  induction n as [n' IH | n' IH | ]; intros r Q Hrepr.
  - destruct (IH r Q Hrepr) as [Q' [Hr' Haff']].
    exists (Em1add (Em1add Q' Q') Q). split.
    + cbn [Edwards_xyzt_smult_pos].
      apply repr_add; [ apply repr_add; exact Hr' | exact Hrepr ].
    + rewrite !Eto_affine_m1add, Haff'.
      rewrite Pos2Z.inj_xI.
      rewrite (ScalarMult.scalarmult_add_l (2 * Z.pos n')%Z 1%Z (Eto_affine Q)).
      rewrite ScalarMult.scalarmult_1_l.
      replace (2 * Z.pos n')%Z with (Z.pos n' + Z.pos n')%Z by ring.
      rewrite ScalarMult.scalarmult_add_l. reflexivity.
  - destruct (IH r Q Hrepr) as [Q' [Hr' Haff']].
    exists (Em1add Q' Q'). split.
    + cbn [Edwards_xyzt_smult_pos]. apply repr_add; exact Hr'.
    + rewrite Eto_affine_m1add, Haff'.
      rewrite Pos2Z.inj_xO.
      replace (2 * Z.pos n')%Z with (Z.pos n' + Z.pos n')%Z by ring.
      rewrite ScalarMult.scalarmult_add_l. reflexivity.
  - exists Q. split.
    + cbn [Edwards_xyzt_smult_pos]. exact Hrepr.
    + rewrite ScalarMult.scalarmult_1_l. reflexivity.
Qed.

(** ** [B] in extended coords (Z=5 chosen to avoid F.div), and its affine image is [B]. *)
Definition B_ext : Ext_point.
Proof.
  refine (exist _ (F.of_Z _ 5 * F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202,
                   F.of_Z _ 4, F.of_Z _ 5,
                   F.of_Z _ 4 * F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202,
                   F.one) _).
  Decidable.vm_decide.
Defined.

Lemma repr_B : repr B_xyzt B_ext.
Proof.
  unfold repr, B_ext, B_xyzt. cbn [proj1_sig].
  apply pair_equal_spec; split;
    [ apply pair_equal_spec; split; [ apply pair_equal_spec; split | ] | ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - ring.
Qed.

Lemma B_ext_eq_from : Eext_eq B_ext (Efrom_affine Curve25519.E.B).
Proof. Decidable.vm_decide. Qed.

Lemma Eto_affine_B : E.eq (Eto_affine B_ext) Curve25519.E.B.
Proof.
  pose proof (_ : RelationClasses.Equivalence (@E.eq (F p) (@eq (F p)) F.one (@F.add p) (@F.mul p) E.a E.d)) as HE.
  eapply RelationClasses.transitivity.
  - exact (Extended.Proper_to_affine (field:=Curve25519.field) (Feq_dec:=F.eq_dec) (nonzero_a:=E.nonzero_a) B_ext (Efrom_affine Curve25519.E.B) B_ext_eq_from).
  - exact (Extended.to_affine_from_affine (field:=Curve25519.field) (Feq_dec:=F.eq_dec) (nonzero_a:=E.nonzero_a) Curve25519.E.B).
Qed.

(** Coordinate-equality implies [E.eq] (both are the affine [proj1_sig]). *)
Lemma Eeq_of_proj (P Q : Curve25519.E.point) :
  proj1_sig P = proj1_sig Q -> E.eq P Q.
Proof.
  intro Hpq. unfold E.eq, E.coordinates.
  destruct P as [ [xP yP] HP]; destruct Q as [ [xQ yQ] HQ].
  cbn [proj1_sig] in Hpq. inversion Hpq; subst. split; reflexivity.
Qed.

(** [to_affine_raw] of an XYZT-identity tuple [(0, c, c, _)] is the affine identity [(0,1)].
    Stated over an ABSTRACT tuple [r] so that the kernel never reduces the (252-doubling)
    [Edwards_xyzt_smult_pos l_pos B_xyzt] term when this is applied — only its opaque
    [lB_is_xyzt_identity] projections are checked.  (Avoids the big-literal slow-Qed trap.) *)
Lemma to_affine_raw_zero (r : FF * FF * FF * FF) :
  fst (fst (fst r)) = F.zero ->
  snd (fst r) = snd (fst (fst r)) ->
  snd (fst r) <> F.zero ->
  to_affine_raw r = (F.zero, F.one).
Proof.
  intros HX HYZ HZnz. unfold to_affine_raw.
  pose proof (@F.inv_nonzero p Curve25519.prime_p _ HZnz) as Hinv.
  (* [Hinv] : F.inv (snd (fst r)) * snd (fst r) = 1 *)
  apply pair_equal_spec; split.
  - rewrite HX. ring.
  - rewrite <- HYZ. rewrite <- Hinv. ring.
Qed.

(** The affine image of the raw [ℓ·B] XYZT tuple is the affine identity [(0,1)].

    One [native_decide_eq] per coordinate: native code runs the 252 doublings and the
    [F.inv = F.pow (p-2)], and the kernel checks the [native_cast_no_check] cast at Qed.

    This was an [Axiom] from 2026-05-27, recorded as an out-of-memory failure of native
    compilation on a 14 GB machine.  On 2026-11-02 (Rocq 9.2, 15 GB, no other build running)
    the same proof took 20.6 s at Qed, with the compiler at 446 MB. *)
Lemma to_affine_lB :
  to_affine_raw (Edwards_xyzt_smult_pos l_pos B_xyzt) = (F.zero, F.one).
Proof.
  unfold to_affine_raw.
  apply pair_equal_spec; split; native_decide_eq.
Qed.

(** [Escalar n] respects [E.eq], for an arbitrary scalar [n].  With [n] abstract, unification
    cannot unfold [scalarmult_ref n] (a [Z.peano_rect]). *)
Lemma Escalar_Proper_r (n : Z) (P Q : Curve25519.E.point) :
  E.eq P Q -> E.eq (Escalar n P) (Escalar n Q).
Proof.
  intros HPQ. apply (ScalarMult.Proper_scalarmult_ref (groupG := Egroup)); [ reflexivity | exact HPQ ].
Qed.

(** (B3) [ℓ·B = E.zero] in the affine Edwards group, via the XYZT identity fact.
    [Escalar ℓ B] connects to the raw scalar mult by [smult_pos_repr_affine], and the raw
    result's affine image is [(0,1)] by [to_affine_lB].

    Earlier versions stepped from [Escalar ℓ B] to [Escalar ℓ (Eto_affine B_ext)] with
    [apply (ScalarMult.Proper_scalarmult_ref (groupG := Egroup))] on the goal itself.  That
    tactic, not the Qed, was the slow step: its unification calls the kernel conversion, which
    reduces [scalarmult_ref (Z.pos l_pos) _], a unary [Z.peano_rect] (still running after 60 s
    in rocq-mcp on 2026-11-02, and after 10 minutes in a local build).  [Escalar_Proper_r]
    states the same step for an abstract scalar, and [exact] then matches it syntactically;
    each tactic and the Qed take at most 0.004 s in `dune build`.

    An [Axiom] declaration of this statement exceeded 11 GB on Rocq 9.2; see
    docs/slow-proofs.md. *)
Lemma E_mul_l_B_zero : E.eq (Escalar (Z.pos l_pos) Curve25519.E.B) Curve25519.E.zero.
Proof.
  pose proof (_ : RelationClasses.Equivalence (@E.eq (F p) (@eq (F p)) F.one (@F.add p) (@F.mul p) E.a E.d)) as HE.
  pose proof (smult_pos_repr_affine l_pos B_xyzt B_ext repr_B) as Hsm.
  destruct Hsm as [Q' [Hr' Haff']].
  assert (Hid : E.eq (Eto_affine Q') Curve25519.E.zero).
  { apply Eeq_of_proj. rewrite <- (to_affine_raw_repr _ _ Hr').
    change (proj1_sig Curve25519.E.zero) with (@F.zero p, @F.one p).
    exact to_affine_lB. }
  eapply RelationClasses.transitivity; [ | exact Hid ].
  eapply RelationClasses.transitivity; [ | symmetry; exact Haff' ].
  exact (Escalar_Proper_r (Z.pos l_pos) _ _ (RelationClasses.symmetry Eto_affine_B)).
Qed.

(** ** [Curve25519.E.add] is Proper for [E.eq] (from the group's monoid structure). *)
Lemma Eadd_Proper :
  Morphisms.Proper
    (Morphisms.respectful E.eq (Morphisms.respectful E.eq E.eq)) Curve25519.E.add.
Proof. exact (Hierarchy.monoid_op_Proper (monoid := Hierarchy.group_monoid (group:=Egroup))). Qed.

(** (B4) [nB n] (iterated [E.add B]) equals [scalarmult_ref (Z.of_nat n) B]. *)
Lemma nB_eq_scalarmult :
  forall n : nat, E.eq (nB n) (Escalar (Z.of_nat n) Curve25519.E.B).
Proof.
  pose proof (_ : RelationClasses.Equivalence (@E.eq (F p) (@eq (F p)) F.one (@F.add p) (@F.mul p) E.a E.d)) as HE.
  induction n as [ | n IH].
  - change (nB 0) with Curve25519.E.zero.
    change (Z.of_nat 0) with 0%Z.
    rewrite (ScalarMult.scalarmult_0_l (is_scalarmult := Escalar_is)).
    reflexivity.
  - change (nB (S n)) with (Curve25519.E.add Curve25519.E.B (nB n)).
    rewrite Nat2Z.inj_succ.
    rewrite (ScalarMult.scalarmult_succ_l (groupG := Egroup) (mul_is_scalarmult := Escalar_is)).
    apply Eadd_Proper; [ reflexivity | exact IH ].
Qed.

(** (B5) [nB ℓ = E.zero]: the order of [B] is [ℓ]. *)
Lemma nB_l_zero : E.eq (nB (Z.to_nat (Z.pos l_pos))) Curve25519.E.zero.
Proof.
  pose proof (_ : RelationClasses.Equivalence (@E.eq (F p) (@eq (F p)) F.one (@F.add p) (@F.mul p) E.a E.d)) as HE.
  eapply RelationClasses.transitivity; [ apply nB_eq_scalarmult | ].
  rewrite Z2Nat.id by (apply Pos2Z.is_nonneg).
  exact E_mul_l_B_zero.
Qed.
