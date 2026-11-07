(** * ZModTowerF: ZModTower's Fp6 and Fp12 over [F p], with xi as a parameter, and the bridge.

    [ZModTower.v] computes the tower on integers, reducing mod p after every operation.  This file
    gives the same formulas on fiat-crypto's [F p], over the Fp2 of [Theory/BLS12Pairing/Pairing.v]
    (u^2 = -1, the Fp2 of ZModTower and of BN254), with the sextic non-residue [xi : Fp2] a
    parameter (Pairing.v fixes xi = 1 + u for BLS12-381):

      Fp6  = Fp2[v]/(v^3 - xi)   [fq6_*]    Fp12 = Fp6[w]/(w^2 - v)   [fq12_*]

    and proves that [ofZ12] (F.of_Z componentwise) maps each ZModTower operation the final
    exponentiation uses to the F-level one: [zfp12_mul], [zfp12_sqr], [zfp12_one], [zfp12_conj],
    [zfp12_pow], [zfp12_inv], [zfp12_frob_p2] and [PairingSpec.final_exp] on [zmod_ops].  It also
    proves that ZModTower's results are canonical (components in [0, p)), on which [ofZ12] is
    injective, so equalities at the F level transfer back to ZModTower.

    The formulas are those of ZModTower, operation by operation, so that the bridge is a rewrite;
    the algebra of the F-level tower (ring laws, fields, Frobenius) is not here.  No [Admitted],
    no [Axiom].
*)

From Stdlib Require Import ZArith.ZArith micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.PairingSpecDefs.

Local Open Scope Z_scope.

Section TowerF.
  Context (p : positive).
  Local Notation Fp2 := (F p * F p)%type.

  Definition Fp6F : Type := (Fp2 * Fp2 * Fp2)%type.
  Definition Fp12F : Type := (Fp6F * Fp6F)%type.

  Context (xi : Fp2).

  (** ** Fp6 (ZModTower's [zfp6_*], over F p) *)

  Definition fq6_c0 (a : Fp6F) : Fp2 := fst (fst a).
  Definition fq6_c1 (a : Fp6F) : Fp2 := snd (fst a).
  Definition fq6_c2 (a : Fp6F) : Fp2 := snd a.
  Definition mk_fq6 (c0 c1 c2 : Fp2) : Fp6F := ((c0, c1), c2).

  Definition fq2_mul_xi (a : Fp2) : Fp2 := Pairing.fp2_mul p a xi.

  Definition fq6_mul_v (a : Fp6F) : Fp6F :=
    mk_fq6 (fq2_mul_xi (fq6_c2 a)) (fq6_c0 a) (fq6_c1 a).

  Definition fq6_add (a b : Fp6F) : Fp6F :=
    mk_fq6 (Pairing.fp2_add p (fq6_c0 a) (fq6_c0 b))
           (Pairing.fp2_add p (fq6_c1 a) (fq6_c1 b))
           (Pairing.fp2_add p (fq6_c2 a) (fq6_c2 b)).
  Definition fq6_sub (a b : Fp6F) : Fp6F :=
    mk_fq6 (Pairing.fp2_sub p (fq6_c0 a) (fq6_c0 b))
           (Pairing.fp2_sub p (fq6_c1 a) (fq6_c1 b))
           (Pairing.fp2_sub p (fq6_c2 a) (fq6_c2 b)).
  Definition fq6_neg (a : Fp6F) : Fp6F :=
    let '((a0, a1), a2) := a in
    ((Pairing.fp2_neg p a0, Pairing.fp2_neg p a1), Pairing.fp2_neg p a2).

  Definition fq6_mul (a b : Fp6F) : Fp6F :=
    let a0 := fq6_c0 a in let a1 := fq6_c1 a in let a2 := fq6_c2 a in
    let b0 := fq6_c0 b in let b1 := fq6_c1 b in let b2 := fq6_c2 b in
    let t0 := Pairing.fp2_mul p a0 b0 in
    let t1 := Pairing.fp2_mul p a1 b1 in
    let t2 := Pairing.fp2_mul p a2 b2 in
    let c0 := Pairing.fp2_add p t0
                (fq2_mul_xi
                  (Pairing.fp2_sub p
                    (Pairing.fp2_sub p
                      (Pairing.fp2_mul p (Pairing.fp2_add p a1 a2) (Pairing.fp2_add p b1 b2))
                      t1)
                    t2)) in
    let c1 := Pairing.fp2_add p
                (Pairing.fp2_sub p
                  (Pairing.fp2_sub p
                    (Pairing.fp2_mul p (Pairing.fp2_add p a0 a1) (Pairing.fp2_add p b0 b1))
                    t0)
                  t1)
                (fq2_mul_xi t2) in
    let c2 := Pairing.fp2_sub p
                (Pairing.fp2_add p
                  (Pairing.fp2_sub p
                    (Pairing.fp2_mul p (Pairing.fp2_add p a0 a2) (Pairing.fp2_add p b0 b2))
                    t0)
                  t1)
                t2 in
    mk_fq6 c0 c1 c2.

  Definition fq6_zero : Fp6F := mk_fq6 (Pairing.fp2_zero p) (Pairing.fp2_zero p) (Pairing.fp2_zero p).
  Definition fq6_one : Fp6F := mk_fq6 (Pairing.fp2_one p) (Pairing.fp2_zero p) (Pairing.fp2_zero p).

  (** ** Fp12 (ZModTower's [zfp12_*], over F p) *)

  Definition fq12_mul (a b : Fp12F) : Fp12F :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    let t0 := fq6_mul a0 b0 in
    let t1 := fq6_mul a1 b1 in
    let c0 := fq6_add t0 (fq6_mul_v t1) in
    let c1 := fq6_sub (fq6_sub (fq6_mul (fq6_add a0 a1) (fq6_add b0 b1)) t0) t1 in
    (c0, c1).

  Definition fq12_sqr (a : Fp12F) : Fp12F := fq12_mul a a.
  Definition fq12_one : Fp12F := (fq6_one, fq6_zero).
  Definition fq12_zero : Fp12F := (fq6_zero, fq6_zero).
  Definition fq12_add (a b : Fp12F) : Fp12F := (fq6_add (fst a) (fst b), fq6_add (snd a) (snd b)).
  Definition fq12_sub (a b : Fp12F) : Fp12F := (fq6_sub (fst a) (fst b), fq6_sub (snd a) (snd b)).
  Definition fq12_neg (a : Fp12F) : Fp12F := (fq6_neg (fst a), fq6_neg (snd a)).
  Definition fq12_conj (a : Fp12F) : Fp12F := (fst a, fq6_neg (snd a)).

  Fixpoint fq12_pow_aux (base : Fp12F) (exp : Z) (acc : Fp12F) (fuel : nat) : Fp12F :=
    match fuel with
    | O => acc
    | S fuel' =>
      let acc' := if Z.odd exp then fq12_mul acc base else acc in
      let base' := fq12_sqr base in
      fq12_pow_aux base' (Z.div2 exp) acc' fuel'
    end.

  Definition fq12_pow (base : Fp12F) (exp : Z) : Fp12F :=
    fq12_pow_aux base exp fq12_one (Z.to_nat (Z.log2 (Z.abs exp) + 2)).

  (** The final exponentiation of [PairingSpec] with ZModTower's extra operations
      ([zfp12_inv] = power p^12 - 2, [zfp12_frob_p2] = power p^2), at the F level. *)
  Definition fq12_final_exp (r : Z) (f : Fp12F) : Fp12F :=
    let P := Z.pos p in
    let t := fq12_mul (fq12_conj f) (fq12_pow f (P ^ 12 - 2)) in
    fq12_pow (fq12_mul (fq12_pow t (P ^ 2)) t) ((P ^ 4 - P ^ 2 + 1) / r).

End TowerF.

(** * The bridge from ZModTower *)

Section Bridge.
  Context (p : positive).
  Local Notation P := (Z.pos p).
  Local Notation Fp2 := (F p * F p)%type.

  Definition ofZ2 (a : Fp2_Z) : Fp2 := (F.of_Z p (fst a), F.of_Z p (snd a)).
  Definition ofZ6 (a : Fp6_Z) : Fp6F p := ((ofZ2 (fst (fst a)), ofZ2 (snd (fst a))), ofZ2 (snd a)).
  Definition ofZ12 (a : Fp12_Z) : Fp12F p := (ofZ6 (fst a), ofZ6 (snd a)).

  (** ** Fp *)

  Lemma ofZ_add a b : F.of_Z p (zfp_add P a b) = F.add (F.of_Z p a) (F.of_Z p b).
  Proof. unfold zfp_add. rewrite <- F.of_Z_mod. apply F.of_Z_add. Qed.
  Lemma ofZ_sub a b : F.of_Z p (zfp_sub P a b) = F.sub (F.of_Z p a) (F.of_Z p b).
  Proof. unfold zfp_sub. rewrite <- F.of_Z_mod. apply F.of_Z_sub. Qed.
  Lemma ofZ_mul a b : F.of_Z p (zfp_mul P a b) = F.mul (F.of_Z p a) (F.of_Z p b).
  Proof. unfold zfp_mul. rewrite <- F.of_Z_mod. apply F.of_Z_mul. Qed.
  Lemma ofZ_neg a : F.of_Z p (zfp_neg P a) = F.opp (F.of_Z p a).
  Proof.
    unfold zfp_neg. rewrite <- F.of_Z_mod, <- F.of_Z_opp. apply F.eq_of_Z_iff.
    replace (P - a) with (- a + 1 * P) by lia. apply Z_mod_plus_full.
  Qed.

  (** ** Fp2 *)

  Lemma ofZ2_add a b : ofZ2 (zfp2_add P a b) = Pairing.fp2_add p (ofZ2 a) (ofZ2 b).
  Proof. unfold zfp2_add, fp2_add, ofZ2; cbn [fst snd]. now rewrite !ofZ_add. Qed.
  Lemma ofZ2_sub a b : ofZ2 (zfp2_sub P a b) = Pairing.fp2_sub p (ofZ2 a) (ofZ2 b).
  Proof. unfold zfp2_sub, fp2_sub, ofZ2; cbn [fst snd]. now rewrite !ofZ_sub. Qed.
  Lemma ofZ2_neg a : ofZ2 (zfp2_neg P a) = Pairing.fp2_neg p (ofZ2 a).
  Proof. unfold zfp2_neg, fp2_neg, ofZ2; cbn [fst snd]. now rewrite !ofZ_neg. Qed.
  Lemma ofZ2_mul a b : ofZ2 (zfp2_mul P a b) = Pairing.fp2_mul p (ofZ2 a) (ofZ2 b).
  Proof.
    unfold zfp2_mul, fp2_mul, ofZ2; cbn [fst snd].
    now rewrite ofZ_sub, ofZ_add, !ofZ_mul.
  Qed.

  (** ** Fp6 *)

  Context (xiZ : Fp2_Z).
  Local Notation xi := (ofZ2 xiZ).

  Lemma ofZ6_mk c0 c1 c2 : ofZ6 (mk_fp6 c0 c1 c2) = mk_fq6 p (ofZ2 c0) (ofZ2 c1) (ofZ2 c2).
  Proof. reflexivity. Qed.
  Lemma ofZ6_c0 a : ofZ2 (fp6_c0 a) = fq6_c0 p (ofZ6 a). Proof. reflexivity. Qed.
  Lemma ofZ6_c1 a : ofZ2 (fp6_c1 a) = fq6_c1 p (ofZ6 a). Proof. reflexivity. Qed.
  Lemma ofZ6_c2 a : ofZ2 (fp6_c2 a) = fq6_c2 p (ofZ6 a). Proof. reflexivity. Qed.
  Lemma ofZ2_mul_xi a : ofZ2 (zfp2_mul_xi P xiZ a) = fq2_mul_xi p xi (ofZ2 a).
  Proof. unfold zfp2_mul_xi, fq2_mul_xi. apply ofZ2_mul. Qed.

  Ltac push6 :=
    repeat first [ rewrite ofZ6_mk | rewrite ofZ2_add | rewrite ofZ2_sub | rewrite ofZ2_neg
                 | rewrite ofZ2_mul_xi | rewrite ofZ2_mul
                 | rewrite ofZ6_c0 | rewrite ofZ6_c1 | rewrite ofZ6_c2 ].

  Lemma ofZ6_add a b : ofZ6 (zfp6_add P a b) = fq6_add p (ofZ6 a) (ofZ6 b).
  Proof. unfold zfp6_add, fq6_add. push6. reflexivity. Qed.
  Lemma ofZ6_sub a b : ofZ6 (zfp6_sub P a b) = fq6_sub p (ofZ6 a) (ofZ6 b).
  Proof. unfold zfp6_sub, fq6_sub. push6. reflexivity. Qed.
  Lemma ofZ6_neg a : ofZ6 (zfp6_neg P a) = fq6_neg p (ofZ6 a).
  Proof.
    destruct a as [[a0 a1] a2]. unfold zfp6_neg, fq6_neg, ofZ6; cbn [fst snd].
    now rewrite !ofZ2_neg.
  Qed.
  Lemma ofZ6_mul_v a : ofZ6 (zfp6_mul_v P xiZ a) = fq6_mul_v p xi (ofZ6 a).
  Proof. unfold zfp6_mul_v, fq6_mul_v. push6. reflexivity. Qed.
  Lemma ofZ6_mul a b : ofZ6 (zfp6_mul P xiZ a b) = fq6_mul p xi (ofZ6 a) (ofZ6 b).
  Proof. unfold zfp6_mul, fq6_mul. cbv zeta. push6. reflexivity. Qed.

  (** ** Fp12 *)

  Lemma ofZ12_mul a b : ofZ12 (zfp12_mul P xiZ a b) = fq12_mul p xi (ofZ12 a) (ofZ12 b).
  Proof.
    destruct a as [a0 a1], b as [b0 b1].
    unfold zfp12_mul, fq12_mul, fp12_c0, fp12_c1, ofZ12; cbv zeta; cbn [fst snd].
    now rewrite !ofZ6_sub, !ofZ6_add, ofZ6_mul_v, !ofZ6_mul, !ofZ6_add.
  Qed.
  Lemma ofZ12_sqr a : ofZ12 (zfp12_sqr P xiZ a) = fq12_sqr p xi (ofZ12 a).
  Proof. apply ofZ12_mul. Qed.
  Lemma ofZ12_one : ofZ12 zfp12_one = fq12_one p.
  Proof. reflexivity. Qed.
  Lemma ofZ12_conj a : ofZ12 (zfp12_conj P a) = fq12_conj p (ofZ12 a).
  Proof. destruct a as [a0 a1]. unfold zfp12_conj, fq12_conj, ofZ12; cbn [fst snd]. now rewrite ofZ6_neg. Qed.

  Lemma ofZ12_pow_aux fuel base e acc :
    ofZ12 (zfp12_pow_aux P xiZ base e acc fuel)
    = fq12_pow_aux p xi (ofZ12 base) e (ofZ12 acc) fuel.
  Proof.
    revert base e acc; induction fuel as [|fuel IH]; intros base e acc; [reflexivity|].
    cbn [zfp12_pow_aux fq12_pow_aux]. rewrite IH, ofZ12_sqr.
    destruct (Z.odd e); [rewrite ofZ12_mul|]; reflexivity.
  Qed.
  Lemma ofZ12_pow a e : ofZ12 (zfp12_pow P xiZ a e) = fq12_pow p xi (ofZ12 a) e.
  Proof. unfold zfp12_pow, fq12_pow. now rewrite ofZ12_pow_aux. Qed.
  Lemma ofZ12_inv a : ofZ12 (zfp12_inv P xiZ a) = fq12_pow p xi (ofZ12 a) (P ^ 12 - 2).
  Proof. apply ofZ12_pow. Qed.
  Lemma ofZ12_frob_p2 a : ofZ12 (zfp12_frob_p2 P xiZ a) = fq12_pow p xi (ofZ12 a) (P ^ 2).
  Proof. apply ofZ12_pow. Qed.

  (** ** Canonical values: components in [0, p) *)

  Definition canon (z : Z) : Prop := 0 <= z < P.
  Definition canon2 (a : Fp2_Z) : Prop := canon (fst a) /\ canon (snd a).
  Definition canon6 (a : Fp6_Z) : Prop := canon2 (fst (fst a)) /\ canon2 (snd (fst a)) /\ canon2 (snd a).
  Definition canon12 (a : Fp12_Z) : Prop := canon6 (fst a) /\ canon6 (snd a).

  Lemma canon_mod z : canon (z mod P).
  Proof. unfold canon. apply Z.mod_pos_bound. lia. Qed.

  Lemma canon_inj a b : canon a -> canon b -> F.of_Z p a = F.of_Z p b -> a = b.
  Proof.
    unfold canon; intros Ha Hb H. apply F.eq_of_Z_iff in H.
    now rewrite !Z.mod_small in H by lia.
  Qed.
  Lemma canon2_inj a b : canon2 a -> canon2 b -> ofZ2 a = ofZ2 b -> a = b.
  Proof.
    destruct a as [a0 a1], b as [b0 b1]; unfold canon2, ofZ2; cbn [fst snd].
    intros [Ha0 Ha1] [Hb0 Hb1] Heq.
    pose proof (f_equal fst Heq) as E0; pose proof (f_equal snd Heq) as E1; cbn [fst snd] in E0, E1.
    f_equal; apply canon_inj; assumption.
  Qed.
  Lemma canon6_inj a b : canon6 a -> canon6 b -> ofZ6 a = ofZ6 b -> a = b.
  Proof.
    destruct a as [[a0 a1] a2], b as [[b0 b1] b2]; unfold canon6, ofZ6; cbn [fst snd].
    intros (Ha0&Ha1&Ha2) (Hb0&Hb1&Hb2) Heq.
    pose proof (f_equal (fun x => fst (fst x)) Heq) as E0.
    pose proof (f_equal (fun x => snd (fst x)) Heq) as E1.
    pose proof (f_equal snd Heq) as E2; cbn [fst snd] in E0, E1, E2.
    f_equal; [f_equal|]; apply canon2_inj; assumption.
  Qed.
  Lemma canon12_inj a b : canon12 a -> canon12 b -> ofZ12 a = ofZ12 b -> a = b.
  Proof.
    destruct a as [a0 a1], b as [b0 b1]; unfold canon12, ofZ12; cbn [fst snd].
    intros [Ha0 Ha1] [Hb0 Hb1] Heq.
    pose proof (f_equal fst Heq) as E0; pose proof (f_equal snd Heq) as E1; cbn [fst snd] in E0, E1.
    f_equal; apply canon6_inj; assumption.
  Qed.

  Lemma canon2_add a b : canon2 (zfp2_add P a b).
  Proof. split; apply canon_mod. Qed.
  Lemma canon2_sub a b : canon2 (zfp2_sub P a b).
  Proof. split; apply canon_mod. Qed.
  Lemma canon2_mul a b : canon2 (zfp2_mul P a b).
  Proof. split; apply canon_mod. Qed.
  Lemma canon6_add a b : canon6 (zfp6_add P a b).
  Proof. repeat split; apply canon_mod. Qed.
  Lemma canon6_sub a b : canon6 (zfp6_sub P a b).
  Proof. repeat split; apply canon_mod. Qed.
  Lemma canon12_mul a b : canon12 (zfp12_mul P xiZ a b).
  Proof. split; [apply canon6_add | apply canon6_sub]. Qed.

  Lemma canon12_one : 1 < P -> canon12 zfp12_one.
  Proof. intros H; repeat split; cbn; lia. Qed.

  Lemma canon12_pow_aux fuel base e acc :
    canon12 acc -> canon12 (zfp12_pow_aux P xiZ base e acc fuel).
  Proof.
    revert base e acc; induction fuel as [|fuel IH]; intros base e acc Hacc; [exact Hacc|].
    cbn [zfp12_pow_aux]. apply IH. destruct (Z.odd e); [apply canon12_mul | exact Hacc].
  Qed.
  Lemma canon12_pow a e : 1 < P -> canon12 (zfp12_pow P xiZ a e).
  Proof. intros H. apply canon12_pow_aux, canon12_one, H. Qed.

  (** F.to_Z componentwise: a section of [ofZ12] with canonical values. *)
  Definition toZ2 (a : Fp2) : Fp2_Z := (F.to_Z (fst a), F.to_Z (snd a)).
  Definition toZ6 (a : Fp6F p) : Fp6_Z :=
    ((toZ2 (fst (fst a)), toZ2 (snd (fst a))), toZ2 (snd a)).
  Definition toZ12 (a : Fp12F p) : Fp12_Z := (toZ6 (fst a), toZ6 (snd a)).

  Lemma ofZ12_toZ12 a : ofZ12 (toZ12 a) = a.
  Proof.
    destruct a as [[[[? ?] [? ?]] [? ?]] [[[? ?] [? ?]] [? ?]]].
    unfold ofZ12, ofZ6, ofZ2, toZ12, toZ6, toZ2; cbn [fst snd].
    now rewrite !F.of_Z_to_Z.
  Qed.
  Lemma canon12_toZ12 a : canon12 (toZ12 a).
  Proof.
    assert (H : forall x : F p, canon (F.to_Z x)) by (intros x; apply F.to_Z_range; lia).
    destruct a as [[[[? ?] [? ?]] [? ?]] [[[? ?] [? ?]] [? ?]]]; repeat split; apply H.
  Qed.

End Bridge.

(** * The final exponentiation of [PairingSpec] on [zmod_ops] *)

Section FinalExp.
  Context (c : CurveParams) (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z).
  Context (p : positive) (Hp : prime_p c = Z.pos p).
  Local Notation xiZ := (xi_re c, xi_im c).

  Lemma ofZ12_final_exp (f : Fp12_Z) :
    ofZ12 p (PairingSpec.final_exp (zmod_ops c ml)
               (zfp12_conj (prime_p c)) (zfp12_inv (prime_p c) xiZ)
               (zfp12_frob_p2 (prime_p c) xiZ) (zfp12_pow (prime_p c) xiZ)
               (prime_p c) (scalar_r c) f)
    = fq12_final_exp p (ofZ2 p xiZ) (scalar_r c) (ofZ12 p f).
  Proof.
    unfold PairingSpec.final_exp, PairingSpec.final_exp_hard, PairingSpec.final_exp_easy,
      fq12_final_exp.
    change (fp12_mul (zmod_ops c ml)) with (zfp12_mul (prime_p c) xiZ).
    rewrite Hp.
    now rewrite ofZ12_pow, !ofZ12_mul, ofZ12_frob_p2, ofZ12_mul, ofZ12_conj, ofZ12_inv.
  Qed.

  Lemma canon12_final_exp (f : Fp12_Z) : 1 < Z.pos p ->
    canon12 p (PairingSpec.final_exp (zmod_ops c ml)
                 (zfp12_conj (prime_p c)) (zfp12_inv (prime_p c) xiZ)
                 (zfp12_frob_p2 (prime_p c) xiZ) (zfp12_pow (prime_p c) xiZ)
                 (prime_p c) (scalar_r c) f).
  Proof.
    intros H. unfold PairingSpec.final_exp, PairingSpec.final_exp_hard.
    rewrite Hp. now apply canon12_pow.
  Qed.

End FinalExp.
