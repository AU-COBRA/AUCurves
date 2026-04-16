(** * FProjBridge.v — bridge from [F q]-level proofs to [Fp2_Z]-level admits.

    The symbolic algebra of [zproj_double_simulates] and
    [zproj_add_simulates] is proved in [FProjAlgebra.v] over [F q]
    (the prime-field type).  The [zproj_*] admits in [MillerEquiv.v]
    are stated over [Fp2_Z = Z * Z].  This file provides the
    conversion and the round-trip / homomorphism lemmas that lift
    the F-level theorems to the Z-level, closing the admits.

    The conversion is componentwise:
      [fp2z_to_F  : Fp2_Z -> F q * F q]
      [fp2F_to_Z  : F q * F q -> Fp2_Z]
    and is an isomorphism between canonical [Fp2_Z] values and
    arbitrary [F q * F q] values. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CanonicityHelpers.

Local Open Scope Z_scope.

Section FProjBridge.
  Context (q : positive).

  Definition fp2z_to_F (x : Fp2_Z) : F q * F q :=
    (F.of_Z q (fst x), F.of_Z q (snd x)).

  Definition fp2F_to_Z (x : F q * F q) : Fp2_Z :=
    (F.to_Z (fst x), F.to_Z (snd x)).

  Lemma fp2z_to_F_to_Z x :
    fp2_canonical (Z.pos q) x ->
    fp2F_to_Z (fp2z_to_F x) = x.
  Proof.
    destruct x as [x0 x1]. intros [H0 H1]; cbn [fst snd] in H0, H1.
    unfold fp2z_to_F, fp2F_to_Z. cbn [fst snd].
    rewrite !F.to_Z_of_Z, !Z.mod_small by lia.
    reflexivity.
  Qed.

  Lemma fp2F_to_Z_to_F x :
    fp2z_to_F (fp2F_to_Z x) = x.
  Proof.
    destruct x as [x0 x1].
    unfold fp2z_to_F, fp2F_to_Z. cbn [fst snd].
    rewrite !F.of_Z_to_Z. reflexivity.
  Qed.

  (** Homomorphism lemmas — [zfp*] on canonical [Fp2_Z] inputs
      matches [F]-level arithmetic after the conversion. *)

  Lemma F_of_Z_mod (x : Z) :
    F.of_Z q (x mod Z.pos q) = F.of_Z q x.
  Proof.
    apply F.eq_to_Z_iff. rewrite !F.to_Z_of_Z.
    rewrite Z.mod_mod by lia. reflexivity.
  Qed.

  Lemma zfp_add_to_F (x y : Z) :
    F.of_Z q (zfp_add (Z.pos q) x y) = (F.of_Z q x + F.of_Z q y)%F.
  Proof.
    unfold zfp_add. rewrite F_of_Z_mod. apply F.of_Z_add.
  Qed.

  Lemma zfp_sub_to_F (x y : Z) :
    F.of_Z q (zfp_sub (Z.pos q) x y) = (F.of_Z q x - F.of_Z q y)%F.
  Proof.
    unfold zfp_sub. rewrite F_of_Z_mod. apply F.of_Z_sub.
  Qed.

  Lemma zfp_mul_to_F (x y : Z) :
    F.of_Z q (zfp_mul (Z.pos q) x y) = (F.of_Z q x * F.of_Z q y)%F.
  Proof.
    unfold zfp_mul. rewrite F_of_Z_mod. apply F.of_Z_mul.
  Qed.

  Lemma zfp2_mul_to_F (x y : Fp2_Z) :
    fp2z_to_F (zfp2_mul (Z.pos q) x y) =
    let '(a, b) := fp2z_to_F x in
    let '(c, d) := fp2z_to_F y in
    ((a * c - b * d)%F, (a * d + b * c)%F).
  Proof.
    destruct x as [x0 x1]; destruct y as [y0 y1].
    unfold fp2z_to_F, zfp2_mul. cbn [fst snd].
    rewrite zfp_sub_to_F, !zfp_mul_to_F.
    rewrite zfp_add_to_F, !zfp_mul_to_F.
    reflexivity.
  Qed.

  Lemma zfp2_sqr_to_F (x : Fp2_Z) :
    fp2z_to_F (zfp2_sqr (Z.pos q) x) =
    let '(a, b) := fp2z_to_F x in
    ((a * a - b * b)%F, (a * b + b * a)%F).
  Proof. apply zfp2_mul_to_F. Qed.

  Lemma zfp2_add_to_F (x y : Fp2_Z) :
    fp2z_to_F (zfp2_add (Z.pos q) x y) =
    let '(a, b) := fp2z_to_F x in
    let '(c, d) := fp2z_to_F y in
    ((a + c)%F, (b + d)%F).
  Proof.
    destruct x as [x0 x1]; destruct y as [y0 y1].
    unfold fp2z_to_F, zfp2_add. cbn [fst snd].
    rewrite !zfp_add_to_F. reflexivity.
  Qed.

  Lemma zfp2_sub_to_F (x y : Fp2_Z) :
    fp2z_to_F (zfp2_sub (Z.pos q) x y) =
    let '(a, b) := fp2z_to_F x in
    let '(c, d) := fp2z_to_F y in
    ((a - c)%F, (b - d)%F).
  Proof.
    destruct x as [x0 x1]; destruct y as [y0 y1].
    unfold fp2z_to_F, zfp2_sub. cbn [fst snd].
    rewrite !zfp_sub_to_F. reflexivity.
  Qed.

  (** [proj_affine_rel] at the Z-level factors through [fp2z_to_F].
      Applying [fp2z_to_F] to both sides of
      [zfp2_mul Tx (zfp2_sqr TZ) = TX] and using the homomorphism
      lemmas [zfp2_mul_to_F] / [zfp2_sqr_to_F] gives the F-level
      equation, which is what [FProjAlgebra] needs. *)

  Lemma proj_invariant_to_F (Tx TZ TX : Fp2_Z) :
    zfp2_mul (Z.pos q) Tx (zfp2_sqr (Z.pos q) TZ) = TX ->
    let '(tx_r, tx_i) := fp2z_to_F Tx in
    let '(tz_r, tz_i) := fp2z_to_F TZ in
    let '(TX_r, TX_i) := fp2z_to_F TX in
    let tz2_r := (tz_r * tz_r - tz_i * tz_i)%F in
    let tz2_i := (tz_r * tz_i + tz_i * tz_r)%F in
    (tx_r * tz2_r - tx_i * tz2_i = TX_r)%F
    /\ (tx_r * tz2_i + tx_i * tz2_r = TX_i)%F.
  Proof.
    intro H.
    (* Apply fp2z_to_F to both sides of H. *)
    assert (HF : fp2z_to_F (zfp2_mul (Z.pos q) Tx (zfp2_sqr (Z.pos q) TZ))
                 = fp2z_to_F TX) by (rewrite H; reflexivity).
    rewrite zfp2_mul_to_F in HF.
    rewrite zfp2_sqr_to_F in HF.
    (* HF is now a pair equation. *)
    destruct (fp2z_to_F Tx) as [a b] eqn:Htx.
    destruct (fp2z_to_F TZ) as [c d] eqn:Htz.
    destruct (fp2z_to_F TX) as [e g] eqn:HtX.
    cbn in HF.
    injection HF as HFr HFi.
    split; assumption.
  Qed.

End FProjBridge.
