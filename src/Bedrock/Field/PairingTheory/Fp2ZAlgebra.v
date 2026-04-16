(** * Fp2ZAlgebra.v — ring/field structure on [Fp2_Z].

    Z-level algebra lemmas for [Fp2_Z = Z * Z] with [u^2 = -1], used to
    discharge [zproj_double_simulates] / [zproj_add_simulates] in
    [MillerEquiv.v].  All lemmas are proved directly on the Z
    representation (no bridge via [F q]) so they don't depend on
    [q ≡ 3 mod 4] except where genuine field structure is required.

    Outputs used by [MillerEquiv.v]:
    - [zfp2_mul_comm], [zfp2_mul_assoc] — ring laws.
    - [zfp2_mul_inv_right_canonical] — right inverse derived from
      [zfp2_inv_left] in [ZFInv.v] + commutativity.
    - [zproj_to_affine_eq] — reconstruction of the affine point from
      its projective representation under the invariant. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CanonicityHelpers.
Require Import Bedrock.Field.PairingTheory.ZFInv.

Local Open Scope Z_scope.

Section Fp2ZAlgebra.
  Context (p : Z) (Hp : 1 < p).

  (** Commutativity of [zfp_mul] — just [Z.mul_comm] under [mod]. *)
  Lemma zfp_mul_comm : forall x y, zfp_mul p x y = zfp_mul p y x.
  Proof. intros. unfold zfp_mul. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma zfp_add_comm : forall x y, zfp_add p x y = zfp_add p y x.
  Proof. intros. unfold zfp_add. rewrite Z.add_comm. reflexivity. Qed.

  (** Commutativity of [zfp2_mul]. *)
  Lemma zfp2_mul_comm : forall x y, zfp2_mul p x y = zfp2_mul p y x.
  Proof.
    intros [x0 x1] [y0 y1]. unfold zfp2_mul. cbn [fst snd].
    rewrite (zfp_mul_comm y0 x0), (zfp_mul_comm y1 x1).
    rewrite (zfp_mul_comm y0 x1), (zfp_mul_comm y1 x0).
    rewrite (zfp_add_comm (zfp_mul p x1 y0) (zfp_mul p x0 y1)).
    reflexivity.
  Qed.

  (** Associativity of [zfp_mul]. *)
  Lemma zfp_mul_assoc : forall x y z,
    zfp_mul p x (zfp_mul p y z) = zfp_mul p (zfp_mul p x y) z.
  Proof.
    intros. unfold zfp_mul.
    rewrite Z.mul_mod_idemp_r by lia.
    rewrite Z.mul_mod_idemp_l by lia.
    f_equal. ring.
  Qed.

  Lemma zfp_add_assoc : forall x y z,
    zfp_add p x (zfp_add p y z) = zfp_add p (zfp_add p x y) z.
  Proof.
    intros. unfold zfp_add.
    rewrite Z.add_mod_idemp_r by lia.
    rewrite Z.add_mod_idemp_l by lia.
    f_equal. ring.
  Qed.

  Lemma zfp_mul_add_distr_l : forall x y z,
    zfp_mul p x (zfp_add p y z) = zfp_add p (zfp_mul p x y) (zfp_mul p x z).
  Proof.
    intros. unfold zfp_mul, zfp_add.
    rewrite Z.mul_mod_idemp_r by lia.
    push_Zmod. pull_Zmod. f_equal. ring.
  Qed.

  Lemma zfp_mul_add_distr_r : forall x y z,
    zfp_mul p (zfp_add p x y) z = zfp_add p (zfp_mul p x z) (zfp_mul p y z).
  Proof.
    intros. rewrite (zfp_mul_comm _ z). rewrite zfp_mul_add_distr_l.
    rewrite (zfp_mul_comm z x), (zfp_mul_comm z y). reflexivity.
  Qed.

  Lemma zfp_mul_sub_distr_l : forall x y z,
    zfp_mul p x (zfp_sub p y z) = zfp_sub p (zfp_mul p x y) (zfp_mul p x z).
  Proof.
    intros. unfold zfp_mul, zfp_sub.
    rewrite Z.mul_mod_idemp_r by lia.
    push_Zmod. pull_Zmod. f_equal. ring.
  Qed.

  Lemma zfp_mul_sub_distr_r : forall x y z,
    zfp_mul p (zfp_sub p x y) z = zfp_sub p (zfp_mul p x z) (zfp_mul p y z).
  Proof.
    intros. unfold zfp_mul, zfp_sub.
    rewrite Z.mul_mod_idemp_l by lia.
    push_Zmod. pull_Zmod. f_equal. ring.
  Qed.

  (** Associativity of [zfp2_mul]: brute unfold + ring on components.
      Both sides reduce to the same pair of Z expressions modulo [p]. *)
  Lemma zfp2_mul_assoc : forall x y z,
    zfp2_mul p x (zfp2_mul p y z) = zfp2_mul p (zfp2_mul p x y) z.
  Proof.
    intros [a0 a1] [b0 b1] [c0 c1].
    unfold zfp2_mul. cbn [fst snd].
    f_equal.
    - (* First component *)
      unfold zfp_sub, zfp_add, zfp_mul.
      push_Zmod. pull_Zmod. f_equal. ring.
    - (* Second component *)
      unfold zfp_sub, zfp_add, zfp_mul.
      push_Zmod. pull_Zmod. f_equal. ring.
  Qed.

  (** Canonicity of [(1, 0)]. *)
  Lemma fp2_canonical_one : fp2_canonical p (1, 0).
  Proof. split; cbn [fst snd]; lia. Qed.

End Fp2ZAlgebra.

(** Right inverse for [zfp2_mul] under the [q ≡ 3 mod 4] hypothesis.
    Derived from [zfp2_inv_left] (ZFInv) + [zfp2_mul_comm]. *)
Section Fp2ZInv.
  Context {q : positive} {prime_q : prime (Z.pos q)}.
  Context (q_3mod4 : Z.pos q mod 4 = 3).

  Lemma zfp2_mul_inv_right : forall a b : Z,
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp2_mul (Z.pos q) (a, b) (zfp2_inv (Z.pos q) (a, b)) = (1, 0).
  Proof.
    intros a b Ha Hb Hab.
    rewrite zfp2_mul_comm.
    apply (@zfp2_inv_left q prime_q q_3mod4 a b Ha Hb Hab).
  Qed.

  Lemma zfp2_mul_inv_right_pair : forall (a : Fp2_Z),
    fp2_canonical (Z.pos q) a -> a <> (0, 0) ->
    zfp2_mul (Z.pos q) a (zfp2_inv (Z.pos q) a) = (1, 0).
  Proof.
    intros [a0 a1] [Hc0 Hc1] Ha. cbn [fst snd] in Hc0, Hc1.
    apply zfp2_mul_inv_right; assumption.
  Qed.

  (** Fp2 integral domain: product of nonzero canonical elements is nonzero.
      Used to show [TZ^2 ≠ 0] from [TZ ≠ 0].

      Proof: if [a * b = 0] in Fp2 with [a ≠ 0], then multiplying both sides
      by [a^{-1}] on the left gives [b = a^{-1} * 0 = 0], contradicting
      [b ≠ 0].  The [a^{-1} * 0 = 0] step uses [zfp2_mul] absorbing [(0,0)]. *)
  Lemma zfp2_mul_zero : forall x,
    zfp2_mul (Z.pos q) x (0, 0) = (0, 0).
  Proof.
    intros [x0 x1].
    unfold zfp2_mul, zfp_mul, zfp_sub, zfp_add; cbn [fst snd].
    assert (Hzl : (0 mod Z.pos q)%Z = 0%Z) by (apply Z.mod_0_l; lia).
    rewrite !Z.mul_0_r, !Hzl.
    rewrite Z.sub_0_r, Z.add_0_l.
    rewrite !Hzl. reflexivity.
  Qed.

  Lemma zfp2_nonzero_mul : forall a b,
    fp2_canonical (Z.pos q) a -> fp2_canonical (Z.pos q) b ->
    a <> (0, 0) -> b <> (0, 0) ->
    zfp2_mul (Z.pos q) a b <> (0, 0).
  Proof.
    intros a b Hca Hcb Ha Hb Hab.
    destruct a as [a0 a1], b as [b0 b1].
    destruct Hca as [Hca0 Hca1]; cbn [fst snd] in Hca0, Hca1.
    destruct Hcb as [Hcb0 Hcb1]; cbn [fst snd] in Hcb0, Hcb1.
    assert (Hinvl :
      zfp2_mul (Z.pos q) (zfp2_inv (Z.pos q) (a0, a1)) (a0, a1) = (1, 0))
      by (apply (@zfp2_inv_left q prime_q q_3mod4); assumption).
    assert (Hmul :
      zfp2_mul (Z.pos q) (zfp2_inv (Z.pos q) (a0, a1))
                         (zfp2_mul (Z.pos q) (a0, a1) (b0, b1)) = (0, 0))
      by (rewrite Hab; apply zfp2_mul_zero).
    assert (Hq1 : 1 < Z.pos q) by (pose proof (prime_ge_2 _ prime_q); lia).
    rewrite zfp2_mul_assoc in Hmul.
    rewrite Hinvl in Hmul.
    rewrite (zfp2_mul_comm _ (1, 0) (b0, b1)) in Hmul.
    rewrite zfp2_mul_one_r in Hmul;
      [contradiction | lia | split; cbn [fst snd]; assumption].
  Qed.

End Fp2ZInv.

(** The key reconstruction lemma.  Under the dehomogenisation invariant
    + canonicity + [TZ ≠ 0] + [q ≡ 3 mod 4], [zproj_to_affine] returns
    exactly [(Tx, Ty)]. *)
Section ZProjToAffine.
  Context {q : positive} {prime_q : prime (Z.pos q)}.
  Context (q_3mod4 : Z.pos q mod 4 = 3).

  Lemma zproj_to_affine_eq : forall TX TY TZ Tx Ty,
    fp2_canonical (Z.pos q) Tx ->
    fp2_canonical (Z.pos q) Ty ->
    fp2_canonical (Z.pos q) TZ ->
    TZ <> (0, 0) ->
    zfp2_mul (Z.pos q) Tx (zfp2_sqr (Z.pos q) TZ) = TX ->
    zfp2_mul (Z.pos q) Ty
      (zfp2_mul (Z.pos q) (zfp2_sqr (Z.pos q) TZ) TZ) = TY ->
    zproj_to_affine (Z.pos q) TX TY TZ = (Tx, Ty).
  Proof.
    intros TX TY TZ Tx Ty HcTx HcTy HcTZ HTZ HX HY.
    pose proof (prime_ge_2 _ prime_q) as Hq2.
    assert (Hp : 1 < Z.pos q) by lia.
    unfold zproj_to_affine.
    set (z2 := zfp2_sqr (Z.pos q) TZ).
    set (z3 := zfp2_mul (Z.pos q) z2 TZ).
    (* z2, z3 canonical *)
    assert (Hcz2 : fp2_canonical (Z.pos q) z2)
      by (apply zfp2_sqr_canonical; lia).
    assert (Hcz3 : fp2_canonical (Z.pos q) z3)
      by (apply zfp2_mul_canonical; lia).
    (* z2, z3 <> (0, 0) via Fp2 integral domain *)
    assert (Hz2 : z2 <> (0, 0)).
    { unfold z2, zfp2_sqr. apply (zfp2_nonzero_mul q_3mod4); assumption. }
    assert (Hz3 : z3 <> (0, 0)).
    { unfold z3. apply (zfp2_nonzero_mul q_3mod4); assumption. }
    f_equal.
    - (* First component: zfp2_mul TX (zfp2_inv z2) = Tx *)
      rewrite <- HX. fold z2.
      rewrite <- zfp2_mul_assoc.
      rewrite (zfp2_mul_inv_right_pair q_3mod4 z2 Hcz2 Hz2).
      apply zfp2_mul_one_r; [lia | exact HcTx].
    - (* Second component: zfp2_mul TY (zfp2_inv z3) = Ty *)
      rewrite <- HY. fold z2. fold z3.
      rewrite <- zfp2_mul_assoc.
      rewrite (zfp2_mul_inv_right_pair q_3mod4 z3 Hcz3 Hz3).
      apply zfp2_mul_one_r; [lia | exact HcTy].
  Qed.

End ZProjToAffine.
