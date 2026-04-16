(** * Fp2ZAlgebraBeta.v — beta-parametric ring/field laws on [Fp2_Z].

    Generalises [Fp2ZAlgebra] to curves where [Fp2 = Fp[u]/(u² - beta)]
    for arbitrary quadratic nonresidue [beta].  Needed by BLS12-377
    which has [beta = -5] (not [-1]).

    Structure parallels [Fp2ZAlgebra]:
    - Ring laws ([comm], [assoc], [distrib]) for arbitrary [beta].
    - [zfp2_mul_beta_one_r] — right identity (canonical input).
    - [zfp2_mul_inv_right_beta] — right inverse under the nonresidue
      hypothesis (deferred — requires a beta-aware [zfp2_inv_left_beta]).
    - [zproj_to_affine_eq_beta] — reconstruction lemma, deferred. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CanonicityHelpers.

Local Open Scope Z_scope.

Section Fp2ZAlgebraBeta.
  Context (p : Z) (beta : Z).

  (** Commutativity of [zfp2_mul_beta] — pure ring, no constraint on beta. *)
  Lemma zfp2_mul_beta_comm : forall x y,
    zfp2_mul_beta p beta x y = zfp2_mul_beta p beta y x.
  Proof.
    intros [x0 x1] [y0 y1]. unfold zfp2_mul_beta. cbn [fst snd].
    unfold zfp_mul, zfp_add.
    f_equal.
    - rewrite (Z.mul_comm y0 x0), (Z.mul_comm y1 x1). reflexivity.
    - rewrite (Z.mul_comm y0 x1), (Z.mul_comm y1 x0).
      rewrite (Z.add_comm (x1 * y0 mod p) (x0 * y1 mod p)).
      reflexivity.
  Qed.

  (** Associativity of [zfp2_mul_beta] — brute ring on components. *)
  Lemma zfp2_mul_beta_assoc : forall x y z,
    zfp2_mul_beta p beta x (zfp2_mul_beta p beta y z)
      = zfp2_mul_beta p beta (zfp2_mul_beta p beta x y) z.
  Proof.
    intros [a0 a1] [b0 b1] [c0 c1].
    unfold zfp2_mul_beta. cbn [fst snd].
    unfold zfp_add, zfp_mul.
    f_equal.
    - push_Zmod. pull_Zmod. f_equal. ring.
    - push_Zmod. pull_Zmod. f_equal. ring.
  Qed.

  (** [(a, b) * (1, 0) = (a, b)] for canonical [(a, b)], any beta. *)
  Lemma zfp2_mul_beta_one_r : forall a,
    1 < p ->
    fp2_canonical p a ->
    zfp2_mul_beta p beta a (1, 0) = a.
  Proof.
    intros [a0 a1] Hp [Hc0 Hc1]. cbn [fst snd] in Hc0, Hc1.
    unfold zfp2_mul_beta. cbn [fst snd].
    unfold zfp_mul, zfp_add.
    f_equal.
    - rewrite Z.mul_1_r. rewrite Z.mul_0_r, Zmod_0_l.
      rewrite Z.mul_0_r, Zmod_0_l.
      rewrite Z.add_0_r. rewrite Z.mod_mod by lia.
      apply Z.mod_small; lia.
    - rewrite Z.mul_0_r, Zmod_0_l.
      rewrite Z.mul_1_r.
      rewrite Z.add_0_l. rewrite Z.mod_mod by lia.
      apply Z.mod_small; lia.
  Qed.

  (** Output canonicity: every [zfp2_mul_beta] result has components in [[0, p)]. *)
  Lemma zfp2_mul_beta_canonical : forall x y,
    0 < p ->
    fp2_canonical p (zfp2_mul_beta p beta x y).
  Proof.
    intros [x0 x1] [y0 y1] Hp. unfold zfp2_mul_beta, fp2_canonical.
    cbn [fst snd].
    split; unfold zfp_add; apply Z.mod_pos_bound; lia.
  Qed.

  Lemma zfp2_sqr_beta_canonical : forall x,
    0 < p -> fp2_canonical p (zfp2_sqr_beta p beta x).
  Proof. intros. apply zfp2_mul_beta_canonical; assumption. Qed.

End Fp2ZAlgebraBeta.
