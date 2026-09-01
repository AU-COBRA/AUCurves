(** * A machine-checkable certificate that a depressed cubic has no root
      modulo a prime.

    [CubicNoRoot.no_root] proves

      forall r : Z,  (r^3 + a r + b) mod p <> 0

    from two [vm_compute]-checkable side conditions: [b mod p <> 0] and
    one equation [mul3 hcert wcert = one3] in the quotient ring
    R = (Z/p)[x] / (x^3 + a x + b), represented here by coefficient
    triples [(c2, c1, c0)] standing for [c2 x^2 + c1 x + c0].

    The argument is the standard root test, run as a certificate rather
    than as a decision procedure:

      - If [r] is a root, then evaluation at [r] is a ring
        homomorphism R -> Z/p ([ev_mul3]).
      - [r^p = r] in Z/p (Fermat), so the element
        [hcert = x^p - x] of R is killed by that homomorphism
        ([ev hcert r = 0]).
      - [wcert] is an explicit inverse of [hcert] in R, so
        [1 = ev (hcert * wcert) r = ev hcert r * ev wcert r = 0],
        which is absurd.

    [hcert] and [wcert] are computed, not supplied: [hcert] is
    [x^p - x] by square-and-multiply in R, and [wcert] is
    [hcert^(p^3 - 2)], which is the inverse of [hcert] exactly when R is
    a field, i.e. exactly when the cubic is irreducible.  The single
    hypothesis [mul3 hcert wcert = one3] therefore both states and
    checks that.  Both are ~O(log p) ring operations on machine-sized
    integers; at a 256-bit prime the whole check is about 1300
    multiplications of coefficient triples.

    Nothing here is curve-specific.  [Bedrock.Group.CurveAdd.P256NoTwoTorsion]
    instantiates it at the NIST P-256 prime and curve constants, which
    is what discharges [RcbProjectiveLaws.no_two_torsion] — the
    statement that the curve has no F-rational point of order two, and
    hence that [Projective.add] is total. *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import Crypto.Util.NumTheoryUtil.

Local Open Scope Z_scope.

Module CubicNoRoot.

Section Certificate.

  Context (p : Z) (Hp : prime p) (az bz : Z).

  Local Notation T := (Z * Z * Z)%type.

  (** [(c2, c1, c0)] denotes [c2 x^2 + c1 x + c0]; [ev u r] is that
      polynomial evaluated at [r], over Z (all reduction mod [p] is
      done by the congruence lemmas, never by [ev]). *)
  Definition ev (u : T) (r : Z) : Z :=
    let '(u2, u1, u0) := u in u2 * r * r + u1 * r + u0.

  (** Multiplication in [(Z/p)[x] / (x^3 + az x + bz)].  The product has
      degree 4; the reduction uses [x^3 = -az x - bz] and hence
      [x^4 = -az x^2 - bz x]. *)
  Definition mul3 (u v : T) : T :=
    let '(a2, a1, a0) := u in
    let '(b2, b1, b0) := v in
    let c4 := a2 * b2 in
    let c3 := a2 * b1 + a1 * b2 in
    let c2 := a2 * b0 + a1 * b1 + a0 * b2 in
    let c1 := a1 * b0 + a0 * b1 in
    let c0 := a0 * b0 in
    ((c2 - c4 * az) mod p,
     (c1 - c3 * az - c4 * bz) mod p,
     (c0 - c3 * bz) mod p).

  Definition sub3 (u v : T) : T :=
    let '(a2, a1, a0) := u in
    let '(b2, b1, b0) := v in
    ((a2 - b2) mod p, (a1 - b1) mod p, (a0 - b0) mod p).

  Definition one3 : T := (0, 0, 1).
  Definition X3 : T := (0, 1, 0).

  Fixpoint pow3 (u : T) (n : positive) : T :=
    match n with
    | xH => u
    | xO m => let q := pow3 u m in mul3 q q
    | xI m => let q := pow3 u m in mul3 (mul3 q q) u
    end.

  (** [x^p - x] in R, and its candidate inverse. *)
  Definition hcert : T := sub3 (pow3 X3 (Z.to_pos p)) X3.
  Definition wcert : T := pow3 hcert (Z.to_pos (p * p * p - 2)).

  (* ---------------------------------------------------------------- *)
  (** ** Congruence plumbing                                           *)
  (* ---------------------------------------------------------------- *)

  Lemma p_pos : 0 < p.
  Proof. pose proof (prime_ge_2 p Hp). lia. Qed.

  Lemma p_gt_1 : 1 < p.
  Proof. pose proof (prime_ge_2 p Hp). lia. Qed.

  Lemma cong_of_sub (x y : Z) : (x - y) mod p = 0 -> x mod p = y mod p.
  Proof.
    intro H. pose proof p_pos.
    apply Z.mod_divide in H; [| lia].
    destruct H as [k Hk].
    replace x with (y + k * p) by lia.
    apply Z_mod_plus_full.
  Qed.

  Lemma cong_mul (x x' y y' : Z) :
    x mod p = x' mod p -> y mod p = y' mod p ->
    (x * y) mod p = (x' * y') mod p.
  Proof.
    intros Hx Hy. rewrite Zmult_mod, Hx, Hy, <- Zmult_mod. reflexivity.
  Qed.

  Lemma ev_mod3 (u2 u1 u0 r : Z) :
    ev (u2 mod p, u1 mod p, u0 mod p) r mod p = ev (u2, u1, u0) r mod p.
  Proof.
    cbv [ev]. apply cong_of_sub. pose proof p_pos.
    rewrite (Z.mod_eq u2 p) by lia.
    rewrite (Z.mod_eq u1 p) by lia.
    rewrite (Z.mod_eq u0 p) by lia.
    match goal with
    | |- ?e mod p = 0 =>
        replace e with
          ((- (u2 / p) * r * r - (u1 / p) * r - (u0 / p)) * p) by ring
    end.
    apply Z_mod_mult.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Evaluation at a root is a ring homomorphism                   *)
  (* ---------------------------------------------------------------- *)

  Lemma mul_root_mod (r : Z) (Hr : (r * r * r + az * r + bz) mod p = 0)
        (k : Z) : ((r * r * r + az * r + bz) * k) mod p = 0.
  Proof. rewrite Zmult_mod, Hr, Z.mul_0_l. apply Zmod_0_l. Qed.

  Lemma ev_mul3 (r : Z) (Hr : (r * r * r + az * r + bz) mod p = 0)
        (u v : T) :
    ev (mul3 u v) r mod p = (ev u r * ev v r) mod p.
  Proof.
    destruct u as [[a2 a1] a0]. destruct v as [[b2 b1] b0].
    cbv [mul3]. rewrite ev_mod3. cbv [ev].
    apply cong_of_sub.
    match goal with
    | |- ?e mod p = 0 =>
        replace e with
          ((r * r * r + az * r + bz)
             * (- (a2 * b2 * r + (a2 * b1 + a1 * b2)))) by ring
    end.
    apply mul_root_mod. exact Hr.
  Qed.

  Lemma ev_sub3 (r : Z) (u v : T) :
    ev (sub3 u v) r mod p = (ev u r - ev v r) mod p.
  Proof.
    destruct u as [[a2 a1] a0]. destruct v as [[b2 b1] b0].
    cbv [sub3]. rewrite ev_mod3. cbv [ev].
    apply cong_of_sub.
    match goal with
    | |- ?e mod p = 0 => replace e with 0 by ring
    end.
    apply Zmod_0_l.
  Qed.

  Lemma zpow_xO (x : Z) (n : positive) :
    x ^ Z.pos (xO n) = x ^ Z.pos n * x ^ Z.pos n.
  Proof.
    replace (Z.pos (xO n)) with (Z.pos n + Z.pos n) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
  Qed.

  Lemma zpow_xI (x : Z) (n : positive) :
    x ^ Z.pos (xI n) = x ^ Z.pos n * x ^ Z.pos n * x.
  Proof.
    replace (Z.pos (xI n)) with (Z.pos n + Z.pos n + 1) by lia.
    rewrite !Z.pow_add_r by lia.
    rewrite Z.pow_1_r. reflexivity.
  Qed.

  Lemma ev_pow3 (r : Z) (Hr : (r * r * r + az * r + bz) mod p = 0)
        (u : T) :
    forall n : positive, ev (pow3 u n) r mod p = (ev u r ^ Z.pos n) mod p.
  Proof.
    induction n as [n IH | n IH | ]; cbn [pow3].
    - rewrite zpow_xI, (ev_mul3 r Hr).
      apply cong_mul; [| reflexivity].
      rewrite (ev_mul3 r Hr). apply cong_mul; exact IH.
    - rewrite zpow_xO, (ev_mul3 r Hr). apply cong_mul; exact IH.
    - rewrite Z.pow_1_r. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** The theorem                                                   *)
  (* ---------------------------------------------------------------- *)

  Theorem no_root
    (Hbz : bz mod p <> 0)
    (Hcert : mul3 hcert wcert = one3) :
    forall r : Z, (r * r * r + az * r + bz) mod p <> 0.
  Proof.
    intros r Hr.
    pose proof p_pos as Hp0. pose proof p_gt_1 as Hp1.
    (** [r] is invertible: otherwise [b] would vanish. *)
    assert (Hrm : r mod p <> 0).
    { intro Hr0.
      assert (Hd : (bz - (r * r * r + az * r + bz)) mod p = 0).
      { replace (bz - (r * r * r + az * r + bz))
          with ((- (r * r + az)) * r) by ring.
        rewrite Zmult_mod, Hr0, Z.mul_0_r. apply Zmod_0_l. }
      apply cong_of_sub in Hd. rewrite Hr in Hd. exact (Hbz Hd). }
    (** Fermat: [r^p = r] in Z/p. *)
    assert (HF : r ^ (p - 1) mod p = 1)
      by (apply (NumTheoryUtil.fermat_little p Hp); exact Hrm).
    assert (Hpow : r ^ p = r * r ^ (p - 1)).
    { replace p with (Z.succ (p - 1)) at 1 by lia.
      apply Z.pow_succ_r. lia. }
    assert (Hrp : r ^ p mod p = r mod p).
    { rewrite Hpow, Zmult_mod, HF, Z.mul_1_r, Zmod_mod. reflexivity. }
    (** [ev X3 r = r], and [Z.to_pos p] is [p]. *)
    assert (HevX : ev X3 r = r) by (cbv [ev X3]; ring).
    assert (Hpos : Z.pos (Z.to_pos p) = p) by (apply Z2Pos.id; lia).
    (** Hence [x^p - x] evaluates to zero. *)
    assert (Hh : ev hcert r mod p = 0).
    { cbv [hcert]. rewrite ev_sub3, Zminus_mod, (ev_pow3 r Hr).
      rewrite HevX, Hpos, Hrp, Z.sub_diag. apply Zmod_0_l. }
    (** But the certificate says it is invertible. *)
    assert (Hone : ev one3 r mod p = 0).
    { rewrite <- Hcert, (ev_mul3 r Hr), Zmult_mod, Hh, Z.mul_0_l.
      apply Zmod_0_l. }
    cbv [ev one3] in Hone.
    replace (0 * r * r + 0 * r + 1) with 1 in Hone by ring.
    rewrite Z.mod_1_l in Hone by lia.
    discriminate Hone.
  Qed.

End Certificate.

End CubicNoRoot.
