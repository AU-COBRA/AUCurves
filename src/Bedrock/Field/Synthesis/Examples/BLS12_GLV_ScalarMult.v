(** * BLS12-381 GLV Shamir scalar multiplication.

    Defines Shamir's trick for simultaneous double-scalar multiplication
    and proves the GLV main theorem: for P in G1[r],
      [k]P = [k1]P + [k2]φ(P)
    where (k1, k2) = glv_decompose(k). *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Monoid.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Util.ZUtil.Peano.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_ScalarReduce.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_Decompose.
Require Bedrock.Field.Synthesis.Examples.BLS12_Endomorphism.
Local Open Scope Z_scope.

(** ** Z bit decomposition helper *)

Definition b2z (b : bool) : Z := if b then 1 else 0.

Lemma Z_mod_pow2_succ : forall k n,
  0 <= k -> 0 <= n ->
  k mod 2 ^ (n + 1) = k mod 2 ^ n + b2z (Z.testbit k n) * 2 ^ n.
Proof.
  intros k n Hk Hn.
  assert (Hpow : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  set (q := k / 2 ^ n).
  set (r := k mod 2 ^ n).
  assert (Hkqr : k = 2 ^ n * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (Hr : 0 <= r < 2 ^ n) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Hqd : q = 2 * (q / 2) + q mod 2) by (apply Z.div_mod; lia).
  assert (Hqm : 0 <= q mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  (* Relate b2z(testbit) to (k/2^n) mod 2 *)
  assert (Hb : b2z (Z.testbit k n) = q mod 2).
  { subst q. unfold b2z.
    destruct (Z.testbit k n) eqn:Htb.
    - apply Z.testbit_true in Htb; lia.
    - apply Z.testbit_false in Htb; lia. }
  rewrite Hb.
  (* Now: k mod 2^(n+1) = r + (q mod 2) * 2^n *)
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
  rewrite Hkqr.
  replace (2 ^ n * q + r) with (2 ^ n * (2 * (q / 2)) + (r + q mod 2 * 2 ^ n))
    by lia.
  rewrite Z.mul_assoc.
  replace (2 ^ n * 2 * (q / 2) + (r + q mod 2 * 2 ^ n))
    with ((r + q mod 2 * 2 ^ n) + (q / 2) * (2 ^ n * 2)) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. nia.
Qed.

(* ================================================================== *)
(** * Part 1: Shamir's trick Gallina specification                     *)
(* ================================================================== *)

Section ShamirMult.
  Context {G eq add zero opp} `{groupG : @group G eq add zero opp}.
  Context {mul : Z -> G -> G} `{mul_is_sm : @is_scalarmult G eq add zero opp mul}.
  Context {add_comm : @is_commutative G eq add}.
  Local Infix "=" := eq : type_scope.
  Local Infix "+" := add.
  Local Infix "*" := mul.

  (** Shamir's trick: MSB-first simultaneous double-and-add.
      Processes bits from position [bits-1] down to 0. *)
  Fixpoint shamir_mult (bits : nat) (k1 k2 : Z) (P Q acc : G) : G :=
    match bits with
    | O => acc
    | S n =>
      let acc' := acc + acc in                           (* double *)
      let acc'' := acc' + b2z (Z.testbit k1 (Z.of_nat n)) * P in  (* cond add P *)
      let acc''' := acc'' + b2z (Z.testbit k2 (Z.of_nat n)) * Q in (* cond add Q *)
      shamir_mult n k1 k2 P Q acc'''
    end.

  (** ** Auxiliary lemmas *)

  (** Scalar multiplication distributes over group addition (right).
      Requires the group to be commutative (abelian). *)
  Lemma scalarmult_add_r : forall n (P Q : G),
    n * (P + Q) = n * P + n * Q.
  Proof.
    induction n using Z.peano_rect_strong; intros;
      rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by lia.
    - rewrite !scalarmult_0_l, left_identity; reflexivity.
    - rewrite !scalarmult_succ_l, IHn.
      rewrite <- !associative.
      enough (H1 : Q + (n * P + n * Q) = n * P + (Q + n * Q))
        by (rewrite H1; reflexivity).
      rewrite (associative Q (n * P) (n * Q)).
      rewrite (commutative Q (n * P)).
      rewrite <- (associative (n * P) Q (n * Q)).
      reflexivity.
    - rewrite !scalarmult_pred_l, IHn.
      rewrite Group.inv_op.
      rewrite (commutative (opp Q) (opp P)).
      rewrite <- !associative.
      enough (H1 : opp Q + (n * P + n * Q) = n * P + (opp Q + n * Q))
        by (rewrite H1; reflexivity).
      rewrite (associative (opp Q) (n * P) (n * Q)).
      rewrite (commutative (opp Q) (n * P)).
      rewrite <- (associative (n * P) (opp Q) (n * Q)).
      reflexivity.
  Qed.

  (** ** Generalized accumulator invariant.

      After processing [bits] iterations, the initial accumulator [acc]
      has been doubled [bits] times (contributing [2^bits * acc]) and
      the bits of k1, k2 below position [bits] contribute
      [(k1 mod 2^bits)*P + (k2 mod 2^bits)*Q]. *)

  Lemma shamir_mult_acc : forall bits k1 k2 (P Q acc : G),
    0 <= k1 -> 0 <= k2 ->
    shamir_mult bits k1 k2 P Q acc
    = (2 ^ Z.of_nat bits) * acc
      + (k1 mod 2 ^ Z.of_nat bits) * P
      + (k2 mod 2 ^ Z.of_nat bits) * Q.
  Proof.
    induction bits as [|n IHn]; intros k1 k2 P Q acc Hk1 Hk2.
    - (* Base case: bits = 0 *)
      simpl. change (2 ^ 0) with 1.
      rewrite Z.mod_1_r, Z.mod_1_r.
      rewrite !scalarmult_0_l.
      rewrite scalarmult_1_l, !right_identity.
      reflexivity.
    - (* Inductive case: bits = S n *)
      simpl shamir_mult.
      rewrite IHn by lia.
      (* Bit decomposition: k mod 2^(S n) = k mod 2^n + b2z(testbit k n) * 2^n *)
      assert (Hk1_decomp := Z_mod_pow2_succ k1 (Z.of_nat n) Hk1 ltac:(lia)).
      assert (Hk2_decomp := Z_mod_pow2_succ k2 (Z.of_nat n) Hk2 ltac:(lia)).
      replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) in * by lia.
      rewrite Hk1_decomp, Hk2_decomp.
      rewrite !scalarmult_add_l.
      (* 2^n*acc + 2^n*acc = 2^(S n)*acc *)
      rewrite !scalarmult_add_r.
      rewrite <- (scalarmult_add_l (2 ^ Z.of_nat n) (2 ^ Z.of_nat n) acc).
      replace (2 ^ Z.of_nat n + 2 ^ Z.of_nat n)%Z with (2 ^ Z.of_nat (S n))
        by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
      (* 2^n * (b2z * P) = (b2z * 2^n) * P *)
      rewrite !(scalarmult_assoc (2 ^ Z.of_nat n)).
      (* Rearrange the sum *)
      rewrite <- !associative.
      set (a := b2z (Z.testbit k1 (Z.of_nat n)) * 2 ^ Z.of_nat n * P).
      set (b := b2z (Z.testbit k2 (Z.of_nat n)) * 2 ^ Z.of_nat n * Q).
      set (c := k1 mod 2 ^ Z.of_nat n * P).
      set (d := k2 mod 2 ^ Z.of_nat n * Q).
      (* LHS inner: a + (b + (c + d)), RHS inner: c + (a + (d + b)) *)
      rewrite (associative b c d).
      rewrite (commutative b c).
      rewrite <- (associative c b d).
      rewrite (associative a c (b + d)).
      rewrite (commutative a c).
      rewrite <- (associative c a (b + d)).
      rewrite (commutative b d).
      reflexivity.
  Qed.

  (** ** Main correctness theorem for Shamir's trick. *)

  Lemma shamir_mult_correct : forall bits k1 k2 P Q,
    0 <= k1 < 2 ^ (Z.of_nat bits) ->
    0 <= k2 < 2 ^ (Z.of_nat bits) ->
    shamir_mult bits k1 k2 P Q zero = k1 * P + k2 * Q.
  Proof.
    intros bits k1 k2 P Q Hk1 Hk2.
    rewrite shamir_mult_acc by lia.
    rewrite scalarmult_zero_r, left_identity.
    rewrite !Z.mod_small by lia.
    reflexivity.
  Qed.

  (** ** Single-scalar specializations *)

  Lemma shamir_mult_k2_zero : forall bits k1 P Q,
    0 <= k1 < 2 ^ (Z.of_nat bits) ->
    shamir_mult bits k1 0 P Q zero = k1 * P.
  Proof.
    intros bits k1 P Q Hk1.
    assert (H02 : 0 <= 0 < 2 ^ Z.of_nat bits)
      by (split; [lia | apply Z.pow_pos_nonneg; lia]).
    rewrite shamir_mult_correct by lia.
    rewrite scalarmult_0_l, right_identity.
    reflexivity.
  Qed.

  Lemma shamir_mult_k1_zero : forall bits k2 P Q,
    0 <= k2 < 2 ^ (Z.of_nat bits) ->
    shamir_mult bits 0 k2 P Q zero = k2 * Q.
  Proof.
    intros bits k2 P Q Hk2.
    assert (H02 : 0 <= 0 < 2 ^ Z.of_nat bits)
      by (split; [lia | apply Z.pow_pos_nonneg; lia]).
    rewrite shamir_mult_correct by lia.
    rewrite scalarmult_0_l, left_identity.
    reflexivity.
  Qed.

  (* ================================================================== *)
  (** * Part 2: GLV main theorem                                         *)
  (* ================================================================== *)

  Context {phi : G -> G}.
  Context {phi_hom : @Monoid.is_homomorphism G eq add G eq add phi}.

  (** For P in G1[r] with phi(P) = [lambda]P, the GLV decomposition gives:
      [k]P = [k1]P + [k2]phi(P) via Shamir's trick with 129 iterations. *)
  Theorem glv_scalarmult_correct : forall k P,
    0 <= k < bls12_r ->
    bls12_r * P = zero ->
    bls12_lambda * P = phi P ->
    let '(k1, k2) := glv_decompose k in
    shamir_mult 129 k1 k2 P (phi P) zero = k * P.
  Proof.
    intros k P0 Hk Horder Hphi.
    unfold glv_decompose.
    set (k1 := k mod bls12_lambda).
    set (k2 := k / bls12_lambda).
    pose proof (glv_decompose_correct k ltac:(lia)) as Hdecomp.
    unfold glv_decompose in Hdecomp. fold k1 k2 in Hdecomp.
    pose proof (glv_k1_bound k ltac:(lia)) as Hk1.
    unfold glv_decompose in Hk1. fold k1 in Hk1.
    pose proof (glv_k2_bound k Hk) as Hk2.
    unfold glv_decompose in Hk2. fold k2 in Hk2.
    pose proof bls12_lambda_128bits as Hlam128.
    assert (Hk1_129 : 0 <= k1 < 2 ^ 129) by lia.
    assert (Hk2_129 : 0 <= k2 < 2 ^ 129) by lia.
    rewrite shamir_mult_correct by (change (Z.of_nat 129) with 129; lia).
    rewrite <- Hphi.
    rewrite scalarmult_assoc.
    rewrite <- scalarmult_add_l.
    replace (k1 + bls12_lambda * k2)%Z with k by lia.
    reflexivity.
  Qed.

  (** Corollary: GLV with prior scalar reduction for arbitrary-size k. *)
  Corollary glv_scalarmult_reduced : forall k P,
    0 <= k ->
    bls12_r * P = zero ->
    bls12_lambda * P = phi P ->
    let k' := k mod bls12_r in
    let '(k1, k2) := glv_decompose k' in
    shamir_mult 129 k1 k2 P (phi P) zero = k * P.
  Proof.
    intros k P0 Hk Horder Hphi.
    pose proof bls12_r_pos.
    pose proof bls12_r_nonzero.
    pose proof (scalarmult_mod_order bls12_r P0 ltac:(auto) Horder k) as Hmod.
    assert (Hkr : 0 <= k mod bls12_r < bls12_r) by (apply Z.mod_pos_bound; lia).
    pose proof (glv_scalarmult_correct (k mod bls12_r) P0 Hkr Horder Hphi) as Hglv.
    unfold glv_decompose in Hglv |- *.
    rewrite Hglv.
    exact Hmod.
  Qed.

End ShamirMult.

(* ================================================================== *)
(** * Part 3: Bedrock2 function body -- TODO                           *)
(* ================================================================== *)

(** The bedrock2 implementation of GLV Shamir scalar multiplication
    would be structured as:

    func bls12_glv_scmul(out_x, out_y, out_z, P_x, P_y, P_z, k) {
      // Step 1: Reduce scalar mod r (conditional subtraction)
      scalar_reduce(k_reduced, k)

      // Step 2: GLV decomposition (k = k1 + k2*lambda via division)
      k1 = k_reduced mod lambda    // low 128 bits
      k2 = k_reduced / lambda      // high ~128 bits

      // Step 3: Precompute phi(P) = (omega * P_x, P_y, P_z)
      field_mul(phi_x, omega_const, P_x)
      copy(phi_y, P_y)
      copy(phi_z, P_z)

      // Step 4: Shamir's trick -- 129 iterations
      out = O  // identity point
      for i from 128 downto 0:
        curve_double(out, out)
        if testbit(k1, i): curve_add(out, out, P)
        if testbit(k2, i): curve_add(out, out, phi_P)
    }

    Prerequisites:
    - curve_add and curve_double with bedrock2 WP proofs
    - field_mul for omega application
    - scalar bit extraction (from BignumShift.v)
    - Existing pattern from BLS12_MillerLoop.v for wp_while loops *)
