(** * Fe25519Pow22523 — verified ref10/dalek [fe_pow22523] addition chain.
 *
 *  The curve25519 base field is [F_p] with [p = 2^255 - 19].  The
 *  Ristretto255 decoder's [sqrt_ratio_m1] is built around the fixed
 *  power [(.)^((p-5)/8)].  Since
 *
 *      (p - 5) / 8 = (2^255 - 24) / 8 = 2^252 - 3,
 *
 *  the standard ref10 / dalek [fe_pow22523] addition chain computes
 *  [z^(2^252 - 3) mod p] using ~250 squarings and ~11 multiplications.
 *
 *  This file gives a pure-[Z] Gallina model [fe25519_pow22523] of that
 *  chain and proves it equals [pow_mod (z mod p) ((p-5)/8) p], with
 *  ZERO new axioms.  A later step wraps the chain into a [rust_cmd_ed]
 *  AST; this file is the algebraic core only.
 *
 *  Proof technique: exponent tracking.  Every intermediate value is of
 *  the form [(z ^ e) mod p] for a concrete [Z] exponent [e].  Two
 *  homomorphism lemmas ([mulm_pow], [sqm_pow]) let us push field
 *  multiply / square into addition / doubling of the exponent, and an
 *  [iter_sq] helper handles the repeated-squaring blocks in one shot.
 *  The kernel therefore never sees a 250-deep nested power term.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Local Open Scope Z_scope.

(** The prime is positive — needed to discharge every [mod] side-condition. *)
Lemma ed25519_p_pos : 0 < ed25519_p.
Proof. unfold ed25519_p. lia. Qed.

(** ** Local re-proof of [pow_mod_pos_correct].
    Copied from [Ristretto_ZMirror.v] so this file's imports stay minimal
    (only [CompressVerified] + Stdlib).  [Ristretto_ZMirror] is heavy. *)
Lemma pow_mod_pos_correct :
  forall (p : positive) (b m : Z),
    0 < m ->
    pow_mod_pos b p m = (b ^ Z.pos p) mod m.
Proof.
  induction p as [p IHp | p IHp | ]; intros b m Hm; simpl pow_mod_pos.
  - rewrite !IHp by exact Hm.
    rewrite Pos2Z.inj_xI.
    rewrite <- Zmult_mod.
    rewrite Z.mul_mod_idemp_l by lia.
    f_equal.
    replace (2 * Z.pos p + 1) with (Z.pos p + Z.pos p + 1) by lia.
    rewrite !Z.pow_add_r by (try lia; apply Pos2Z.pos_is_nonneg).
    rewrite Z.pow_1_r. ring.
  - rewrite !IHp by exact Hm.
    rewrite Pos2Z.inj_xO.
    rewrite <- Zmult_mod.
    f_equal.
    replace (2 * Z.pos p) with (Z.pos p + Z.pos p) by lia.
    rewrite Z.pow_add_r by apply Pos2Z.pos_is_nonneg.
    reflexivity.
  - rewrite Z.pow_1_r. reflexivity.
Qed.

(** [pow_mod] specialised to a nonnegative [Z] exponent. *)
Lemma pow_mod_correct :
  forall (b e m : Z),
    0 < m -> 0 <= e ->
    pow_mod b e m = (b ^ e) mod m.
Proof.
  intros b e m Hm He. destruct e as [|p|p].
  - reflexivity.
  - apply pow_mod_pos_correct; exact Hm.
  - lia.
Qed.

(** ** Field operations mod p. *)
Definition mulm (a b : Z) : Z := (a * b) mod ed25519_p.
Definition sqm  (a   : Z) : Z := (a * a) mod ed25519_p.

(** ** The two homomorphism lemmas — the heart of the proof.
    Multiplying two reduced powers adds exponents; squaring doubles. *)
Lemma mulm_pow :
  forall z a b, 0 <= a -> 0 <= b ->
    mulm ((z ^ a) mod ed25519_p) ((z ^ b) mod ed25519_p)
    = (z ^ (a + b)) mod ed25519_p.
Proof.
  intros z a b Ha Hb. unfold mulm.
  rewrite <- Zmult_mod.
  rewrite Z.pow_add_r by assumption.
  reflexivity.
Qed.

Lemma sqm_pow :
  forall z a, 0 <= a ->
    sqm ((z ^ a) mod ed25519_p) = (z ^ (2 * a)) mod ed25519_p.
Proof.
  intros z a Ha. unfold sqm.
  rewrite <- Zmult_mod.
  replace (2 * a) with (a + a) by ring.
  rewrite Z.pow_add_r by assumption.
  reflexivity.
Qed.

(** ** Repeated-squaring block.
    [iter_sq n a] squares [a] exactly [n] times. *)
Fixpoint iter_sq (n : nat) (a : Z) : Z :=
  match n with
  | O   => a
  | S k => iter_sq k (sqm a)
  end.

(** Squaring [n] times multiplies the exponent by [2^n]. *)
Lemma iter_sq_pow :
  forall n z e, 0 <= e ->
    iter_sq n ((z ^ e) mod ed25519_p)
    = (z ^ (e * 2 ^ (Z.of_nat n))) mod ed25519_p.
Proof.
  induction n as [|k IHk]; intros z e He; simpl iter_sq.
  - rewrite Z.mul_1_r. reflexivity.
  - rewrite sqm_pow by exact He.
    rewrite IHk by lia.
    f_equal. f_equal.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** ** The ref10 / dalek [fe_pow22523] addition chain, as a pure [Z]
    function.  We normalise the input as [z mod p] so every intermediate
    is a reduced power.  Comments give the exponent reached at each step. *)
Definition fe25519_pow22523 (z : Z) : Z :=
  let z  := z mod ed25519_p in
  let t0 := sqm z in                  (* z^2                       *)
  let t1 := sqm (sqm t0) in           (* z^8                       *)
  let t1 := mulm z t1 in              (* z^9                       *)
  let t0 := mulm t0 t1 in             (* z^11                      *)
  let t0 := sqm t0 in                 (* z^22                      *)
  let t0 := mulm t1 t0 in             (* z^31  = z^(2^5 - 1)       *)
  let t1 := iter_sq 5 t0 in           (* z^(2^10 - 2^5)            *)
  let t0 := mulm t1 t0 in             (* z^(2^10 - 1)              *)
  let t1 := iter_sq 10 t0 in          (* z^(2^20 - 2^10)           *)
  let t1 := mulm t1 t0 in             (* z^(2^20 - 1)              *)
  let t2 := iter_sq 20 t1 in          (* z^(2^40 - 2^20)           *)
  let t1 := mulm t2 t1 in             (* z^(2^40 - 1)              *)
  let t1 := iter_sq 10 t1 in          (* z^(2^50 - 2^10)           *)
  let t0 := mulm t1 t0 in             (* z^(2^50 - 1)              *)
  let t1 := iter_sq 50 t0 in          (* z^(2^100 - 2^50)          *)
  let t1 := mulm t1 t0 in             (* z^(2^100 - 1)             *)
  let t2 := iter_sq 100 t1 in         (* z^(2^200 - 2^100)         *)
  let t1 := mulm t2 t1 in             (* z^(2^200 - 1)             *)
  let t1 := iter_sq 50 t1 in          (* z^(2^250 - 2^50)          *)
  let t0 := mulm t1 t0 in             (* z^(2^250 - 1)             *)
  let t0 := sqm (sqm t0) in           (* z^(2^252 - 4)             *)
  let r  := mulm z t0 in              (* z^(2^252 - 3)             *)
  r.

(** ** Each intermediate as a reduced power of [z].
    We track exponents through the chain by a single [unfold] + a
    cascade of [mulm_pow] / [sqm_pow] / [iter_sq_pow] rewrites, each
    side-condition being [0 <= <concrete exponent>] discharged by [lia].
    The final exponent reduces to [2^252 - 3]. *)
Lemma fe25519_pow22523_pow :
  forall z, fe25519_pow22523 z = (z ^ (2 ^ 252 - 3)) mod ed25519_p.
Proof.
  intros z. unfold fe25519_pow22523.
  (* Replace the normalised input by [z^1 mod p]. *)
  replace (z mod ed25519_p) with ((z ^ 1) mod ed25519_p)
    by (rewrite Z.pow_1_r; reflexivity).
  (* Now drive every [let] through the homomorphism lemmas. *)
  repeat first
    [ rewrite mulm_pow by lia
    | rewrite sqm_pow by lia
    | rewrite iter_sq_pow by lia ].
  (* All steps closed; the residual exponent is concrete arithmetic,
     which [f_equal] discharges by reducing it to [2^252 - 3]. *)
  f_equal.
Qed.

(** [(p-5)/8] really is [2^252 - 3]. *)
Lemma exp_pm5_div8 : (ed25519_p - 5) / 8 = 2 ^ 252 - 3.
Proof. unfold ed25519_p. vm_compute. reflexivity. Qed.

(** ** Headline correctness theorem.
    The chain computes the [(p-5)/8] power, expressed via [pow_mod]. *)
Theorem fe25519_pow22523_correct :
  forall z,
    fe25519_pow22523 z
    = pow_mod (z mod ed25519_p) ((ed25519_p - 5) / 8) ed25519_p.
Proof.
  intros z.
  rewrite fe25519_pow22523_pow.
  rewrite pow_mod_correct by (try apply ed25519_p_pos; rewrite exp_pm5_div8; lia).
  rewrite exp_pm5_div8.
  (* Goal: (z ^ (2^252-3)) mod p = ((z mod p) ^ (2^252-3)) mod p. *)
  rewrite Z.mod_pow_l. reflexivity.
Qed.

(** ** Clean rewrite target for consumers:
    the chain equals the literal [(p-5)/8] power mod p. *)
Corollary fe25519_pow22523_pow_pm5_div8 :
  forall z,
    fe25519_pow22523 z = (z ^ ((ed25519_p - 5) / 8)) mod ed25519_p.
Proof.
  intros z. rewrite fe25519_pow22523_pow, exp_pm5_div8. reflexivity.
Qed.
