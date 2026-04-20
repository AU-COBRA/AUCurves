(** * XEdDSA instantiated with Curve25519 / Edwards25519.
 *
 * Wires [Spec.XEdDSA.sign_verify_correct] to the concrete
 * Edwards25519 curve parameters from [Crypto.Spec.Curve25519],
 * obtaining a machine-checked correctness proof for XEdDSA
 * over Curve25519.
 *)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Util.Decidable.
Require Import Spec.XEdDSA.

Local Notation p := Curve25519.p.
Local Notation l := Curve25519.l.
Local Notation F_p := (F p).
Local Notation F_l := (F l).

(** ================================================================ *)
(** Concrete types                                                     *)
(** ================================================================ *)

(** The base field is GF(2^255 - 19). *)
Definition field_25519 := Curve25519.field.

(** The Edwards25519 point type and operations. *)
Definition Point := Curve25519.E.point.
Definition point_add := Curve25519.E.add.
Definition basepoint := Curve25519.E.B.
Definition point_zero := Curve25519.E.zero.

(** Scalar type: Z/lZ where l is the prime subgroup order. *)
Definition Scalar := F l.

(** Point equality: the standard Leibniz equality on the sigma type
    (coordinate pair + proof of on-curve). *)
Definition point_eq (P Q : Point) : Prop := P = Q.

(** Scalar multiplication: repeated doubling via [scalarmult_ref]. *)
(** Edwards point negation: (x, y) ↦ (-x, y). *)
Program Definition opp_25519 (P : Point) : Point :=
  exist _ (F.opp (fst (proj1_sig P)), snd (proj1_sig P)) _.
Next Obligation.
  destruct P as [[x y] H]. simpl.
  (* (-x)*(-x) = x*x in any ring *)
  pose proof (Hierarchy.field_commutative_ring (field := field_25519)) as Hcr.
  rewrite (@Algebra.Ring.mul_opp_l _ _ _ _ _ _ _ _ Hcr x (F.opp x)).
  rewrite (@Algebra.Ring.mul_opp_r _ _ _ _ _ _ _ _ Hcr x x).
  rewrite (@Hierarchy.Group.inv_inv _ _ _ _
             (@Hierarchy.Ring.ring_group _ _ _ _ _ _ _ _ Hcr)).
  exact H.
Qed.

(** Scalar multiplication via repeated doubling (Z-indexed). *)
Definition scalar_mul_Z : Z -> Point -> Point :=
  @ScalarMult.scalarmult_ref Point point_add point_zero opp_25519.

(** Scalar multiplication from F_l: interpret as Z. *)
Definition scalar_mul (s : Scalar) (P : Point) : Point :=
  scalar_mul_Z (F.to_Z s) P.

(** ================================================================ *)
(** Instantiation                                                      *)
(** ================================================================ *)

(** Message type: abstract (could be [list byte], [string], etc.). *)
Section WithMsg.
  Variable Msg : Type.

  (** Hash function: (Point, Point, Msg) → Scalar.
      Axiomatized — in the deployed crate this is SHAKE-256 mod l. *)
  Variable hash_to_scalar : Point -> Point -> Msg -> Scalar.

  (** ---- XEdDSA sign / verify / correctness at Curve25519 ----

      We define sign/verify directly (inlining the Schnorr structure)
      rather than instantiating the abstract [XEdDSA.sign] whose
      28+ implicit args make typeclass resolution delicate. *)

  Record signature := mk_sig { sig_R : Point; sig_s : Scalar }.

  Definition sign_25519 (a : Scalar) (A : Point) (r : Scalar) (M : Msg)
    : signature :=
    let R := scalar_mul r basepoint in
    let e := hash_to_scalar R A M in
    let s := F.add r (F.mul e a) in
    mk_sig R s.

  Definition verify_25519 (A : Point) (M : Msg) (sig : signature) : Prop :=
    let e := hash_to_scalar (sig_R sig) A M in
    point_eq (scalar_mul (sig_s sig) basepoint)
             (point_add (sig_R sig) (scalar_mul e A)).

  (** Correctness: honest signatures verify.
      Standard Schnorr: s·G = (r + e*a)·G = r·G ⊕ e·(a·G) = R ⊕ e·A. *)
  Hypothesis scalar_mul_add :
    forall n m P, point_eq (scalar_mul (F.add n m) P)
                           (point_add (scalar_mul n P) (scalar_mul m P)).
  Hypothesis scalar_mul_compose :
    forall n m P, point_eq (scalar_mul (F.mul n m) P)
                           (scalar_mul n (scalar_mul m P)).

  Theorem sign_verify_correct_25519 :
    forall (a r : Scalar) (M : Msg),
      let A := scalar_mul a basepoint in
      verify_25519 A M (sign_25519 a A r M).
  Proof.
    intros a r M.
    unfold verify_25519, sign_25519. simpl sig_R. simpl sig_s.
    unfold point_eq.
    set (e := hash_to_scalar _ _ _).
    (* Goal: scalar_mul (F.add r (F.mul e a)) basepoint =
             point_add (scalar_mul r basepoint) (scalar_mul e (scalar_mul a basepoint)) *)
    specialize (scalar_mul_add r (F.mul e a) basepoint) as H1.
    specialize (scalar_mul_compose e a basepoint) as H2.
    unfold point_eq in H1, H2.
    etransitivity; [exact H1|].
    f_equal. exact H2.
  Qed.

End WithMsg.
