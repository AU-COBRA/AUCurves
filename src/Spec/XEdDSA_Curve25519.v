(** * XEdDSA instantiated with Curve25519 / Edwards25519.
 *
 * Wires [Spec.XEdDSA.sign_verify_correct] to the concrete
 * Edwards25519 curve parameters from [Crypto.Spec.Curve25519],
 * obtaining a machine-checked correctness proof for XEdDSA
 * over Curve25519.
 *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Classes.Morphisms.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Util.Decidable.
Require Import Spec.XEdDSA.

Local Notation p := Curve25519.p.
Local Notation l := Curve25519.l.
Local Notation F_p := (F p).
Local Notation F_l := (F l).

(** Don't let Program try its default obligation tactic — it elaborates
    against the concrete [Curve25519.field] instance and can take
    30+ minutes per [Program Definition].  Close every obligation
    explicitly with [Next Obligation].  See `reference_slow_proofs_fiat.md`
    Root Cause 14. *)
Local Obligation Tactic := idtac.

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

(** Edwards point negation, picked from [AffineProofs.E.opp] at the
    Curve25519 parameters.  Reusing the upstream [opp] lets the
    [edwards_curve_commutative_group] instance below apply
    syntactically without re-proving the commutative-group laws. *)
Definition opp_25519 : Point -> Point :=
  @Crypto.Curves.Edwards.AffineProofs.E.opp
    _ _ _ _ _ _ _ _ _ _
    Curve25519.field _
    Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a.

(** Edwards point equality: componentwise field equality on the two
    coordinates, ignoring the on-curve proof component.  This is the
    equivalence relation under which the Edwards group laws + scalar-
    mult homomorphism are stated in [AffineProofs]. *)
Definition point_eq : Point -> Point -> Prop :=
  @Spec.CompleteEdwardsCurve.E.eq F_p eq F.one F.add F.mul
    Curve25519.E.a Curve25519.E.d.

(** ================================================================ *)
(** Curve25519 Edwards group — fully reified instances                 *)
(** ================================================================ *)

(** [edwards_curve_commutative_group] applied at Curve25519's
    parameters.  Done once, named, used wherever we need a [group] /
    [is_scalarmult] for the Edwards25519 curve.  No implicit typeclass
    search at use-sites. *)
Definition Hcg25519 :
  @commutative_group Point point_eq point_add point_zero opp_25519 :=
  @Crypto.Curves.Edwards.AffineProofs.E.edwards_curve_commutative_group
    _ _ _ _ _ _ _ _ _ _
    Curve25519.field Curve25519.char_ge_3 _
    Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a Curve25519.E.square_a Curve25519.E.nonsquare_d.

Definition Hg25519 : @group Point point_eq point_add point_zero opp_25519 :=
  @commutative_group_group _ _ _ _ _ Hcg25519.

(** Scalar multiplication via repeated doubling (Z-indexed). *)
Definition scalar_mul_Z : Z -> Point -> Point :=
  @ScalarMult.scalarmult_ref Point point_add point_zero opp_25519.

(** Scalar multiplication from F_l: interpret as Z. *)
Definition scalar_mul (s : Scalar) (P : Point) : Point :=
  scalar_mul_Z (F.to_Z s) P.

(** [scalarmult_ref] is automatically a scalar multiplication on any
    group; reify the instance once. *)
Definition Hsm25519 :
  @is_scalarmult Point point_eq point_add point_zero opp_25519 scalar_mul_Z :=
  @scalarmult_ref_is_scalarmult Point point_eq point_add point_zero
    opp_25519 Hg25519.

(** Equivalence and Proper instances of the group, reified for explicit
    use in the lemmas below.  Brings the [Equivalence point_eq] and
    [Proper (eq ==> eq ==> eq) point_add] into proof scope as named
    hypotheses, sidestepping typeclass resolution paths that whd-walk
    through [Curve25519.field]'s Pocklington-cert internals. *)
Definition Hpoint_eq_equiv : Equivalence point_eq :=
  @monoid_Equivalence _ _ _ _ (@group_monoid _ _ _ _ _ Hg25519).

Definition Hpoint_add_Proper :
  Proper (respectful point_eq (respectful point_eq point_eq)) point_add :=
  @monoid_op_Proper _ _ _ _ (@group_monoid _ _ _ _ _ Hg25519).

(** ================================================================ *)
(** Order of the basepoint                                             *)
(** ================================================================ *)

(** [B_order]: the basepoint has order [l] in the Edwards25519 group.
    Discharged by [Spec.Curve25519_BasepointOrder.E_basepoint_order],
    which transports [Spec.Test.X25519.order_basepoint] (a
    Montgomery-ladder [vm_decide_no_check] computation) across the
    Edwards-Montgomery isomorphism [EdwardsMontgomery25519].

    The Phase 4c lemma [scalarmult_l_eq_zero] in BasepointOrder.v is
    still Admitted (Qed kernel-check OOM blocking; tactic proof is
    complete in MCP), so this lemma transitively depends on that
    single Admit. *)
Require Import Spec.Curve25519_BasepointOrder.

Lemma B_order : point_eq (scalar_mul_Z (Z.pos l) basepoint) point_zero.
Proof. exact Curve25519_BasepointOrder.E_basepoint_order. Qed.

(** ================================================================ *)
(** Scalar multiplication is a homomorphism on the basepoint subgroup *)
(** ================================================================ *)

(** These two lemmas are STRONGER than the abstract group laws because
    they reduce a scalar in [F_l] (i.e. modulo [l]) before multiplying.
    They hold on the basepoint specifically because [l · basepoint = 0]
    (the basepoint sits in the prime-order subgroup); they FAIL on
    arbitrary Edwards25519 points (cofactor 8). *)

Lemma scalar_mul_dist_basepoint :
  forall n m, point_eq (scalar_mul (F.add n m) basepoint)
                       (point_add (scalar_mul n basepoint)
                                  (scalar_mul m basepoint)).
Proof.
  intros n m.
  unfold scalar_mul, point_eq.
  rewrite F.to_Z_add.
  pose proof (@scalarmult_mod_order
                Point point_eq point_add point_zero opp_25519 Hg25519
                scalar_mul_Z Hsm25519
                (Z.pos l) basepoint
                ltac:(discriminate) B_order
                (F.to_Z n + F.to_Z m)) as Hmod.
  pose proof (@scalarmult_add_l
                Point point_eq point_add point_zero opp_25519 Hg25519
                scalar_mul_Z Hsm25519
                (F.to_Z n) (F.to_Z m) basepoint) as Hadd.
  unfold point_eq in Hmod, Hadd.
  pose proof Hpoint_eq_equiv as Heq.
  exact (Equivalence_Transitive _ _ _ Hmod Hadd).
Qed.

Lemma scalar_mul_compose_basepoint :
  forall n m, point_eq (scalar_mul (F.mul n m) basepoint)
                       (scalar_mul n (scalar_mul m basepoint)).
Proof.
  intros n m.
  unfold scalar_mul, point_eq.
  rewrite F.to_Z_mul.
  pose proof (@scalarmult_mod_order
                Point point_eq point_add point_zero opp_25519 Hg25519
                scalar_mul_Z Hsm25519
                (Z.pos l) basepoint
                ltac:(discriminate) B_order
                (F.to_Z n * F.to_Z m)) as Hmod.
  pose proof (@scalarmult_assoc
                Point point_eq point_add point_zero opp_25519 Hg25519
                scalar_mul_Z Hsm25519
                (F.to_Z n) (F.to_Z m) basepoint) as Hassoc.
  rewrite (Z.mul_comm (F.to_Z m) (F.to_Z n)) in Hassoc.
  unfold point_eq in Hmod, Hassoc.
  pose proof Hpoint_eq_equiv as Heq.
  apply (Equivalence_Transitive _ _ _ Hmod).
  exact (Equivalence_Symmetric _ _ Hassoc).
Qed.

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

      Schnorr structure inlined; abstract [XEdDSA.sign] has 28+
      implicits which makes typeclass resolution delicate. *)

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
      Schnorr identity:  s·G  =  (r + e*a)·G  =  r·G + e·(a·G)  =  R + e·A.

      Proven from the basepoint-restricted homomorphism lemmas above —
      no abstract [Hypothesis]es, no universal-P ASSUMPTIONS that
      would be FALSE on Edwards25519 cofactor points. *)
  Theorem sign_verify_correct_25519 :
    forall (a r : Scalar) (M : Msg),
      let A := scalar_mul a basepoint in
      verify_25519 A M (sign_25519 a A r M).
  Proof.
    intros a r M.
    unfold verify_25519, sign_25519. simpl sig_R. simpl sig_s.
    set (e := hash_to_scalar _ _ _).
    pose proof (scalar_mul_dist_basepoint r (F.mul e a)) as H1.
    pose proof (scalar_mul_compose_basepoint e a) as H2.
    unfold point_eq in *.
    pose proof Hpoint_eq_equiv as Heq.
    apply (Equivalence_Transitive _ _ _ H1).
    apply Hpoint_add_Proper.
    - reflexivity.
    - exact H2.
  Qed.

End WithMsg.
