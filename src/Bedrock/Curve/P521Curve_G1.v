(** * P521Curve_G1 — algebraic layer for secp521r1 group operations.
 *
 *  P-521 is the one NIST P-curve outside the WordByWordMontgomery
 *  pipeline (its field is unsaturated Solinas, p = 2^521 - 1), so
 *  the [P256_G1_Add_Spec]-style bedrock2 WP chain does not apply.
 *  This file provides the algebraic backbone for the P-521 group
 *  operations instead:
 *
 *  1. [prime_p521_lucas]: primality of 2^521 - 1 via Coqprime's
 *     Lucas–Lehmer test — a full proof, upgrading the Track-Q
 *     [Axiom prime_p521] in [p521_prime.v] (kept there untouched for
 *     its existing clients).
 *  2. The secp521r1 curve instance (a = -3, b, discriminant ≠ 0,
 *     characteristic bounds) and its commutative group structure.
 *  3. The instantiation of fiat-crypto's verified complete projective
 *     RCB addition ([Projective.add], which is literally Algorithm 1
 *     of Renes–Costello–Batina 2015 — the same 40-op dataflow
 *     implemented by [p521-safe-rust/src/group.rs] and by the
 *     emitted body in [NistG1AddRustCmd.v]) and the theorem that it
 *     computes the affine group law ([p521_rcb_add_correct]).
 *
 *  The remaining gap between this layer and the Rust artifacts is
 *  the representation bridge (Solinas tight-limb buffers vs. F p521),
 *  the per-leaf fiat-crypto contracts, and the not_exceptional side
 *  condition; see the audit entry in HAND_WRITTEN_AUDIT.md.
 *)

From Stdlib Require Import ZArith Znumtheory Lia List.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
From Crypto Require Import PrimeFieldTheorems.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
From Coqprime.PrimalityTest Require Import LucasLehmer.

Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. The Mersenne prime p = 2^521 - 1, via Lucas–Lehmer            *)
(* ================================================================ *)

Definition p521 : positive := Eval vm_compute in Z.to_pos (2^521 - 1).

Lemma p521_is_Mp : Z.pos p521 = Mp 521.
Proof. vm_compute. reflexivity. Qed.

(** Full primality proof: M_521 passes the Lucas–Lehmer test.
    [lucas_test] runs the 519-step S-sequence mod 2^521 - 1; the
    check is a single vm_compute. *)
#[export] Instance prime_p521_lucas : prime p521.
Proof.
  rewrite p521_is_Mp.
  apply LucasTest.
  vm_cast_no_check (@eq_refl bool true).
Qed.

(* ================================================================ *)
(* §2. The secp521r1 curve over F p521                               *)
(* ================================================================ *)

Add Field Private_field_p521 :
  (Algebra.Field.field_theory_for_stdlib_tactic (T:=F p521)).

#[local] Definition a : F p521 := F.opp (1+1+1).
#[local] Definition b : F p521 :=
  F.of_Z _ 0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00.

(** [lia] stalls on the 521-bit literal (cf. the P-256 template, where
    it is instant at 256 bits); transitivity through the small bound
    plus a [vm_compute] comparison closes each goal immediately. *)
#[export] Instance p521_char_ge_3 :
  @Ring.char_ge (F p521) eq F.zero F.one F.opp F.add F.sub F.mul 3.
Proof.
  intros n Hn. apply (@F.char_gt p521).
  eapply Pos.lt_trans; [exact Hn | vm_compute; reflexivity].
Qed.

#[export] Instance p521_char_ge_12 :
  @Ring.char_ge (F p521) eq F.zero F.one F.opp F.add F.sub F.mul 12.
Proof.
  intros n Hn. apply (@F.char_gt p521).
  eapply Pos.lt_trans; [exact Hn | vm_compute; reflexivity].
Qed.

#[export] Instance p521_char_ge_21 :
  @Ring.char_ge (F p521) eq F.zero F.one F.opp F.add F.sub F.mul 21.
Proof.
  intros n Hn. apply (@F.char_gt p521).
  eapply Pos.lt_trans; [exact Hn | vm_compute; reflexivity].
Qed.

#[local] Definition three_b : F p521 := (b + b + b)%F.

Lemma three_b_correct : three_b = (b + b + b)%F.
Proof. reflexivity. Qed.

Lemma discriminant_nonzero :
  id ((1+1+1+1)*a*a*a + (1+1+1+1+1+1+1+1+1)*(1+1+1)*b*b <> 0)%F.
Proof. cbv [id]. Decidable.vm_decide. Qed.

#[local] Notation Wpoint := (@W.point (F p521) eq F.add F.mul a b).

#[refine, export] Instance p521_curve_commutative_group :
  Hierarchy.commutative_group (T:=Wpoint) :=
  (W.commutative_group p521_char_ge_3 (a:=a) (b:=b)).
Proof. cbv [id]. Decidable.vm_decide. Defined.

(** secp521r1 group order (FIPS 186-4 D.1.2.5); primality of n is
    not needed by this file and is left to a future Pocklington
    certificate. *)
Definition p521_group_order : Z :=
  0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409.

(* ================================================================ *)
(* §3. The verified RCB complete projective addition for P-521       *)
(* ================================================================ *)

Section P521_Projective.

  #[local] Notation Ppoint :=
    (@Projective.point (F p521) eq F.zero F.add F.mul a b).

  #[local] Notation Padd :=
    (@Projective.add (F p521)
       eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div
       a b _ p521_char_ge_3 _
       three_b three_b_correct discriminant_nonzero p521_char_ge_21).

  #[local] Notation P_to_affine :=
    (@Projective.to_affine (F p521) eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div a b _ _).

  #[local] Notation P_of_affine :=
    (@Projective.of_affine (F p521) eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div a b _ _).

  (** The RCB Algorithm-1 projective addition computes the affine
      group law on secp521r1.  [Projective.add]'s let-chain is the
      same 40-op dataflow as the Rust [p521-safe-rust::group::g1_add]
      and the emitted [NistG1AddRustCmd] body. *)
  Theorem p521_rcb_add_correct :
    forall (P Q : Ppoint) except,
      W.eq (P_to_affine (Padd P Q except))
           (W.add (P_to_affine P) (P_to_affine Q)).
  Proof.
    intros P Q except.
    apply Projective.to_affine_add.
  Qed.

  (* NOTE: this fiat-crypto revision has no
     [Projective.to_affine_of_affine] round-trip lemma (the
     [P256Curve_G1_bedrock.v] corollary that cites it predates a
     rewrite of Projective.v and does not compile against the current
     submodule).  [p521_rcb_add_correct] above is the load-bearing
     statement; an affine-input corollary can be added once the
     round-trip lemma exists upstream. *)

End P521_Projective.
