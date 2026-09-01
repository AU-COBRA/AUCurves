(** * The NIST P-256 curve has no F-rational point of order two.

    [Projective.add] is a partial function: it takes a
    [not_exceptional] proof, and that proof exists for every pair of
    points exactly when the curve has no point of order two, i.e. when
    x^3 + a x + b has no root in F_p
    ([RcbProjectiveLaws.not_exceptional_of_no_two_torsion], Qed).

    This file discharges that arithmetic fact for P-256 by instantiating
    [CubicNoRoot.no_root] at the P-256 prime and curve constants.  The
    two side conditions are [vm_compute] checks; nothing is assumed.

    Stated in terms of [F.to_Z] of the two constants rather than of a
    particular spelling of them, so that a consumer holding the curve
    coefficients in any form ([feval] of a stored felem, [F.of_Z] of a
    literal) discharges the hypotheses by [vm_compute] rather than by
    conversion. *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Group.CurveAdd.CubicNoRoot.

Local Open Scope Z_scope.

Section P256NoTwoTorsion.

  Existing Instances p256_field_parameters p256_field_parameters_ok.

  (** The curve constants as canonical residues.  [p256_aZ] is [-3] and
      [p256_bZ] is the NIST constant [b]. *)
  Definition p256_aZ : Z := Eval vm_compute in
    ((-3) mod (2^256 - 2^224 + 2^192 + 2^96 - 1)).
  Definition p256_bZ : Z :=
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b.

  Lemma p256_prime_M : Znumtheory.prime (Z.pos M_pos).
  Proof. exact M_prime. Qed.

  Lemma p256_Hbz : p256_bZ mod (Z.pos M_pos) <> 0.
  Proof. vm_compute. discriminate. Qed.

  (** The certificate: [x^p - x] is invertible in
      (Z/p)[x] / (x^3 - 3x + b), so that quotient is a field, so the
      cubic is irreducible, so it has no root. *)
  Lemma p256_Hcert :
    CubicNoRoot.mul3 (Z.pos M_pos) p256_aZ p256_bZ
      (CubicNoRoot.hcert (Z.pos M_pos) p256_aZ p256_bZ)
      (CubicNoRoot.wcert (Z.pos M_pos) p256_aZ p256_bZ)
    = CubicNoRoot.one3.
  (** [native_compute], not [vm_compute]: the check is about 1900
      multiplications of coefficient triples, each nine [Z.mul] and
      three [Z.modulo] on 256-bit operands.  Under the VM that is Coq's
      binary-[positive] arithmetic and runs past five minutes; under the
      native compiler it is 97 s including the Qed. *)
  Proof. native_compute. reflexivity. Qed.

  (** [x^3 - 3x + b] has no root modulo the P-256 prime. *)
  Theorem p256_no_root_Z :
    forall r : Z, (r * r * r + p256_aZ * r + p256_bZ) mod (Z.pos M_pos) <> 0.
  Proof.
    exact (CubicNoRoot.no_root (Z.pos M_pos) p256_prime_M p256_aZ p256_bZ
             p256_Hbz p256_Hcert).
  Qed.

  (** The same fact in the field, in the shape
      [RcbProjectiveLaws.no_two_torsion] asks for. *)
  Theorem p256_cubic_no_root :
    forall a b : F M_pos,
      F.to_Z a = p256_aZ ->
      F.to_Z b = p256_bZ ->
      forall x : F M_pos, ((x * x * x + a * x + b) <> 0)%F.
  Proof.
    intros a b Ha Hb x Hx.
    apply (p256_no_root_Z (F.to_Z x)).
    assert (Heq : F.of_Z M_pos (F.to_Z x * F.to_Z x * F.to_Z x
                                + p256_aZ * F.to_Z x + p256_bZ)
                  = (x * x * x + a * x + b)%F).
    { rewrite <- Ha, <- Hb.
      rewrite !F.of_Z_add, !F.of_Z_mul, !F.of_Z_to_Z. reflexivity. }
    rewrite <- F.to_Z_of_Z, Heq, Hx.
    apply F.to_Z_0.
  Qed.

End P256NoTwoTorsion.
