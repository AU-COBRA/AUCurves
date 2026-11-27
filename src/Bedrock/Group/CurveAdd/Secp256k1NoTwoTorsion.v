(** * secp256k1 has no F-rational point of order two.

    The secp256k1 analogue of [P256NoTwoTorsion.v]: [Projective.add] is total
    on y^2 = x^3 + 7 over F_p (p = 2^256 - 2^32 - 977) because x^3 + 7 has no
    root modulo p ([RcbProjectiveLaws.not_exceptional_of_no_two_torsion]).  The
    fact is [CubicNoRoot.no_root] at p, a = 0, b = 7; its certificate (x^p - x
    is invertible in (Z/p)[x] / (x^3 + 7)) is checked by [native_compute].
    (It also follows from the group order being the odd prime n; the
    certificate does not need n.)  Nothing is assumed. *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Bedrock.Group.CurveAdd.CubicNoRoot.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_Secp256k1.

Local Open Scope Z_scope.

Section Secp256k1NoTwoTorsion.

  Existing Instances Field256k1.field_parameters secp256k1_field_parameters_ok.

  Definition secp256k1_aZ : Z := 0.
  Definition secp256k1_bZ : Z := 7.

  Lemma secp256k1_prime_M : Znumtheory.prime (Z.pos M_pos).
  Proof. exact M_prime. Qed.

  Lemma secp256k1_Hbz : secp256k1_bZ mod (Z.pos M_pos) <> 0.
  Proof. vm_compute. discriminate. Qed.

  (** The certificate: [x^p - x] is invertible in (Z/p)[x] / (x^3 + 7). *)
  Lemma secp256k1_Hcert :
    CubicNoRoot.mul3 (Z.pos M_pos) secp256k1_aZ secp256k1_bZ
      (CubicNoRoot.hcert (Z.pos M_pos) secp256k1_aZ secp256k1_bZ)
      (CubicNoRoot.wcert (Z.pos M_pos) secp256k1_aZ secp256k1_bZ)
    = CubicNoRoot.one3.
  Proof. native_compute. reflexivity. Qed.

  (** [x^3 + 7] has no root modulo p. *)
  Theorem secp256k1_no_root_Z :
    forall r : Z, (r * r * r + secp256k1_aZ * r + secp256k1_bZ) mod (Z.pos M_pos) <> 0.
  Proof.
    exact (CubicNoRoot.no_root (Z.pos M_pos) secp256k1_prime_M secp256k1_aZ secp256k1_bZ
             secp256k1_Hbz secp256k1_Hcert).
  Qed.

  (** The same fact in the field, in the shape
      [RcbProjectiveLaws.no_two_torsion] asks for. *)
  Theorem secp256k1_cubic_no_root :
    forall a b : F M_pos,
      F.to_Z a = secp256k1_aZ ->
      F.to_Z b = secp256k1_bZ ->
      forall x : F M_pos, ((x * x * x + a * x + b) <> 0)%F.
  Proof.
    intros a b Ha Hb x Hx.
    apply (secp256k1_no_root_Z (F.to_Z x)).
    assert (Heq : F.of_Z M_pos (F.to_Z x * F.to_Z x * F.to_Z x
                                + secp256k1_aZ * F.to_Z x + secp256k1_bZ)
                  = (x * x * x + a * x + b)%F).
    { rewrite <- Ha, <- Hb.
      rewrite !F.of_Z_add, !F.of_Z_mul, !F.of_Z_to_Z. reflexivity. }
    rewrite <- F.to_Z_of_Z, Heq, Hx.
    apply F.to_Z_0.
  Qed.

End Secp256k1NoTwoTorsion.
