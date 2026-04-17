(** * BLS12-381 efficient endomorphism for GLV scalar multiplication.

    The BLS12-381 curve admits an efficiently computable endomorphism
      phi(x, y) = (omega * x, y)
    where omega is a primitive cube root of unity in Fp (the base field).

    On the r-torsion subgroup G1[r], this endomorphism acts as
    multiplication by the scalar lambda:
      phi(P) = [lambda] P    for all P in G1[r].

    The eigenvalue lambda satisfies lambda^2 + lambda + 1 = 0 (mod r),
    and omega satisfies omega^3 = 1 (mod p), omega <> 1.

    Key relationships to the curve parameter u = -0xd201000000010000:
      lambda = u^2 - 1 (mod r)
      omega  = g^((p-1)/3) for any generator g of Fp*

    The GLV decomposition splits a scalar k into k1 + k2 * lambda (mod r)
    with k1, k2 roughly half-size, enabling a two-dimensional multi-scalar
    multiplication that halves the number of point doublings. *)

From Stdlib Require Import ZArith Lia.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_ScalarReduce.

Local Open Scope Z_scope.

(** ** BLS12-381 curve parameter and field prime.

    These duplicate definitions from [bls12_prime] and [BLS12_ScalarReduce]
    to avoid the heavy dependency on the full field synthesis pipeline.
    We prove consistency with [bls12_u] and [bls12_r] from ScalarReduce. *)

Definition bls12_p : Z :=
  Eval vm_compute in (((bls12_u - 1)^2 * (bls12_u^4 - bls12_u^2 + 1)) / 3 + bls12_u).

Lemma bls12_p_val : bls12_p =
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Proof. vm_compute. reflexivity. Qed.

(** ** The cube root of unity omega in Fp.

    omega satisfies X^2 + X + 1 = 0 (mod p), equivalently omega^3 = 1
    and omega <> 1.  It is the image of a generator g under the map
    g |-> g^((p-1)/3). *)

Definition bls12_omega : Z :=
  793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350.

(** ** The GLV eigenvalue lambda in Fr.

    lambda = u^2 - 1, which satisfies X^2 + X + 1 = 0 (mod r).
    The endomorphism phi acts as [lambda] on G1[r]. *)

Definition bls12_lambda : Z :=
  228988810152649578064853576960394133503.

(** ** Properties of omega *)

Lemma bls12_omega_cube_root :
  (bls12_omega ^ 3) mod bls12_p = 1 mod bls12_p.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_omega_not_one :
  bls12_omega mod bls12_p <> 1 mod bls12_p.
Proof. vm_compute. discriminate. Qed.

Lemma bls12_omega_minimal_poly :
  (bls12_omega ^ 2 + bls12_omega + 1) mod bls12_p = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_omega_range : 0 < bls12_omega < bls12_p.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Properties of lambda *)

Lemma bls12_lambda_eigenvalue :
  (bls12_lambda ^ 2 + bls12_lambda + 1) mod bls12_r = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_lambda_not_one :
  bls12_lambda mod bls12_r <> 1 mod bls12_r.
Proof. vm_compute. discriminate. Qed.

Lemma bls12_lambda_range : 0 < bls12_lambda < bls12_r.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Relationship to curve parameter u *)

Lemma bls12_lambda_from_u :
  bls12_lambda = bls12_u ^ 2 - 1.
Proof. vm_compute. reflexivity. Qed.

(** ** GLV lattice basis.

    The kernel lattice L = { (a, b) in Z^2 : a + b * lambda = 0 (mod r) }
    has a Gauss-reduced basis:
      v1 = (lambda, -1)
      v2 = (1,  u^2)

    The determinant of [v1 | v2] equals r, since
      lambda * u^2 - (-1) * 1 = lambda * (lambda + 1) + 1
                                = lambda^2 + lambda + 1 = r.

    These vectors have entries of about 128 bits (half the size of r),
    which is optimal for the GLV two-dimensional decomposition. *)

Definition glv_v1 : Z * Z := (bls12_lambda, -1).
Definition glv_v2 : Z * Z := (1, bls12_lambda + 1).

(** v1 is in the lattice *)
Lemma glv_v1_in_lattice :
  (fst glv_v1 + snd glv_v1 * bls12_lambda) mod bls12_r = 0.
Proof. vm_compute. reflexivity. Qed.

(** v2 is in the lattice *)
Lemma glv_v2_in_lattice :
  (fst glv_v2 + snd glv_v2 * bls12_lambda) mod bls12_r = 0.
Proof. vm_compute. reflexivity. Qed.

(** The determinant of the lattice basis equals r *)
Lemma glv_lattice_det :
  fst glv_v1 * snd glv_v2 - snd glv_v1 * fst glv_v2 = bls12_r.
Proof. vm_compute. reflexivity. Qed.

(** The lattice vectors are 128-bit, i.e., half the size of the 255-bit r *)
Lemma glv_v1_half_size :
  Z.abs (fst glv_v1) < 2 ^ 128 /\ Z.abs (snd glv_v1) < 2 ^ 128.
Proof. vm_compute. split; reflexivity. Qed.

Lemma glv_v2_half_size :
  Z.abs (fst glv_v2) < 2 ^ 128 /\ Z.abs (snd glv_v2) < 2 ^ 128.
Proof. vm_compute. split; reflexivity. Qed.
