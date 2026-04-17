(** * BLS12-377 efficient endomorphism for GLV scalar multiplication.

    The BLS12-377 curve admits an efficiently computable endomorphism
      phi(x, y) = (omega * x, y)
    where omega is a primitive cube root of unity in Fp (the base field).

    On the r-torsion subgroup G1[r], this endomorphism acts as
    multiplication by the scalar lambda:
      phi(P) = [lambda] P    for all P in G1[r].

    Key relationships to the curve parameter u = 0x8508c00000000001:
      lambda = u^2 - 1 (mod r)
      omega  = g^((p-1)/3) for any generator g of Fp* *)

From Stdlib Require Import ZArith Lia.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_ScalarReduce.

Local Open Scope Z_scope.

(** ** BLS12-377 field prime *)

Definition bls377_p : Z :=
  Eval vm_compute in (((bls377_u - 1)^2 * (bls377_u^4 - bls377_u^2 + 1)) / 3 + bls377_u).

Lemma bls377_p_val : bls377_p =
  0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001.
Proof. vm_compute. reflexivity. Qed.

(** ** The cube root of unity omega in Fp *)

Definition bls377_omega : Z :=
  0x9b3af05dd14f6ec619aaf7d34594aabc5ed1347970dec00452217cc900000008508c00000000001.

(** ** The GLV eigenvalue lambda in Fr *)

Definition bls377_lambda : Z :=
  Eval vm_compute in (bls377_u ^ 2 - 1).

(** ** Properties of omega *)

Lemma bls377_omega_cube_root :
  (bls377_omega ^ 3) mod bls377_p = 1 mod bls377_p.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_omega_not_one :
  bls377_omega mod bls377_p <> 1 mod bls377_p.
Proof. vm_compute. discriminate. Qed.

Lemma bls377_omega_minimal_poly :
  (bls377_omega ^ 2 + bls377_omega + 1) mod bls377_p = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_omega_range : 0 < bls377_omega < bls377_p.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Properties of lambda *)

Lemma bls377_lambda_eigenvalue :
  (bls377_lambda ^ 2 + bls377_lambda + 1) mod bls377_r = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_lambda_not_one :
  bls377_lambda mod bls377_r <> 1 mod bls377_r.
Proof. vm_compute. discriminate. Qed.

Lemma bls377_lambda_range : 0 < bls377_lambda < bls377_r.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Relationship to curve parameter u *)

Lemma bls377_lambda_from_u :
  bls377_lambda = bls377_u ^ 2 - 1.
Proof. vm_compute. reflexivity. Qed.

(** ** GLV lattice basis *)

Definition glv377_v1 : Z * Z := (bls377_lambda, -1).
Definition glv377_v2 : Z * Z := (1, bls377_lambda + 1).

Lemma glv377_v1_in_lattice :
  (fst glv377_v1 + snd glv377_v1 * bls377_lambda) mod bls377_r = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma glv377_v2_in_lattice :
  (fst glv377_v2 + snd glv377_v2 * bls377_lambda) mod bls377_r = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma glv377_lattice_det :
  fst glv377_v1 * snd glv377_v2 - snd glv377_v1 * fst glv377_v2 = bls377_r.
Proof. vm_compute. reflexivity. Qed.

Lemma glv377_v1_half_size :
  Z.abs (fst glv377_v1) < 2 ^ 127 /\ Z.abs (snd glv377_v1) < 2 ^ 127.
Proof. vm_compute. split; reflexivity. Qed.

Lemma glv377_v2_half_size :
  Z.abs (fst glv377_v2) < 2 ^ 127 /\ Z.abs (snd glv377_v2) < 2 ^ 127.
Proof. vm_compute. split; reflexivity. Qed.
