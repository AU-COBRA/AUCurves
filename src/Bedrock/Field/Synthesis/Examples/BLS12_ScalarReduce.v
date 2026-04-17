(** * BLS12-381 scalar reduction mod subgroup order r.

    The BLS12-381 subgroup order is:
      r = u^4 - u^2 + 1  where u = -0xd201000000010000
        = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

    This is 255 bits. A 256-bit input scalar k satisfies k < 2^256 < 3r,
    so at most two conditional subtractions reduce k to [0, r).

    The key correctness lemma is [scalarmult_mod_order] from
    Crypto.Algebra.ScalarMult: for any group element P of order r,
      [k mod r] P = [k] P *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(** *** BLS12-381 curve parameter and subgroup order *)

Definition bls12_u : Z := -0xd201000000010000.

(** The subgroup order r = u^4 - u^2 + 1 *)
Definition bls12_r : Z :=
  Eval vm_compute in (bls12_u^4 - bls12_u^2 + 1).

(** *** Key properties of r *)

Lemma bls12_r_val : bls12_r =
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_r_pos : 0 < bls12_r.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_r_nonzero : bls12_r <> 0.
Proof. intro H. discriminate H. Qed.

Lemma bls12_r_255bits : 2^254 < bls12_r < 2^255.
Proof. vm_compute. split; reflexivity. Qed.

(** A 256-bit scalar k satisfies k < 3r *)
Lemma bls12_256bit_lt_3r : 2^256 < 3 * bls12_r.
Proof. vm_compute. reflexivity. Qed.

(** *** Conditional subtraction *)

(** [cond_sub k r] returns (k - r) if k >= r, else k. *)
Definition cond_sub (k r : Z) : Z :=
  if k <? r then k else k - r.

(** Two conditional subtractions reduce k < 3r to k mod r. *)
Lemma double_cond_sub_mod : forall k,
  0 <= k < 3 * bls12_r ->
  cond_sub (cond_sub k bls12_r) bls12_r = k mod bls12_r.
Proof.
  intros k [Hk0 Hk3].
  unfold cond_sub.
  pose proof bls12_r_pos as Hr.
  destruct (Z.ltb_spec k bls12_r) as [Hlt1|Hge1].
  - (* k < r: no subtraction needed *)
    destruct (Z.ltb_spec k bls12_r) as [Hlt2|Hge2].
    + symmetry. apply Z.mod_small. lia.
    + lia.
  - (* k >= r: subtract once *)
    destruct (Z.ltb_spec (k - bls12_r) bls12_r) as [Hlt2|Hge2].
    + (* r <= k < 2r: one subtraction suffices *)
      symmetry. rewrite <- (Z.mod_unique_pos k bls12_r 1 (k - bls12_r)); lia.
    + (* 2r <= k < 3r: two subtractions needed *)
      symmetry. rewrite <- (Z.mod_unique_pos k bls12_r 2 (k - 2 * bls12_r)); lia.
Qed.

(** *** Connection to scalar multiplication *)

(** For any group element P of order r, reducing the scalar mod r
    preserves the scalar multiplication result.

    By [scalarmult_mod_order] (Crypto.Algebra.ScalarMult, line 135):
      forall l B, l <> 0 -> l*B = zero -> forall n, n mod l * B = n * B

    Instantiating with l := bls12_r, B := P (the BLS12-381 G1 generator),
    and using [double_cond_sub_mod] to show the conditional subtraction
    computes k mod r, we get:

      [cond_sub (cond_sub k r) r] * P = [k] * P

    The hypothesis [bls12_r * P = zero] is the group order property,
    which holds for all P in the r-torsion subgroup G1[r]. *)

Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Algebra.Hierarchy.

Section ScalarMultReduction.
  Context {G eq add zero opp} `{groupG:@group G eq add zero opp}.
  Context {mul:Z->G->G} `{@is_scalarmult G eq add zero opp mul}.
  Local Infix "=" := eq : type_scope.
  Local Infix "*" := mul.

  (** Main theorem: for any P of order bls12_r, the two-conditional-subtraction
      reduction preserves scalar multiplication. *)
  Theorem bls12_scalar_reduce_correct : forall P k,
    bls12_r * P = zero ->
    0 <= k < 3 * bls12_r ->
    (cond_sub (cond_sub k bls12_r) bls12_r) * P = k * P.
  Proof.
    intros P k Horder Hk.
    rewrite double_cond_sub_mod by exact Hk.
    exact (scalarmult_mod_order bls12_r P bls12_r_nonzero Horder k).
  Qed.

End ScalarMultReduction.
