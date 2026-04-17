(** * BLS12-377 scalar reduction mod subgroup order r.

    The BLS12-377 subgroup order is:
      r = u^4 - u^2 + 1  where u = 0x8508c00000000001
        = 0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001

    This is 253 bits. *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(** *** BLS12-377 curve parameter and subgroup order *)

Definition bls377_u : Z := 0x8508c00000000001.

(** The subgroup order r = u^4 - u^2 + 1 *)
Definition bls377_r : Z :=
  Eval vm_compute in (bls377_u^4 - bls377_u^2 + 1).

(** *** Key properties of r *)

Lemma bls377_r_val : bls377_r =
  0x12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_r_pos : 0 < bls377_r.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_r_nonzero : bls377_r <> 0.
Proof. intro H. discriminate H. Qed.

Lemma bls377_r_253bits : 2^252 < bls377_r < 2^253.
Proof. vm_compute. split; reflexivity. Qed.

(** *** Conditional subtraction *)

Definition cond_sub (k r : Z) : Z :=
  if k <? r then k else k - r.

Lemma double_cond_sub_mod : forall k,
  0 <= k < 3 * bls377_r ->
  cond_sub (cond_sub k bls377_r) bls377_r = k mod bls377_r.
Proof.
  intros k [Hk0 Hk3].
  unfold cond_sub.
  pose proof bls377_r_pos as Hr.
  destruct (Z.ltb_spec k bls377_r) as [Hlt1|Hge1].
  - destruct (Z.ltb_spec k bls377_r) as [Hlt2|Hge2].
    + symmetry. apply Z.mod_small. lia.
    + lia.
  - destruct (Z.ltb_spec (k - bls377_r) bls377_r) as [Hlt2|Hge2].
    + symmetry. rewrite <- (Z.mod_unique_pos k bls377_r 1 (k - bls377_r)); lia.
    + symmetry. rewrite <- (Z.mod_unique_pos k bls377_r 2 (k - 2 * bls377_r)); lia.
Qed.

(** *** Connection to scalar multiplication *)

Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Algebra.Hierarchy.

Section ScalarMultReduction.
  Context {G eq add zero opp} `{groupG:@group G eq add zero opp}.
  Context {mul:Z->G->G} `{@is_scalarmult G eq add zero opp mul}.
  Local Infix "=" := eq : type_scope.
  Local Infix "*" := mul.

  Theorem bls377_scalar_reduce_correct : forall P k,
    bls377_r * P = zero ->
    0 <= k < 3 * bls377_r ->
    (cond_sub (cond_sub k bls377_r) bls377_r) * P = k * P.
  Proof.
    intros P k Horder Hk.
    rewrite double_cond_sub_mod by exact Hk.
    exact (scalarmult_mod_order bls377_r P bls377_r_nonzero Horder k).
  Qed.

End ScalarMultReduction.
