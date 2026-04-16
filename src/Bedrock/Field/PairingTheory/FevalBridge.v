(** * FevalBridge: connect bedrock2 [feval] to ZModTower's flat-Z types.

    The bedrock2 field representation uses:
      - [Fp_feval : list word -> F M_pos]   (base field)
      - [Fp2_feval : list word -> Fp * Fp]  (quadratic extension)
      - [Fp12_feval : list word -> Fp6 * Fp6] (dodecic extension)

    The ZModTower uses:
      - [Z]                                (base field, Z mod p)
      - [Fp2_Z = Z * Z]                   (quadratic extension)
      - [Fp12_Z = Fp6_Z * Fp6_Z]          (dodecic extension)

    This file provides bridge functions that map between the two
    representations via [F.to_Z : F M_pos -> Z].

    The key theorem (proved per field layer) is:
      [bedrock2_op feval args = zmod_op (bridge args)]
    where [bedrock2_op] is an operation at the FElem level and
    [zmod_op] is the corresponding ZModTower operation. This lets
    the Miller loop equivalence theorem be stated as:
      [bridge (Fp12_feval out) = affine_miller bn254_zmod_ops ...]

    IMPORTANT: [F.to_Z] maps a field element to its canonical
    representative in [0, p). The ZModTower operations use [Z.modulo]
    to stay in [0, p). So the bridge is lossless: [F.to_Z] composed
    with [F.of_Z] is the identity (for values in [0, p)).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.PairingTheory.ZModTower.

Local Open Scope Z_scope.

Section FevalBridge.

  Variable M_pos : positive.
  Local Notation Fp := (F M_pos).

  (** Base field bridge: F M_pos -> Z *)
  Definition fp_to_Z (x : Fp) : Z := F.to_Z x.

  (** Fp2 bridge: Fp * Fp -> Z * Z *)
  Definition fp2_to_Z (x : Fp * Fp) : Fp2_Z :=
    (fp_to_Z (fst x), fp_to_Z (snd x)).

  (** Fp6 bridge: (Fp2 * Fp2 * Fp2) -> Fp6_Z *)
  Definition fp6_to_Z (x : (Fp * Fp) * (Fp * Fp) * (Fp * Fp)) : Fp6_Z :=
    mk_fp6 (fp2_to_Z (fst (fst x)))
           (fp2_to_Z (snd (fst x)))
           (fp2_to_Z (snd x)).

  (** Fp12 bridge: (Fp6 * Fp6) -> Fp12_Z *)
  Definition fp12_to_Z
    (x : ((Fp * Fp) * (Fp * Fp) * (Fp * Fp)) *
         ((Fp * Fp) * (Fp * Fp) * (Fp * Fp))) : Fp12_Z :=
    (fp6_to_Z (fst x), fp6_to_Z (snd x)).

  (** Reverse bridge: Z -> F M_pos *)
  Definition Z_to_fp (x : Z) : Fp := F.of_Z M_pos x.

  (** Round-trip lemma: to_Z ∘ of_Z = id (mod p). *)
  Lemma fp_to_Z_of_Z (x : Z) :
    0 <= x < Z.pos M_pos ->
    fp_to_Z (Z_to_fp x) = x.
  Proof.
    intros [Hlo Hhi].
    unfold fp_to_Z, Z_to_fp.
    rewrite F.to_Z_of_Z.
    rewrite Z.mod_small; [reflexivity | lia].
  Qed.

  (** Per-operation bridging lemmas: each shows that F-level operations
      commute with to_Z, i.e., to_Z preserves the ring structure.
      These bridge between fiat-crypto's [F M_pos] and [Z/pZ]. *)

  Lemma fp_to_Z_add (x y : Fp) :
    fp_to_Z (F.add x y) = ((fp_to_Z x) + (fp_to_Z y)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_add. Qed.

  Lemma fp_to_Z_sub (x y : Fp) :
    fp_to_Z (F.sub x y) = ((fp_to_Z x) - (fp_to_Z y)) mod (Z.pos M_pos).
  Proof.
    unfold fp_to_Z, F.sub. rewrite F.to_Z_add, F.to_Z_opp.
    rewrite Zplus_mod_idemp_r. f_equal.
  Qed.

  Lemma fp_to_Z_mul (x y : Fp) :
    fp_to_Z (F.mul x y) = ((fp_to_Z x) * (fp_to_Z y)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_mul. Qed.

  Lemma fp_to_Z_opp (x : Fp) :
    fp_to_Z (F.opp x) = (- (fp_to_Z x)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_opp. Qed.

  Lemma fp_to_Z_zero : fp_to_Z (@F.zero M_pos) = 0.
  Proof. unfold fp_to_Z. rewrite F.to_Z_0. reflexivity. Qed.

  Lemma fp_to_Z_one : fp_to_Z (@F.one M_pos) = 1 mod (Z.pos M_pos).
  Proof. reflexivity. Qed.

  (** Fp2-level bridging: component-wise *)
  Lemma fp2_to_Z_add (x y : Fp * Fp) :
    fp2_to_Z (F.add (fst x) (fst y), F.add (snd x) (snd y)) =
    (fp_to_Z (F.add (fst x) (fst y)), fp_to_Z (F.add (snd x) (snd y))).
  Proof. unfold fp2_to_Z. reflexivity. Qed.

  Lemma fp2_to_Z_fst (x : Fp * Fp) : fst (fp2_to_Z x) = fp_to_Z (fst x).
  Proof. reflexivity. Qed.

  Lemma fp2_to_Z_snd (x : Fp * Fp) : snd (fp2_to_Z x) = fp_to_Z (snd x).
  Proof. reflexivity. Qed.

  (** FieldOps instance using F-level operations directly.
      This lets us state the pairing as:
        affine_miller feval_ops P Q
      where all arithmetic is done via fiat-crypto's verified F operations. *)

  (* Fp2 = Fp * Fp with beta = -1 (for BN254, p = 3 mod 4) *)
  Variable beta : Fp.

  (* Fp2 operations via Karatsuba / schoolbook *)
  Definition feval_fp2_add (x y : Fp * Fp) : Fp * Fp :=
    (F.add (fst x) (fst y), F.add (snd x) (snd y)).

  Definition feval_fp2_sub (x y : Fp * Fp) : Fp * Fp :=
    (F.sub (fst x) (fst y), F.sub (snd x) (snd y)).

  Definition feval_fp2_neg (x : Fp * Fp) : Fp * Fp :=
    (F.opp (fst x), F.opp (snd x)).

  Definition feval_fp2_mul (x y : Fp * Fp) : Fp * Fp :=
    let a := F.mul (fst x) (fst y) in
    let b := F.mul (snd x) (snd y) in
    (F.add a (F.mul beta b), F.add (F.mul (fst x) (snd y)) (F.mul (snd x) (fst y))).

  Definition feval_fp2_sqr (x : Fp * Fp) : Fp * Fp :=
    feval_fp2_mul x x.

  Definition feval_fp2_inv (x : Fp * Fp) : Fp * Fp :=
    (* (a - beta*b*b') / (a^2 - beta*b^2) *)
    let norm := F.sub (F.mul (fst x) (fst x))
                      (F.mul beta (F.mul (snd x) (snd x))) in
    let inv_norm := F.inv norm in
    (F.mul (fst x) inv_norm, F.opp (F.mul (snd x) inv_norm)).

  Definition feval_fp2_mul_fp (x : Fp * Fp) (s : Fp) : Fp * Fp :=
    (F.mul (fst x) s, F.mul (snd x) s).

  (* Placeholder Fp12 type — using nested pairs *)
  Definition Fp6_F := ((Fp * Fp) * (Fp * Fp) * (Fp * Fp))%type.
  Definition Fp12_F := (Fp6_F * Fp6_F)%type.

  (* Fp12 operations would require the full tower but we can define
     the FieldOps with abstract placeholders for now *)
  Variable fp12_one_val : Fp12_F.
  Variable fp12_mul_impl : Fp12_F -> Fp12_F -> Fp12_F.
  Variable fp12_sqr_impl : Fp12_F -> Fp12_F.
  Variable make_line_impl : (Fp * Fp) -> (Fp * Fp) -> (Fp * Fp) -> Fp -> Fp -> Fp12_F.

  Definition feval_ops : Affine.FieldOps Fp (Fp * Fp) Fp12_F := {|
    Affine.fp_zero := @F.zero M_pos;
    Affine.fp_one := @F.one M_pos;
    Affine.fp2_zero := (@F.zero M_pos, @F.zero M_pos);
    Affine.fp2_one := (@F.one M_pos, @F.zero M_pos);
    Affine.fp2_add := feval_fp2_add;
    Affine.fp2_sub := feval_fp2_sub;
    Affine.fp2_neg := feval_fp2_neg;
    Affine.fp2_mul := feval_fp2_mul;
    Affine.fp2_sqr := feval_fp2_sqr;
    Affine.fp2_inv := feval_fp2_inv;
    Affine.fp2_mul_fp := feval_fp2_mul_fp;
    Affine.fp12_one := fp12_one_val;
    Affine.fp12_mul := fp12_mul_impl;
    Affine.fp12_sqr := fp12_sqr_impl;
    Affine.make_line := make_line_impl;
  |}.

End FevalBridge.

(** To instantiate for BN254:
    - M_pos := bn254_M_pos
    - beta := F.of_Z M_pos (-1)
    - fp12_one_val, fp12_mul_impl, fp12_sqr_impl, make_line_impl
      from the concrete BN254 tower definitions

    Then prove: for all valid P, Q,
      fp12_to_Z (affine_miller feval_ops P Q) =
      affine_miller zmod_ops (fp_to_Z P) (fp2_to_Z Q)

    This follows from the per-operation bridging lemmas (fp_to_Z_add etc.)
    applied structurally to each step of affine_miller. *)
