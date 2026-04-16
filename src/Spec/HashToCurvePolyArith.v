(** * Polynomial arithmetic on [list Z] for verifying polynomial identities.

    Provides Z-level polynomial operations and a bridge lemma connecting
    them to the [horner_eval] on [F p_pos] from HashToCurve.v.
    Used by the isogeny correctness proof. *)

From Stdlib Require Import ZArith BinPos List Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================== *)
(** * Z-level polynomial evaluation (Horner's method)                  *)
(* ================================================================== *)

(** Evaluate a polynomial [c0; c1; ...; cn] at x:
    c0 + x*(c1 + x*(c2 + ... + x*cn)) *)
Fixpoint poly_eval_Z (cs : list Z) (x : Z) : Z :=
  match cs with
  | [] => 0
  | [c] => c
  | c :: cs' => c + x * poly_eval_Z cs' x
  end.

(* ================================================================== *)
(** * Z-level polynomial arithmetic (mod p)                            *)
(* ================================================================== *)

(** Pointwise addition of coefficient lists (mod p). *)
Fixpoint poly_add_Z (p : Z) (f g : list Z) : list Z :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' => (a + b) mod p :: poly_add_Z p f' g'
  end.

(** Scalar multiplication (mod p). *)
Definition poly_scale_Z (p : Z) (c : Z) (f : list Z) : list Z :=
  map (fun a => (c * a) mod p) f.

(** Polynomial multiplication via convolution (mod p).
    Computes f * g by distributing f[0]*g + x*(f[1..]*g). *)
Fixpoint poly_mul_Z (p : Z) (f g : list Z) : list Z :=
  match f with
  | [] => []
  | a :: f' =>
    poly_add_Z p (poly_scale_Z p a g) (0 :: poly_mul_Z p f' g)
  end.

(** Polynomial power (mod p). *)
Fixpoint poly_pow_Z (p : Z) (f : list Z) (n : nat) : list Z :=
  match n with
  | O => [1]
  | S n' => poly_mul_Z p f (poly_pow_Z p f n')
  end.

(** Reduce all coefficients mod p. *)
Definition poly_reduce (p : Z) (f : list Z) : list Z :=
  map (fun c => c mod p) f.

(** Strip trailing zeros for comparison. *)
Fixpoint poly_strip (f : list Z) : list Z :=
  match f with
  | [] => []
  | x :: rest =>
    let rest' := poly_strip rest in
    match rest' with
    | [] => if Z.eqb x 0 then [] else [x]
    | _ => x :: rest'
    end
  end.

(* ================================================================== *)
(** * Bridge: Z-level evaluation to F-level horner_eval                *)
(* ================================================================== *)

(** Key bridge lemma: horner_eval on (map of_Z cs) equals of_Z of the
    Z-level evaluation. Uses the fact that of_Z is a ring homomorphism. *)
Lemma horner_eval_of_Z : forall (cs : list Z) (x : Fp),
  horner_eval (map (F.of_Z p_pos) cs) x =
  F.of_Z p_pos (poly_eval_Z cs (F.to_Z x)).
Proof.
  induction cs as [|c rest IH]; intros x; [simpl; reflexivity|].
  destruct rest as [|c2 rest']; [simpl; reflexivity|].
  (* Key step: relate the two horner evaluations directly *)
  assert (Hh : horner_eval (map (F.of_Z p_pos) (c :: c2 :: rest')) x =
    (F.of_Z p_pos c +f x *f horner_eval (map (F.of_Z p_pos) (c2 :: rest')) x)%F).
  { reflexivity. }
  assert (Hp : poly_eval_Z (c :: c2 :: rest') (F.to_Z x) =
    c + F.to_Z x * poly_eval_Z (c2 :: rest') (F.to_Z x)).
  { reflexivity. }
  rewrite Hh, Hp, IH.
  rewrite <- (F.of_Z_to_Z x) at 1.
  rewrite <- F.of_Z_mul, <- F.of_Z_add.
  reflexivity.
Qed.

(** For monic polynomials (implicit leading 1): *)
Lemma horner_eval_monic_of_Z : forall (cs : list Z) (x : Fp),
  horner_eval_monic (map (F.of_Z p_pos) cs) x =
  F.of_Z p_pos (poly_eval_Z (cs ++ [1]) (F.to_Z x)).
Proof.
  intros cs x. unfold horner_eval_monic.
  rewrite <- horner_eval_of_Z.
  f_equal. rewrite map_app. reflexivity.
Qed.

(** poly_eval_Z respects mod on coefficients: reducing coefficients mod p
    doesn't change the evaluation mod p. *)
(** Helper: of_Z is invariant under mod. *)
Lemma of_Z_mod : forall (z : Z),
  F.of_Z p_pos (z mod Z.pos p_pos) = F.of_Z p_pos z.
Proof. intro z. apply F.eq_to_Z_iff. rewrite !F.to_Z_of_Z, Zmod_mod. reflexivity. Qed.

(** poly_eval_Z respects of_Z: reducing coefficients mod p
    doesn't change the F-level evaluation. *)
Lemma poly_eval_of_Z_reduce : forall (cs : list Z) (x : Z),
  F.of_Z p_pos (poly_eval_Z (map (fun c => c mod Z.pos p_pos) cs) x) =
  F.of_Z p_pos (poly_eval_Z cs x).
Proof.
  induction cs as [|c rest IH]; intro x.
  - simpl. reflexivity.
  - destruct rest as [|c2 rest'].
    + simpl. apply of_Z_mod.
    + (* Key: F.of_Z p_pos a = F.of_Z p_pos b when a ≡ b (mod p).
         We use of_Z ring homomorphism properties. *)
      change (map (fun c0 => c0 mod Z.pos p_pos) (c :: c2 :: rest'))
        with ((c mod Z.pos p_pos) :: map (fun c0 => c0 mod Z.pos p_pos) (c2 :: rest')).
      change (F.of_Z p_pos (c mod Z.pos p_pos + x * poly_eval_Z (map (fun c0 => c0 mod Z.pos p_pos) (c2 :: rest')) x) =
              F.of_Z p_pos (c + x * poly_eval_Z (c2 :: rest') x)).
      (* Use of_Z_add and of_Z_mul to decompose *)
      rewrite !F.of_Z_add, !F.of_Z_mul.
      rewrite IH, of_Z_mod. reflexivity.
Qed.

(** Coefficient-wise equality mod p implies evaluation equality mod p. *)
Lemma poly_eval_mod_ext : forall (f g : list Z) (x : Z),
  poly_reduce (Z.pos p_pos) f = poly_reduce (Z.pos p_pos) g ->
  F.of_Z p_pos (poly_eval_Z f x) = F.of_Z p_pos (poly_eval_Z g x).
Proof.
  intros f g x Heq.
  rewrite <- (poly_eval_of_Z_reduce f x).
  rewrite <- (poly_eval_of_Z_reduce g x).
  unfold poly_reduce in Heq. rewrite Heq. reflexivity.
Qed.

(** Combined: if coefficient lists match mod p, then F-level evaluations match. *)
Lemma poly_identity_bridge : forall (lhs rhs : list Z),
  poly_reduce (Z.pos p_pos) lhs = poly_reduce (Z.pos p_pos) rhs ->
  forall x : Fp,
    F.of_Z p_pos (poly_eval_Z lhs (F.to_Z x)) =
    F.of_Z p_pos (poly_eval_Z rhs (F.to_Z x)).
Proof.
  intros lhs rhs Heq x. apply poly_eval_mod_ext. exact Heq.
Qed.

