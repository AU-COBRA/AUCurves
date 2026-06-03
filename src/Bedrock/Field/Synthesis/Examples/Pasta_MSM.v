(** * Pasta (Pallas / Vesta) multi-scalar multiplication — leaf.

    A computable multi-scalar multiplication (MSM) over the Pasta affine
    group law from [Pasta_TestVectors.v]:

      MSM([(k_0, P_0), ..., (k_{n-1}, P_{n-1})]) = sum_i [k_i] P_i

    This is the leaf artifact a Halo2-style polynomial-commitment prover
    needs over the Pasta cycle (Pallas / Vesta): the verified group law
    ([aadd]/[adbl], proved equivalent to fiat-crypto's [Projective.add]
    in [PallasCurveSpecsEquiv.v] / [VestaCurveSpecsEquiv.v]) lifted to a
    scalar-multiply and a multi-scalar combination.

    Gated by a KAT: the bilinearity identities
      [k]G computed by double-and-add agrees with the iterated additions
      ([2]G + [3]G = [5]G), and a 2-term MSM matches its expansion,
    each result checked on-curve. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Bedrock.Field.Synthesis.Examples.Pasta_TestVectors.

Import ListNotations.
Local Open Scope Z_scope.

(* =================================================================== *)
(** * Scalar multiplication and MSM over the affine group law           *)
(* =================================================================== *)

(** [scalar_mul p k P]: double-and-add, fuelled for 255-bit scalars. *)
Fixpoint smul_fuel (fuel : nat) (p k : Z) (P : apoint) : apoint :=
  match fuel with
  | O => None
  | S f =>
      if Z.leb k 0 then None
      else
        let half := smul_fuel f p (Z.div2 k) P in
        let dbl := adbl p half in
        if Z.odd k then aadd p dbl P else dbl
  end.

Definition smul (p k : Z) (P : apoint) : apoint := smul_fuel 256 p k P.

(** [msm p terms]: sum_i [k_i] P_i over the affine group law. *)
Definition msm (p : Z) (terms : list (Z * apoint)) : apoint :=
  fold_right (fun kP acc => aadd p (smul p (fst kP) (snd kP)) acc) None terms.

(* =================================================================== *)
(** * Pallas KAT                                                        *)
(* =================================================================== *)

Module PallasMSM.
  Import Pallas.

  (** [k]G via double-and-add agrees with the iterated reference points. *)
  Lemma smul_2G : smul p 2 G = G2. Proof. vm_compute. reflexivity. Qed.
  Lemma smul_3G : smul p 3 G = G3. Proof. vm_compute. reflexivity. Qed.
  Lemma smul_5G : smul p 5 G = G5. Proof. vm_compute. reflexivity. Qed.

  (** Group-law additivity: [2]G + [3]G = [5]G. *)
  Lemma add_2G_3G : aadd p G2 G3 = G5. Proof. vm_compute. reflexivity. Qed.

  (** A genuine 2-term MSM: [2]*G + [3]*G = [5]G. *)
  Lemma msm_2_3 : msm p [(2, G); (3, G)] = G5.
  Proof. vm_compute. reflexivity. Qed.

  (** The MSM result lies on the curve. *)
  Lemma msm_2_3_on_curve : on_curve p b (msm p [(2, G); (3, G)]).
  Proof. vm_compute. reflexivity. Qed.
End PallasMSM.

(* =================================================================== *)
(** * Vesta KAT                                                         *)
(* =================================================================== *)

Module VestaMSM.
  Import Vesta.

  Lemma smul_2G : smul p 2 G = G2. Proof. vm_compute. reflexivity. Qed.
  Lemma smul_3G : smul p 3 G = G3. Proof. vm_compute. reflexivity. Qed.
  Lemma smul_5G : smul p 5 G = G5. Proof. vm_compute. reflexivity. Qed.

  Lemma add_2G_3G : aadd p G2 G3 = G5. Proof. vm_compute. reflexivity. Qed.

  Lemma msm_2_3 : msm p [(2, G); (3, G)] = G5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma msm_2_3_on_curve : on_curve p b (msm p [(2, G); (3, G)]).
  Proof. vm_compute. reflexivity. Qed.
End VestaMSM.
