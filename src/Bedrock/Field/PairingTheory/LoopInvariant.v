(** * LoopInvariant: the Miller loop invariant (continuation form).

    [affine_miller_aux ops n i Px Py Qx Qy f Tx Ty] processes [i]
    remaining iterations starting from accumulator [(f, Tx, Ty)].
    The full result is [affine_miller_aux ops n nbits Px Py Qx Qy 1 Q].

    The CONTINUATION invariant at iteration [i] (counting down) says:
      [affine_miller_aux ops n i Px Py Qx Qy f Tx Ty = FULL_RESULT]
    i.e., "starting from (f, Tx, Ty) and running [i] more iterations
    produces the same result as the full computation."

    At i = nbits (loop entry), this holds because (f, Tx, Ty) = (1, Q).
    At i = 0 (loop exit), this gives f = FULL_RESULT (since 0 iterations
    return the accumulator unchanged).
    Each step from S i to i holds by definition of affine_miller_aux.
*)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.ZModTower.

Local Open Scope Z_scope.

Section LoopInvariant.

  Context (ops : FieldOps Z Fp2_Z Fp12_Z).
  Variable n : Z.
  Variables Px Py : Z.
  Variables Qx Qy : Fp2_Z.

  Let nbits := Z.to_nat (Z.log2 n).
  Let full_result := affine_miller_aux ops n nbits Px Py Qx Qy
                       (fp12_one ops) Qx Qy.

  (** Continuation invariant: "completing i more iterations from
      (f, Tx, Ty) gives the full result." *)
  Definition cont_inv (i : nat) (f : Fp12_Z) (Tx Ty : Fp2_Z) : Prop :=
    affine_miller_aux ops n i Px Py Qx Qy f Tx Ty = full_result.

  (** Init: at i = nbits with (f, Tx, Ty) = (1, Q), the invariant holds
      trivially because both sides are the same call. *)
  Lemma cont_inv_init :
    cont_inv nbits (fp12_one ops) Qx Qy.
  Proof. unfold cont_inv, full_result. reflexivity. Qed.

  (** Step: one iteration preserves the invariant.
      affine_miller_aux at (S i) unfolds to: compute one step, then
      recurse at i. So if cont_inv (S i) f Tx Ty holds, then
      cont_inv i f' Tx' Ty' holds where (f', Tx', Ty') is the result
      of one double_step + conditional add_step applied to (f, Tx, Ty). *)
  (** The step is simply: unfold one level of affine_miller_aux. *)
  Lemma cont_inv_step (i : nat) (f : Fp12_Z) (Tx Ty : Fp2_Z)
    (f' : Fp12_Z) (Tx' Ty' : Fp2_Z)
    (Hstep :
      let '(fd, txd, tyd) := double_step ops f Tx Ty Px Py in
      let r := if Z.testbit n (Z.of_nat i) then
                 add_step ops fd txd tyd Qx Qy Px Py
               else (fd, txd, tyd) in
      (f', Tx', Ty') = r) :
    cont_inv (S i) f Tx Ty ->
    cont_inv i f' Tx' Ty'.
  Proof.
    unfold cont_inv. intro H.
    (* affine_miller_aux (S i) ... f Tx Ty = full_result.
       By definition, this unfolds to:
         let r = one_step(f, Tx, Ty) in
         affine_miller_aux i ... r.c0 r.c1 r.c2 = full_result.
       Hstep says (f', Tx', Ty') = one_step(f, Tx, Ty).
       So affine_miller_aux i ... f' Tx' Ty' = full_result. *)
    change (affine_miller_aux ops n (S i) Px Py Qx Qy f Tx Ty)
      with (let '(fd, txd, tyd) := double_step ops f Tx Ty Px Py in
            let '(fa, txa, tya) :=
              if Z.testbit n (Z.of_nat i) then
                add_step ops fd txd tyd Qx Qy Px Py
              else (fd, txd, tyd) in
            affine_miller_aux ops n i Px Py Qx Qy fa txa tya) in H.
    destruct (double_step ops f Tx Ty Px Py) as [[fd txd] tyd] in *.
    destruct (Z.testbit n (Z.of_nat i)) in *.
    - destruct (add_step ops fd txd tyd Qx Qy Px Py) as [[fa txa] tya] in *.
      injection Hstep as -> -> ->. exact H.
    - injection Hstep as -> -> ->. exact H.
  Qed.

  (** Exit: at i = 0, affine_miller_aux returns the accumulator unchanged,
      so the invariant gives f = full_result. *)
  Lemma cont_inv_exit (f : Fp12_Z) (Tx Ty : Fp2_Z) :
    cont_inv 0 f Tx Ty ->
    f = fst (fst full_result).
  Proof.
    unfold cont_inv.
    simpl affine_miller_aux.
    intros H. rewrite <- H. reflexivity.
  Qed.

  (** Final connection to [affine_miller]. *)
  Lemma cont_inv_gives_affine_miller (f : Fp12_Z) (Tx Ty : Fp2_Z) :
    cont_inv 0 f Tx Ty ->
    f = affine_miller ops n Px Py Qx Qy.
  Proof.
    unfold cont_inv. simpl affine_miller_aux.
    unfold affine_miller, full_result, nbits.
    set (r := affine_miller_aux ops n _ Px Py Qx Qy _ Qx Qy).
    intro H. assert (f = fst (fst r)) by (rewrite <- H; reflexivity).
    destruct r as [[? ?] ?]; exact H0.
  Qed.

End LoopInvariant.
