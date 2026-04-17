(** * Generic quadratic extension F[u]/(u² - nr) for any field F.
    Unlike QuadraticExtensionsGeneric.v (which uses F p), this works for
    any type with FieldParameters.

    Used by GenericQuadraticSpecs.v to build FieldParameters/FieldRepresentation
    for arbitrary base fields (Fp, Fp2, Fp4, Fp6, ...). *)

Require Import Bedrock.Specs.AbstractField.

Section QuadExtAbstract.
  Context {F : Type} {fp : FieldParameters F}.

  Variable nonresidue : F.

  Local Notation QE := (F * F)%type.

  Definition qe_zero : QE := (Fzero, Fzero).
  Definition qe_one  : QE := (Fone, Fzero).

  Definition qe_add (x y : QE) : QE :=
    (Fadd (fst x) (fst y), Fadd (snd x) (snd y)).

  Definition qe_sub (x y : QE) : QE :=
    (Fsub (fst x) (fst y), Fsub (snd x) (snd y)).

  Definition qe_opp (x : QE) : QE :=
    (Fopp (fst x), Fopp (snd x)).

  (** (a + bu)(c + du) = (ac + nr·bd) + (ad + bc)u *)
  Definition qe_mul (x y : QE) : QE :=
    (Fadd (Fmul (fst x) (fst y)) (Fmul nonresidue (Fmul (snd x) (snd y))),
     Fadd (Fmul (fst x) (snd y)) (Fmul (snd x) (fst y))).

  (** (a + bu)^{-1} = (a, -b) / (a² - nr·b²) *)
  Definition qe_inv (x : QE) : QE :=
    let norm := Fsub (Fmul (fst x) (fst x)) (Fmul nonresidue (Fmul (snd x) (snd x))) in
    let inv_norm := Finv norm in
    (Fmul (fst x) inv_norm, Fmul (Fopp (snd x)) inv_norm).

  Definition qe_div (x y : QE) : QE := qe_mul x (qe_inv y).

  (** Decidable Leibniz equality from base field decidable equality. *)
  Variable eq_dec_F : forall x y : F, {x = y} + {x <> y}.

  Lemma eq_dec_QE : forall x y : QE, {x = y} + {x <> y}.
  Proof.
    intros [a0 a1] [b0 b1].
    destruct (eq_dec_F a0 b0); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_F a1 b1); [|right; intro H; inversion H; contradiction].
    left; subst; reflexivity.
  Defined.

End QuadExtAbstract.
