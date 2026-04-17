(** * Generic algebraic identities for quadratic extensions.
    Requires: a stdlib [ring_theory] for the base field. *)

Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
From Stdlib Require Import Ring_theory Ring.

Section QuadraticFeval.
  Context {F : Type} {fp : FieldParameters F}.
  Variable nonresidue : F.

  Hypothesis Frt : ring_theory (@Fzero _ fp) (@Fone _ fp)
    (@Fadd _ fp) (@Fmul _ fp) (@Fsub _ fp) (@Fopp _ fp) (@eq F).
  Add Ring base_ring : Frt.

  Local Notation QE := (F * F)%type.

  Lemma qe_sub_sub_eq_sub_add : forall x y z : QE,
    @qe_sub _ fp (@qe_sub _ fp x y) z =
    @qe_sub _ fp x (@qe_add _ fp y z).
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold qe_sub, qe_add; simpl fst; simpl snd. f_equal; ring.
  Qed.

  Lemma qe_add_sub_eq_sub_add : forall x y z : QE,
    @qe_add _ fp (@qe_sub _ fp x y) z =
    @qe_sub _ fp (@qe_add _ fp x z) y.
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold qe_add, qe_sub; simpl fst; simpl snd. f_equal; ring.
  Qed.

  Lemma qe_mul_comm : forall x y : QE,
    @qe_mul _ fp nonresidue x y = @qe_mul _ fp nonresidue y x.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold qe_mul; simpl fst; simpl snd. f_equal; ring.
  Qed.

  Lemma qe_mul_self_alt : forall x : QE,
    @qe_mul _ fp nonresidue x x =
    (Fadd (Fmul (fst x) (fst x)) (Fmul nonresidue (Fmul (snd x) (snd x))),
     Fadd (Fmul (fst x) (snd x)) (Fmul (fst x) (snd x))).
  Proof.
    intros [a0 a1]. unfold qe_mul; simpl fst; simpl snd. f_equal; ring.
  Qed.

  Lemma qe_karatsuba_cross_term : forall a b : QE,
    @qe_sub _ fp
      (@qe_sub _ fp
        (@qe_mul _ fp nonresidue (@qe_add _ fp a b) (@qe_add _ fp a b))
        (@qe_mul _ fp nonresidue a a))
      (@qe_mul _ fp nonresidue b b) =
    @qe_add _ fp (@qe_mul _ fp nonresidue a b) (@qe_mul _ fp nonresidue a b).
  Proof.
    intros [a0 a1] [b0 b1].
    unfold qe_mul, qe_add, qe_sub; simpl fst; simpl snd. f_equal; ring.
  Qed.

End QuadraticFeval.
