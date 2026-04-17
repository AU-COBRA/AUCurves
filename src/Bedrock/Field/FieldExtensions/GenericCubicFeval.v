(** * Generic algebraic identities for cubic extensions.
    Requires: a stdlib [ring_theory] for the base field,
    and [mul_by_nr_add] (linearity of mul_by_nonresidue). *)

Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
From Stdlib Require Import Ring_theory Ring.

Section CubicFeval.
  Context {F : Type} {fp : FieldParameters F}.
  Variable mul_by_nr : F -> F.

  Hypothesis Frt : ring_theory (@Fzero _ fp) (@Fone _ fp)
    (@Fadd _ fp) (@Fmul _ fp) (@Fsub _ fp) (@Fopp _ fp) (@eq F).
  Add Ring base_ring_ce : Frt.

  Hypothesis mul_by_nr_add : forall x y,
    mul_by_nr (Fadd x y) = Fadd (mul_by_nr x) (mul_by_nr y).
  Hypothesis mul_by_nr_sub : forall x y,
    mul_by_nr (Fsub x y) = Fsub (mul_by_nr x) (mul_by_nr y).

  Local Notation CE := (F * F * F)%type.

  Lemma ce_sub_sub_eq_sub_add : forall x y z : CE,
    @ce_sub _ fp (@ce_sub _ fp x y) z =
    @ce_sub _ fp x (@ce_add _ fp y z).
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2] [[z0 z1] z2].
    unfold ce_sub, ce_add, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    f_equal; [f_equal |]; ring.
  Qed.

  Lemma ce_add_sub_eq_sub_add : forall x y z : CE,
    @ce_add _ fp (@ce_sub _ fp x y) z =
    @ce_sub _ fp (@ce_add _ fp x z) y.
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2] [[z0 z1] z2].
    unfold ce_add, ce_sub, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    f_equal; [f_equal |]; ring.
  Qed.

  Lemma ce_mul_self_eq_sqr : forall a : CE,
    ce_mul mul_by_nr a a = ce_sqr mul_by_nr a.
  Proof.
    intros [[a0 a1] a2].
    unfold ce_mul, ce_sqr, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    f_equal; [f_equal |].
    - f_equal.
      assert (Harg : Fsub (Fsub (Fmul (Fadd a1 a2) (Fadd a1 a2)) (Fmul a1 a1)) (Fmul a2 a2) = Fadd (Fmul a1 a2) (Fmul a1 a2)) by ring.
      rewrite Harg. reflexivity.
    - f_equal; ring.
    - (* c2: pure ring, no mul_by_nr *) ring.
  Qed.

  Lemma ce_karatsuba_cross_term : forall a b : CE,
    @ce_sub _ fp
      (@ce_sub _ fp
        (ce_mul mul_by_nr (@ce_add _ fp a b) (@ce_add _ fp a b))
        (ce_mul mul_by_nr a a))
      (ce_mul mul_by_nr b b) =
    @ce_add _ fp (ce_mul mul_by_nr a b) (ce_mul mul_by_nr a b).
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold ce_mul, ce_add, ce_sub, ce_build, ce_c0, ce_c1, ce_c2;
      simpl fst; simpl snd.
    (* Split componentwise: ((c0,c1),c2) = ((c0',c1'),c2') *)
    apply (fun H1 H2 H3 => f_equal2 pair (f_equal2 pair H1 H2) H3).
    - (* c0: simplify mul_by_nr arguments via ring, distribute, generalize *)
      assert (HK : forall x y : F,
        Fsub (Fsub (Fmul (Fadd x y) (Fadd x y)) (Fmul x x)) (Fmul y y) =
        Fadd (Fmul x y) (Fmul x y)) by (intros; ring).
      replace (mul_by_nr (Fsub (Fsub (Fmul (Fadd (Fadd a1 b1) (Fadd a2 b2)) (Fadd (Fadd a1 b1) (Fadd a2 b2))) (Fmul (Fadd a1 b1) (Fadd a1 b1))) (Fmul (Fadd a2 b2) (Fadd a2 b2))))
        with (mul_by_nr (Fadd (Fmul (Fadd a1 b1) (Fadd a2 b2)) (Fmul (Fadd a1 b1) (Fadd a2 b2))))
        by (f_equal; symmetry; apply HK).
      replace (mul_by_nr (Fsub (Fsub (Fmul (Fadd a1 a2) (Fadd a1 a2)) (Fmul a1 a1)) (Fmul a2 a2)))
        with (mul_by_nr (Fadd (Fmul a1 a2) (Fmul a1 a2)))
        by (f_equal; symmetry; apply HK).
      replace (mul_by_nr (Fsub (Fsub (Fmul (Fadd b1 b2) (Fadd b1 b2)) (Fmul b1 b1)) (Fmul b2 b2)))
        with (mul_by_nr (Fadd (Fmul b1 b2) (Fmul b1 b2)))
        by (f_equal; symmetry; apply HK).
      assert (HK2 : forall x1 x2 y1 y2 : F,
        Fsub (Fsub (Fmul (Fadd x1 x2) (Fadd y1 y2)) (Fmul x1 y1)) (Fmul x2 y2) =
        Fadd (Fmul x1 y2) (Fmul x2 y1)) by (intros; ring).
      replace (mul_by_nr (Fsub (Fsub (Fmul (Fadd a1 a2) (Fadd b1 b2)) (Fmul a1 b1)) (Fmul a2 b2)))
        with (mul_by_nr (Fadd (Fmul a1 b2) (Fmul a2 b1)))
        by (f_equal; symmetry; apply HK2).
      clear HK HK2. rewrite !mul_by_nr_add.
      replace (Fmul (Fadd a1 b1) (Fadd a2 b2))
        with (Fadd (Fadd (Fmul a1 a2) (Fmul a1 b2)) (Fadd (Fmul b1 a2) (Fmul b1 b2))) by ring.
      rewrite !mul_by_nr_add.
      replace (Fmul b1 a2) with (Fmul a2 b1) by ring.
      generalize (mul_by_nr (Fmul a1 a2)) (mul_by_nr (Fmul a1 b2))
                 (mul_by_nr (Fmul a2 b1)) (mul_by_nr (Fmul b1 b2)).
      intros; ring.
    - (* c1: same technique — extract mul_by_nr, combine, simplify *)
      assert (HFS : forall X Y Z W : F,
        Fsub (Fadd X (mul_by_nr Y)) (Fadd Z (mul_by_nr W)) =
        Fadd (Fsub X Z) (Fsub (mul_by_nr Y) (mul_by_nr W)))
        by (intros; ring).
      rewrite !HFS. clear HFS. rewrite <- !mul_by_nr_sub.
      assert (HFS2 : forall X Y Z W : F,
        Fsub (Fadd X (mul_by_nr Y)) (Fadd Z (mul_by_nr W)) =
        Fadd (Fsub X Z) (Fsub (mul_by_nr Y) (mul_by_nr W)))
        by (intros; ring).
      rewrite HFS2. clear HFS2. rewrite <- mul_by_nr_sub.
      assert (HK : forall x y : F,
        Fsub (Fsub (Fmul (Fadd x y) (Fadd x y)) (Fmul x x)) (Fmul y y) =
        Fadd (Fmul x y) (Fmul x y)) by (intros; ring).
      replace (mul_by_nr (Fsub (Fsub (Fmul (Fadd a2 b2) (Fadd a2 b2)) (Fmul a2 a2)) (Fmul b2 b2)))
        with (mul_by_nr (Fadd (Fmul a2 b2) (Fmul a2 b2)))
        by (f_equal; symmetry; apply HK).
      clear HK. rewrite mul_by_nr_add.
      generalize (mul_by_nr (Fmul a2 b2)). intro; ring.
    - (* c2: no mul_by_nr *) ring.
  Qed.

  Lemma ce_mul_comm : forall x y : CE,
    ce_mul mul_by_nr x y = ce_mul mul_by_nr y x.
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2].
    unfold ce_mul, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    apply (fun H1 H2 H3 => f_equal2 pair (f_equal2 pair H1 H2) H3);
      unfold ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    - (* c0 *) f_equal. { ring. } f_equal. ring.
    - (* c1 *) f_equal. { f_equal; ring. } f_equal. ring.
    - (* c2 *) f_equal. { f_equal; ring. } ring.
  Qed.

End CubicFeval.
