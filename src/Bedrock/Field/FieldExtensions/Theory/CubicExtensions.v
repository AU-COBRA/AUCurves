(* Cubic field extension theory for Fp6 = Fp2[v]/(v³ - ξ)
   where Fp2 = Fp[u]/(u² - β) and ξ ∈ Fp2 is a cubic non-residue.
   For BLS12-381: β = -1 (so u² = -1) and ξ = 1 + u. *)

From Coq Require Import ZArith Znumtheory.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
From Coq Require Import Field.
Require Import Coqprime.elliptic.GZnZ.
From Coqprime Require Import Zp.
From Coqprime Require Import Pmod.
Require Import Zpow_facts.
Require Import Znat.

Section CubicExtension.

  Variable p : positive.
  Hypothesis p_prime : prime p.
  Hypothesis p_odd : 2 < p.

  (* --- Fp notations --- *)

  Notation Fp := (F p).
  Notation "x +p y" := (@F.add p x y) (at level 100).
  Notation "x *p y" := (@F.mul p x y) (at level 90).
  Notation "x -p y" := (@F.sub p x y) (at level 100).
  Notation "x /p y" := (@F.div p x y) (at level 90).
  Notation "'0p'" := (@F.zero p).
  Notation "'1p'" := (@F.one p).

  (* Register Fp as a field for the `field` tactic *)
  Add Field Fp_field : field_theory_for_stdlib_tactic.

  (* --- Fp2 definitions (parameterized by quadratic non-residue β) --- *)

  Variable beta : Fp.
  Hypothesis beta_nonzero : beta <> 0p.

  Notation "'β'" := beta.

  Notation Fp2 := (Fp * Fp)%type.

  Definition fp2_zero : Fp2 := (0p, 0p).
  Definition fp2_one : Fp2 := (1p, 0p).

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (fst a +p fst b, snd a +p snd b).

  Definition fp2_opp (a : Fp2) : Fp2 :=
    (@F.opp p (fst a), @F.opp p (snd a)).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (fst a -p fst b, snd a -p snd b).

  (* Multiplication in Fp[u]/(u² - β): (a₀ + a₁u)(b₀ + b₁u) = (a₀b₀ + β·a₁b₁) + (a₀b₁ + a₁b₀)u *)
  Definition fp2_mul (a b : Fp2) : Fp2 :=
    (fst a *p fst b +p β *p snd a *p snd b,
     fst a *p snd b +p snd a *p fst b).

  (* Helper: equality of Fp2 pairs *)
  Lemma Fp2irr : forall (x1 x2 y1 y2 : Fp),
    x1 = y1 -> x2 = y2 -> (x1, x2) = (y1, y2).
  Proof. intros; subst; reflexivity. Qed.

  (* Fp2 ring theory *)
  Lemma RFp2 : ring_theory fp2_zero fp2_one fp2_add fp2_mul fp2_sub fp2_opp (@eq Fp2).
  Proof.
    split; intros; case x; intros; refine (Fp2irr _ _ _ _ _ _); simpl; field.
  Qed.

  (* --- Cubic non-residue ξ ∈ Fp2 --- *)

  Variable xi0 : Fp.  (* real part of ξ *)
  Variable xi1 : Fp.  (* imaginary part of ξ *)

  (* For BLS12-381, ξ = 1 + u, so xi0 = 1, xi1 = 1 *)

  Definition xi : Fp2 := (xi0, xi1).

  (* ξ-multiplication: multiply an Fp2 element by ξ *)
  (* (a₀ + a₁u)(ξ₀ + ξ₁u) = (a₀ξ₀ + β·a₁ξ₁) + (a₀ξ₁ + a₁ξ₀)u *)
  Definition fp2_mul_xi (a : Fp2) : Fp2 := fp2_mul a xi.

  (* --- Fp6 type: triples (c0, c1, c2) representing c0 + c1·v + c2·v² --- *)
  (*     where v³ = ξ                                                       *)

  Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Definition fp6_c0 (x : Fp6) : Fp2 := fst (fst x).
  Definition fp6_c1 (x : Fp6) : Fp2 := snd (fst x).
  Definition fp6_c2 (x : Fp6) : Fp2 := snd x.
  Definition mk_fp6 (c0 c1 c2 : Fp2) : Fp6 := ((c0, c1), c2).

  Definition fp6_zero : Fp6 := mk_fp6 fp2_zero fp2_zero fp2_zero.
  Definition fp6_one : Fp6 := mk_fp6 fp2_one fp2_zero fp2_zero.

  (* Fp6 addition: component-wise *)
  Definition fp6_add (a b : Fp6) : Fp6 :=
    mk_fp6 (fp2_add (fp6_c0 a) (fp6_c0 b))
            (fp2_add (fp6_c1 a) (fp6_c1 b))
            (fp2_add (fp6_c2 a) (fp6_c2 b)).

  (* Fp6 negation: component-wise *)
  Definition fp6_opp (a : Fp6) : Fp6 :=
    mk_fp6 (fp2_opp (fp6_c0 a)) (fp2_opp (fp6_c1 a)) (fp2_opp (fp6_c2 a)).

  (* Fp6 subtraction *)
  Definition fp6_sub (a b : Fp6) : Fp6 :=
    mk_fp6 (fp2_sub (fp6_c0 a) (fp6_c0 b))
            (fp2_sub (fp6_c1 a) (fp6_c1 b))
            (fp2_sub (fp6_c2 a) (fp6_c2 b)).

  (* Fp6 multiplication using Karatsuba-like algorithm:
     Given a = a0 + a1·v + a2·v²  and  b = b0 + b1·v + b2·v²
     where v³ = ξ, the product is:

     c0 = a0·b0 + ξ·((a1+a2)(b1+b2) - a1·b1 - a2·b2)
     c1 = (a0+a1)(b0+b1) - a0·b0 - a1·b1 + ξ·a2·b2
     c2 = (a0+a2)(b0+b2) - a0·b0 - a2·b2 + a1·b1
  *)
  Definition fp6_mul (a b : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
    let a0b0 := fp2_mul a0 b0 in
    let a1b1 := fp2_mul a1 b1 in
    let a2b2 := fp2_mul a2 b2 in
    let c0 := fp2_add a0b0
                (fp2_mul_xi (fp2_sub (fp2_mul (fp2_add a1 a2) (fp2_add b1 b2))
                                      (fp2_add a1b1 a2b2))) in
    let c1 := fp2_add (fp2_sub (fp2_mul (fp2_add a0 a1) (fp2_add b0 b1))
                                (fp2_add a0b0 a1b1))
                       (fp2_mul_xi a2b2) in
    let c2 := fp2_add (fp2_sub (fp2_mul (fp2_add a0 a2) (fp2_add b0 b2))
                                (fp2_add a0b0 a2b2))
                       a1b1 in
    mk_fp6 c0 c1 c2.

  (* v-shift: v·(c0 + c1·v + c2·v²) = ξ·c2 + c0·v + c1·v² *)
  Definition fp6_mul_by_v (a : Fp6) : Fp6 :=
    mk_fp6 (fp2_mul_xi (fp6_c2 a)) (fp6_c0 a) (fp6_c1 a).

  (* --- Helper lemmas for Fp6 proofs --- *)

  (* Equality of Fp6 triples reduces to component-wise equality *)
  Lemma Fp6irr : forall (a0 a1 a2 b0 b1 b2 : Fp2),
    a0 = b0 -> a1 = b1 -> a2 = b2 -> mk_fp6 a0 a1 a2 = mk_fp6 b0 b1 b2.
  Proof. intros; subst; reflexivity. Qed.

  (* Tactic to decompose Fp6 elements and reduce to Fp equalities *)
  (* Each Fp6 element is (((a0r, a0i), (a1r, a1i)), (a2r, a2i)) *)
  Ltac decompose_fp6 :=
    repeat match goal with
    | [ x : Fp6 |- _ ] =>
      let c0 := fresh "c0" in let c1 := fresh "c1" in let c2 := fresh "c2" in
      destruct x as [[c0 c1] c2]
    | [ x : Fp2 |- _ ] =>
      let r := fresh "r" in let i := fresh "i" in
      destruct x as [r i]
    end.

  Ltac unfold_fp6 :=
    cbv [fp6_add fp6_sub fp6_opp fp6_mul fp6_zero fp6_one
         fp6_c0 fp6_c1 fp6_c2 mk_fp6
         fp2_add fp2_sub fp2_opp fp2_mul fp2_mul_xi fp2_zero fp2_one
         xi fst snd].

  Ltac solve_fp2_eq := apply Fp2irr; simpl; field.

  Ltac fp6_field_step :=
    decompose_fp6; unfold_fp6;
    apply Fp6irr; try solve_fp2_eq.

  (* --- Fp6 ring theory --- *)

  Theorem RFp6 : ring_theory fp6_zero fp6_one fp6_add fp6_mul fp6_sub fp6_opp (@eq Fp6).
  Proof.
    split.
    (* Radd_0_l: 0 + x = x *)
    - intros x; fp6_field_step.
    (* Radd_comm: x + y = y + x *)
    - intros x y; fp6_field_step.
    (* Radd_assoc: x + (y + z) = (x + y) + z *)
    - intros x y z; fp6_field_step.
    (* Rmul_1_l: 1 * x = x *)
    - intros x; fp6_field_step.
    (* Rmul_comm: x * y = y * x *)
    - intros x y; fp6_field_step.
    (* Rmul_assoc: x * (y * z) = (x * y) * z *)
    - intros x y z; fp6_field_step.
    (* Rdistr_l: x * (y + z) = x * y + x * z *)
    - intros x y z; fp6_field_step.
    (* Rsub_def: x - y = x + (-y) *)
    - intros x y; fp6_field_step.
    (* Ropp_def: x + (-x) = 0 *)
    - intros x; fp6_field_step.
  Qed.

  (* --- Fp6 inverse --- *)

  (* For the inverse, we need an Fp2 inverse. We take it as a parameter
     since proving Fp2 is a field requires the quadratic non-residue property
     (shown in QuadraticExtensions.v). *)
  Variable fp2_inv : Fp2 -> Fp2.
  Hypothesis fp2_inv_correct : forall a, a <> fp2_zero -> fp2_mul (fp2_inv a) a = fp2_one.

  Definition fp6_norm (a : Fp6) : Fp2 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let A := fp2_sub (fp2_mul a0 a0) (fp2_mul_xi (fp2_mul a1 a2)) in
    let B := fp2_sub (fp2_mul_xi (fp2_mul a2 a2)) (fp2_mul a0 a1) in
    let C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2) in
    fp2_add (fp2_mul a0 A) (fp2_mul_xi (fp2_add (fp2_mul a2 B) (fp2_mul a1 C))).

  Hypothesis fp6_norm_nonzero : forall a, a <> fp6_zero -> fp6_norm a <> fp2_zero.

  (* Inverse in Fp6 = Fp2[v]/(v³ - ξ).
     Given a = a0 + a1·v + a2·v², the inverse uses the norm:
       A = a0² - ξ·a1·a2
       B = ξ·a2² - a0·a1
       C = a1² - a0·a2
       N = a0·A + ξ·(a2·B + a1·C)
       a⁻¹ = N⁻¹ · (A + B·v + C·v²)
  *)
  Definition fp6_inv (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let A := fp2_sub (fp2_mul a0 a0) (fp2_mul_xi (fp2_mul a1 a2)) in
    let B := fp2_sub (fp2_mul_xi (fp2_mul a2 a2)) (fp2_mul a0 a1) in
    let C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2) in
    let N := fp2_add (fp2_mul a0 A)
                      (fp2_mul_xi (fp2_add (fp2_mul a2 B) (fp2_mul a1 C))) in
    let N_inv := fp2_inv N in
    mk_fp6 (fp2_mul A N_inv) (fp2_mul B N_inv) (fp2_mul C N_inv).

  Definition fp6_div (a b : Fp6) : Fp6 := fp6_mul a (fp6_inv b).

  (* --- Field theory --- *)

  Add Ring Fp2_ring : RFp2.

  (* Notation for fp2_mul_xi unfolded: used in ring proofs *)
  Local Notation "'ξ'" := xi.

  (* The key algebraic identities for the inverse proof.
     After computing (A·Ni, B·Ni, C·Ni) * (a0, a1, a2), the three
     components of the Fp6 product factor as Ni times expressions
     that simplify to N, 0, 0 respectively. *)

  Lemma fp6_inv_c0 : forall (a0 a1 a2 : Fp2),
    let A := fp2_sub (fp2_mul a0 a0) (fp2_mul (fp2_mul a1 a2) ξ) in
    let B := fp2_sub (fp2_mul (fp2_mul a2 a2) ξ) (fp2_mul a0 a1) in
    let C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2) in
    let N := fp2_add (fp2_mul a0 A) (fp2_mul (fp2_add (fp2_mul a2 B) (fp2_mul a1 C)) ξ) in
    fp2_add (fp2_mul A a0) (fp2_mul (fp2_add (fp2_mul B a2) (fp2_mul C a1)) ξ) = N.
  Proof. intros. subst A B C N. ring. Qed.

  Lemma fp6_inv_c1 : forall (a0 a1 a2 : Fp2),
    let A := fp2_sub (fp2_mul a0 a0) (fp2_mul (fp2_mul a1 a2) ξ) in
    let B := fp2_sub (fp2_mul (fp2_mul a2 a2) ξ) (fp2_mul a0 a1) in
    let C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2) in
    fp2_add (fp2_add (fp2_mul A a1) (fp2_mul B a0)) (fp2_mul (fp2_mul C a2) ξ) = fp2_zero.
  Proof. intros. subst A B C. ring. Qed.

  Lemma fp6_inv_c2 : forall (a0 a1 a2 : Fp2),
    let A := fp2_sub (fp2_mul a0 a0) (fp2_mul (fp2_mul a1 a2) ξ) in
    let B := fp2_sub (fp2_mul (fp2_mul a2 a2) ξ) (fp2_mul a0 a1) in
    let C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2) in
    fp2_add (fp2_add (fp2_mul A a2) (fp2_mul B a1)) (fp2_mul C a0) = fp2_zero.
  Proof. intros. subst A B C. ring. Qed.

  Lemma fp6_one_neq_zero : fp6_one <> fp6_zero.
  Proof.
    unfold fp6_one, fp6_zero, mk_fp6, fp2_one, fp2_zero.
    intros H.
    apply (f_equal (fun z => fst (fst z))) in H. simpl in H.
    apply (f_equal (fun z => fst z)) in H. simpl in H.
    exact (F_1_neq_0 field_theory_for_stdlib_tactic H).
  Qed.

  Theorem FFp6 : field_theory fp6_zero fp6_one fp6_add fp6_mul
    fp6_sub fp6_opp fp6_div fp6_inv (@eq Fp6).
  Proof.
    split.
    - exact RFp6.
    - exact fp6_one_neq_zero.
    - reflexivity.
    - intros x Hx.
      destruct x as [[a0 a1] a2].
      (* Define the cofactors A, B, C with fp2_mul_xi unfolded *)
      set (A := fp2_sub (fp2_mul a0 a0) (fp2_mul (fp2_mul a1 a2) ξ)).
      set (B := fp2_sub (fp2_mul (fp2_mul a2 a2) ξ) (fp2_mul a0 a1)).
      set (C := fp2_sub (fp2_mul a1 a1) (fp2_mul a0 a2)).
      set (N := fp2_add (fp2_mul a0 A) (fp2_mul (fp2_add (fp2_mul a2 B) (fp2_mul a1 C)) ξ)).
      set (Ni := fp2_inv N).
      (* N equals fp6_norm applied to x *)
      assert (HNeq : N = fp6_norm ((a0, a1), a2)).
      { subst N A B C. unfold fp6_norm, fp6_c0, fp6_c1, fp6_c2, fst, snd, fp2_mul_xi. reflexivity. }
      (* N is nonzero for nonzero x *)
      assert (HN : N <> fp2_zero).
      { rewrite HNeq. apply fp6_norm_nonzero. exact Hx. }
      assert (HNi : fp2_mul Ni N = fp2_one).
      { apply fp2_inv_correct. exact HN. }
      (* The goal is fp6_mul (fp6_inv ((a0, a1), a2)) ((a0, a1), a2) = fp6_one.
         fp6_inv computes (A*Ni, B*Ni, C*Ni) using Karatsuba multiplication.
         We unfold everything to Fp2 level and use ring to simplify. *)
      unfold fp6_mul, fp6_inv, fp6_one, fp6_c0, fp6_c1, fp6_c2, mk_fp6, fst, snd, fp2_mul_xi.
      (* The A, B, C, N, Ni in the goal should match our set definitions *)
      fold A B C N Ni.
      f_equal. f_equal.
      + (* c0 = fp2_one: show LHS = Ni * N = 1 *)
        transitivity (fp2_mul Ni N); [| exact HNi].
        subst A B C N. ring.
      + (* c1 = fp2_zero *)
        subst A B C. ring.
      + (* c2 = fp2_zero *)
        subst A B C. ring.
  Qed.

  (* --- Decidable equality for Fp6 --- *)

  Lemma eq_dec_Fp2 : forall x y : Fp2, {x = y} + {x <> y}.
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (F.to_Z x1 =? F.to_Z y1) eqn:H1;
    destruct (F.to_Z x2 =? F.to_Z y2) eqn:H2.
    - left. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
      apply (f_equal (fun y => F.of_Z p y)) in H1, H2.
      repeat rewrite F.of_Z_to_Z in H1, H2.
      apply Fp2irr; auto.
    - right; apply Z.eqb_neq in H2; intros contra; inversion contra; subst; auto.
    - right; apply Z.eqb_neq in H1; intros contra; inversion contra; subst; auto.
    - right; apply Z.eqb_neq in H1; intros contra; inversion contra; subst; auto.
  Qed.

  Lemma eq_dec_Fp6 : forall x y : Fp6, {x = y} + {x <> y}.
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2].
    destruct (eq_dec_Fp2 x0 y0), (eq_dec_Fp2 x1 y1), (eq_dec_Fp2 x2 y2);
      first [ left; subst; reflexivity
            | right; intros H; inversion H; subst; contradiction ].
  Qed.

  (* --- Useful lemmas for downstream proofs --- *)

  Lemma fp6_mul_comm : forall a b, fp6_mul a b = fp6_mul b a.
  Proof. exact (Rmul_comm RFp6). Qed.

  Lemma fp6_mul_assoc : forall a b c, fp6_mul a (fp6_mul b c) = fp6_mul (fp6_mul a b) c.
  Proof. exact (Rmul_assoc RFp6). Qed.

  Lemma fp6_add_comm : forall a b, fp6_add a b = fp6_add b a.
  Proof. exact (Radd_comm RFp6). Qed.

  Lemma fp6_add_assoc : forall a b c, fp6_add a (fp6_add b c) = fp6_add (fp6_add a b) c.
  Proof. exact (Radd_assoc RFp6). Qed.

  Lemma fp6_distr_l : forall a b c, fp6_mul (fp6_add a b) c = fp6_add (fp6_mul a c) (fp6_mul b c).
  Proof. exact (Rdistr_l RFp6). Qed.

  Lemma fp6_add_0_l : forall a, fp6_add fp6_zero a = a.
  Proof. exact (Radd_0_l RFp6). Qed.

  Lemma fp6_mul_1_l : forall a, fp6_mul fp6_one a = a.
  Proof. exact (Rmul_1_l RFp6). Qed.

  Lemma fp6_opp_def : forall a, fp6_add a (fp6_opp a) = fp6_zero.
  Proof. exact (Ropp_def RFp6). Qed.

End CubicExtension.
