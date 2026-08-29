(** * RcbGeneralAChain — the closure algebra of the general-a RCB
      complete addition, stated once at the mont_enc level.

    The bedrock2 WP proofs of the G1-add functor instances
    ([Bedrock.Curve.P256_G1_Add_Functor_Instance] and the P-384/P-224
    siblings) end with a goal [BLS12_add_mont_spec ... outx outy outz]
    and a context of forty call equations
    [eval (from_mont z) mod m = (eval (from_mont x) OP eval (from_mont y)) mod m],
    one per field-op call S1..S40 of [WbwMontgomeryG1GeneralA.rcb_ops].
    Rewriting those equations into the goal inside the WP context
    grows the goal as a tree and does not terminate.  Here the same
    algebra is a standalone lemma over fresh names [x1 .. x40]: in-place
    reuse of the bedrock2 temporaries is expanded, each hypothesis
    mentions only earlier names, and the conclusion is the spec at
    [(x37, x34, x40)].  The proof is [subst] followed by [reflexivity]:
    the expanded term is the spec's own let-chain (133 nodes).

    [rcb_general_a_chain_Z] restates the lemma over the Z-lists and
    [valid'] proofs that the WP context actually holds, so that the
    instance closure is [eapply rcb_general_a_chain_Z] followed by one
    [eassumption] per premise. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveG1Equiv.

Section RcbGeneralAChain.
  Open Scope Z_scope.
  Local Coercion Z.of_nat : nat >-> Z.

  Context (m : Z) (bw : Z) (n : nat) (r' : Z) (m' : Z)
          (a_val : Z) (three_b_val : Z)
          (a_small : a_val = a_val mod m)
          (three_b_small : three_b_val = three_b_val mod m).

  Local Notation r := (MontgomeryRingTheory.r bw).

  Context (r'_correct : (r * r') mod m = 1)
          (m'_correct : (m * m') mod r = (-1) mod r)
          (bw_big : 0 < bw)
          (n_nz : n <> 0%nat)
          (m_small : m < r ^ (n%nat))
          (m_big : 1 < m).

  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation from_mont :=
    (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation valid' := (valid' m bw n).
  Local Notation mont_enc := (mont_enc m bw n).
  Local Notation enc_mont := (enc_mont m bw n).

  (* Precedence below [=] (level 70): [x = y *mont z] is [x = (y *mont z)]. *)
  Local Notation "x *mont y" :=
    (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y)
    (at level 40, left associativity).
  Local Notation "x +mont y" :=
    (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y)
    (at level 50, left associativity).
  Local Notation "x -mont y" :=
    (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y)
    (at level 50, left associativity).
  Local Notation valid_valid'_equiv :=
    (valid_valid'_equiv m bw n n_nz m_big).
  Local Notation evfrom_mod :=
    (evfrom_mod' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation eval_from_mont_inj :=
    (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

  Add Ring Mp :
    (MontgomeryRingTheory.mont_enc_ring m bw n r' m'
       r'_correct m'_correct bw_big n_nz m_small m_big).

  Local Notation a_mont :=
    (MontgomeryCurveG1Equiv.a_mont m bw n r' m' a_val a_small
       r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation three_b_mont :=
    (MontgomeryCurveG1Equiv.three_b_mont m bw n r' m' three_b_val
       three_b_small r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation add_mont_spec :=
    (MontgomeryCurveG1Equiv.BLS12_add_mont_spec m bw n r' m' a_val three_b_val
       a_small three_b_small r'_correct m'_correct bw_big n_nz m_small m_big).

  (** ** The chain at the mont_enc level.

      Names follow [rcb_ops] S1..S40; [A] and [B] are the [a_const]
      and [three_b] buffers.  The mapping from bedrock2 temporaries:
      x1=t0 x2=t1 x3=t2 x4=t3 x5=t4 x6=t3 x7=t4 x8=t3 x9=t4 x10=t5
      x11=t4 x12=t5 x13=t4 x14=t5 x15=outx x16=t5 x17=outx x18=t5
      x19=outz x20=outx x21=outz x22=outx x23=outz x24=outy x25=t1
      x26=t1 x27=t2 x28=t4 x29=t1 x30=t2 x31=t2 x32=t4 x33=t0
      x34=outy x35=t0 x36=outx x37=outx x38=t0 x39=outz x40=outz. *)
  Lemma rcb_general_a_chain
        (X1 Y1 Z1 X2 Y2 Z2 A B : mont_enc)
        (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
         x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
         x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 : mont_enc)
        (HA : A = a_mont) (HB : B = three_b_mont)
        (H1  : x1  = X1  *mont X2)
        (H2  : x2  = Y1  *mont Y2)
        (H3  : x3  = Z1  *mont Z2)
        (H4  : x4  = X1  +mont Y1)
        (H5  : x5  = X2  +mont Y2)
        (H6  : x6  = x4  *mont x5)
        (H7  : x7  = x1  +mont x2)
        (H8  : x8  = x6  -mont x7)
        (H9  : x9  = X1  +mont Z1)
        (H10 : x10 = X2  +mont Z2)
        (H11 : x11 = x9  *mont x10)
        (H12 : x12 = x1  +mont x3)
        (H13 : x13 = x11 -mont x12)
        (H14 : x14 = Y1  +mont Z1)
        (H15 : x15 = Y2  +mont Z2)
        (H16 : x16 = x14 *mont x15)
        (H17 : x17 = x2  +mont x3)
        (H18 : x18 = x16 -mont x17)
        (H19 : x19 = A   *mont x13)
        (H20 : x20 = B   *mont x3)
        (H21 : x21 = x20 +mont x19)
        (H22 : x22 = x2  -mont x21)
        (H23 : x23 = x21 +mont x2)
        (H24 : x24 = x22 *mont x23)
        (H25 : x25 = x1  +mont x1)
        (H26 : x26 = x25 +mont x1)
        (H27 : x27 = A   *mont x3)
        (H28 : x28 = B   *mont x13)
        (H29 : x29 = x26 +mont x27)
        (H30 : x30 = x1  -mont x27)
        (H31 : x31 = A   *mont x30)
        (H32 : x32 = x28 +mont x31)
        (H33 : x33 = x29 *mont x32)
        (H34 : x34 = x24 +mont x33)
        (H35 : x35 = x18 *mont x32)
        (H36 : x36 = x8  *mont x22)
        (H37 : x37 = x36 -mont x35)
        (H38 : x38 = x8  *mont x29)
        (H39 : x39 = x18 *mont x23)
        (H40 : x40 = x39 +mont x38) :
    add_mont_spec X1 Y1 Z1 X2 Y2 Z2 x37 x34 x40.
  Proof.
    (* S23 is [outz := outz + t1] in [rcb_ops] but [t1 +mont Z3] in the
       spec; after commuting H23 the substituted term is the spec's
       zeta-reduced let-chain verbatim, so no ring normalization is
       needed: the equality is syntactic. *)
    rewrite (mont_add_comm m bw n r' m' r'_correct m'_correct bw_big n_nz
               m_small m_big x21 x2) in H23.
    unfold MontgomeryCurveG1Equiv.BLS12_add_mont_spec.
    Timeout 120 subst.
    Timeout 120 cbv zeta.
    Timeout 120 reflexivity.
  Qed.

  (** ** Bridge from the WP-context form.

      A call equation [eval (from_mont z) mod m = (eval (from_mont x)
      OP eval (from_mont y)) mod m] with [valid'] witnesses for x, y, z
      is the mont_enc equation [enc_mont z Hz = enc_mont x Hx OP
      enc_mont y Hy].  Identical to the instance-file [mont*_to_Mp]. *)
  Lemma montadd_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    eval (from_mont z) mod m = (eval (from_mont x) + eval (from_mont y)) mod m ->
    enc_mont z Hz = enc_mont x Hx +mont enc_mont y Hy.
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_add_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montsub_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    eval (from_mont z) mod m = (eval (from_mont x) - eval (from_mont y)) mod m ->
    enc_mont z Hz = enc_mont x Hx -mont enc_mont y Hy.
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_sub_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montmul_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    eval (from_mont z) mod m = (eval (from_mont x) * eval (from_mont y)) mod m ->
    enc_mont z Hz = enc_mont x Hx *mont enc_mont y Hy.
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_mul_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Local Notation montmul z x y :=
    (eval (from_mont z) mod m = (eval (from_mont x) * eval (from_mont y)) mod m).
  Local Notation montadd z x y :=
    (eval (from_mont z) mod m = (eval (from_mont x) + eval (from_mont y)) mod m).
  Local Notation montsub z x y :=
    (eval (from_mont z) mod m = (eval (from_mont x) - eval (from_mont y)) mod m).

  (** The chain over Z-lists.  Premise order is the order in which
      [eapply ...; all: eassumption] must resolve them: the forty call
      equations first (each determines its output list from inputs
      already fixed), then the [valid'] witnesses of the intermediates,
      then the two constant-buffer identifications. *)
  Lemma rcb_general_a_chain_Z
        (X1 Y1 Z1 X2 Y2 Z2 A B : list Z)
        (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
         x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
         x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 : list Z)
        (HX1 : valid' X1) (HY1 : valid' Y1) (HZ1 : valid' Z1)
        (HX2 : valid' X2) (HY2 : valid' Y2) (HZ2 : valid' Z2)
        (H37 : valid' x37) (H34 : valid' x34) (H40 : valid' x40)
        (E1  : montmul x1  X1  X2)
        (E2  : montmul x2  Y1  Y2)
        (E3  : montmul x3  Z1  Z2)
        (E4  : montadd x4  X1  Y1)
        (E5  : montadd x5  X2  Y2)
        (E6  : montmul x6  x4  x5)
        (E7  : montadd x7  x1  x2)
        (E8  : montsub x8  x6  x7)
        (E9  : montadd x9  X1  Z1)
        (E10 : montadd x10 X2  Z2)
        (E11 : montmul x11 x9  x10)
        (E12 : montadd x12 x1  x3)
        (E13 : montsub x13 x11 x12)
        (E14 : montadd x14 Y1  Z1)
        (E15 : montadd x15 Y2  Z2)
        (E16 : montmul x16 x14 x15)
        (E17 : montadd x17 x2  x3)
        (E18 : montsub x18 x16 x17)
        (E19 : montmul x19 A   x13)
        (E20 : montmul x20 B   x3)
        (E21 : montadd x21 x20 x19)
        (E22 : montsub x22 x2  x21)
        (E23 : montadd x23 x21 x2)
        (E24 : montmul x24 x22 x23)
        (E25 : montadd x25 x1  x1)
        (E26 : montadd x26 x25 x1)
        (E27 : montmul x27 A   x3)
        (E28 : montmul x28 B   x13)
        (E29 : montadd x29 x26 x27)
        (E30 : montsub x30 x1  x27)
        (E31 : montmul x31 A   x30)
        (E32 : montadd x32 x28 x31)
        (E33 : montmul x33 x29 x32)
        (E34 : montadd x34 x24 x33)
        (E35 : montmul x35 x18 x32)
        (E36 : montmul x36 x8  x22)
        (E37 : montsub x37 x36 x35)
        (E38 : montmul x38 x8  x29)
        (E39 : montmul x39 x18 x23)
        (E40 : montadd x40 x39 x38)
        (H1 : valid' x1) (H2 : valid' x2) (H3 : valid' x3) (H4 : valid' x4)
        (H5 : valid' x5) (H6 : valid' x6) (H7 : valid' x7) (H8 : valid' x8)
        (H9 : valid' x9) (H10 : valid' x10) (H11 : valid' x11)
        (H12 : valid' x12) (H13 : valid' x13) (H14 : valid' x14)
        (H15 : valid' x15) (H16 : valid' x16) (H17 : valid' x17)
        (H18 : valid' x18) (H19 : valid' x19) (H20 : valid' x20)
        (H21 : valid' x21) (H22 : valid' x22) (H23 : valid' x23)
        (H24 : valid' x24) (H25 : valid' x25) (H26 : valid' x26)
        (H27 : valid' x27) (H28 : valid' x28) (H29 : valid' x29)
        (H30 : valid' x30) (H31 : valid' x31) (H32 : valid' x32)
        (H33 : valid' x33) (H35 : valid' x35) (H36 : valid' x36)
        (H38 : valid' x38) (H39 : valid' x39)
        (HAeq : A = val m bw n a_mont)
        (HBeq : B = val m bw n three_b_mont) :
    add_mont_spec (enc_mont X1 HX1) (enc_mont Y1 HY1) (enc_mont Z1 HZ1)
                  (enc_mont X2 HX2) (enc_mont Y2 HY2) (enc_mont Z2 HZ2)
                  (enc_mont x37 H37) (enc_mont x34 H34) (enc_mont x40 H40).
  Proof.
    subst A B.
    assert (HAeq : enc_mont (val m bw n a_mont) (Hvalid m bw n a_mont) = a_mont)
      by (apply mont_enc_irr; reflexivity).
    assert (HBeq : enc_mont (val m bw n three_b_mont) (Hvalid m bw n three_b_mont)
                   = three_b_mont)
      by (apply mont_enc_irr; reflexivity).
    apply (rcb_general_a_chain
             (enc_mont X1 HX1) (enc_mont Y1 HY1) (enc_mont Z1 HZ1)
             (enc_mont X2 HX2) (enc_mont Y2 HY2) (enc_mont Z2 HZ2)
             (enc_mont (val m bw n a_mont) (Hvalid m bw n a_mont))
             (enc_mont (val m bw n three_b_mont) (Hvalid m bw n three_b_mont))
             (enc_mont x1 H1) (enc_mont x2 H2) (enc_mont x3 H3)
             (enc_mont x4 H4) (enc_mont x5 H5) (enc_mont x6 H6)
             (enc_mont x7 H7) (enc_mont x8 H8) (enc_mont x9 H9)
             (enc_mont x10 H10) (enc_mont x11 H11) (enc_mont x12 H12)
             (enc_mont x13 H13) (enc_mont x14 H14) (enc_mont x15 H15)
             (enc_mont x16 H16) (enc_mont x17 H17) (enc_mont x18 H18)
             (enc_mont x19 H19) (enc_mont x20 H20) (enc_mont x21 H21)
             (enc_mont x22 H22) (enc_mont x23 H23) (enc_mont x24 H24)
             (enc_mont x25 H25) (enc_mont x26 H26) (enc_mont x27 H27)
             (enc_mont x28 H28) (enc_mont x29 H29) (enc_mont x30 H30)
             (enc_mont x31 H31) (enc_mont x32 H32) (enc_mont x33 H33)
             (enc_mont x34 H34) (enc_mont x35 H35) (enc_mont x36 H36)
             (enc_mont x37 H37) (enc_mont x38 H38) (enc_mont x39 H39)
             (enc_mont x40 H40) HAeq HBeq).
    (* One [exact] per premise, in premise order.  No [apply]-driven
       unification of [mont_mul] against [mont_add]: that would delta-
       unfold the word-by-word Montgomery bodies. *)
    all: timeout 60 (lazymatch goal with
         | |- (_ = mont_mul _ _ _ _ _ _ _ _ _ _ _ _ _) =>
           refine (montmul_to_Mp _ _ _ _ _ _ _)
         | |- (_ = mont_add _ _ _ _ _ _ _ _ _ _ _ _ _) =>
           refine (montadd_to_Mp _ _ _ _ _ _ _)
         | |- (_ = mont_sub _ _ _ _ _ _ _ _ _ _ _ _ _) =>
           refine (montsub_to_Mp _ _ _ _ _ _ _)
         end).
    all: timeout 60 assumption.
  Qed.

End RcbGeneralAChain.
