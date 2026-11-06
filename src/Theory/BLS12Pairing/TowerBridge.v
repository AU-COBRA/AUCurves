(** * Bridge between the generic tower of Fp6.v / Fp12.v and the tower of Pairing.v.

    With beta = -1 and xi = 1 + u (BLS12-381), the operations of
    [Theory.BLS12Pairing.Fp6] equal those of [Theory.BLS12Pairing.Pairing].
    These are the Fp6-level hypotheses of the sections of
    [Bedrock/Field/Synthesis/Examples/BLS12_Fp12Feval.v] and
    [BLS12_PairingFeval.v] (fp6_add_hyp ... fp6_inv_bridge), proved here
    for every modulus p (no primality needed).
*)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp6.
Require Import Theory.BLS12Pairing.Fp12Ring.
Module P := Theory.BLS12Pairing.Pairing.
Module G := Theory.BLS12Pairing.Fp6.

Section TowerBridge.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).
  Add Ring fp6_ring : (@fp6_ring_theory p).

  Let beta : F := F.of_Z p (-1).
  Let xi_re : F := @F.one p.
  Let xi_im : F := @F.one p.

  Lemma beta_eq : beta = F.opp F.one.
  Proof.
    cbv [beta]. change (-1)%Z with (Z.opp 1).
    rewrite (Ring_theory.morph_opp (F.ring_morph p)). reflexivity.
  Qed.

  Ltac fp2_br :=
    intros;
    repeat match goal with x : (F * F)%type |- _ => destruct x end;
    cbv [G.fp2_add G.fp2_sub G.fp2_neg G.fp2_mul G.fp2_sqr G.fp2_mul_xi G.fp2_conjugate
         G.fp2_mul_fp G.fp2_zero G.fp2_one
         P.fp2_add P.fp2_sub P.fp2_neg P.fp2_mul P.fp2_sqr P.fp2_mul_xi P.fp2_conjugate
         P.fp2_mul_fp P.fp2_zero P.fp2_one fst snd];
    rewrite ?beta_eq; cbv [xi_re xi_im];
    apply injective_projections; cbv [fst snd]; ring.

  (** Fp2 level. *)
  Lemma fp2_add_br : forall a b, G.fp2_add p a b = P.fp2_add p a b.
  Proof. reflexivity. Qed.
  Lemma fp2_sub_br : forall a b, G.fp2_sub p a b = P.fp2_sub p a b.
  Proof. reflexivity. Qed.
  Lemma fp2_neg_br : forall a, G.fp2_neg p a = P.fp2_neg p a.
  Proof. reflexivity. Qed.
  Lemma fp2_mul_br : forall a b, G.fp2_mul p beta a b = P.fp2_mul p a b.
  Proof. fp2_br. Qed.
  Lemma fp2_sqr_br : forall a, G.fp2_sqr p beta a = P.fp2_mul p a a.
  Proof. fp2_br. Qed.
  Lemma fp2_mul_xi_br : forall a, G.fp2_mul_xi p beta xi_re xi_im a = P.fp2_mul_xi p a.
  Proof. fp2_br. Qed.
  Lemma fp2_inv_br : forall a, G.fp2_inv p beta a = P.fp2_inv p a.
  Proof.
    intros [a0 a1]. cbv [G.fp2_inv P.fp2_inv fst snd].
    replace (F.sub (F.mul a0 a0) (F.mul (F.mul beta a1) a1))
      with (F.add (F.mul a0 a0) (F.mul a1 a1)) by (rewrite beta_eq; ring).
    reflexivity.
  Qed.

  Ltac fp6_br :=
    intros;
    repeat match goal with x : (_ * _ * _)%type |- _ => destruct x as [[? ?] ?] end;
    cbv [G.fp6_add G.fp6_sub G.fp6_neg G.fp6_mul G.fp6_sqr G.fp6_mul_by_v G.fp6_mul_fp2
         G.fp6_frobenius G.fp6_frobenius_p2 G.fp6_build G.fp6_c0 G.fp6_c1 G.fp6_c2
         P.fp6_add P.fp6_sub P.fp6_neg P.fp6_mul P.fp6_sqr P.fp6_mul_by_v P.fp6_mul_fp2
         P.fp6_frobenius P.fp6_frobenius_p2 P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd];
    change (G.fp2_add p) with (P.fp2_add p); change (G.fp2_sub p) with (P.fp2_sub p);
    change (G.fp2_neg p) with (P.fp2_neg p);
    change (G.fp2_zero p) with (P.fp2_zero p); change (G.fp2_one p) with (P.fp2_one p);
    change (G.fp2_conjugate p) with (P.fp2_conjugate p);
    rewrite ?fp2_mul_br, ?fp2_sqr_br, ?fp2_mul_xi_br;
    rewrite ?(@fp2_mul_xi_eq p), ?(@fp2_sqr_eq p);
    apply injective_projections; [apply injective_projections|]; cbv [fst snd]; ring.

  (** Fp6 level: the hypotheses of BLS12_Fp12Feval / BLS12_PairingFeval. *)
  Lemma fp6_add_br : forall a b : Fp6, G.fp6_add p a b = P.fp6_add p a b.
  Proof. reflexivity. Qed.
  Lemma fp6_sub_br : forall a b : Fp6, G.fp6_sub p a b = P.fp6_sub p a b.
  Proof. reflexivity. Qed.
  Lemma fp6_neg_br : forall a : Fp6, G.fp6_neg p a = P.fp6_neg p a.
  Proof. reflexivity. Qed.
  Lemma fp6_mul_br : forall a b : Fp6, G.fp6_mul p beta xi_re xi_im a b = P.fp6_mul p a b.
  Proof. fp6_br. Qed.
  Lemma fp6_mul_by_v_br : forall a : Fp6, G.fp6_mul_by_v p beta xi_re xi_im a = P.fp6_mul_by_v p a.
  Proof. fp6_br. Qed.
  Lemma fp6_sqr_br : forall a : Fp6, G.fp6_sqr p beta xi_re xi_im a = P.fp6_sqr p a.
  Proof. fp6_br. Qed.
  Lemma pairing_fp6_mul_self_eq_sqr : forall a : Fp6, P.fp6_mul p a a = P.fp6_sqr p a.
  Proof. intros; rewrite fp6_sqr_eq; reflexivity. Qed.
  Lemma fp6_karatsuba_cross : forall a b : Fp6,
    P.fp6_sub p (P.fp6_sub p (P.fp6_mul p (P.fp6_add p a b) (P.fp6_add p a b))
                             (P.fp6_mul p a a))
              (P.fp6_mul p b b) =
    P.fp6_add p (P.fp6_mul p a b) (P.fp6_mul p a b).
  Proof. intros; ring. Qed.
  Lemma fp6_mul_fp2_br : forall (a : Fp6) (s : Fp2), G.fp6_mul_fp2 p beta a s = P.fp6_mul_fp2 p a s.
  Proof. fp6_br. Qed.
  Lemma fp6_frobenius_br : forall g1 g2 (a : Fp6),
    G.fp6_frobenius p beta g1 g2 a = P.fp6_frobenius p g1 g2 a.
  Proof. fp6_br. Qed.
  Lemma fp6_frobenius_p2_br : forall g1 g2 (a : Fp6),
    G.fp6_frobenius_p2 p beta g1 g2 a = P.fp6_frobenius_p2 p g1 g2 a.
  Proof. fp6_br. Qed.
  Lemma fp6_inv_br : forall a : Fp6, G.fp6_inv p beta xi_re xi_im a = P.fp6_inv p a.
  Proof.
    intros [[a0 a1] a2].
    cbv [G.fp6_inv P.fp6_inv G.fp6_build P.fp6_build G.fp6_c0 G.fp6_c1 G.fp6_c2
         P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    rewrite !fp2_mul_br, !fp2_mul_xi_br, !fp2_inv_br, !(@fp2_sqr_eq p).
    reflexivity.
  Qed.

End TowerBridge.
