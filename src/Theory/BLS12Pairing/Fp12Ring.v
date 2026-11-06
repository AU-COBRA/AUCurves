(** * Ring structure of the Fp2/Fp6/Fp12 tower of Pairing.v.

    The operations of [Theory.BLS12Pairing.Pairing] (u^2 = -1, v^3 = xi = 1+u,
    w^2 = v) form commutative rings with Leibniz equality, for every modulus
    [p] (no primality needed).  Each level is registered with [Add Ring] so
    the next level is proved with [ring] over the previous one.

    Also here:
    - the squaring formulas equal multiplication by self;
    - [pw f n], the N-th power by repeated multiplication, and its laws;
    - [Pairing.fp12_pow_Z f e w = pw f e] for [0 <= e < 2^w];
    - the conjugation [fp12_conjugate] (w -> -w) is a ring automorphism;
    - embeddings of Fp, Fp2, Fp6 into Fp12 and the tower generators U, V, W.
*)

From Stdlib Require Import ZArith NArith BinPos List Lia.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Theory.BLS12Pairing.Pairing.
Module P := Theory.BLS12Pairing.Pairing.

Section Fp12Ring.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Lemma Fp_ring_theory : Ring_theory.ring_theory (@F.zero p) (@F.one p) (@F.add p) (@F.mul p)
    (@F.sub p) (@F.opp p) eq.
  Proof. exact (Algebra.Ring.ring_theory_for_stdlib_tactic (zero:=F.zero) (one:=F.one)). Qed.
  Add Ring Fp_ring : Fp_ring_theory.

  (* ================================================================ *)
  (** ** Fp2                                                           *)
  (* ================================================================ *)

  Local Notation fp2_add := (P.fp2_add p).
  Local Notation fp2_sub := (P.fp2_sub p).
  Local Notation fp2_neg := (P.fp2_neg p).
  Local Notation fp2_mul := (P.fp2_mul p).
  Local Notation fp2_zero := (P.fp2_zero p).
  Local Notation fp2_one := (P.fp2_one p).

  Ltac fp2_solve :=
    intros;
    repeat match goal with x : (F * F)%type |- _ => destruct x end;
    cbv [P.fp2_add P.fp2_sub P.fp2_neg P.fp2_mul P.fp2_zero P.fp2_one P.fp2_sqr
         P.fp2_mul_xi P.fp2_conjugate P.fp2_mul_fp P.fp_to_fp2 fst snd];
    f_equal; ring.

  Lemma fp2_ring_theory :
    Ring_theory.ring_theory fp2_zero fp2_one fp2_add fp2_mul fp2_sub fp2_neg eq.
  Proof. constructor; fp2_solve. Qed.
  Add Ring fp2_ring : fp2_ring_theory.

  Definition xi2 : Fp2 := (F.one, F.one).

  Lemma fp2_mul_xi_eq : forall a, P.fp2_mul_xi p a = fp2_mul xi2 a.
  Proof. cbv [xi2]; fp2_solve. Qed.

  Lemma fp2_sqr_eq : forall a, P.fp2_sqr p a = fp2_mul a a.
  Proof. fp2_solve. Qed.

  Lemma fp2_conj_add : forall a b,
    P.fp2_conjugate p (fp2_add a b) = fp2_add (P.fp2_conjugate p a) (P.fp2_conjugate p b).
  Proof. fp2_solve. Qed.
  Lemma fp2_conj_sub : forall a b,
    P.fp2_conjugate p (fp2_sub a b) = fp2_sub (P.fp2_conjugate p a) (P.fp2_conjugate p b).
  Proof. fp2_solve. Qed.
  Lemma fp2_conj_neg : forall a,
    P.fp2_conjugate p (fp2_neg a) = fp2_neg (P.fp2_conjugate p a).
  Proof. fp2_solve. Qed.
  Lemma fp2_conj_mul : forall a b,
    P.fp2_conjugate p (fp2_mul a b) = fp2_mul (P.fp2_conjugate p a) (P.fp2_conjugate p b).
  Proof. fp2_solve. Qed.
  Lemma fp2_conj_zero : P.fp2_conjugate p fp2_zero = fp2_zero.
  Proof. fp2_solve. Qed.
  Lemma fp2_conj_one : P.fp2_conjugate p fp2_one = fp2_one.
  Proof. fp2_solve. Qed.

  (* ================================================================ *)
  (** ** Fp6                                                           *)
  (* ================================================================ *)

  Local Notation fp6_add := (P.fp6_add p).
  Local Notation fp6_sub := (P.fp6_sub p).
  Local Notation fp6_neg := (P.fp6_neg p).
  Local Notation fp6_mul := (P.fp6_mul p).
  Local Notation fp6_zero := (P.fp6_zero p).
  Local Notation fp6_one := (P.fp6_one p).

  Ltac fp6_unfold :=
    cbv [P.fp6_add P.fp6_sub P.fp6_neg P.fp6_mul P.fp6_zero P.fp6_one P.fp6_sqr
         P.fp6_mul_by_v P.fp6_mul_fp2 P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd];
    rewrite ?fp2_mul_xi_eq, ?fp2_sqr_eq.

  Ltac split6 :=
    apply injective_projections; [apply injective_projections|]; cbn [fst snd].

  Ltac fp6_solve :=
    intros;
    repeat match goal with x : (_ * _ * _)%type |- _ => destruct x as [[? ?] ?] end;
    fp6_unfold; split6; ring.

  Lemma fp6_ring_theory :
    Ring_theory.ring_theory fp6_zero fp6_one fp6_add fp6_mul fp6_sub fp6_neg eq.
  Proof. constructor; fp6_solve. Qed.
  Add Ring fp6_ring : fp6_ring_theory.

  Definition v6 : Fp6 := P.fp6_build p fp2_zero fp2_one fp2_zero.
  (** Fp2 embedded in Fp6 as a constant term. *)
  Definition e26 (a : Fp2) : Fp6 := P.fp6_build p a fp2_zero fp2_zero.

  Lemma fp6_mul_by_v_eq : forall a, P.fp6_mul_by_v p a = fp6_mul v6 a.
  Proof. cbv [v6]; fp6_solve. Qed.

  Lemma fp6_sqr_eq : forall a, P.fp6_sqr p a = fp6_mul a a.
  Proof. fp6_solve. Qed.

  Lemma fp6_mul_fp2_eq : forall a s, P.fp6_mul_fp2 p a s = fp6_mul a (e26 s).
  Proof. cbv [e26]; fp6_solve. Qed.

  Lemma e26_add : forall a b, e26 (fp2_add a b) = fp6_add (e26 a) (e26 b).
  Proof. cbv [e26]; fp6_solve. Qed.
  Lemma e26_mul : forall a b, e26 (fp2_mul a b) = fp6_mul (e26 a) (e26 b).
  Proof. cbv [e26]; fp6_solve. Qed.
  Lemma e26_one : e26 fp2_one = fp6_one.
  Proof. reflexivity. Qed.

  (** Decomposition of an Fp6 element along 1, v, v^2. *)
  Lemma fp6_decomp : forall a0 a1 a2,
    P.fp6_build p a0 a1 a2 =
    fp6_add (e26 a0) (fp6_add (fp6_mul (e26 a1) v6) (fp6_mul (e26 a2) (fp6_mul v6 v6))).
  Proof. cbv [e26 v6]; fp6_solve. Qed.

  Lemma v6_cubed : fp6_mul v6 (fp6_mul v6 v6) = e26 xi2.
  Proof. cbv [e26 v6]; fp6_solve. Qed.

  (* ================================================================ *)
  (** ** Fp12                                                          *)
  (* ================================================================ *)

  Local Notation fp12_add := (P.fp12_add p).
  Local Notation fp12_sub := (P.fp12_sub p).
  Local Notation fp12_neg := (P.fp12_neg p).
  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_zero := (P.fp12_zero p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation fp12_conjugate := (P.fp12_conjugate p).

  Ltac fp12_unfold :=
    cbv [P.fp12_add P.fp12_sub P.fp12_neg P.fp12_mul P.fp12_zero P.fp12_one P.fp12_sqr
         P.fp12_conjugate P.fp12_build P.fp12_c0 P.fp12_c1 fst snd];
    rewrite ?fp6_mul_by_v_eq, ?fp6_sqr_eq.

  Ltac fp12_solve :=
    intros;
    repeat match goal with x : (_ * _)%type |- _ =>
      lazymatch type of x with (F * F)%type => fail | (Fp2 * Fp2 * Fp2)%type => fail
                          | _ => destruct x end end;
    fp12_unfold; apply injective_projections; cbn [fst snd]; ring.

  Lemma fp12_ring_theory :
    Ring_theory.ring_theory fp12_zero fp12_one fp12_add fp12_mul fp12_sub fp12_neg eq.
  Proof. constructor; fp12_solve. Qed.
  Add Ring fp12_ring : fp12_ring_theory.

  Lemma fp12_sqr_eq : forall a, P.fp12_sqr p a = fp12_mul a a.
  Proof. fp12_solve. Qed.

  (** Conjugation w -> -w is a ring automorphism of order 2. *)
  Lemma conj_mul : forall a b,
    fp12_conjugate (fp12_mul a b) = fp12_mul (fp12_conjugate a) (fp12_conjugate b).
  Proof. fp12_solve. Qed.
  Lemma conj_add : forall a b,
    fp12_conjugate (fp12_add a b) = fp12_add (fp12_conjugate a) (fp12_conjugate b).
  Proof. fp12_solve. Qed.
  Lemma conj_one : fp12_conjugate fp12_one = fp12_one.
  Proof. fp12_solve. Qed.
  Lemma conj_conj : forall a, fp12_conjugate (fp12_conjugate a) = a.
  Proof. fp12_solve. Qed.

  (** Embeddings and generators. *)
  Definition e612 (a : Fp6) : Fp12 := P.fp12_build p a fp6_zero.
  Definition e212 (a : Fp2) : Fp12 := e612 (e26 a).
  Definition eF (c : F) : Fp12 := e212 (c, F.zero).
  Definition U12 : Fp12 := e212 (F.zero, F.one).
  Definition V12 : Fp12 := e612 v6.
  Definition W12 : Fp12 := P.fp12_build p fp6_zero fp6_one.

  Lemma e612_add : forall a b, e612 (fp6_add a b) = fp12_add (e612 a) (e612 b).
  Proof. cbv [e612]; fp12_solve. Qed.
  Lemma e612_mul : forall a b, e612 (fp6_mul a b) = fp12_mul (e612 a) (e612 b).
  Proof. cbv [e612]; fp12_solve. Qed.
  Lemma e612_one : e612 fp6_one = fp12_one.
  Proof. reflexivity. Qed.
  Lemma e212_add : forall a b, e212 (fp2_add a b) = fp12_add (e212 a) (e212 b).
  Proof. intros; cbv [e212]; rewrite e26_add, e612_add; reflexivity. Qed.
  Lemma e212_mul : forall a b, e212 (fp2_mul a b) = fp12_mul (e212 a) (e212 b).
  Proof. intros; cbv [e212]; rewrite e26_mul, e612_mul; reflexivity. Qed.
  Lemma e212_one : e212 fp2_one = fp12_one.
  Proof. reflexivity. Qed.

  Lemma fp12_decomp : forall a0 a1 : Fp6,
    (a0, a1) = fp12_add (e612 a0) (fp12_mul (e612 a1) W12).
  Proof. cbv [e612 W12]; fp12_solve. Qed.

  Lemma fp2_decomp : forall c0 c1 : F,
    e212 (c0, c1) = fp12_add (eF c0) (fp12_mul (eF c1) U12).
  Proof.
    intros. cbv [eF U12 e212 e612 e26].
    cbv [P.fp12_add P.fp12_mul P.fp12_build P.fp12_c0 P.fp12_c1 fst snd].
    rewrite fp6_mul_by_v_eq.
    apply injective_projections; cbn [fst snd]; [| ring].
    fp6_unfold. split6; fp2_solve.
  Qed.

  Lemma W12_sq : fp12_mul W12 W12 = V12.
  Proof. cbv [W12 V12 e612]; fp12_solve. Qed.

  Lemma U12_sq : fp12_mul U12 U12 = fp12_neg fp12_one.
  Proof.
    cbv [U12 e212 e612 e26]. fp12_unfold. apply injective_projections; cbn [fst snd]; fp6_unfold; split6; fp2_solve.
  Qed.

  Lemma V12_cubed : fp12_mul V12 (fp12_mul V12 V12) = e212 xi2.
  Proof. cbv [V12 e212]. rewrite <- !e612_mul, v6_cubed. reflexivity. Qed.

  Lemma eF_add : forall a b, eF (F.add a b) = fp12_add (eF a) (eF b).
  Proof.
    intros; cbv [eF]. rewrite <- e212_add. f_equal; fp2_solve.
  Qed.
  Lemma eF_mul : forall a b, eF (F.mul a b) = fp12_mul (eF a) (eF b).
  Proof.
    intros; cbv [eF]. rewrite <- e212_mul. f_equal; fp2_solve.
  Qed.
  Lemma eF_one : eF F.one = fp12_one.
  Proof. reflexivity. Qed.
  Lemma eF_zero : eF F.zero = fp12_zero.
  Proof. reflexivity. Qed.
  Lemma eF_opp : forall a, eF (F.opp a) = fp12_neg (eF a).
  Proof.
    intros; cbv [eF e212 e612 e26]. fp12_unfold. apply injective_projections; cbn [fst snd]; fp6_unfold; split6; fp2_solve.
  Qed.

  (* ================================================================ *)
  (** ** Powers                                                        *)
  (* ================================================================ *)

  Definition pw (f : Fp12) (n : N) : Fp12 := N.iter n (fp12_mul f) fp12_one.

  Lemma pw_0 : forall f, pw f 0 = fp12_one.
  Proof. reflexivity. Qed.

  Lemma pw_succ : forall f n, pw f (N.succ n) = fp12_mul f (pw f n).
  Proof. intros; cbv [pw]; rewrite N.iter_succ; reflexivity. Qed.

  Lemma pw_1 : forall f, pw f 1 = f.
  Proof. intros; change 1%N with (N.succ 0); rewrite pw_succ, pw_0; ring. Qed.

  Lemma pw_add : forall f a b, pw f (a + b) = fp12_mul (pw f a) (pw f b).
  Proof.
    intros f a b; induction a using N.peano_ind.
    - rewrite N.add_0_l, pw_0; ring.
    - rewrite N.add_succ_l, !pw_succ, IHa; ring.
  Qed.

  Lemma pw_mul_base : forall f g n, pw (fp12_mul f g) n = fp12_mul (pw f n) (pw g n).
  Proof.
    intros f g n; induction n using N.peano_ind.
    - rewrite !pw_0; ring.
    - rewrite !pw_succ, IHn; ring.
  Qed.

  Lemma pw_mul : forall f a b, pw f (a * b) = pw (pw f a) b.
  Proof.
    intros f a b; induction b using N.peano_ind.
    - rewrite N.mul_0_r, !pw_0; reflexivity.
    - rewrite N.mul_succ_r, pw_add, pw_succ, IHb; ring.
  Qed.

  Lemma pw_one : forall n, pw fp12_one n = fp12_one.
  Proof. intros n; induction n using N.peano_ind; [reflexivity|]. rewrite pw_succ, IHn; ring. Qed.

  Lemma pw_conj : forall f n, fp12_conjugate (pw f n) = pw (fp12_conjugate f) n.
  Proof.
    intros f n; induction n using N.peano_ind; [apply conj_one|].
    rewrite !pw_succ, conj_mul, IHn; reflexivity.
  Qed.

  Lemma pw_eF : forall c n, pw (eF c) n = eF (F.pow c n).
  Proof.
    intros c n; induction n using N.peano_ind.
    - rewrite pw_0, F.pow_0_r; reflexivity.
    - rewrite pw_succ, IHn, F.pow_succ_r, eF_mul; reflexivity.
  Qed.

  (** Bit-list exponentiation of Pairing.v. *)
  Fixpoint bits_val (bits : list bool) : N :=
    match bits with
    | [] => 0%N
    | b :: rest => ((if b then 2 ^ N.of_nat (length rest) else 0) + bits_val rest)%N
    end.

  Lemma pw_sq : forall a n, pw (fp12_mul a a) n = pw a (2 * n).
  Proof.
    intros a n. rewrite pw_mul.
    replace (pw a 2) with (fp12_mul a a); [reflexivity|].
    change 2%N with (N.succ (N.succ 0)); rewrite !pw_succ, pw_0; ring.
  Qed.

  Lemma pow_bits_aux_started : forall bits base acc,
    P.fp12_pow_bits_aux p base bits acc true =
    fp12_mul (pw acc (2 ^ N.of_nat (length bits))) (pw base (bits_val bits)).
  Proof.
    induction bits as [|b rest IH]; intros base acc.
    - cbn [P.fp12_pow_bits_aux length bits_val N.of_nat]. rewrite N.pow_0_r, pw_1, pw_0; ring.
    - cbn [length bits_val]. rewrite Nat2N.inj_succ, N.pow_succ_r'.
      destruct b; cbn [P.fp12_pow_bits_aux]; rewrite IH, fp12_sqr_eq.
      + rewrite pw_mul_base, pw_sq, pw_add. ring.
      + rewrite pw_sq, N.add_0_l. reflexivity.
  Qed.

  Lemma pow_bits_aux_unstarted : forall bits base,
    P.fp12_pow_bits_aux p base bits fp12_one false = pw base (bits_val bits).
  Proof.
    induction bits as [|b rest IH]; intros base; cbn [P.fp12_pow_bits_aux bits_val length].
    - reflexivity.
    - destruct b.
      + rewrite pow_bits_aux_started, pw_add. ring.
      + rewrite N.add_0_l. apply IH.
  Qed.

  Local Open Scope Z_scope.
  Lemma Z_to_bits_S : forall w z,
    P.Z_to_bits (S w) z = Z.testbit z (Z.of_nat w) :: P.Z_to_bits w z.
  Proof.
    intros. cbv [P.Z_to_bits]. rewrite seq_S, rev_app_distr. reflexivity.
  Qed.

  Lemma Z_to_bits_length : forall w z, length (P.Z_to_bits w z) = w.
  Proof. intros; cbv [P.Z_to_bits]; rewrite length_map, length_rev, length_seq; reflexivity. Qed.

  Lemma bits_val_Z_to_bits : forall w (z : Z), (0 <= z)%Z ->
    Z.of_N (bits_val (P.Z_to_bits w z)) = (z mod 2 ^ Z.of_nat w)%Z.
  Proof.
    induction w as [|w IH]; intros z Hz.
    - cbv [P.Z_to_bits]; cbn. rewrite Z.mod_1_r. reflexivity.
    - rewrite Z_to_bits_S. cbn [bits_val]. rewrite Z_to_bits_length, N2Z.inj_add, IH by lia.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r, (Z.mul_comm 2) by lia.
      rewrite (Z.rem_mul_r z (2 ^ Z.of_nat w) 2) by (try apply Z.pow_nonzero; lia).
      rewrite <- Z.testbit_spec' by lia.
      destruct (Z.testbit z (Z.of_nat w)); cbn [Z.b2z].
      + rewrite N2Z.inj_pow, nat_N_Z. lia.
      + lia.
  Qed.

  Lemma fp12_pow_Z_pw : forall f (e : Z) w, (0 <= e < 2 ^ Z.of_nat w)%Z ->
    P.fp12_pow_Z p f e w = pw f (Z.to_N e).
  Proof.
    intros f e w He. cbv [P.fp12_pow_Z P.fp12_pow_bits].
    rewrite pow_bits_aux_unstarted. f_equal.
    apply N2Z.inj. rewrite bits_val_Z_to_bits, Z2N.id by lia.
    apply Z.mod_small; lia.
  Qed.

End Fp12Ring.
