(** * The Frobenius maps of Pairing.v are the p-th and p^2-th powers.

    For a prime p with p = 3 (mod 4) and p = 1 (mod 3), and Frobenius
    constants of Pairing.v satisfying (xi = 1 + u)

      gamma2    = gamma1^2,       gamma1    = xi^((p-1)/3),   c1    = xi^((p-1)/6),
      gamma2_p2 = gamma1_p2^2,    gamma1_p2 = xi^((p^2-1)/3), c1_p2 = xi^((p^2-1)/6)

    (powers computed in Fp12 on the embedded xi), we prove

      fp12_frobenius    f = f^p,
      fp12_frobenius_p2 f = f^(p^2)

    for every f.  The proof: in characteristic p, x |-> x^p is additive
    (binomial theorem, p | C(p,k)), multiplicative, and fixes Fp (Fermat);
    it sends u, v, w to -u, gamma1 v, c1 w, which pins it down on the basis.

    Consequences: closure of the cyclotomic subgroup under both maps, and
    the output of the easy part of the final exponentiation is cyclotomic.
*)

From Stdlib Require Import ZArith NArith BinPos List Lia Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.NumTheoryUtil.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Module P := Theory.BLS12Pairing.Pairing.

Local Open Scope nat_scope.

(** Binomial coefficients (nat). *)
Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' => binom n' k' + binom n' (S k')
  end.

Lemma binom_0_r : forall n, binom n 0 = 1.
Proof. intros [|n]; reflexivity. Qed.

Lemma binom_gt : forall n k, n < k -> binom n k = 0.
Proof.
  induction n as [|n IH]; intros [|k] H; cbn; try lia.
  rewrite !IH by lia. reflexivity.
Qed.

Lemma binom_diag : forall n, binom n n = 1.
Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH, binom_gt by lia. reflexivity. Qed.

Lemma binom_absorb : forall n k, S k * binom (S n) (S k) = S n * binom n k.
Proof.
  induction n as [|n IH]; intros k.
  - destruct k as [|k]; cbn; lia.
  - destruct k as [|k].
    + specialize (IH 0). cbn [binom] in *. rewrite !binom_0_r in *. lia.
    + pose proof (IH k) as H1. pose proof (IH (S k)) as H2.
      change (binom (S (S n)) (S (S k))) with (binom (S n) (S k) + binom (S n) (S (S k))).
      change (binom (S n) (S k)) with (binom n k + binom n (S k)) in *.
      nia.
Qed.

Lemma prime_divides_binom : forall (q : positive), prime (Z.pos q) ->
  forall k, 0 < k < Pos.to_nat q -> (Z.pos q | Z.of_nat (binom (Pos.to_nat q) k)).
Proof.
  intros q Hq k Hk.
  destruct (Pos.to_nat q) as [|m] eqn:Em; [lia|].
  destruct k as [|k]; [lia|].
  pose proof (binom_absorb m k) as H.
  apply (f_equal Z.of_nat) in H. rewrite !Nat2Z.inj_mul in H.
  assert (Hm : Z.of_nat (S m) = Z.pos q) by (rewrite <- Em, positive_nat_Z; reflexivity).
  rewrite Hm in H.
  apply Gauss with (b := Z.of_nat (S k)).
  - rewrite H. exists (Z.of_nat (binom m k)). ring.
  - apply rel_prime_sym, rel_prime_le_prime; [assumption|]. lia.
Qed.

Section Frobenius.
  Context {p : positive} (Hprime : prime (Z.pos p)).

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).
  Add Ring fp6_ring : (@fp6_ring_theory p).
  Add Ring fp12_ring : (@fp12_ring_theory p).

  Local Notation fp12_add := (P.fp12_add p).
  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_neg := (P.fp12_neg p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation fp12_zero := (P.fp12_zero p).
  Local Notation conj := (P.fp12_conjugate p).
  Local Notation pw := (@pw p).
  Local Notation eF := (@eF p).
  Local Notation e212 := (@e212 p).
  Local Notation e612 := (@e612 p).

  (* ================================================================ *)
  (** ** Fermat                                                        *)
  (* ================================================================ *)

  Lemma F_pow_p : forall c : F, F.pow c (Npos p) = c.
  Proof.
    intros c.
    pose proof (prime_ge_2 _ Hprime) as H2.
    destruct (F.eq_dec c F.zero) as [->|Hc].
    - apply F.pow_0_l. discriminate.
    - apply F.eq_to_Z_iff. rewrite F.to_Z_pow.
      pose proof (F.to_Z_range c ltac:(lia)) as Hr.
      assert (Hnz : (F.to_Z c mod Z.pos p <> 0)%Z).
      { rewrite Z.mod_small by lia. intro E. apply Hc.
        apply F.eq_to_Z_iff. rewrite E. reflexivity. }
      pose proof (fermat_little (Z.pos p) Hprime (F.to_Z c) Hnz) as Hf.
      replace (Z.of_N (Npos p)) with ((Z.pos p - 1) + 1)%Z by lia.
      rewrite Z.pow_add_r, Z.pow_1_r by lia.
      rewrite Z.mul_mod, Hf, Z.mul_1_l, !Z.mod_mod by lia.
      apply Z.mod_small; lia.
  Qed.

  (* ================================================================ *)
  (** ** Binomial theorem and the freshman's dream                     *)
  (* ================================================================ *)

  Definition pwn (f : Fp12) (n : nat) : Fp12 := pw f (N.of_nat n).

  Lemma pwn_0 : forall f, pwn f 0 = fp12_one.
  Proof. reflexivity. Qed.
  Lemma pwn_S : forall f n, pwn f (S n) = fp12_mul f (pwn f n).
  Proof. intros; cbv [pwn]; rewrite Nat2N.inj_succ, pw_succ; reflexivity. Qed.

  Fixpoint ssum (g : nat -> Fp12) (m : nat) : Fp12 :=
    match m with
    | O => g O
    | S m' => fp12_add (ssum g m') (g (S m'))
    end.

  Lemma ssum_ext : forall (g h : nat -> Fp12) (m : nat),
    (forall i : nat, (i <= m)%nat -> g i = h i) -> ssum g m = ssum h m.
  Proof.
    intros g h m; induction m as [|m IH]; intros H; cbn [ssum].
    - apply H; lia.
    - rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
  Qed.

  Lemma ssum_add : forall (g h : nat -> Fp12) (m : nat),
    ssum (fun i => fp12_add (g i) (h i)) m = fp12_add (ssum g m) (ssum h m).
  Proof. intros g h m; induction m as [|m IH]; cbn [ssum]; [reflexivity|]. rewrite IH; ring. Qed.

  Lemma ssum_mul_l : forall c (g : nat -> Fp12) (m : nat),
    ssum (fun i => fp12_mul c (g i)) m = fp12_mul c (ssum g m).
  Proof. intros c g m; induction m as [|m IH]; cbn [ssum]; [reflexivity|]. rewrite IH; ring. Qed.

  Lemma ssum_shift : forall (g : nat -> Fp12) (m : nat),
    ssum g (S m) = fp12_add (g 0) (ssum (fun i => g (S i)) m).
  Proof.
    intros g m; induction m as [|m IH]; cbn [ssum] in *; [reflexivity|].
    rewrite IH; ring.
  Qed.

  Lemma ssum_zero_mid : forall (g : nat -> Fp12) (m : nat),
    (forall i : nat, (0 < i < S m)%nat -> g i = fp12_zero) ->
    ssum g (S m) = fp12_add (g 0) (g (S m)).
  Proof.
    intros g m H. cbn [ssum]. f_equal.
    assert (forall j : nat, (j <= m)%nat -> ssum g j = g 0%nat) as Hj.
    { induction j as [|j IH]; intros Hjm; cbn [ssum]; [reflexivity|].
      rewrite IH, (H (S j)) by lia. ring. }
    apply Hj; lia.
  Qed.

  Definition cf (n : nat) : Fp12 := eF (F.of_Z p (Z.of_nat n)).

  Lemma cf_add : forall a b : nat, cf (a + b)%nat = fp12_add (cf a) (cf b).
  Proof. intros; cbv [cf]; rewrite Nat2Z.inj_add, F.of_Z_add, eF_add; reflexivity. Qed.
  Lemma cf_1 : cf 1 = fp12_one.
  Proof. reflexivity. Qed.
  Lemma cf_0 : cf 0 = fp12_zero.
  Proof. reflexivity. Qed.

  Definition bterm (a b : Fp12) (n i : nat) : Fp12 :=
    fp12_mul (cf (binom n i)) (fp12_mul (pwn a i) (pwn b (n - i))).

  Theorem binomial : forall a b n, pwn (fp12_add a b) n = ssum (bterm a b n) n.
  Proof.
    intros a b n; induction n as [|n IH].
    - cbv [bterm]; cbn [ssum binom Nat.sub]. rewrite cf_1, !pwn_0; ring.
    - rewrite pwn_S, IH.
      (* right-hand side *)
      rewrite ssum_shift.
      transitivity (fp12_add (ssum (fun i => fp12_mul a (bterm a b n i)) n)
                             (ssum (fun i => fp12_mul b (bterm a b n i)) n)).
      { rewrite ssum_mul_l, ssum_mul_l. ring. }
      assert (Hsplit : forall i : nat, (i <= n)%nat ->
        bterm a b (S n) (S i) =
        fp12_add (fp12_mul a (bterm a b n i)) (fp12_mul b (bterm a b n (S i)))).
      { intros i Hi. cbv [bterm]. cbn [binom]. rewrite cf_add, pwn_S.
        replace (S n - S i)%nat with (n - i)%nat by lia.
        destruct (Nat.eq_dec i n) as [->|Hne].
        - rewrite (binom_gt n (S n)) by lia. rewrite cf_0. ring.
        - replace (n - i)%nat with (S (n - S i)) by lia. rewrite pwn_S. ring. }
      rewrite (ssum_ext _ _ n Hsplit), ssum_add.
      assert (Hlast : fp12_mul b (bterm a b n (S n)) = fp12_zero).
      { cbv [bterm]. rewrite (binom_gt n (S n)) by lia. rewrite cf_0. ring. }
      assert (Hfirst : bterm a b (S n) 0 = fp12_mul b (bterm a b n 0)).
      { cbv [bterm]. rewrite !binom_0_r, !Nat.sub_0_r, pwn_S. ring. }
      assert (Hb : ssum (fun i => fp12_mul b (bterm a b n i)) n =
                   fp12_add (bterm a b (S n) 0) (ssum (fun i => fp12_mul b (bterm a b n (S i))) n)).
      { rewrite Hfirst, <- (ssum_shift (fun i => fp12_mul b (bterm a b n i))).
        cbn [ssum]. rewrite Hlast. ring. }
      rewrite Hb. ring.
  Qed.

  Lemma cf_binom_p : forall k : nat, (0 < k < Pos.to_nat p)%nat ->
    cf (binom (Pos.to_nat p) k) = fp12_zero.
  Proof.
    intros k Hk. destruct (prime_divides_binom p Hprime k Hk) as [q Hq].
    cbv [cf]. rewrite Hq, F.of_Z_mod, Z_mod_mult. reflexivity.
  Qed.

  Lemma pw_p_nat : forall f, pw f (Npos p) = pwn f (Pos.to_nat p).
  Proof. intros; cbv [pwn]; rewrite positive_nat_N; reflexivity. Qed.

  Theorem freshman : forall a b,
    pw (fp12_add a b) (Npos p) = fp12_add (pw a (Npos p)) (pw b (Npos p)).
  Proof.
    intros a b. rewrite !pw_p_nat, binomial.
    pose proof (Pos2Nat.is_pos p) as Hpos.
    destruct (Pos.to_nat p) as [|m] eqn:Em; [lia|].
    rewrite ssum_zero_mid.
    - cbv [bterm]. cbn [binom]. rewrite binom_diag, (binom_gt m (S m)), Nat.add_0_r by lia.
      rewrite cf_1, Nat.sub_diag, Nat.sub_0_r, !pwn_0. ring.
    - intros i Hi. cbv [bterm]. rewrite <- Em, cf_binom_p by lia. ring.
  Qed.

  (* ================================================================ *)
  (** ** The p-th power map                                            *)
  (* ================================================================ *)

  Definition psi (f : Fp12) : Fp12 := pw f (Npos p).

  Lemma psi_add : forall a b, psi (fp12_add a b) = fp12_add (psi a) (psi b).
  Proof. apply freshman. Qed.
  Lemma psi_mul : forall a b, psi (fp12_mul a b) = fp12_mul (psi a) (psi b).
  Proof. intros; apply pw_mul_base. Qed.
  Lemma psi_eF : forall c, psi (eF c) = eF c.
  Proof. intros; cbv [psi]; rewrite pw_eF, F_pow_p; reflexivity. Qed.

  (** A ring endomorphism of the shape of the Frobenius maps. *)
  Section Shape.
    Variable phi : Fp12 -> Fp12.
    Variable sigma : Fp2 -> Fp2.
    Variables g1 g2 cw : Fp2.
    Hypothesis phi_add : forall a b, phi (fp12_add a b) = fp12_add (phi a) (phi b).
    Hypothesis phi_mul : forall a b, phi (fp12_mul a b) = fp12_mul (phi a) (phi b).
    Hypothesis phi_e212 : forall c, phi (e212 c) = e212 (sigma c).
    Hypothesis phi_V : phi (V12 (p:=p)) = fp12_mul (e212 g1) (V12 (p:=p)).
    Hypothesis phi_W : phi (W12 (p:=p)) = fp12_mul (e212 cw) (W12 (p:=p)).
    Hypothesis g2_sq : g2 = P.fp2_mul p g1 g1.

    Definition fr6 (x : Fp6) : Fp6 :=
      P.fp6_build p (sigma (P.fp6_c0 p x))
                    (P.fp2_mul p (sigma (P.fp6_c1 p x)) g1)
                    (P.fp2_mul p (sigma (P.fp6_c2 p x)) g2).

    Lemma phi_e612 : forall x, phi (e612 x) = e612 (fr6 x).
    Proof.
      intros [[x0 x1] x2].
      transitivity (phi (e612 (P.fp6_build p x0 x1 x2))); [reflexivity|].
      rewrite fp6_decomp, !e612_add, !e612_mul.
      change (e612 (e26 ?a)) with (e212 a). fold (V12 (p:=p)).
      rewrite !phi_add, !phi_mul, !phi_e212, phi_V.
      cbv [fr6 P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
      rewrite fp6_decomp, !e612_add, !e612_mul.
      change (e612 (e26 ?a)) with (e212 a). fold (V12 (p:=p)).
      rewrite g2_sq, !e212_mul.
      ring.
    Qed.

    Lemma phi_shape : forall a0 a1 : Fp6,
      phi (a0, a1) = (fr6 a0, P.fp6_mul_fp2 p (fr6 a1) cw).
    Proof.
      intros a0 a1.
      rewrite (fp12_decomp a0 a1), (fp12_decomp (fr6 a0)).
      rewrite phi_add, phi_mul, !phi_e612, phi_W, fp6_mul_fp2_eq, e612_mul.
      change (e612 (e26 cw)) with (e212 cw).
      ring.
    Qed.
  End Shape.

  (* ================================================================ *)
  (** ** u, v, w under powers                                          *)
  (* ================================================================ *)

  Lemma Z_div_exact : forall n d r : Z, (0 < d)%Z -> (n mod d = r)%Z ->
    n = (d * ((n - r) / d) + r)%Z.
  Proof.
    intros n d r Hd Hr.
    assert (H : (n - r = d * (n / d))%Z) by (pose proof (Z.div_mod n d); lia).
    rewrite H, (Z.mul_comm d (n / d)), Z.div_mul by lia. lia.
  Qed.

  Lemma N_exact : forall (n d r : Z), (0 < d)%Z -> (0 <= r)%Z -> (0 < n)%Z -> (n mod d = r)%Z ->
    Z.to_N n = (Z.to_N d * Z.to_N ((n - r) / d) + Z.to_N r)%N.
  Proof.
    intros n d r Hd Hr Hn Hm. pose proof (Z_div_exact n d r Hd Hm) as E.
    assert (0 <= (n - r) / d)%Z
      by (apply Z.div_pos; [pose proof (Z.mod_le n d ltac:(lia) Hd); lia | lia]).
    apply N2Z.inj. rewrite N2Z.inj_add, N2Z.inj_mul, !Z2N.id by lia. lia.
  Qed.

  Lemma pw_2 : forall f, pw f 2 = fp12_mul f f.
  Proof. intros. change 2%N with (N.succ (N.succ 0)). rewrite !pw_succ, pw_0. ring. Qed.
  Lemma pw_3 : forall f, pw f 3 = fp12_mul f (fp12_mul f f).
  Proof. intros. change 3%N with (N.succ (N.succ (N.succ 0))). rewrite !pw_succ, pw_0. ring. Qed.

  Lemma pw_U_3mod4 : forall n : Z, (0 < n)%Z -> (n mod 4 = 3)%Z ->
    pw (U12 (p:=p)) (Z.to_N n) = fp12_neg (U12 (p:=p)).
  Proof.
    intros n Hn Hm. rewrite (N_exact n 4 3) by lia.
    rewrite pw_add, pw_mul.
    replace (pw U12 (Z.to_N 4)) with fp12_one.
    - rewrite pw_one. change (Z.to_N 3) with 3%N. rewrite pw_3, U12_sq. ring.
    - change (Z.to_N 4) with (2 * 2)%N. rewrite pw_mul, !pw_2, U12_sq. ring.
  Qed.

  Lemma pw_U_1mod4 : forall n : Z, (0 < n)%Z -> (n mod 4 = 1)%Z ->
    pw (U12 (p:=p)) (Z.to_N n) = U12 (p:=p).
  Proof.
    intros n Hn Hm. rewrite (N_exact n 4 1) by lia.
    rewrite pw_add, pw_mul.
    replace (pw U12 (Z.to_N 4)) with fp12_one.
    - rewrite pw_one. change (Z.to_N 1) with 1%N. rewrite pw_1. ring.
    - change (Z.to_N 4) with (2 * 2)%N. rewrite pw_mul, !pw_2, U12_sq. ring.
  Qed.

  Lemma pw_V_1mod3 : forall n : Z, (0 < n)%Z -> (n mod 3 = 1)%Z ->
    pw (V12 (p:=p)) (Z.to_N n) = fp12_mul (pw (e212 xi2) (Z.to_N ((n - 1) / 3))) (V12 (p:=p)).
  Proof.
    intros n Hn Hm. rewrite (N_exact n 3 1) by lia.
    rewrite pw_add, pw_mul. change (Z.to_N 3) with 3%N. change (Z.to_N 1) with 1%N.
    rewrite pw_3, V12_cubed, pw_1. reflexivity.
  Qed.

  Lemma pw_W_1mod6 : forall n : Z, (0 < n)%Z -> (n mod 6 = 1)%Z ->
    pw (W12 (p:=p)) (Z.to_N n) = fp12_mul (pw (e212 xi2) (Z.to_N ((n - 1) / 6))) (W12 (p:=p)).
  Proof.
    intros n Hn Hm. rewrite (N_exact n 6 1) by lia.
    rewrite pw_add, pw_mul. change (Z.to_N 6) with (2 * 3)%N. change (Z.to_N 1) with 1%N.
    rewrite pw_mul, pw_2, W12_sq, pw_3, V12_cubed, pw_1. reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** fp12_frobenius = p-th power                                   *)
  (* ================================================================ *)

  Hypothesis Hp4 : (Z.pos p mod 4 = 3)%Z.
  Hypothesis Hp3 : (Z.pos p mod 3 = 1)%Z.

  Lemma Hp6 : (Z.pos p mod 6 = 1)%Z.
  Proof.
    pose proof (Z.div_mod (Z.pos p) 6) as A. pose proof (Z.mod_pos_bound (Z.pos p) 6) as B.
    pose proof (Z.div_mod (Z.pos p) 4) as C. pose proof (Z.div_mod (Z.pos p) 3) as D.
    lia.
  Qed.

  Lemma psi_e212 : forall c, psi (e212 c) = e212 (P.fp2_conjugate p c).
  Proof.
    intros [c0 c1]. rewrite fp2_decomp, psi_add, psi_mul, !psi_eF.
    cbv [psi]. replace (Npos p) with (Z.to_N (Z.pos p)) by reflexivity.
    rewrite pw_U_3mod4 by (assumption || lia).
    cbv [P.fp2_conjugate fst snd]. rewrite fp2_decomp, eF_opp. ring.
  Qed.

  Variables gamma1 gamma2 c1 : Fp2.
  Hypothesis Hgamma2 : gamma2 = P.fp2_mul p gamma1 gamma1.
  Hypothesis Hgamma1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 3)) = e212 gamma1.
  Hypothesis Hc1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 6)) = e212 c1.

  Theorem frobenius_is_pow : forall f,
    P.fp12_frobenius p gamma1 gamma2 c1 f = pw f (Npos p).
  Proof.
    intros [a0 a1]. symmetry. change (pw (a0, a1) (Npos p)) with (psi (a0, a1)).
    rewrite (phi_shape psi (P.fp2_conjugate p) gamma1 gamma2 c1 psi_add psi_mul psi_e212).
    - reflexivity.
    - cbv [psi]. replace (Npos p) with (Z.to_N (Z.pos p)) by reflexivity.
      rewrite pw_V_1mod3, Hgamma1 by (assumption || lia). reflexivity.
    - cbv [psi]. replace (Npos p) with (Z.to_N (Z.pos p)) by reflexivity.
      rewrite pw_W_1mod6, Hc1 by (apply Hp6 || lia). reflexivity.
    - exact Hgamma2.
  Qed.

  (* ================================================================ *)
  (** ** fp12_frobenius_p2 = p^2-th power                              *)
  (* ================================================================ *)

  Definition psi2 (f : Fp12) : Fp12 := pw f (Npos (p * p)).

  Lemma psi2_psi : forall f, psi2 f = psi (psi f).
  Proof. intros; cbv [psi2 psi]. rewrite <- pw_mul. reflexivity. Qed.

  Lemma psi2_add : forall a b, psi2 (fp12_add a b) = fp12_add (psi2 a) (psi2 b).
  Proof. intros; rewrite !psi2_psi, !psi_add; reflexivity. Qed.
  Lemma psi2_mul : forall a b, psi2 (fp12_mul a b) = fp12_mul (psi2 a) (psi2 b).
  Proof. intros; apply pw_mul_base. Qed.
  Lemma psi2_e212 : forall c, psi2 (e212 c) = e212 c.
  Proof.
    intros c. rewrite psi2_psi, !psi_e212. f_equal. destruct c; cbv [P.fp2_conjugate fst snd].
    f_equal; ring.
  Qed.

  Lemma Hpp3 : (Z.pos (p * p) mod 3 = 1)%Z.
  Proof. rewrite Pos2Z.inj_mul, Z.mul_mod, Hp3 by lia. reflexivity. Qed.
  Lemma Hpp6 : (Z.pos (p * p) mod 6 = 1)%Z.
  Proof. rewrite Pos2Z.inj_mul, Z.mul_mod, Hp6 by lia. reflexivity. Qed.

  Variables gamma1_p2 gamma2_p2 c1_p2 : Fp2.
  Hypothesis Hgamma2_p2 : gamma2_p2 = P.fp2_mul p gamma1_p2 gamma1_p2.
  Hypothesis Hgamma1_p2 : pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 3)) = e212 gamma1_p2.
  Hypothesis Hc1_p2 : pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 6)) = e212 c1_p2.

  Theorem frobenius_p2_is_pow : forall f,
    P.fp12_frobenius_p2 p gamma1_p2 gamma2_p2 c1_p2 f = pw f (Npos (p * p)).
  Proof.
    intros [a0 a1]. symmetry. change (pw (a0, a1) (Npos (p * p))) with (psi2 (a0, a1)).
    rewrite (phi_shape psi2 (fun c => c) gamma1_p2 gamma2_p2 c1_p2 psi2_add psi2_mul psi2_e212).
    - reflexivity.
    - cbv [psi2]. replace (Npos (p * p)) with (Z.to_N (Z.pos (p * p))) by reflexivity.
      rewrite pw_V_1mod3 by (apply Hpp3 || lia). rewrite Pos2Z.inj_mul, Hgamma1_p2. reflexivity.
    - cbv [psi2]. replace (Npos (p * p)) with (Z.to_N (Z.pos (p * p))) by reflexivity.
      rewrite pw_W_1mod6 by (apply Hpp6 || lia). rewrite Pos2Z.inj_mul, Hc1_p2. reflexivity.
    - exact Hgamma2_p2.
  Qed.

  (* ================================================================ *)
  (** ** Consequences for the cyclotomic subgroup                      *)
  (* ================================================================ *)

  Lemma cyc_frobenius : forall f, cyclotomic f ->
    cyclotomic (P.fp12_frobenius p gamma1 gamma2 c1 f).
  Proof. intros; rewrite frobenius_is_pow; apply cyc_pw; assumption. Qed.

  Lemma cyc_frobenius_p2 : forall f, cyclotomic f ->
    cyclotomic (P.fp12_frobenius_p2 p gamma1_p2 gamma2_p2 c1_p2 f).
  Proof. intros; rewrite frobenius_p2_is_pow; apply cyc_pw; assumption. Qed.

  (** The easy part [result' = frob_p2 (conj f * inv f) * (conj f * inv f)]
      (= f^((p^6-1)(p^2+1))) lies in the cyclotomic subgroup. *)
  Definition easy_part (f : Fp12) : Fp12 :=
    let r := fp12_mul (conj f) (P.fp12_inv p f) in
    fp12_mul (P.fp12_frobenius_p2 p gamma1_p2 gamma2_p2 c1_p2 r) r.

  Lemma cyc_easy_first : forall f, fp12_mul f (P.fp12_inv p f) = fp12_one ->
    cyclotomic (fp12_mul (conj f) (P.fp12_inv p f)).
  Proof.
    intros f Hf. cbv [cyclotomic]. rewrite conj_mul, conj_conj.
    transitivity (fp12_mul (conj (fp12_mul f (P.fp12_inv p f))) (fp12_mul f (P.fp12_inv p f))).
    - rewrite conj_mul. ring.
    - rewrite Hf, conj_one. ring.
  Qed.

  Theorem easy_part_cyclotomic : forall f, fp12_mul f (P.fp12_inv p f) = fp12_one ->
    cyclotomic (easy_part f).
  Proof.
    intros f Hf. cbv [easy_part]. pose proof (cyc_easy_first f Hf).
    apply cyc_mul; [apply cyc_frobenius_p2|]; assumption.
  Qed.

End Frobenius.
