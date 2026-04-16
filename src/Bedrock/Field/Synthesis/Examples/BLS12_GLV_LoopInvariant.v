(** * Algebraic lemmas for GLV loop invariant restoration.

    Proves that one LSB-first loop iteration preserves the invariant:
    - accumulator: out' = curve_add(scmul(k1 mod 2^(iter+1), P), scmul(k2 mod 2^(iter+1), Phi))
    - doubling: P' = scmul(2^(iter+1), P_init)

    All lemmas are purely algebraic — no bedrock2/WP. *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

Section GLV_Algebra.
  Context {F : Type}.
  Context (Fzero Fone : F).
  Context (curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)).
  Let id : F * F * F := (Fzero, Fone, Fzero).

  Context (curve_add_id_r : forall x y z, curve_add (x, y, z) id = (x, y, z)).
  Context (curve_add_id_l : forall x y z, curve_add id (x, y, z) = (x, y, z)).
  Context (curve_add_assoc : forall P Q R,
    curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).

  Fixpoint scmul (n : nat) (P : F * F * F) : F * F * F :=
    match n with O => id | S m => curve_add P (scmul m P) end.

  Lemma curve_add_id_r' : forall P, curve_add P id = P.
  Proof. intros [[]]; apply curve_add_id_r. Qed.
  Lemma curve_add_id_l' : forall P, curve_add id P = P.
  Proof. intros [[]]; apply curve_add_id_l. Qed.

  Lemma scmul_1 : forall P, scmul 1 P = P.
  Proof. intros. simpl. apply curve_add_id_r'. Qed.

  Lemma scmul_add : forall a b P,
    scmul (a + b) P = curve_add (scmul a P) (scmul b P).
  Proof.
    induction a as [|a' IH]; intros b P; simpl.
    - rewrite curve_add_id_l'. reflexivity.
    - rewrite IH. rewrite curve_add_assoc. reflexivity.
  Qed.

  (** Doubling: scmul(2^(n+1), P) = curve_add(scmul(2^n, P), scmul(2^n, P)) *)
  Lemma scmul_pow2_succ : forall n P,
    0 <= n ->
    scmul (Z.to_nat (2 ^ (n + 1))) P =
    curve_add (scmul (Z.to_nat (2 ^ n)) P) (scmul (Z.to_nat (2 ^ n)) P).
  Proof.
    intros.
    rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
    rewrite Z2Nat.inj_mul by (try apply Z.pow_nonneg; lia).
    change (Z.to_nat 2) with 2%nat.
    replace (Z.to_nat (2 ^ n) * 2)%nat with (Z.to_nat (2 ^ n) + Z.to_nat (2 ^ n))%nat by lia.
    apply scmul_add.
  Qed.

  (** 4-term rearrangement: (A+B)+C+D = (A+C)+(B+D) *)
  Lemma curve_add_4_rearrange : forall A B C D,
    curve_add (curve_add (curve_add A B) C) D =
    curve_add (curve_add A C) (curve_add B D).
  Proof.
    intros.
    rewrite <- (curve_add_assoc (curve_add A B) C D).
    rewrite <- (curve_add_assoc A B (curve_add C D)).
    rewrite (curve_add_assoc B C D).
    rewrite (curve_add_comm B C).
    rewrite <- (curve_add_assoc C B D).
    rewrite (curve_add_assoc A C (curve_add B D)).
    reflexivity.
  Qed.

  (** Bit-step: scmul(k mod 2^(n+1), P) =
      curve_add(scmul(k mod 2^n, P), scmul(b2z(testbit k n), scmul(2^n, P))) *)
  Lemma scmul_bit_step : forall k n P,
    0 <= k -> 0 <= n ->
    scmul (Z.to_nat (k mod 2 ^ (n + 1))) P =
    curve_add
      (scmul (Z.to_nat (k mod 2 ^ n)) P)
      (scmul (Z.to_nat (Z.b2z (Z.testbit k n)))
             (scmul (Z.to_nat (2 ^ n)) P)).
  Proof.
    intros k n P Hk Hn.
    assert (Hpow : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
    assert (Hmod : 0 <= k mod 2 ^ n < 2 ^ n) by (apply Z.mod_pos_bound; lia).
    rewrite Z.testbit_odd. set (q := Z.shiftr k n). unfold Z.b2z.
    destruct (Z.odd q) eqn:Hodd.
    - (* bit = true: scmul 1 Q = Q *)
      rewrite scmul_1.
      assert (Hqmod : q mod 2 = 1) by (pose proof (Zmod_odd q); rewrite Hodd in *; lia).
      subst q. rewrite Z.shiftr_div_pow2 in Hqmod by lia.
      assert (Hdecomp : k mod 2 ^ (n + 1) = k mod 2 ^ n + 2 ^ n).
      { rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2.
        rewrite Z.rem_mul_r by lia. f_equal. lia. }
      rewrite Hdecomp. rewrite Z2Nat.inj_add by lia. apply scmul_add.
    - (* bit = false: scmul 0 Q = id *)
      simpl scmul at 2. rewrite curve_add_id_r'.
      assert (Hqmod : q mod 2 = 0) by (pose proof (Zmod_odd q); rewrite Hodd in *; lia).
      subst q. rewrite Z.shiftr_div_pow2 in Hqmod by lia.
      assert (Hdecomp : k mod 2 ^ (n + 1) = k mod 2 ^ n).
      { rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2.
        rewrite Z.rem_mul_r by lia. lia. }
      rewrite Hdecomp. reflexivity.
  Qed.

  (** Main loop step: one LSB-first iteration preserves the accumulator invariant *)
  Lemma glv_loop_step : forall k1 k2 iter P_init Phi_init,
    0 <= k1 -> 0 <= k2 -> 0 <= iter ->
    let km1  := Z.to_nat (k1 mod 2 ^ iter) in
    let km2  := Z.to_nat (k2 mod 2 ^ iter) in
    let km1' := Z.to_nat (k1 mod 2 ^ (iter + 1)) in
    let km2' := Z.to_nat (k2 mod 2 ^ (iter + 1)) in
    let currentP   := scmul (Z.to_nat (2 ^ iter)) P_init in
    let currentPhi := scmul (Z.to_nat (2 ^ iter)) Phi_init in
    let out := curve_add (scmul km1 P_init) (scmul km2 Phi_init) in
    let b1 := Z.b2z (Z.testbit k1 iter) in
    let b2 := Z.b2z (Z.testbit k2 iter) in
    let out1 := curve_add out (scmul (Z.to_nat b1) currentP) in
    let out2 := curve_add out1 (scmul (Z.to_nat b2) currentPhi) in
    out2 = curve_add (scmul km1' P_init) (scmul km2' Phi_init).
  Proof.
    intros.
    subst out1 out2 out km1' km2' currentP currentPhi b1 b2.
    rewrite (scmul_bit_step k1 iter P_init) by lia.
    rewrite (scmul_bit_step k2 iter Phi_init) by lia.
    subst km1 km2.
    apply curve_add_4_rearrange.
  Qed.

  (** Z arithmetic helpers *)
  Lemma Z_shiftr_step : forall k n,
    0 <= n ->
    Z.shiftr k (n + 1) = Z.shiftr k n / 2.
  Proof.
    intros. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.shiftr_div_pow2 k n) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
    symmetry. apply Z.div_div; lia.
  Qed.

  Lemma Z_shiftr_mod2_b2z : forall k n,
    0 <= k -> 0 <= n ->
    Z.shiftr k n mod 2 = Z.b2z (Z.testbit k n).
  Proof.
    intros. unfold Z.b2z. rewrite Z.testbit_odd.
    rewrite Zmod_odd. destruct (Z.odd _); reflexivity.
  Qed.

  (** Combined invariant step: packages scalar shift, accumulator, and doubling.
      Given invariant at [iter], produces invariant at [iter+1]. *)
  Lemma glv_inv_step : forall k1_init k2_init iter P_init Phi_init
    (k1_eval k2_eval : Z) (Out curP curPhi : F * F * F),
    0 <= k1_init -> 0 <= k2_init -> 0 <= iter ->
    k1_eval = Z.shiftr k1_init iter ->
    k2_eval = Z.shiftr k2_init iter ->
    Out = curve_add (scmul (Z.to_nat (k1_init mod 2 ^ iter)) P_init)
                    (scmul (Z.to_nat (k2_init mod 2 ^ iter)) Phi_init) ->
    curP = scmul (Z.to_nat (2 ^ iter)) P_init ->
    curPhi = scmul (Z.to_nat (2 ^ iter)) Phi_init ->
    (* Scalar shift *)
    k1_eval / 2 = Z.shiftr k1_init (iter + 1)
    /\ k2_eval / 2 = Z.shiftr k2_init (iter + 1)
    (* Accumulator update *)
    /\ (let b1 := Z.b2z (Z.testbit k1_init iter) in
        let b2 := Z.b2z (Z.testbit k2_init iter) in
        curve_add (curve_add Out (scmul (Z.to_nat b1) curP))
                  (scmul (Z.to_nat b2) curPhi)
        = curve_add (scmul (Z.to_nat (k1_init mod 2 ^ (iter + 1))) P_init)
                    (scmul (Z.to_nat (k2_init mod 2 ^ (iter + 1))) Phi_init))
    (* Point doubling *)
    /\ curve_add curP curP = scmul (Z.to_nat (2 ^ (iter + 1))) P_init
    /\ curve_add curPhi curPhi = scmul (Z.to_nat (2 ^ (iter + 1))) Phi_init.
  Proof.
    intros * Hk1 Hk2 Hi Hk1e Hk2e Hout HcurP HcurPhi.
    subst. repeat split.
    - symmetry. apply Z_shiftr_step; lia.
    - symmetry. apply Z_shiftr_step; lia.
    - apply glv_loop_step; lia.
    - symmetry. apply scmul_pow2_succ; lia.
    - symmetry. apply scmul_pow2_succ; lia.
  Qed.

End GLV_Algebra.

(** ** Nat/Z iteration arithmetic *)

Lemma vi_iter_step : forall vi : nat, forall glv_iterations : Z,
  (vi > 0)%nat ->
  (vi <= Z.to_nat glv_iterations)%nat ->
  glv_iterations = 129 ->
  let iter := glv_iterations - Z.of_nat vi in
  let iter' := glv_iterations - Z.of_nat (vi - 1) in
  iter' = iter + 1
  /\ (vi - 1)%nat = Z.to_nat (glv_iterations - iter')
  /\ 0 <= iter.
Proof.
  intros vi gl Hgt Hle Hgl. subst gl.
  split. { lia. }
  replace (129 - (129 - Z.of_nat (vi - 1))) with (Z.of_nat (vi - 1)) by lia.
  rewrite Nat2Z.id. split; [reflexivity|]. lia.
Qed.

(** Shift_scalar postcondition implies eval / 2 = next shiftr *)
Lemma shiftr_from_div2 : forall k_eval k_init iter,
  0 <= iter ->
  k_eval = Z.shiftr k_init iter ->
  k_eval / 2 = Z.shiftr k_init (iter + 1).
Proof.
  intros * Hi Hk. subst k_eval.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
  apply Z.div_div; lia.
Qed.

(** Shift_scalar bit matches testbit *)
Lemma shift_scalar_bit : forall k_eval k_init iter,
  0 <= k_init -> 0 <= iter ->
  k_eval = Z.shiftr k_init iter ->
  k_eval mod 2 = Z.b2z (Z.testbit k_init iter).
Proof.
  intros. subst. unfold Z.b2z. rewrite Z.testbit_odd.
  rewrite Zmod_odd. destruct (Z.odd _); reflexivity.
Qed.
