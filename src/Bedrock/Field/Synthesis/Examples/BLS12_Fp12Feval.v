(** * Fp12 feval bridge: bedrock2 algebraic models = Pairing.v Gallina models.
 *
 *  Each lemma shows that the Fp12 operation from Theory.BLS12Pairing.Fp12
 *  (which the bedrock2 FieldParameters instance uses as Fmul, Fadd, etc.)
 *  equals the corresponding operation in Theory.BLS12Pairing.Pairing.
 *
 *  Proof strategy: since both Fp12.v and Pairing.v use the same algebraic
 *  structure (Karatsuba etc.) differing only in the underlying Fp6/Fp2 ops,
 *  we state Fp6-level bridge hypotheses and lift them to Fp12 by congruence.
 *
 *  To control term sizes during rewriting, Fp6 operations are made Opaque
 *  so that Rocq does not unfold them during `rewrite`.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp6.
Require Import Theory.BLS12Pairing.Fp12.

Local Open Scope Z_scope.

(* Make all Fp6-level and Pairing-level Fp6 operations opaque to prevent
   term explosion during rewriting. The bridge hypotheses relate these
   opaque terms; we never need to look inside them. *)
Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_neg Pairing.fp6_mul
  Pairing.fp6_sqr Pairing.fp6_mul_by_v Pairing.fp6_inv Pairing.fp6_mul_fp2
  Pairing.fp6_frobenius Pairing.fp6_frobenius_p2.

Section Fp12Bridge.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Let beta : Fp := F.of_Z p (-1).
  Let xi_re : Fp := @F.one p.
  Let xi_im : Fp := @F.one p.

  (* Fp6 bridge hypotheses *)
  Hypothesis fp6_add_hyp : forall a b : Fp6',
    Fp6.fp6_add p a b = Pairing.fp6_add p a b.
  Hypothesis fp6_sub_hyp : forall a b : Fp6',
    Fp6.fp6_sub p a b = Pairing.fp6_sub p a b.
  Hypothesis fp6_neg_hyp : forall a : Fp6',
    Fp6.fp6_neg p a = Pairing.fp6_neg p a.
  Hypothesis fp6_mul_hyp : forall a b : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a b = Pairing.fp6_mul p a b.
  Hypothesis fp6_mul_by_v_hyp : forall a : Fp6',
    Fp6.fp6_mul_by_v p beta xi_re xi_im a = Pairing.fp6_mul_by_v p a.
  Hypothesis fp6_sqr_hyp : forall a : Fp6',
    Fp6.fp6_sqr p beta xi_re xi_im a = Pairing.fp6_sqr p a.
  Hypothesis pairing_fp6_mul_self_eq_sqr : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Hypothesis fp6_karatsuba_cross_term : forall a b : Fp6',
    Pairing.fp6_sub p
      (Pairing.fp6_sub p
        (Pairing.fp6_mul p (Pairing.fp6_add p a b) (Pairing.fp6_add p a b))
        (Pairing.fp6_mul p a a))
      (Pairing.fp6_mul p b b) =
    Pairing.fp6_add p (Pairing.fp6_mul p a b) (Pairing.fp6_mul p a b).

  (* ================================================================ *)
  (** ** Fp12 bridge lemmas                                           *)
  (* ================================================================ *)

  Lemma fp12_add_eq : forall a b : Fp12',
    Fp12.fp12_add p a b = Pairing.fp12_add p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp12.fp12_add, Pairing.fp12_add; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_add_hyp. reflexivity.
  Qed.

  Lemma fp12_sub_eq : forall a b : Fp12',
    Fp12.fp12_sub p a b = Pairing.fp12_sub p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp12.fp12_sub, Pairing.fp12_sub; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_sub_hyp. reflexivity.
  Qed.

  Lemma fp12_neg_eq : forall a : Fp12',
    Fp12.fp12_neg p a = Pairing.fp12_neg p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_neg, Pairing.fp12_neg; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_neg_hyp. reflexivity.
  Qed.

  Lemma fp12_mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp12.fp12_mul, Pairing.fp12_mul; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_mul_hyp, !fp6_add_hyp, !fp6_sub_hyp, !fp6_mul_by_v_hyp.
    reflexivity.
  Qed.

  Lemma fp12_sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_sqr, Pairing.fp12_sqr; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_mul_hyp, !fp6_add_hyp, !fp6_mul_by_v_hyp,
            !pairing_fp6_mul_self_eq_sqr.
    reflexivity.
  Qed.

  Lemma fp12_conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_conjugate, Pairing.fp12_conjugate; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_neg_hyp. reflexivity.
  Qed.

  Lemma bedrock2_fp12_square_eq_pairing_sqr : forall x : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im x x = Pairing.fp12_sqr p x.
  Proof.
    intros [a0 a1].
    rewrite fp12_mul_eq.
    unfold Pairing.fp12_mul, Pairing.fp12_sqr; cbn [fst snd
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    (* Apply cross-term identity BEFORE mul_self_eq_sqr to avoid
       pairing_fp6_mul_self_eq_sqr from rewriting inside the cross term *)
    rewrite fp6_karatsuba_cross_term.
    rewrite !pairing_fp6_mul_self_eq_sqr.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** Fp12 frobenius bridges                                       *)
  (* ================================================================ *)

  Variable fg1 fg2 fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_c1 w_frob_p2_c1 : Fp2.

  Hypothesis fp6_frobenius_hyp : forall a : Fp6',
    Fp6.fp6_frobenius p beta fg1 fg2 a =
    Pairing.fp6_frobenius p fg1 fg2 a.
  Hypothesis fp6_frobenius_p2_hyp : forall a : Fp6',
    Fp6.fp6_frobenius_p2 p beta fg1_p2 fg2_p2 a =
    Pairing.fp6_frobenius_p2 p fg1_p2 fg2_p2 a.
  Hypothesis fp6_mul_fp2_hyp : forall (a : Fp6') (s : Fp2),
    Fp6.fp6_mul_fp2 p beta a s = Pairing.fp6_mul_fp2 p a s.

  Lemma fp12_frobenius_eq : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    Pairing.fp12_frobenius p fg1 fg2 w_frob_c1 a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius, Pairing.fp12_frobenius; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_frobenius_hyp, !fp6_mul_fp2_hyp. reflexivity.
  Qed.

  Lemma fp12_frobenius_p2_eq : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius_p2, Pairing.fp12_frobenius_p2; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_frobenius_p2_hyp, !fp6_mul_fp2_hyp. reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** Fp12 inv bridge                                              *)
  (* ================================================================ *)

  Hypothesis fp6_inv_hyp : forall a : Fp6',
    Fp6.fp6_inv p beta xi_re xi_im a = Pairing.fp6_inv p a.

  Lemma fp12_inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_inv, Pairing.fp12_inv; cbn [fst snd
      Fp12.fp12_c0 Fp12.fp12_c1 Fp12.mk_fp12
      Pairing.fp12_c0 Pairing.fp12_c1 Pairing.fp12_build].
    rewrite !fp6_mul_hyp, !fp6_sub_hyp, !fp6_mul_by_v_hyp,
            !fp6_neg_hyp, !fp6_inv_hyp, !pairing_fp6_mul_self_eq_sqr.
    reflexivity.
  Qed.

End Fp12Bridge.

(* ================================================================ *)
(** ** Combined rewriting database                                   *)
(* ================================================================ *)

#[export] Hint Rewrite
  fp12_add_eq fp12_sub_eq fp12_neg_eq fp12_conjugate_eq
  : fp12_feval_bridge.

(* Make Fp12 operations opaque to prevent term explosion in Miller proofs.
   The bridge lemmas above are the only way to relate the two sides. *)
Local Opaque Fp12.fp12_mul Fp12.fp12_sqr Fp12.fp12_add Fp12.fp12_sub
  Fp12.fp12_neg Fp12.fp12_conjugate Fp12.fp12_inv.
Local Opaque Pairing.fp12_mul Pairing.fp12_sqr Pairing.fp12_add
  Pairing.fp12_sub Pairing.fp12_neg Pairing.fp12_conjugate Pairing.fp12_inv.

(* ================================================================ *)
(** ** Part 2: Miller loop feval correctness                        *)
(* ================================================================ *)

Section MillerLoopFeval.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Let beta : Fp := F.of_Z p (-1).
  Let xi_re : Fp := @F.one p.
  Let xi_im : Fp := @F.one p.

  (* Fp6 bridge hypotheses *)
  Hypothesis fp6_add_bridge : forall a b : Fp6',
    Fp6.fp6_add p a b = Pairing.fp6_add p a b.
  Hypothesis fp6_sub_bridge : forall a b : Fp6',
    Fp6.fp6_sub p a b = Pairing.fp6_sub p a b.
  Hypothesis fp6_neg_bridge : forall a : Fp6',
    Fp6.fp6_neg p a = Pairing.fp6_neg p a.
  Hypothesis fp6_mul_bridge : forall a b : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a b = Pairing.fp6_mul p a b.
  Hypothesis fp6_mul_by_v_bridge : forall a : Fp6',
    Fp6.fp6_mul_by_v p beta xi_re xi_im a = Pairing.fp6_mul_by_v p a.
  Hypothesis fp6_sqr_bridge : forall a : Fp6',
    Fp6.fp6_sqr p beta xi_re xi_im a = Pairing.fp6_sqr p a.
  Hypothesis pairing_fp6_mul_self_bridge : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Hypothesis fp6_karatsuba_cross_bridge : forall a b : Fp6',
    Pairing.fp6_sub p
      (Pairing.fp6_sub p
        (Pairing.fp6_mul p (Pairing.fp6_add p a b) (Pairing.fp6_add p a b))
        (Pairing.fp6_mul p a a))
      (Pairing.fp6_mul p b b) =
    Pairing.fp6_add p (Pairing.fp6_mul p a b) (Pairing.fp6_mul p a b).

  Local Lemma mul_bridge : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Proof. apply fp12_mul_eq; assumption. Qed.

  Local Lemma square_bridge : forall x : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im x x = Pairing.fp12_sqr p x.
  Proof. apply bedrock2_fp12_square_eq_pairing_sqr; assumption. Qed.

  Lemma miller_doubling_feval : forall f line : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im
      (Fp12.fp12_mul p beta xi_re xi_im f f) line =
    Pairing.fp12_mul p (Pairing.fp12_sqr p f) line.
  Proof.
    intros. rewrite square_bridge. rewrite mul_bridge. reflexivity.
  Qed.

  Definition bedrock2_miller_step (q_x q_y : Fp2) (x_p y_p : Fp)
    (state : Fp12' * (Fp2 * Fp2)) (bit : bool) : Fp12' * (Fp2 * Fp2) :=
    let '(f, (t_x, t_y)) := state in
    let x_t_sq := Pairing.fp2_sqr p t_x in
    let three_x_t_sq := Pairing.fp2_add p (Pairing.fp2_add p x_t_sq x_t_sq) x_t_sq in
    let two_y_t := Pairing.fp2_add p t_y t_y in
    let lambda_d := Pairing.fp2_mul p three_x_t_sq (Pairing.fp2_inv p two_y_t) in
    let line_d := Pairing.make_line p lambda_d t_x t_y x_p y_p in
    let f' := Fp12.fp12_mul p beta xi_re xi_im
                (Fp12.fp12_mul p beta xi_re xi_im f f) line_d in
    let '(new_t_x, new_t_y) := Pairing.ec2_double_with_lambda p t_x t_y lambda_d in
    if bit then
      let lambda_a := Pairing.fp2_mul p (Pairing.fp2_sub p q_y new_t_y)
                                        (Pairing.fp2_inv p (Pairing.fp2_sub p q_x new_t_x)) in
      let line_a := Pairing.make_line p lambda_a new_t_x new_t_y x_p y_p in
      let f'' := Fp12.fp12_mul p beta xi_re xi_im f' line_a in
      (f'', Pairing.ec2_add_with_lambda p new_t_x new_t_y q_x lambda_a)
    else
      (f', (new_t_x, new_t_y)).

  Lemma miller_step_feval : forall q_x q_y x_p y_p state bit,
    bedrock2_miller_step q_x q_y x_p y_p state bit =
    Pairing.miller_loop_step p q_x q_y x_p y_p state bit.
  Proof.
    intros q_x q_y x_p y_p [f [t_x t_y]] bit.
    unfold bedrock2_miller_step, Pairing.miller_loop_step.
    (* Reduce let-bindings for the Fp2 computations (identical on both sides) *)
    set (x_t_sq := Pairing.fp2_sqr p t_x).
    set (three := Pairing.fp2_add p (Pairing.fp2_add p x_t_sq x_t_sq) x_t_sq).
    set (two_y := Pairing.fp2_add p t_y t_y).
    set (lam_d := Pairing.fp2_mul p three (Pairing.fp2_inv p two_y)).
    set (line_d := Pairing.make_line p lam_d t_x t_y x_p y_p).
    (* Now the Fp12 operations are exposed *)
    rewrite square_bridge.
    rewrite mul_bridge.
    destruct (Pairing.ec2_double_with_lambda p t_x t_y _) as [new_t_x new_t_y].
    destruct bit.
    - rewrite mul_bridge. reflexivity.
    - reflexivity.
  Qed.

  Theorem miller_fold_feval : forall bits q_x q_y x_p y_p init,
    fold_left (bedrock2_miller_step q_x q_y x_p y_p) bits init =
    fold_left (Pairing.miller_loop_step p q_x q_y x_p y_p) bits init.
  Proof.
    induction bits as [|b bs IH]; intros.
    - reflexivity.
    - simpl fold_left. rewrite miller_step_feval. apply IH.
  Qed.

  Corollary miller_loop_f_feval : forall bits q_x q_y x_p y_p init,
    fst (fold_left (bedrock2_miller_step q_x q_y x_p y_p) bits init) =
    fst (fold_left (Pairing.miller_loop_step p q_x q_y x_p y_p) bits init).
  Proof.
    intros. rewrite miller_fold_feval. reflexivity.
  Qed.

  Local Lemma fp12_one_eq : Fp12.fp12_one p = Pairing.fp12_one p.
  Proof.
    unfold Fp12.fp12_one, Pairing.fp12_one,
           Fp12.mk_fp12, Pairing.fp12_build.
    (* Both reduce to (fp6_one, fp6_zero) -- the underlying
       fp6_one/fp6_zero are definitionally equal between modules *)
    reflexivity.
  Qed.

  Theorem miller_loop_feval_correct :
    forall (q_x q_y : Fp2) (x_p y_p : Fp),
      fst (fold_left
             (bedrock2_miller_step q_x q_y x_p y_p)
             (Pairing.bls_x_bits)
             (Fp12.fp12_one p, (q_x, q_y))) =
      fst (fold_left
             (Pairing.miller_loop_step p q_x q_y x_p y_p)
             (Pairing.bls_x_bits)
             (Pairing.fp12_one p, (q_x, q_y))).
  Proof.
    intros. rewrite fp12_one_eq. apply miller_loop_f_feval.
  Qed.

End MillerLoopFeval.

(* ================================================================ *)
(** ** Summary of proof obligations                                  *)
(*                                                                   *)
(* To fully instantiate the above theorems, the Fp6 feval bridge    *)
(* must provide 8 lemmas:                                            *)
(*   fp6_add_eq, fp6_sub_eq, fp6_neg_eq :                           *)
(*     Definitional equality (reflexivity).                          *)
(*   fp6_mul_eq, fp6_mul_by_v_eq :                                  *)
(*     From Fp2 bridge (mulp2 = fp2_mul, mul_xi bridges).           *)
(*   fp6_sqr_eq :                                                   *)
(*     From Fp2 bridge for sqr and mul.                             *)
(*   pairing_fp6_mul_self_eq_sqr :                                   *)
(*     Algebraic: Karatsuba mul(a,a) = Chung-Hasan sqr(a).          *)
(*   fp6_karatsuba_cross_term :                                      *)
(*     Algebraic: (a+b)^2 - a^2 - b^2 = 2*a*b in Fp6.              *)
(*                                                                   *)
(* Plus for frobenius/inv:                                           *)
(*   fp6_frobenius_eq, fp6_frobenius_p2_eq, fp6_mul_fp2_eq,         *)
(*   fp6_inv_eq.                                                     *)
(* ================================================================ *)
