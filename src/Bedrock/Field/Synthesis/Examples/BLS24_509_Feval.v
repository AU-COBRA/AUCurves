(** * BLS24-509 feval chain: bedrock2 algebraic models = Tower.v Gallina spec.

    Proves that the abstract extension operations (from
    QuadraticExtensionsAbstract / CubicExtensionsAbstract) used by
    the bedrock2 FieldParameters instances compute the same results
    as the Gallina tower spec (Tower.v).

    Tower: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24

      Fp2  = Fp[u]/(u^2+1),      beta = -1            (quadratic)
      Fp4  = Fp2[v]/(v^2-xi),    xi = (1,1)            (quadratic)
      Fp8  = Fp4[w]/(w^2-v),     v in Fp4              (quadratic)
      Fp24 = Fp8[t]/(t^3-w),     mul_by_nr = fp8_mul_by_w  (cubic)

    Since both sides use the SAME algebraic formulas (componentwise
    add/sub/neg, standard mul formula, etc.), most bridges are
    definitional equality or short ring proofs (for beta = -1).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Ring_theory Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Bedrock.Spec.BLS24Pairing.Tower.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * Fp ring setup                                                    *)
(* ================================================================== *)

Section FpRing.
  Variable p : positive.

  Lemma Fp_ring_theory :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.

End FpRing.

(* ================================================================== *)
(** * All feval bridges in a single section                            *)
(* ================================================================== *)

Section AllFeval.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.
  Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

  (* -------------------------------------------------------------- *)
  (* Shared definitions                                              *)
  (* -------------------------------------------------------------- *)

  (** The Fp-level FieldParameters used by the bedrock2 instances. *)
  Local Instance fp_params : FieldParameters Fp :=
    {| Fzero := @F.zero p; Fone := @F.one p; Feq := @eq Fp;
       Fopp := @F.opp p; Finv := @F.inv p;
       Fadd := @F.add p; Fsub := @F.sub p;
       Fmul := @F.mul p; Fdiv := @F.div p;
       Feq_dec := @F.eq_dec p;
       a24 := @F.zero p;
       mul := "mul"; add := "add"; sub := "sub";
       opp := "opp"; square := "square";
       scmula24 := "scmula24"; inv := "inv";
       from_bytes := "from_bytes"; to_bytes := "to_bytes";
       select_znz := "select_znz"; felem_copy := "felem_copy";
       from_word := "from_word"; from_list := "from_list" |}.

  Let beta : Fp := F.of_Z p (-1).
  Let xi : Fp2 := (@F.one p, @F.one p).

  Local Instance fp2_params : FieldParameters Fp2 :=
    {| Fzero := @qe_zero _ fp_params;
       Fone  := @qe_one _ fp_params;
       Feq   := @eq Fp2;
       Fopp  := @qe_opp _ fp_params;
       Finv  := @qe_inv _ fp_params beta;
       Fadd  := @qe_add _ fp_params;
       Fsub  := @qe_sub _ fp_params;
       Fmul  := @qe_mul _ fp_params beta;
       Fdiv  := @qe_div _ fp_params beta;
       Feq_dec := @eq_dec_QE _ (@F.eq_dec p);
       a24   := @qe_zero _ fp_params;
       mul := "mul"; add := "add"; sub := "sub";
       opp := "opp"; square := "square";
       scmula24 := "scmula24"; inv := "inv";
       from_bytes := "from_bytes"; to_bytes := "to_bytes";
       select_znz := "select_znz"; felem_copy := "felem_copy";
       from_word := "from_word"; from_list := "from_list" |}.

  Let v_in_Fp4 : Fp4 :=
    ((@F.zero p, @F.zero p), (@F.one p, @F.zero p)).

  Local Instance fp4_params : FieldParameters Fp4 :=
    {| Fzero := @qe_zero _ fp2_params;
       Fone  := @qe_one _ fp2_params;
       Feq   := @eq Fp4;
       Fopp  := @qe_opp _ fp2_params;
       Finv  := @qe_inv _ fp2_params xi;
       Fadd  := @qe_add _ fp2_params;
       Fsub  := @qe_sub _ fp2_params;
       Fmul  := @qe_mul _ fp2_params xi;
       Fdiv  := @qe_div _ fp2_params xi;
       Feq_dec := @eq_dec_QE _ (@eq_dec_QE _ (@F.eq_dec p));
       a24   := @qe_zero _ fp2_params;
       mul := "mul"; add := "add"; sub := "sub";
       opp := "opp"; square := "square";
       scmula24 := "scmula24"; inv := "inv";
       from_bytes := "from_bytes"; to_bytes := "to_bytes";
       select_znz := "select_znz"; felem_copy := "felem_copy";
       from_word := "from_word"; from_list := "from_list" |}.

  Local Instance fp8_params : FieldParameters Fp8 :=
    {| Fzero := @qe_zero _ fp4_params;
       Fone  := @qe_one _ fp4_params;
       Feq   := @eq Fp8;
       Fopp  := @qe_opp _ fp4_params;
       Finv  := @qe_inv _ fp4_params v_in_Fp4;
       Fadd  := @qe_add _ fp4_params;
       Fsub  := @qe_sub _ fp4_params;
       Fmul  := @qe_mul _ fp4_params v_in_Fp4;
       Fdiv  := @qe_div _ fp4_params v_in_Fp4;
       Feq_dec := @eq_dec_QE _ (@eq_dec_QE _ (@eq_dec_QE _ (@F.eq_dec p)));
       a24   := @qe_zero _ fp4_params;
       mul := "mul"; add := "add"; sub := "sub";
       opp := "opp"; square := "square";
       scmula24 := "scmula24"; inv := "inv";
       from_bytes := "from_bytes"; to_bytes := "to_bytes";
       select_znz := "select_znz"; felem_copy := "felem_copy";
       from_word := "from_word"; from_list := "from_list" |}.

  Local Lemma beta_is_opp_one : beta = @F.opp p (@F.one p).
  Proof.
    unfold beta. change (-1)%Z with (Z.opp 1%Z).
    rewrite F.of_Z_opp. reflexivity.
  Qed.

  Add Ring Fp_ring : (Fp_ring_theory p).

  (* ================================================================ *)
  (* Fp2 bridges: qe_ops (Fp, beta=-1) = Tower.fp2_ops               *)
  (* ================================================================ *)

  (** qe_add = Tower.fp2_add *)
  Lemma fp2_add_bridge : forall a b : Fp2,
    @qe_add _ fp_params a b = Tower.fp2_add p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** qe_sub = Tower.fp2_sub *)
  Lemma fp2_sub_bridge : forall a b : Fp2,
    @qe_sub _ fp_params a b = Tower.fp2_sub p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** qe_opp = Tower.fp2_neg *)
  Lemma fp2_neg_bridge : forall a : Fp2,
    @qe_opp _ fp_params a = Tower.fp2_neg p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** qe_mul beta = Tower.fp2_mul *)
  Lemma fp2_mul_bridge : forall a b : Fp2,
    @qe_mul _ fp_params beta a b = Tower.fp2_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold qe_mul, Tower.fp2_mul, Fadd, Fmul, fp_params; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  (** qe_mul beta x x = Tower.fp2_sqr x *)
  Lemma fp2_sqr_bridge : forall a : Fp2,
    @qe_mul _ fp_params beta a a = Tower.fp2_sqr p a.
  Proof.
    intros [a0 a1].
    unfold qe_mul, Tower.fp2_sqr, Fadd, Fmul, fp_params; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  (** qe_inv beta = Tower.fp2_inv *)
  Lemma fp2_inv_bridge : forall a : Fp2,
    @qe_inv _ fp_params beta a = Tower.fp2_inv p a.
  Proof.
    intros [a0 a1].
    unfold qe_inv, Tower.fp2_inv, Fadd, Fmul, Fsub, Fopp, Finv, fp_params;
      simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    replace (a0 * a0 - F.opp 1 * (a1 * a1))%F
      with (a0 * a0 + a1 * a1)%F by ring.
    reflexivity.
  Qed.

  (** Conjugate *)
  Lemma fp2_conjugate_bridge : forall a : Fp2,
    (fst a, @F.opp p (snd a)) = Tower.fp2_conjugate p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** mul_by_xi: qe_mul beta (1,1) a = Tower.fp2_mul_xi a *)
  Lemma fp2_mul_xi_bridge : forall a : Fp2,
    @qe_mul _ fp_params beta (@F.one p, @F.one p) a = Tower.fp2_mul_xi p a.
  Proof.
    intros [a0 a1].
    unfold qe_mul, Tower.fp2_mul_xi, Fadd, Fmul, fp_params; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  (* ================================================================ *)
  (* Fp4 bridges: qe_ops (Fp2, xi=(1,1)) = Tower.fp4_ops             *)
  (* ================================================================ *)

  (** Fp4 add/sub/neg: componentwise Fp2 operations = Tower *)
  Lemma fp4_add_bridge : forall a b : Fp4,
    @qe_add _ fp2_params a b = Tower.fp4_add p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  Lemma fp4_sub_bridge : forall a b : Fp4,
    @qe_sub _ fp2_params a b = Tower.fp4_sub p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  Lemma fp4_neg_bridge : forall a : Fp4,
    @qe_opp _ fp2_params a = Tower.fp4_neg p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** Local helper: fp2_mul_xi stated in terms of section's xi *)
  Local Lemma fp2_mul_xi_eq : forall a : Fp2,
    @qe_mul _ fp_params beta xi a = Tower.fp2_mul_xi p a.
  Proof. intros; unfold xi; apply fp2_mul_xi_bridge. Qed.

  (** qe_mul xi = Tower.fp4_mul *)
  Lemma fp4_mul_bridge : forall a b : Fp4,
    @qe_mul _ fp2_params xi a b = Tower.fp4_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold qe_mul at 1; simpl fst; simpl snd.
    change (@Fmul Fp2 fp2_params) with (@qe_mul Fp fp_params beta);
    change (@Fadd Fp2 fp2_params) with (@qe_add Fp fp_params).
    unfold Tower.fp4_mul; simpl fst; simpl snd.
    rewrite !fp2_mul_xi_eq, !fp2_mul_bridge, !fp2_add_bridge.
    reflexivity.
  Qed.

  (** qe_inv xi = Tower.fp4_inv *)
  Lemma fp4_inv_bridge : forall a : Fp4,
    @qe_inv _ fp2_params xi a = Tower.fp4_inv p a.
  Proof.
    intros [a0 a1].
    unfold qe_inv at 1; simpl fst; simpl snd.
    change (@Fmul Fp2 fp2_params) with (@qe_mul Fp fp_params beta);
    change (@Fsub Fp2 fp2_params) with (@qe_sub Fp fp_params);
    change (@Fopp Fp2 fp2_params) with (@qe_opp Fp fp_params);
    change (@Finv Fp2 fp2_params) with (@qe_inv Fp fp_params beta).
    rewrite !fp2_mul_xi_eq, !fp2_mul_bridge,
            !fp2_sub_bridge, !fp2_inv_bridge, !fp2_neg_bridge.
    unfold Tower.fp4_inv; simpl fst; simpl snd.
    reflexivity.
  Qed.

  (** mul_by_v: used as mul_by_nonresidue at the Fp8 level. *)
  Lemma fp4_mul_by_v_bridge : forall a : Fp4,
    (@qe_mul _ fp_params beta xi (snd a), fst a) = Tower.fp4_mul_by_v p a.
  Proof.
    intros [a0 a1].
    unfold Tower.fp4_mul_by_v; simpl fst; simpl snd.
    rewrite fp2_mul_xi_eq. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Fp8 bridges: qe_ops (Fp4, v_in_Fp4) = Tower.fp8_ops             *)
  (* ================================================================ *)

  (** Fp4 mul by v via full multiplication *)
  Local Lemma fp4_mul_by_v_eq : forall a : Fp4,
    @qe_mul _ fp2_params xi v_in_Fp4 a = Tower.fp4_mul_by_v p a.
  Proof.
    intros [[a00 a01] [a10 a11]].
    rewrite fp4_mul_bridge.
    unfold Tower.fp4_mul, Tower.fp4_mul_by_v; simpl fst; simpl snd.
    unfold v_in_Fp4; simpl fst; simpl snd.
    unfold Tower.fp2_mul, Tower.fp2_add, Tower.fp2_mul_xi; simpl fst; simpl snd.
    f_equal.
    - f_equal; ring.
    - f_equal; ring.
  Qed.

  Lemma fp8_add_bridge : forall a b : Fp8,
    @qe_add _ fp4_params a b = Tower.fp8_add p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  Lemma fp8_sub_bridge : forall a b : Fp8,
    @qe_sub _ fp4_params a b = Tower.fp8_sub p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  Lemma fp8_neg_bridge : forall a : Fp8,
    @qe_opp _ fp4_params a = Tower.fp8_neg p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** qe_mul v_in_Fp4 = Tower.fp8_mul *)
  Lemma fp8_mul_bridge : forall a b : Fp8,
    @qe_mul _ fp4_params v_in_Fp4 a b = Tower.fp8_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold qe_mul at 1; simpl fst; simpl snd.
    change (@Fmul Fp4 fp4_params) with (@qe_mul Fp2 fp2_params xi);
    change (@Fadd Fp4 fp4_params) with (@qe_add Fp2 fp2_params).
    unfold Tower.fp8_mul; simpl fst; simpl snd.
    rewrite !fp4_mul_by_v_eq, !fp4_mul_bridge, !fp4_add_bridge.
    reflexivity.
  Qed.

  (** qe_inv v_in_Fp4 = Tower.fp8_inv *)
  Lemma fp8_inv_bridge : forall a : Fp8,
    @qe_inv _ fp4_params v_in_Fp4 a = Tower.fp8_inv p a.
  Proof.
    intros [a0 a1].
    unfold qe_inv at 1; simpl fst; simpl snd.
    change (@Fmul Fp4 fp4_params) with (@qe_mul Fp2 fp2_params xi);
    change (@Fadd Fp4 fp4_params) with (@qe_add Fp2 fp2_params);
    change (@Fsub Fp4 fp4_params) with (@qe_sub Fp2 fp2_params);
    change (@Fopp Fp4 fp4_params) with (@qe_opp Fp2 fp2_params);
    change (@Finv Fp4 fp4_params) with (@qe_inv Fp2 fp2_params xi).
    rewrite !fp4_mul_by_v_eq, !fp4_mul_bridge,
            !fp4_sub_bridge, !fp4_inv_bridge, !fp4_neg_bridge.
    unfold Tower.fp8_inv; simpl fst; simpl snd.
    reflexivity.
  Qed.

  (** mul_by_w: nonresidue multiplication Fp8 -> Fp24. *)
  Lemma fp8_mul_by_w_bridge : forall a : Fp8,
    (@qe_mul _ fp2_params xi v_in_Fp4 (snd a), fst a) =
    Tower.fp8_mul_by_w p a.
  Proof.
    intros [a0 a1].
    unfold Tower.fp8_mul_by_w; simpl fst; simpl snd.
    rewrite fp4_mul_by_v_eq. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Fp24 bridges: ce_ops (Fp8, mul_by_w) = Tower.fp24_ops            *)
  (* ================================================================ *)

  (** The mul_by_nr model for Fp24's cubic extension. *)
  Let mul_by_w (x : Fp8) : Fp8 :=
    let fp2_mul_xi_model (a : Fp2) : Fp2 :=
      (F.sub (fst a) (snd a), F.add (fst a) (snd a)) in
    let fp4_mul_by_v_model (c : Fp4) : Fp4 :=
      (fp2_mul_xi_model (snd c), fst c) in
    (fp4_mul_by_v_model (snd x), fst x).

  Local Lemma mul_by_w_eq : forall x : Fp8,
    mul_by_w x = Tower.fp8_mul_by_w p x.
  Proof.
    intros [[e0_lo e0_hi] [e1_lo e1_hi]].
    unfold mul_by_w, Tower.fp8_mul_by_w, Tower.fp4_mul_by_v, Tower.fp2_mul_xi.
    simpl fst; simpl snd. reflexivity.
  Qed.

  Lemma fp24_add_bridge : forall a b : Fp24,
    @ce_add _ fp8_params a b = Tower.fp24_add p a b.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold ce_add, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    change (@Fadd Fp8 fp8_params) with (@qe_add Fp4 fp4_params).
    unfold Tower.fp24_add, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite !fp8_add_bridge. reflexivity.
  Qed.

  Lemma fp24_sub_bridge : forall a b : Fp24,
    @ce_sub _ fp8_params a b = Tower.fp24_sub p a b.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold ce_sub, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    change (@Fsub Fp8 fp8_params) with (@qe_sub Fp4 fp4_params).
    unfold Tower.fp24_sub, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite !fp8_sub_bridge. reflexivity.
  Qed.

  Lemma fp24_neg_bridge : forall a : Fp24,
    @ce_opp _ fp8_params a = Tower.fp24_neg p a.
  Proof.
    intros [[a0 a1] a2].
    unfold ce_opp, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    change (@Fopp Fp8 fp8_params) with (@qe_opp Fp4 fp4_params).
    unfold Tower.fp24_neg, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite !fp8_neg_bridge. reflexivity.
  Qed.

  (** ce_mul mul_by_w = Tower.fp24_mul *)
  Lemma fp24_mul_bridge : forall a b : Fp24,
    @ce_mul _ fp8_params mul_by_w a b = Tower.fp24_mul p a b.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold ce_mul, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    change (@Fmul Fp8 fp8_params) with (@qe_mul Fp4 fp4_params v_in_Fp4);
    change (@Fadd Fp8 fp8_params) with (@qe_add Fp4 fp4_params);
    change (@Fsub Fp8 fp8_params) with (@qe_sub Fp4 fp4_params).
    unfold Tower.fp24_mul, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite !fp8_mul_bridge, !fp8_add_bridge, !fp8_sub_bridge, !mul_by_w_eq.
    reflexivity.
  Qed.

  Lemma fp24_conjugate_bridge : forall a : Fp24,
    ce_build (ce_c0 a) (@Fopp _ fp8_params (ce_c1 a)) (ce_c2 a) =
    Tower.fp24_conjugate p a.
  Proof.
    intros [[a0 a1] a2].
    unfold ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    change (@Fopp Fp8 fp8_params) with (@qe_opp Fp4 fp4_params).
    unfold Tower.fp24_conjugate, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite fp8_neg_bridge. reflexivity.
  Qed.

  Lemma fp24_mul_by_t_bridge : forall a : Fp24,
    @ce_mul_by_v _ mul_by_w a = Tower.fp24_mul_by_t p a.
  Proof.
    intros [[a0 a1] a2].
    unfold ce_mul_by_v, ce_build, ce_c0, ce_c1, ce_c2; simpl fst; simpl snd.
    unfold Tower.fp24_mul_by_t, Tower.fp24_build,
           Tower.fp24_c0, Tower.fp24_c1, Tower.fp24_c2; simpl fst; simpl snd.
    rewrite mul_by_w_eq. reflexivity.
  Qed.

  (* ================================================================ *)
  (* Algebraic identities at the Fp4 level (fast: ring on Fp2 pairs) *)
  (* ================================================================ *)

  Local Ltac fp4_pair_ring :=
    apply (fun H1 H2 => f_equal2 pair H1 H2);
    unfold Tower.fp4_add, Tower.fp4_sub, Tower.fp2_add, Tower.fp2_sub;
    simpl fst; simpl snd; f_equal; ring.

  Lemma fp4_sub_sub_eq_sub_add : forall x y z : Fp4,
    Tower.fp4_sub p (Tower.fp4_sub p x y) z =
    Tower.fp4_sub p x (Tower.fp4_add p y z).
  Proof. intros [[??][??]] [[??][??]] [[??][??]]. fp4_pair_ring. Qed.

  Lemma fp4_add_comm : forall x y : Fp4,
    Tower.fp4_add p x y = Tower.fp4_add p y x.
  Proof. intros [[??][??]] [[??][??]]. fp4_pair_ring. Qed.

  Lemma fp4_mul_comm : forall x y : Fp4,
    Tower.fp4_mul p x y = Tower.fp4_mul p y x.
  Proof.
    intros [[a0 a1][a2 a3]] [[b0 b1][b2 b3]].
    unfold Tower.fp4_mul, Tower.fp4_add, Tower.fp2_mul, Tower.fp2_add,
           Tower.fp2_mul_xi; simpl fst; simpl snd.
    apply (fun H1 H2 => f_equal2 pair H1 H2); f_equal; ring.
  Qed.

  (* ================================================================ *)
  (* Algebraic identities at the Fp8 level (COMPOSITIONAL — fast)     *)
  (* ================================================================ *)

  (** Sub-associativity: (x - y) - z = x - (y + z) — via Fp4 *)
  Lemma fp8_sub_sub_eq_sub_add : forall x y z : Fp8,
    Tower.fp8_sub p (Tower.fp8_sub p x y) z =
    Tower.fp8_sub p x (Tower.fp8_add p y z).
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold Tower.fp8_sub, Tower.fp8_add; simpl fst; simpl snd.
    apply (fun H1 H2 => f_equal2 pair H1 H2);
      apply fp4_sub_sub_eq_sub_add.
  Qed.

  (** Karatsuba cross term — via Fp4 operations, NOT unfolded to Fp *)
  Lemma fp8_karatsuba_cross_term : forall a b : Fp8,
    Tower.fp8_sub p
      (Tower.fp8_sub p
        (Tower.fp8_mul p (Tower.fp8_add p a b) (Tower.fp8_add p a b))
        (Tower.fp8_mul p a a))
      (Tower.fp8_mul p b b) =
    Tower.fp8_add p (Tower.fp8_mul p a b) (Tower.fp8_mul p a b).
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Tower.fp8_mul, Tower.fp8_add, Tower.fp8_sub; simpl fst; simpl snd.
    (* Now goal has Fp4 operations only — use f_equal2 to split *)
    apply (fun H1 H2 => f_equal2 pair H1 H2).
    - (* c0: involves fp4_mul_by_v — need to unfold one more level *)
      unfold Tower.fp4_mul_by_v.
      (* Now: fp4_add/sub/mul + fp2_mul_xi — destruct Fp4 elements *)
      destruct a0 as [[a00 a01][a02 a03]]; destruct a1 as [[a10 a11][a12 a13]];
      destruct b0 as [[b00 b01][b02 b03]]; destruct b1 as [[b10 b11][b12 b13]].
      unfold Tower.fp4_mul, Tower.fp4_add, Tower.fp4_sub,
             Tower.fp2_mul, Tower.fp2_add, Tower.fp2_sub,
             Tower.fp2_mul_xi; simpl fst; simpl snd.
      apply (fun H1 H2 => f_equal2 pair H1 H2); f_equal; ring.
    - (* c1: pure fp4 operations *)
      destruct a0 as [[a00 a01][a02 a03]]; destruct a1 as [[a10 a11][a12 a13]];
      destruct b0 as [[b00 b01][b02 b03]]; destruct b1 as [[b10 b11][b12 b13]].
      unfold Tower.fp4_mul, Tower.fp4_add, Tower.fp4_sub,
             Tower.fp2_mul, Tower.fp2_add, Tower.fp2_sub,
             Tower.fp2_mul_xi; simpl fst; simpl snd.
      apply (fun H1 H2 => f_equal2 pair H1 H2); f_equal; ring.
  Qed.

  (** mul_self: fp8_mul a a has squaring-style form *)
  Lemma fp8_mul_self_alt : forall a : Fp8,
    Tower.fp8_mul p a a =
    let a0 := fst a in let a1 := snd a in
    (Tower.fp4_add p (Tower.fp4_mul p a0 a0)
                     (Tower.fp4_mul_by_v p (Tower.fp4_mul p a1 a1)),
     Tower.fp4_add p (Tower.fp4_mul p a0 a1) (Tower.fp4_mul p a0 a1)).
  Proof.
    intros [a0 a1]; unfold Tower.fp8_mul; simpl fst; simpl snd.
    f_equal. f_equal. apply fp4_mul_comm.
  Qed.

End AllFeval.

(* ================================================================== *)
(** * Hint databases for easy rewriting                                *)
(* ================================================================== *)

#[export] Hint Rewrite
  fp2_add_bridge fp2_sub_bridge fp2_neg_bridge
  fp2_mul_bridge fp2_sqr_bridge fp2_inv_bridge
  fp2_conjugate_bridge fp2_mul_xi_bridge
  : bls24_fp2_feval_bridge.

#[export] Hint Rewrite
  fp4_add_bridge fp4_sub_bridge fp4_neg_bridge
  fp4_mul_bridge fp4_inv_bridge fp4_mul_by_v_bridge
  : bls24_fp4_feval_bridge.

#[export] Hint Rewrite
  fp8_add_bridge fp8_sub_bridge fp8_neg_bridge
  fp8_mul_bridge fp8_inv_bridge fp8_mul_by_w_bridge
  : bls24_fp8_feval_bridge.

#[export] Hint Rewrite
  fp24_add_bridge fp24_sub_bridge fp24_neg_bridge
  fp24_mul_bridge fp24_conjugate_bridge fp24_mul_by_t_bridge
  : bls24_fp24_feval_bridge.
