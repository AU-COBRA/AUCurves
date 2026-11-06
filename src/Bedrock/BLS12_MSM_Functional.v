(** * BLS12_MSM_Functional — what [msm_bls12] computes, as a sum k_i P_i.

    [BLS12_MSM.msm_bls12_prog_ok] proves, with no algebraic premise,
    that the bedrock2 program [msm_bls12] returns the triple
    [msm_prog_output] = [BLS12_MSM.msm_prog] (program order, buckets
    start from the identity, raw triples).  This file proves:

    - [msm_prog_correct]: in any commutative monoid up to an
      equivalence [eqv] (laws only up to [eqv], [dbl a == a + a]),
      [msm_prog c nw ss ps == sum_i [wval c nw s_i] p_i], where
      [wval c nw s = sum_{w < nw} 2^(c w) * digit_w(s)];
    - [f_msm_prog], [f_msm_ref]: a map commuting with identity,
      addition and doubling commutes with [msm_prog] and with the
      reference sum (Leibniz);
    - [wval_limbs]: for four 64-bit limbs, [wval 9 29] is the 256-bit
      little-endian integer of the limbs;
    - [msm_prog_rcb_correct]: for the complete a = 0 RCB formulas
      ([PointDoubleA0.ladderstep_triple] = Algorithm 7, the formula of
      [CurveAdd.ladderstep_gallina], and [rcb_double_a0_triple] =
      Algorithm 9) on points that satisfy [RcbProjectiveLaws.oncurve],
      [msm_prog] is [pt_eq] to [sum_i k_i P_i], the sum being computed
      with the same addition ([smul] = repeated addition) from the
      identity (0 : 1 : 0).  Its laws up to [pt_eq] come from
      [RcbProjectiveLaws] (fiat-crypto's [Projective.add] and the affine
      group [W.commutative_group]); the only extra premise is the
      curve's [no_two_torsion], discharged for BLS12-381 in
      [BLS12_MSM_Closed.v].

    No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(** ** 0. [reduce_buckets] as a fold                                   *)
(* ================================================================== *)

Lemma reduce_buckets_fold_gen {G : Type} (id : G) (add : G -> G -> G) (bs : list G) :
  reduce_buckets G id add bs
  = snd (fold_left (fun p b => let r' := add (fst p) b in (r', add (snd p) r'))
                   (rev bs) (id, id)).
Proof.
  unfold reduce_buckets.
  assert (H : forall l r a,
    (fix go (bs0 : list G) (running acc : G) {struct bs0} : G :=
       match bs0 with
       | [] => acc
       | b :: rest => let running' := add running b in
                      let acc' := add acc running' in go rest running' acc'
       end) l r a
    = snd (fold_left (fun p b => let r' := add (fst p) b in (r', add (snd p) r')) l (r, a))).
  { induction l as [|b l IH]; intros r a; [reflexivity|]. cbn. apply IH. }
  apply H.
Qed.

(* ================================================================== *)
(** ** 1. In a commutative monoid up to an equivalence                *)
(* ================================================================== *)

Section Monoid.
  Context {G : Type} (eqv : G -> G -> Prop) {eqv_Equivalence : Equivalence eqv}.
  Context (id : G) (add : G -> G -> G) (dbl : G -> G).
  Context {add_Proper : Proper (eqv ==> eqv ==> eqv) add}.
  Context (add_assoc : forall a b c, eqv (add (add a b) c) (add a (add b c)))
          (add_comm : forall a b, eqv (add a b) (add b a))
          (add_id_l : forall a, eqv (add id a) a)
          (dbl_add : forall a, eqv (dbl a) (add a a)).

  Local Infix "==" := eqv (at level 70).
  Local Infix "+" := add.

  Lemma add_id_r a : a + id == a.
  Proof. rewrite add_comm. apply add_id_l. Qed.

  Lemma add_swap a b c : a + (b + c) == b + (a + c).
  Proof. rewrite <- !add_assoc, (add_comm a b). reflexivity. Qed.

  Lemma add_4 a b c d : (a + b) + (c + d) == (a + c) + (b + d).
  Proof. rewrite !add_assoc, (add_swap b c d). reflexivity. Qed.

  Fixpoint smul (n : nat) (x : G) : G :=
    match n with O => id | S n => x + smul n x end.

  #[local] Instance smul_Proper n : Proper (eqv ==> eqv) (smul n).
  Proof. intros x y Hxy. induction n as [|n IH]; cbn; [reflexivity|]. apply add_Proper; assumption. Qed.

  Lemma smul_add a b x : smul (a + b) x == smul a x + smul b x.
  Proof.
    induction a as [|a IH]; cbn [smul Nat.add]; [symmetry; apply add_id_l|].
    rewrite IH, add_assoc. reflexivity.
  Qed.

  Lemma smul_id n : smul n id == id.
  Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. apply add_id_l. Qed.

  Lemma smul_dist n x y : smul n (x + y) == smul n x + smul n y.
  Proof.
    induction n as [|n IH]; cbn [smul]; [symmetry; apply add_id_l|].
    rewrite IH. apply add_4.
  Qed.

  Lemma smul_mul a b x : smul (a * b) x == smul a (smul b x).
  Proof.
    induction a as [|a IH]; cbn [smul Nat.mul]; [reflexivity|].
    rewrite smul_add, IH. reflexivity.
  Qed.

  Lemma iter_dbl k x : Nat.iter k dbl x == smul (2 ^ k) x.
  Proof.
    induction k as [|k IH].
    - cbn. symmetry. apply add_id_r.
    - change (Nat.iter (S k) dbl x) with (dbl (Nat.iter k dbl x)).
      rewrite dbl_add, IH.
      replace (2 ^ S k)%nat with (2 ^ k + 2 ^ k)%nat by (cbn; lia).
      rewrite smul_add. reflexivity.
  Qed.

  (** Sums over lists. *)
  Definition gsum (l : list G) : G := fold_right add id l.

  Lemma gsum_app l1 l2 : gsum (l1 ++ l2) == gsum l1 + gsum l2.
  Proof.
    induction l1 as [|x l1 IH]; cbn; [symmetry; apply add_id_l|].
    rewrite IH. symmetry. apply add_assoc.
  Qed.

  Lemma gsum_rev l : gsum (rev l) == gsum l.
  Proof.
    induction l as [|x l IH]; cbn [rev]; [reflexivity|].
    rewrite gsum_app, IH. cbn. rewrite add_id_r. apply add_comm.
  Qed.

  Lemma gsum_map_add {T} (u v : T -> G) (l : list T) :
    gsum (map (fun t => u t + v t) l) == gsum (map u l) + gsum (map v l).
  Proof.
    induction l as [|t l IH]; cbn; [symmetry; apply add_id_l|].
    rewrite IH. apply add_4.
  Qed.

  Lemma gsum_map_ext {T} (u v : T -> G) (l : list T) :
    (forall t, u t == v t) -> gsum (map u l) == gsum (map v l).
  Proof.
    intros H. induction l as [|t l IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity.
  Qed.

  Lemma smul_gsum {T} n (u : T -> G) (l : list T) :
    smul n (gsum (map u l)) == gsum (map (fun t => smul n (u t)) l).
  Proof.
    induction l as [|t l IH]; cbn; [apply smul_id|]. rewrite smul_dist, IH. reflexivity.
  Qed.

  (** Running-sum reduction: [reduce_buckets] computes
      [sum_k (k+1) * bs_k], written recursively as [wsum]. *)
  Fixpoint psum (bs : list G) : G :=
    match bs with [] => id | b :: bs => b + psum bs end.
  Fixpoint wsum (bs : list G) : G :=
    match bs with [] => id | b :: bs' => psum bs + wsum bs' end.

  Definition rstep (p : G * G) (b : G) : G * G :=
    let r' := fst p + b in (r', snd p + r').

  Lemma reduce_buckets_fold (bs : list G) :
    reduce_buckets G id add bs = snd (fold_left rstep (rev bs) (id, id)).
  Proof. apply reduce_buckets_fold_gen. Qed.

  Lemma fold_rstep (bs : list G) (r a : G) :
    fst (fold_left rstep (rev bs) (r, a)) == r + psum bs /\
    snd (fold_left rstep (rev bs) (r, a)) == a + (smul (length bs) r + wsum bs).
  Proof.
    induction bs as [|b bs IH].
    - cbn. split; [symmetry; apply add_id_r|]. rewrite add_id_l. symmetry. apply add_id_r.
    - cbn [rev]. rewrite fold_left_app. cbn [fold_left].
      destruct (fold_left rstep (rev bs) (r, a)) as [r1 a1] eqn:E.
      cbn [rstep fst snd] in *. destruct IH as [Hr Ha].
      split.
      + rewrite Hr. cbn [psum]. rewrite add_assoc, (add_comm (psum bs) b). reflexivity.
      + rewrite Ha, Hr. cbn [psum wsum smul length].
        (* a + (smul n r + wsum bs) + (r + psum bs + b)
           == a + ((r + smul n r) + ((b + psum bs) + wsum bs)) *)
        rewrite add_assoc. apply add_Proper; [reflexivity|].
        rewrite (add_4 r (smul (length bs) r) (b + psum bs) (wsum bs)).
        rewrite (add_comm (smul (length bs) r + wsum bs)).
        apply add_Proper; [|reflexivity].
        rewrite add_assoc, (add_comm (psum bs) b). reflexivity.
  Qed.

  Lemma reduce_buckets_wsum (bs : list G) :
    reduce_buckets G id add bs == wsum bs.
  Proof.
    rewrite reduce_buckets_fold. destruct (fold_rstep bs id id) as [_ H].
    rewrite H, smul_id, !add_id_l. reflexivity.
  Qed.

  Lemma psum_repeat n : psum (repeat id n) == id.
  Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. apply add_id_l. Qed.

  Lemma wsum_repeat n : wsum (repeat id n) == id.
  Proof.
    induction n as [|n IH]; cbn [repeat wsum]; [reflexivity|].
    rewrite IH, add_id_r. change (psum (id :: repeat id n)) with (id + psum (repeat id n)).
    rewrite psum_repeat. apply add_id_l.
  Qed.

  (** One bucket update adds [(j+1) * p] to the weighted sum. *)
  Lemma wsum_upd (j : nat) (bs : list G) (p : G) :
    (j < length bs)%nat ->
    psum (firstn j bs ++ [nth j bs id + p] ++ skipn (S j) bs) == psum bs + p /\
    wsum (firstn j bs ++ [nth j bs id + p] ++ skipn (S j) bs) == wsum bs + smul (S j) p.
  Proof.
    revert j. induction bs as [|b bs IH]; intros j Hj; [cbn in Hj; lia|].
    destruct j as [|j].
    - cbn [firstn skipn nth app psum wsum smul].
      assert (Hp : (b + p) + psum bs == (b + psum bs) + p).
      { rewrite !add_assoc, (add_comm p). reflexivity. }
      split; [exact Hp|].
      rewrite Hp, add_id_r. rewrite !add_assoc, (add_comm p (wsum bs)). reflexivity.
    - cbn [length] in Hj. destruct (IH j ltac:(lia)) as [Hp Hw].
      change (firstn (S j) (b :: bs)) with (b :: firstn j bs).
      change (nth (S j) (b :: bs) id) with (nth j bs id).
      change (skipn (S (S j)) (b :: bs)) with (skipn (S j) bs).
      set (L := firstn j bs ++ [nth j bs id + p] ++ skipn (S j) bs) in *.
      change ((b :: firstn j bs) ++ [nth j bs id + p] ++ skipn (S j) bs) with (b :: L).
      cbn [psum wsum smul]. rewrite Hp, Hw. split.
      + symmetry. apply add_assoc.
      + rewrite <- (add_assoc b (psum bs) p), add_4. reflexivity.
  Qed.

  (** Digits. *)
  Section Window.
    Context (w cc : nat).
    Definition digit (s : list Z) : nat := Z.to_nat (get_window s w cc).
    Definition wterm (sp : list Z * G) : G := smul (digit (fst sp)) (snd sp).

    Definition upd (bkts : list G) (sp : list Z * G) : list G :=
      let '(s, p) := sp in
      let idx := Z.to_nat (get_window s w cc) in
      if (idx =? 0)%nat then bkts
      else firstn (idx - 1) bkts ++ [nth (idx - 1) bkts id + p] ++ skipn idx bkts.

    Lemma length_upd bs sp :
      (digit (fst sp) <= length bs)%nat -> length (upd bs sp) = length bs.
    Proof.
      destruct sp as [s p]. unfold digit; cbn [upd fst].
      destruct (Nat.eqb_spec (Z.to_nat (get_window s w cc)) 0); intros H; [reflexivity|].
      rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia.
    Qed.

    Lemma wsum_upd_sp bs sp :
      (digit (fst sp) <= length bs)%nat ->
      wsum (upd bs sp) == wsum bs + wterm sp.
    Proof.
      destruct sp as [s p]. unfold wterm, upd, digit; cbn [fst snd].
      intros H. destruct (Z.to_nat (get_window s w cc)) as [|j] eqn:Ed.
      - cbn [Nat.eqb smul]. symmetry. apply add_id_r.
      - cbn [Nat.eqb]. replace (S j - 1)%nat with j by lia.
        apply (proj2 (wsum_upd j bs p ltac:(lia))).
    Qed.

    Lemma wsum_fold_upd l bs :
      Forall (fun sp => digit (fst sp) <= length bs)%nat l ->
      wsum (fold_left upd l bs) == wsum bs + gsum (map wterm l).
    Proof.
      revert bs. induction l as [|sp l IH]; intros bs Hall; cbn [fold_left map gsum fold_right].
      - symmetry. apply add_id_r.
      - inversion Hall as [|? ? Hsp Hl]; subst.
        rewrite IH.
        + rewrite wsum_upd_sp by exact Hsp. apply add_assoc.
        + rewrite length_upd by exact Hsp. exact Hl.
    Qed.
  End Window.

  Lemma get_window_lt (s : list Z) (w cc : nat) :
    (Z.to_nat (get_window s w cc) < Nat.pow 2 cc)%nat.
  Proof.
    unfold get_window.
    set (val' := if Nat.ltb 64 _ then _ else _).
    rewrite Z.land_ones by lia.
    assert (Hpos : 0 < 2 ^ Z.of_nat cc) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound val' (2 ^ Z.of_nat cc) Hpos) as [Hlo Hhi].
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Hlo.
    rewrite Nat2Z.inj_pow. cbn. exact Hhi.
  Qed.

  Lemma process_window_prog_sum ss ps w cc :
    process_window_prog G id add ss ps w cc (Nat.pow 2 cc - 1)
    == gsum (map (wterm w cc) (combine ss ps)).
  Proof.
    unfold process_window_prog.
    rewrite reduce_buckets_wsum.
    change (fold_left _ (rev (combine ss ps)) _) with
      (fold_left (upd w cc) (rev (combine ss ps)) (repeat id (Nat.pow 2 cc - 1))).
    rewrite wsum_fold_upd.
    - rewrite wsum_repeat, add_id_l, map_rev, gsum_rev. reflexivity.
    - apply Forall_forall. intros sp _. rewrite repeat_length. unfold digit.
      pose proof (get_window_lt (fst sp) w cc). lia.
  Qed.

  (** The windowed value of a scalar: [sum_{w < k} 2^(c w) digit_w]. *)
  Fixpoint wval (cc k : nat) (s : list Z) : nat :=
    match k with
    | O => O
    | S k => (2 ^ (cc * k) * digit k cc s + wval cc k s)%nat
    end.

  Definition msm_ref (cc k : nat) (ss : list (list Z)) (ps : list G) : G :=
    gsum (map (fun sp => smul (wval cc k (fst sp)) (snd sp)) (combine ss ps)).

  Theorem msm_prog_correct cc nw ss ps :
    msm_prog G id add dbl cc nw ss ps == msm_ref cc nw ss ps.
  Proof.
    unfold msm_prog, msm_ref.
    assert (Hgo : forall k acc,
      (fix go (w : nat) (acc : G) {struct w} : G :=
         match w with
         | 0%nat => acc
         | S w' =>
             go w' (Nat.iter cc dbl acc
                    + process_window_prog G id add ss ps w' cc (Nat.pow 2 cc - 1))
         end) k acc
      == smul (2 ^ (cc * k)) acc
         + gsum (map (fun sp => smul (wval cc k (fst sp)) (snd sp)) (combine ss ps))).
    { induction k as [|k IH]; intros acc.
      - cbn [wval smul]. rewrite Nat.mul_0_r. cbn [Nat.pow smul].
        rewrite add_id_r.
        assert (H0 : forall l : list (list Z * G), gsum (map (fun _ => id) l) == id).
        { induction l as [|? l IHl]; cbn; [reflexivity|]. rewrite IHl. apply add_id_l. }
        rewrite H0. symmetry. apply add_id_r.
      - rewrite IH. rewrite iter_dbl, process_window_prog_sum.
        rewrite smul_dist, <- smul_mul, smul_gsum, add_assoc.
        replace (2 ^ (cc * k) * 2 ^ cc)%nat with (2 ^ (cc * S k))%nat
          by (rewrite <- Nat.pow_add_r; f_equal; lia).
        apply add_Proper; [reflexivity|].
        rewrite <- gsum_map_add. apply gsum_map_ext.
        intros [s p]. unfold wterm; cbn [fst snd wval].
        rewrite <- smul_mul, <- smul_add. reflexivity. }
    rewrite Hgo, smul_id, add_id_l. reflexivity.
  Qed.
End Monoid.

(* ================================================================== *)
(** ** 2. Homomorphisms commute with the program-order MSM             *)
(* ================================================================== *)

Section Transfer.
  Context {A B : Type}.
  Context (idA : A) (addA : A -> A -> A) (dblA : A -> A).
  Context (idB : B) (addB : B -> B -> B) (dblB : B -> B).
  Context (f : A -> B).
  Context (f_id : f idA = idB)
          (f_add : forall x y, f (addA x y) = addB (f x) (f y))
          (f_dbl : forall x, f (dblA x) = dblB (f x)).

  Definition map_snd_pair (sp : list Z * A) : list Z * B :=
    (fst sp, f (snd sp)).

  Lemma map_combine_snd (ss : list (list Z)) (ps : list A) :
    map map_snd_pair (combine ss ps) = combine ss (map f ps).
  Proof.
    revert ps. induction ss as [|s ss IH]; intros [|p ps]; cbn; try reflexivity.
    f_equal. apply IH.
  Qed.

  Lemma f_reduce_buckets (bs : list A) :
    f (reduce_buckets A idA addA bs) = reduce_buckets B idB addB (map f bs).
  Proof.
    rewrite !reduce_buckets_fold_gen, <- map_rev.
    assert (H : forall l r a,
      f (snd (fold_left (fun p b => let r' := addA (fst p) b in (r', addA (snd p) r')) l (r, a)))
      = snd (fold_left (fun p b => let r' := addB (fst p) b in (r', addB (snd p) r'))
                       (map f l) (f r, f a))).
    { induction l as [|b l IH]; intros r a; [reflexivity|].
      cbn [fold_left map fst snd]. rewrite IH, !f_add. reflexivity. }
    rewrite H, f_id. reflexivity.
  Qed.

  Lemma f_iter (k : nat) (x : A) :
    f (Nat.iter k dblA x) = Nat.iter k dblB (f x).
  Proof.
    induction k as [|k IH]; [reflexivity|].
    change (Nat.iter (S k) dblA x) with (dblA (Nat.iter k dblA x)).
    change (Nat.iter (S k) dblB (f x)) with (dblB (Nat.iter k dblB (f x))).
    rewrite f_dbl, IH. reflexivity.
  Qed.

  Section Upd.
    Context (w c : nat).
    Definition updA (bkts : list A) (sp : list Z * A) : list A :=
      let '(s, p) := sp in
      let idx := Z.to_nat (get_window s w c) in
      if (idx =? 0)%nat then bkts
      else firstn (idx - 1) bkts ++ [addA (nth (idx - 1) bkts idA) p] ++ skipn idx bkts.
    Definition updB (bkts : list B) (sp : list Z * B) : list B :=
      let '(s, p) := sp in
      let idx := Z.to_nat (get_window s w c) in
      if (idx =? 0)%nat then bkts
      else firstn (idx - 1) bkts ++ [addB (nth (idx - 1) bkts idB) p] ++ skipn idx bkts.

    Lemma f_upd bs sp : map f (updA bs sp) = updB (map f bs) (map_snd_pair sp).
    Proof.
      destruct sp as [s p]. cbn [updA updB map_snd_pair fst snd].
      destruct (Z.to_nat (get_window s w c) =? 0)%nat; [reflexivity|].
      rewrite !map_app, firstn_map, skipn_map. cbn [map].
      rewrite f_add, <- f_id, map_nth. reflexivity.
    Qed.

    Lemma f_fold_upd l bs :
      map f (fold_left updA l bs) = fold_left updB (map map_snd_pair l) (map f bs).
    Proof.
      revert bs. induction l as [|sp l IH]; intros bs; [reflexivity|].
      cbn [fold_left map]. rewrite IH, f_upd. reflexivity.
    Qed.
  End Upd.

  Lemma f_process_window_prog ss ps w c nb :
    f (process_window_prog A idA addA ss ps w c nb)
    = process_window_prog B idB addB ss (map f ps) w c nb.
  Proof.
    unfold process_window_prog.
    rewrite f_reduce_buckets. f_equal.
    change (fold_left _ (rev (combine ss ps)) _) with
      (fold_left (updA w c) (rev (combine ss ps)) (repeat idA nb)).
    change (fold_left _ (rev (combine ss (map f ps))) _) with
      (fold_left (updB w c) (rev (combine ss (map f ps))) (repeat idB nb)).
    rewrite f_fold_upd, map_rev, map_combine_snd, map_repeat, f_id.
    reflexivity.
  Qed.

  Theorem f_msm_prog c nw ss ps :
    f (msm_prog A idA addA dblA c nw ss ps)
    = msm_prog B idB addB dblB c nw ss (map f ps).
  Proof.
    unfold msm_prog.
    assert (H : forall k acc,
      f ((fix go (w : nat) (acc : A) {struct w} : A :=
           match w with
           | 0%nat => acc
           | S w' => go w' (addA (Nat.iter c dblA acc)
                             (process_window_prog A idA addA ss ps w' c (2 ^ c - 1)))
           end) k acc)
      = (fix go (w : nat) (acc : B) {struct w} : B :=
           match w with
           | 0%nat => acc
           | S w' => go w' (addB (Nat.iter c dblB acc)
                             (process_window_prog B idB addB ss (map f ps) w' c (2 ^ c - 1)))
           end) k (f acc)).
    { induction k as [|k IH]; intros acc; [reflexivity|].
      cbn -[process_window_prog Nat.iter].
      rewrite IH, f_add, f_iter, f_process_window_prog. reflexivity. }
    rewrite H, f_id. reflexivity.
  Qed.

  Lemma f_smul n x : f (smul idA addA n x) = smul idB addB n (f x).
  Proof.
    induction n as [|n IH]; cbn [smul]; [exact f_id|]. rewrite f_add, IH. reflexivity.
  Qed.

  Theorem f_msm_ref cc k ss ps :
    f (msm_ref idA addA cc k ss ps) = msm_ref idB addB cc k ss (map f ps).
  Proof.
    unfold msm_ref, gsum. rewrite <- map_combine_snd, map_map.
    induction (combine ss ps) as [|[s p] l IH]; cbn [map fold_right]; [exact f_id|].
    rewrite f_add, IH, f_smul. reflexivity.
  Qed.
End Transfer.

(* ================================================================== *)
(** ** 3. The windowed value of four 64-bit limbs                       *)
(* ================================================================== *)

(* fiat-crypto's [Z.lor_shiftl], restated to keep this part Stdlib-only. *)
Lemma lor_shiftl_add (a b n : Z) :
  0 <= n -> 0 <= a < 2 ^ n -> Z.lor a (Z.shiftl b n) = a + Z.shiftl b n.
Proof.
  intros Hn Ha.
  assert (Hland : Z.land a (Z.shiftl b n) = 0).
  { apply Z.bits_inj'. intros t Ht. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec t n).
    + rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
    + rewrite <- (Z.mod_small a (2 ^ n)) by lia.
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- (Z.lxor_lor _ _ Hland). symmetry. apply Z.add_nocarry_lxor. exact Hland.
Qed.

Section Limbs.
  Context (l0 l1 l2 l3 : Z).
  Context (H0 : 0 <= l0 < 2 ^ 64) (H1 : 0 <= l1 < 2 ^ 64)
          (H2 : 0 <= l2 < 2 ^ 64) (H3 : 0 <= l3 < 2 ^ 64).

  (** The 256-bit little-endian integer of four 64-bit limbs. *)
  Definition limbsZ : Z := l0 + 2 ^ 64 * (l1 + 2 ^ 64 * (l2 + 2 ^ 64 * l3)).

  Definition suffix (L : Z) : Z :=
    if L =? 0 then l0 + 2 ^ 64 * (l1 + 2 ^ 64 * (l2 + 2 ^ 64 * (l3 + 2 ^ 64 * 0)))
    else if L =? 1 then l1 + 2 ^ 64 * (l2 + 2 ^ 64 * (l3 + 2 ^ 64 * 0))
    else if L =? 2 then l2 + 2 ^ 64 * (l3 + 2 ^ 64 * 0)
    else l3 + 2 ^ 64 * 0.

  Lemma limbsZ_bounds : 0 <= limbsZ < 2 ^ 256.
  Proof. unfold limbsZ. nia. Qed.

  Lemma div_shift (a b k sh : Z) :
    0 <= a < 2 ^ k -> 0 <= k -> 0 <= sh -> 0 <= b ->
    (a + 2 ^ k * b) / 2 ^ (k + sh) = b / 2 ^ sh.
  Proof.
    intros Ha Hk Hsh Hb.
    rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
    f_equal. rewrite Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; lia).
    rewrite Z.div_small by lia. lia.
  Qed.

  Lemma limbsZ_div (L sh : Z) :
    0 <= L <= 3 -> 0 <= sh ->
    limbsZ / 2 ^ (64 * L + sh) = suffix L / 2 ^ sh.
  Proof.
    intros HL Hsh. unfold limbsZ, suffix.
    rewrite !Z.mul_0_r, !Z.add_0_r.
    assert (HL4 : L = 0 \/ L = 1 \/ L = 2 \/ L = 3) by lia.
    destruct HL4 as [HL4|[HL4|[HL4|HL4]]]; subst L; cbn [Z.eqb Pos.eqb].
    - now rewrite Z.mul_0_r, Z.add_0_l.
    - replace (64 * 1 + sh) with (64 + sh) by lia.
      apply div_shift; nia.
    - replace (64 * 2 + sh) with (64 + (64 + sh)) by lia.
      rewrite div_shift by nia. apply div_shift; nia.
    - replace (64 * 3 + sh) with (64 + (64 + (64 + sh))) by lia.
      rewrite div_shift by nia. rewrite div_shift by nia. apply div_shift; nia.
  Qed.

  Lemma GA (l U sh : Z) :
    0 <= l < 2 ^ 64 -> 0 <= U -> 0 <= sh -> sh + 9 <= 64 ->
    Z.land (Z.shiftr l sh) (Z.ones 9) = ((l + 2 ^ 64 * U) / 2 ^ sh) mod 2 ^ 9.
  Proof.
    intros Hl HU Hsh Hs9.
    rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    replace (2 ^ 64 * U) with ((2 ^ (64 - sh) * U) * 2 ^ sh)
      by (rewrite <- Z.mul_assoc, (Z.mul_comm U), Z.mul_assoc, <- Z.pow_add_r by lia;
          f_equal; f_equal; lia).
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    assert (Hp : 2 ^ (64 - sh) = 2 ^ (64 - sh - 9) * 2 ^ 9)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Hp.
    replace (2 ^ (64 - sh - 9) * 2 ^ 9 * U) with ((2 ^ (64 - sh - 9) * U) * 2 ^ 9) by ring.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
    reflexivity.
  Qed.

  Lemma GA0 (l sh : Z) :
    0 <= sh ->
    Z.land (Z.shiftr l sh) (Z.ones 9) = ((l + 2 ^ 64 * 0) / 2 ^ sh) mod 2 ^ 9.
  Proof.
    intros Hsh. rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    now rewrite Z.mul_0_r, Z.add_0_r.
  Qed.

  Lemma GB (l l' R sh k : Z) :
    0 <= l < 2 ^ 64 -> 0 <= l' -> 0 <= R -> 0 <= sh < 64 -> 64 < sh + 9 ->
    k = 64 - sh ->
    Z.land (Z.lor (Z.shiftr l sh) (Z.shiftl l' k)) (Z.ones 9)
    = ((l + 2 ^ 64 * (l' + 2 ^ 64 * R)) / 2 ^ sh) mod 2 ^ 9.
  Proof.
    intros Hl Hl' HR Hsh Hs9 ->.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hlo : 0 <= l / 2 ^ sh < 2 ^ (64 - sh)).
    { split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z.pow_add_r by lia. replace (sh + (64 - sh)) with 64 by lia. lia. }
    rewrite lor_shiftl_add by lia.
    rewrite Z.shiftl_mul_pow2, Z.land_ones by lia.
    replace (2 ^ 64 * (l' + 2 ^ 64 * R)) with ((l' * 2 ^ (64 - sh) + (2 ^ (128 - sh)) * R) * 2 ^ sh).
    2:{ rewrite Z.mul_add_distr_r, <- !Z.mul_assoc, <- Z.pow_add_r by lia.
        rewrite (Z.mul_comm R), Z.mul_assoc, <- Z.pow_add_r by lia.
        replace (64 - sh + sh) with 64 by lia. replace (128 - sh + sh) with (64 + 64) by lia.
        rewrite Z.pow_add_r by lia. ring. }
    rewrite Z.div_add by (apply Z.pow_nonzero; lia).
    rewrite Z.add_assoc.
    assert (Hp : 2 ^ (128 - sh) = 2 ^ (128 - sh - 9) * 2 ^ 9)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Hp.
    replace (2 ^ (128 - sh - 9) * 2 ^ 9 * R) with ((2 ^ (128 - sh - 9) * R) * 2 ^ 9) by ring.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
    reflexivity.
  Qed.

  Ltac solve_digit :=
    match goal with
    | |- _ = (limbsZ / 2 ^ ?e) mod 2 ^ 9 =>
      let v := eval vm_compute in e in
      let L := eval vm_compute in (v / 64) in
      let sh := eval vm_compute in (v mod 64) in
      replace e with (64 * L + sh) by reflexivity;
      rewrite (limbsZ_div L sh) by lia; cbn [suffix Z.eqb Pos.eqb];
      first [ apply GA; lia | apply GB; lia | apply GA0; lia ]
    end.

  Lemma get_window_limbs (w : nat) :
    (w < 29)%nat ->
    get_window [l0; l1; l2; l3] w 9 = (limbsZ / 2 ^ (9 * Z.of_nat w)) mod 2 ^ 9.
  Proof.
    intros Hw.
    do 29 (destruct w as [|w];
           [ unfold get_window;
             cbn -[Z.land Z.shiftr Z.shiftl Z.lor Z.ones Z.pow Z.div Z.modulo
                   Z.add Z.mul Z.sub limbsZ];
             solve_digit | ]).
    lia.
  Qed.

  Lemma get_window_limbs_nonneg (w : nat) :
    (w < 29)%nat -> 0 <= get_window [l0; l1; l2; l3] w 9.
  Proof.
    intros Hw. rewrite get_window_limbs by exact Hw.
    apply Z.mod_pos_bound. lia.
  Qed.
End Limbs.

Lemma mod_mul_r_pos (a b c : Z) :
  0 < b -> 0 < c -> a mod (b * c) = a mod b + b * ((a / b) mod c).
Proof.
  intros Hb Hc. symmetry. apply Z.mod_unique_pos with (q := (a / b) / c).
  - pose proof (Z.mod_pos_bound a b Hb). pose proof (Z.mod_pos_bound (a / b) c Hc). nia.
  - pose proof (Z.div_mod a b ltac:(lia)) as E1.
    pose proof (Z.div_mod (a / b) c ltac:(lia)) as E2.
    set (q := a / b) in *. set (q2 := q / c) in *.
    set (r := a mod b) in *. set (r2 := q mod c) in *. nia.
Qed.

Lemma wval_mod (l0 l1 l2 l3 : Z) (k : nat) :
  0 <= l0 < 2 ^ 64 -> 0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 -> 0 <= l3 < 2 ^ 64 ->
  (k <= 29)%nat ->
  Z.of_nat (wval 9 k [l0; l1; l2; l3])
  = limbsZ l0 l1 l2 l3 mod 2 ^ (9 * Z.of_nat k).
Proof.
  intros H0 H1 H2 H3 Hk.
  pose proof (limbsZ_bounds l0 l1 l2 l3 H0 H1 H2 H3) as HS.
  induction k as [|k IH].
  - cbn [wval]. rewrite Z.mul_0_r, Z.pow_0_r, Z.mod_1_r. reflexivity.
  - cbn [wval]. unfold digit.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_pow, Z2Nat.id
      by (apply get_window_limbs_nonneg; lia).
    rewrite IH by lia.
    rewrite get_window_limbs by lia.
    rewrite Nat2Z.inj_mul.
    replace (9 * Z.of_nat (S k)) with (9 * Z.of_nat k + 9) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite mod_mul_r_pos by (apply Z.pow_pos_nonneg; lia).
    change (Z.of_nat 2) with 2. change (Z.of_nat 9) with 9. lia.
Qed.

(** The 29 nine-bit windows of [msm_bls12] cover the 256-bit scalar. *)
Theorem wval_limbs (l0 l1 l2 l3 : Z) :
  0 <= l0 < 2 ^ 64 -> 0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 -> 0 <= l3 < 2 ^ 64 ->
  wval 9 29 [l0; l1; l2; l3] = Z.to_nat (limbsZ l0 l1 l2 l3).
Proof.
  intros H0 H1 H2 H3.
  apply Nat2Z.inj. rewrite wval_mod by (assumption || lia).
  pose proof (limbsZ_bounds l0 l1 l2 l3 H0 H1 H2 H3) as HS.
  rewrite Z2Nat.id by lia.
  apply Z.mod_small. split; [lia|].
  eapply Z.lt_le_trans; [apply HS|]. apply Z.pow_le_mono_r; lia.
Qed.

(* ================================================================== *)
(** ** 4. The complete a = 0 RCB formulas, up to [pt_eq]                *)
(* ================================================================== *)

Section RcbInstance.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).
  Local Open Scope F_scope.

  Add Ring Fp_ring_msm : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Context (M_gt_27 : (27 < M_pos)%positive).
  Context (b three_b : F).
  Context (Hthree_b : three_b = b + b + b).
  Context (Hdisc : id
    ((((1 + 1 + 1 + 1) * 0 * 0 * 0
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)%F)).
  Context (Hno2 : no_two_torsion 0 b).

  Local Notation oncurve := (RcbProjectiveLaws.oncurve 0 b).
  Local Notation cadd := (RcbProjectiveLaws.cadd 0 three_b).
  Local Notation add_raw := (ladderstep_triple three_b).
  Local Notation dbl_raw := (rcb_double_a0_triple three_b).

  Definition Hexcept_rcb :=
    not_exceptional_of_no_two_torsion M_gt_27 0 b three_b Hthree_b Hdisc Hno2.

  (** [ladderstep_triple] (the formula of [CurveAdd.ladderstep_gallina],
      RCB Algorithm 7) is [RcbProjectiveLaws.cadd] at a = 0.  Same
      statement and proof as [BN254_wNAF_Laws.bn254_curve_add_is_cadd]
      ([bn254_curve_add] is definitionally [ladderstep_triple]); repeated
      here so as not to depend on the wNAF files that one lives with. *)
  Lemma ladderstep_triple_is_cadd (P Q : F * F * F) :
    add_raw P Q = cadd P Q.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2].
    cbv [ladderstep_triple RcbProjectiveLaws.cadd
         ladderstep_gallina rcb_add_general_gallina
         nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split;
      [ apply pair_equal_spec; split | ]; timeout 120 ring.
  Qed.

  Lemma oncurve_add_raw p q : oncurve p -> oncurve q -> oncurve (add_raw p q).
  Proof.
    intros Hp Hq. rewrite ladderstep_triple_is_cadd.
    exact (oncurve_cadd M_gt_27 0 b three_b Hthree_b Hdisc Hexcept_rcb p q Hp Hq).
  Qed.

  Lemma oncurve_a0_of p : oncurve p -> oncurve_a0 b p.
  Proof.
    destruct p as [[X Y] Z]. cbv [RcbProjectiveLaws.oncurve oncurve_a0].
    intros [H _]. rewrite H. ring.
  Qed.

  Lemma dbl_raw_eq p : oncurve p -> dbl_raw p = add_raw p p.
  Proof.
    intros Hp. apply (rcb_double_a0_eq_ladderstep b); [exact Hthree_b|].
    apply oncurve_a0_of. exact Hp.
  Qed.

  (** The on-curve triples, with the program's operations. *)
  Definition Gs : Type := { p : F * F * F | oncurve p }.
  Definition ids : Gs := exist _ id_pt (oncurve_id M_gt_27 0 b three_b Hthree_b).
  Definition adds (x y : Gs) : Gs :=
    exist _ (add_raw (proj1_sig x) (proj1_sig y))
      (oncurve_add_raw _ _ (proj2_sig x) (proj2_sig y)).
  Definition dbls (x : Gs) : Gs :=
    exist _ (dbl_raw (proj1_sig x))
      (eq_ind_r oncurve (oncurve_add_raw _ _ (proj2_sig x) (proj2_sig x))
         (dbl_raw_eq _ (proj2_sig x))).
  Definition eqs (x y : Gs) : Prop := pt_eq (proj1_sig x) (proj1_sig y).

  #[local] Instance eqs_Equivalence : Equivalence eqs.
  Proof.
    pose proof (pt_eq_Equivalence M_gt_27 b three_b Hthree_b) as E.
    split; unfold eqs.
    - intros x. reflexivity.
    - intros x y H. symmetry. exact H.
    - intros x y z H1 H2. etransitivity; eassumption.
  Qed.

  #[local] Instance adds_Proper : Proper (eqs ==> eqs ==> eqs) adds.
  Proof.
    intros [x Hx] [x' Hx'] Ex [y Hy] [y' Hy'] Ey. unfold eqs, adds in *; cbn [proj1_sig] in *.
    rewrite !ladderstep_triple_is_cadd.
    exact (cadd_Proper M_gt_27 0 b three_b Hthree_b Hdisc Hexcept_rcb
             x x' y y' Hx Hx' Hy Hy' Ex Ey).
  Qed.

  Lemma adds_assoc a b' c : eqs (adds (adds a b') c) (adds a (adds b' c)).
  Proof.
    destruct a as [x Hx], b' as [y Hy], c as [z Hz]. unfold eqs, adds; cbn [proj1_sig].
    rewrite !ladderstep_triple_is_cadd.
    pose proof (pt_eq_Equivalence M_gt_27 b three_b Hthree_b) as E.
    symmetry.
    exact (cadd_assoc M_gt_27 0 b three_b Hthree_b Hdisc Hexcept_rcb x y z Hx Hy Hz).
  Qed.

  Lemma adds_comm a b' : eqs (adds a b') (adds b' a).
  Proof.
    destruct a as [x Hx], b' as [y Hy]. unfold eqs, adds; cbn [proj1_sig].
    rewrite !ladderstep_triple_is_cadd.
    exact (cadd_comm M_gt_27 0 b three_b Hthree_b Hdisc Hexcept_rcb x y Hx Hy).
  Qed.

  Lemma adds_id_l a : eqs (adds ids a) a.
  Proof.
    destruct a as [x Hx]. unfold eqs, adds, ids; cbn [proj1_sig].
    rewrite !ladderstep_triple_is_cadd.
    exact (cadd_id_l M_gt_27 0 b three_b Hthree_b Hdisc Hexcept_rcb x Hx).
  Qed.

  Lemma dbls_add a : eqs (dbls a) (adds a a).
  Proof.
    destruct a as [x Hx]. unfold eqs, adds, dbls; cbn [proj1_sig].
    rewrite (dbl_raw_eq x Hx).
    pose proof (pt_eq_Equivalence M_gt_27 b three_b Hthree_b) as E. reflexivity.
  Qed.

  Lemma lift_points (ps : list (F * F * F)) :
    Forall oncurve ps -> exists qs : list Gs, map (@proj1_sig _ _) qs = ps.
  Proof.
    induction 1 as [|p ps Hp _ [qs IH]].
    - exists []. reflexivity.
    - exists (exist _ p Hp :: qs). cbn. rewrite IH. reflexivity.
  Qed.

  (** The program-order MSM over the RCB formulas, on on-curve points,
      is projectively equal to [sum_i [wval c nw s_i] P_i] (repeated
      RCB addition from (0 : 1 : 0)). *)
  Theorem msm_prog_rcb_correct cc nw (ss : list (list Z)) (ps : list (F * F * F)) :
    Forall oncurve ps ->
    pt_eq (msm_prog (F * F * F) id_pt add_raw dbl_raw cc nw ss ps)
          (msm_ref id_pt add_raw cc nw ss ps).
  Proof.
    intros Hps. destruct (lift_points ps Hps) as [qs <-].
    rewrite <- (f_msm_prog ids adds dbls id_pt add_raw dbl_raw (@proj1_sig _ _)
                  eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)).
    rewrite <- (f_msm_ref ids adds id_pt add_raw (@proj1_sig _ _)
                  eq_refl (fun _ _ => eq_refl)).
    change (eqs (msm_prog Gs ids adds dbls cc nw ss qs) (msm_ref ids adds cc nw ss qs)).
    apply (msm_prog_correct eqs ids adds dbls adds_assoc adds_comm adds_id_l dbls_add).
  Qed.

  (** The on-curve predicate is closed under the program's operations,
      and the output of [msm_prog] on on-curve points is on the curve. *)
  Lemma oncurve_msm_prog cc nw ss (ps : list (F * F * F)) :
    Forall oncurve ps ->
    oncurve (msm_prog (F * F * F) id_pt add_raw dbl_raw cc nw ss ps).
  Proof.
    intros Hps. destruct (lift_points ps Hps) as [qs <-].
    rewrite <- (f_msm_prog ids adds dbls id_pt add_raw dbl_raw (@proj1_sig _ _)
                  eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)).
    apply proj2_sig.
  Qed.
End RcbInstance.
