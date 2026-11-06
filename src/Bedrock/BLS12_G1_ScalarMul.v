(** * BLS12_G1_ScalarMul — G1 scalar multiplication as a proved bedrock2 program.

    [g1_scalar_mul] is a bedrock2 function that multiplies a point by a
    256-bit scalar (four little-endian 64-bit limbs) with the
    most-significant-bit-first double-and-add method:

      out := (0 : 1 : 0);
      for i = 255 down to 0:
        out := double(out);
        if bit i of the scalar is set: out := out + P

    It calls the same three callees as the Pippenger MSM
    [BLS12_MSM.msm_bls12], under the same contracts
    ([BLS12_MSM.CurveAddAliasedOK], [CurveDoubleInplaceOK],
    [StoreZero3OK]), so in the BLS12-381 instantiation the callees are
    the copy-out wrappers ["msm_curve_add"] / ["msm_curve_double"] and
    ["store_zero"], whose contracts are proved in [BLS12_MSM_Wrappers].

    This file proves:
    - [dadd_correct]: in a commutative monoid up to an equivalence
      (with [dbl a == a + a]), the program-order Gallina function
      [smul_prog] equals [k P] for the integer [k] whose bits the
      program reads;
    - [bits_limbs]: for four 64-bit limbs, that integer is the 256-bit
      little-endian value of the limbs;
    - [smul_prog_rcb_correct]: for the complete a = 0 RCB formulas on an
      on-curve point, [smul_prog] is [pt_eq] to [k P] (repeated RCB
      addition from (0 : 1 : 0));
    - [g1_scalar_mul_ok]: the bedrock2 function returns [smul_prog] on
      the raw triples, assuming only the three callee contracts.
    The closed BLS12-381 statement is
    [BLS12_MSM_Closed.g1_scalar_mul_closed].

    The branch on the scalar bit makes the running time depend on the
    scalar; this is a variable-time scalar multiplication.

    No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require bedrock2.Loops.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Import Syntax BinInt String List.ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(** ** 1. Gallina: double-and-add in program order                     *)
(* ================================================================== *)

(** Bit [i] of the scalar given as limbs [s] (64 bits per limb). *)
Definition scalar_bit (s : list Z) (i : nat) : bool :=
  Z.testbit (nth (Nat.div i 64) s 0) (Z.of_nat (Nat.modulo i 64)).

Section DoubleAdd.
  Context {G : Type} (add : G -> G -> G) (dbl : G -> G).

  (** [n] more iterations from accumulator [acc]: iteration [n - 1]
      doubles and then adds [p] if bit [n - 1] is set. *)
  Fixpoint dadd_from (s : list Z) (p : G) (n : nat) (acc : G) : G :=
    match n with
    | O => acc
    | S n' =>
        let a := dbl acc in
        dadd_from s p n' (if scalar_bit s n' then add a p else a)
    end.

  Definition smul_prog (id : G) (s : list Z) (p : G) : G :=
    dadd_from s p 256 id.

  Lemma smul_prog_eq id s p : smul_prog id s p = dadd_from s p 256 id.
  Proof. reflexivity. Qed.
End DoubleAdd.

(** The integer formed by the low [n] bits the program reads. *)
Fixpoint low_bits (s : list Z) (n : nat) : nat :=
  match n with
  | O => O
  | S n' => ((if scalar_bit s n' then 2 ^ n' else 0) + low_bits s n')%nat
  end.

(* ================================================================== *)
(** ** 2. Correctness in a commutative monoid up to an equivalence      *)
(* ================================================================== *)

Section DaddMonoid.
  Context {G : Type} (eqv : G -> G -> Prop) {eqv_Equivalence : Equivalence eqv}.
  Context (id : G) (add : G -> G -> G) (dbl : G -> G).
  Context {add_Proper : Proper (eqv ==> eqv ==> eqv) add}.
  Context (add_assoc : forall a b c, eqv (add (add a b) c) (add a (add b c)))
          (add_comm : forall a b, eqv (add a b) (add b a))
          (add_id_l : forall a, eqv (add id a) a)
          (dbl_add : forall a, eqv (dbl a) (add a a)).

  Local Infix "==" := eqv (at level 70).
  Local Notation smul := (smul id add).

  Lemma dbl_Proper : Proper (eqv ==> eqv) dbl.
  Proof. intros x y Hxy. rewrite !dbl_add, Hxy. reflexivity. Qed.

  Lemma smul_Proper' n : Proper (eqv ==> eqv) (smul n).
  Proof.
    intros x y Hxy. induction n as [|n IH]; cbn [BLS12_MSM_Functional.smul];
      [reflexivity|]. apply add_Proper; assumption.
  Qed.

  Lemma smul_add' a b x : smul (a + b) x == add (smul a x) (smul b x).
  Proof. exact (smul_add eqv id add add_assoc add_id_l a b x). Qed.

  Lemma dadd_from_Proper s p n : Proper (eqv ==> eqv) (dadd_from add dbl s p n).
  Proof.
    induction n as [|n IH]; intros x y Hxy; cbn [dadd_from]; [exact Hxy|].
    apply IH. pose proof (dbl_Proper x y Hxy) as Hd.
    destruct (scalar_bit s n); [apply add_Proper; [exact Hd | reflexivity] | exact Hd].
  Qed.

  Lemma dadd_from_smul s p n a :
    dadd_from add dbl s p n (smul a p) == smul (2 ^ n * a + low_bits s n) p.
  Proof.
    revert a. induction n as [|n IH]; intros a.
    - cbn [dadd_from low_bits]. rewrite Nat.pow_0_r, Nat.mul_1_l, Nat.add_0_r. reflexivity.
    - cbn [dadd_from low_bits].
      assert (Hd : dbl (smul a p) == smul (a + a) p).
      { rewrite dbl_add, smul_add'. reflexivity. }
      destruct (scalar_bit s n).
      + assert (Hs : add (dbl (smul a p)) p == smul (S (a + a)) p).
        { rewrite Hd. cbn [BLS12_MSM_Functional.smul]. apply add_comm. }
        rewrite (dadd_from_Proper s p n _ _ Hs), IH.
        assert (E : (2 ^ n * S (a + a) + low_bits s n
                     = 2 ^ S n * a + (2 ^ n + low_bits s n))%nat)
          by (rewrite Nat.pow_succ_r'; nia).
        rewrite E. reflexivity.
      + rewrite (dadd_from_Proper s p n _ _ Hd), IH.
        assert (E : (2 ^ n * (a + a) + low_bits s n
                     = 2 ^ S n * a + (0 + low_bits s n))%nat)
          by (rewrite Nat.pow_succ_r'; nia).
        rewrite E. reflexivity.
  Qed.
End DaddMonoid.

(* ================================================================== *)
(** ** 3. The bits of four 64-bit limbs                                 *)
(* ================================================================== *)

Lemma testbit_split (a b k : Z) :
  0 <= a < 2 ^ 64 -> 0 <= k ->
  Z.testbit (a + 2 ^ 64 * b) k
  = if k <? 64 then Z.testbit a k else Z.testbit b (k - 64).
Proof.
  intros Ha Hk. destruct (Z.ltb_spec k 64) as [Hlt|Hge].
  - rewrite <- (Z.mod_pow2_bits_low (a + 2 ^ 64 * b) 64 k) by lia.
    rewrite (Z.mul_comm (2 ^ 64) b), Z.mod_add by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - replace k with ((k - 64) + 64) at 1 by lia.
    rewrite <- Z.div_pow2_bits by lia.
    rewrite (Z.mul_comm (2 ^ 64) b), Z.div_add by lia.
    rewrite Z.div_small by lia. reflexivity.
Qed.

Section LimbBits.
  Context (l0 l1 l2 l3 : Z).
  Context (H0 : 0 <= l0 < 2 ^ 64) (H1 : 0 <= l1 < 2 ^ 64)
          (H2 : 0 <= l2 < 2 ^ 64) (H3 : 0 <= l3 < 2 ^ 64).

  Lemma scalar_bit_limbs (n : nat) :
    (n < 256)%nat ->
    scalar_bit [l0; l1; l2; l3] n = Z.testbit (limbsZ l0 l1 l2 l3) (Z.of_nat n).
  Proof.
    intros Hn. unfold scalar_bit, limbsZ.
    pose proof (Nat.div_mod n 64 ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as Hr.
    set (q := Nat.div n 64) in *. set (r := Nat.modulo n 64) in *.
    assert (Hq : (q < 4)%nat) by lia.
    rewrite (testbit_split l0) by lia.
    destruct (Z.ltb_spec (Z.of_nat n) 64).
    { assert (q = 0%nat) as -> by lia. cbn [nth]. f_equal. lia. }
    rewrite (testbit_split l1) by lia.
    destruct (Z.ltb_spec (Z.of_nat n - 64) 64).
    { assert (q = 1%nat) as -> by lia. cbn [nth]. f_equal. lia. }
    rewrite (testbit_split l2) by lia.
    destruct (Z.ltb_spec (Z.of_nat n - 64 - 64) 64).
    { assert (q = 2%nat) as -> by lia. cbn [nth]. f_equal. lia. }
    assert (q = 3%nat) as -> by lia. cbn [nth]. f_equal. lia.
  Qed.

  Lemma low_bits_mod (n : nat) :
    (n <= 256)%nat ->
    Z.of_nat (low_bits [l0; l1; l2; l3] n)
    = limbsZ l0 l1 l2 l3 mod 2 ^ Z.of_nat n.
  Proof.
    induction n as [|n IH]; intros Hn.
    - cbn [low_bits]. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
    - cbn [low_bits]. rewrite Nat2Z.inj_add, IH by lia.
      rewrite scalar_bit_limbs by lia.
      replace (2 ^ Z.of_nat (S n)) with (2 ^ Z.of_nat n * 2)
        by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
      rewrite mod_mul_r_pos by (try apply Z.pow_pos_nonneg; lia).
      rewrite <- Z.testbit_spec' by lia.
      destruct (Z.testbit (limbsZ l0 l1 l2 l3) (Z.of_nat n)); cbn [Z.b2z].
      + rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2. lia.
      + lia.
  Qed.

  (** The program reads exactly the 256-bit integer of the limbs. *)
  Theorem bits_limbs :
    low_bits [l0; l1; l2; l3] 256 = Z.to_nat (limbsZ l0 l1 l2 l3).
  Proof.
    apply Nat2Z.inj. rewrite low_bits_mod by lia.
    pose proof (limbsZ_bounds l0 l1 l2 l3 H0 H1 H2 H3) as HS.
    rewrite Z2Nat.id by lia.
    apply Z.mod_small. exact HS.
  Qed.
End LimbBits.

(* ================================================================== *)
(** ** 3b. The complete a = 0 RCB formulas, up to [pt_eq]               *)
(* ================================================================== *)

Section DaddTransfer.
  Context {A B : Type} (addA : A -> A -> A) (dblA : A -> A)
          (addB : B -> B -> B) (dblB : B -> B) (f : A -> B).
  Context (f_add : forall x y, f (addA x y) = addB (f x) (f y))
          (f_dbl : forall x, f (dblA x) = dblB (f x)).

  Lemma f_dadd_from s p n acc :
    f (dadd_from addA dblA s p n acc) = dadd_from addB dblB s (f p) n (f acc).
  Proof.
    revert acc. induction n as [|n IH]; intros acc; [reflexivity|].
    cbn [dadd_from]. rewrite IH. f_equal.
    destruct (scalar_bit s n); rewrite ?f_add, f_dbl; reflexivity.
  Qed.
End DaddTransfer.

Section RcbDadd.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).
  Local Open Scope F_scope.
  Context (M_gt_27 : (27 < M_pos)%positive).
  Context (b three_b : F).
  Context (Hthree_b : three_b = b + b + b).
  Context (Hdisc : id
    ((((1 + 1 + 1 + 1) * 0 * 0 * 0
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)%F)).
  Context (Hno2 : no_two_torsion 0 b).

  Local Notation oncurve := (RcbProjectiveLaws.oncurve 0 b).
  Local Notation add_raw := (ladderstep_triple three_b).
  Local Notation dbl_raw := (rcb_double_a0_triple three_b).
  Local Notation Gs := (@Gs _ b).
  Local Notation adds := (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation dbls := (@dbls _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation ids := (@ids _ field_parameters_ok M_gt_27 b three_b Hthree_b).
  Local Notation eqs := (@eqs _ b).

  Lemma dadd_from_rcb_correct (n : nat) (s : list Z) (P : F * F * F) :
    oncurve P ->
    pt_eq (dadd_from add_raw dbl_raw s P n id_pt)
          (smul id_pt add_raw (low_bits s n) P).
  Proof.
    intros HP.
    pose proof (@eqs_Equivalence _ field_parameters_ok M_gt_27 b three_b Hthree_b) as E.
    pose proof (@adds_Proper _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2) as AP.
    pose proof (dadd_from_smul eqs ids adds dbls
                  (@adds_assoc _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
                  (@adds_comm _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
                  (@adds_id_l _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
                  (@dbls_add _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
                  s (exist oncurve P HP) n 0) as H.
    rewrite Nat.mul_0_r, Nat.add_0_l in H.
    unfold eqs in H.
    rewrite (f_dadd_from adds dbls add_raw dbl_raw (@proj1_sig _ _)
               (fun _ _ => eq_refl) (fun _ => eq_refl)) in H.
    rewrite (f_smul ids adds id_pt add_raw (@proj1_sig _ _)
               eq_refl (fun _ _ => eq_refl) (low_bits s n)) in H.
    cbn [proj1_sig smul] in H.
    exact H.
  Qed.

  (** Double-and-add over the RCB formulas, on an on-curve point, is
      [pt_eq] to [k P] (repeated RCB addition from (0 : 1 : 0)), where
      [k] is the integer formed by the 256 bits read. *)
  Theorem smul_prog_rcb_correct (s : list Z) (P : F * F * F) :
    oncurve P ->
    pt_eq (smul_prog add_raw dbl_raw id_pt s P)
          (smul id_pt add_raw (low_bits s 256) P).
  Proof.
    intros HP. rewrite smul_prog_eq. exact (dadd_from_rcb_correct 256 s P HP).
  Qed.
End RcbDadd.

(* ================================================================== *)
(** ** 4. The bedrock2 program                                          *)
(* ================================================================== *)

Local Open Scope string_scope.

Section Program.
  Context (curve_add_name curve_double_name store_zero_name : string).

  (** Loop body: [i := i - 1; out := 2 out;
      a := scalar + ((i >> 6) << 3); bit := (load(a) >> (i & 63)) & 1;
      if bit { out := out + P }]. *)
  Definition g1_scalar_mul_loop_body : Syntax.cmd :=
    cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
    (cmd.seq (cmd.call [] curve_double_name
                [expr.var "outx"; expr.var "outy"; expr.var "outz";
                 expr.var "outx"; expr.var "outy"; expr.var "outz"])
    (cmd.seq (cmd.set "a"
                (expr.op bopname.add (expr.var "scalar")
                   (expr.op bopname.slu
                      (expr.op bopname.sru (expr.var "i") (expr.literal 6))
                      (expr.literal 3))))
    (cmd.seq (cmd.set "bit"
                (expr.op bopname.and
                   (expr.op bopname.sru
                      (expr.load access_size.word (expr.var "a"))
                      (expr.op bopname.and (expr.var "i") (expr.literal 63)))
                   (expr.literal 1)))
       (cmd.cond (expr.var "bit")
          (cmd.call [] curve_add_name
             [expr.var "outx"; expr.var "px";
              expr.var "outy"; expr.var "py";
              expr.var "outz"; expr.var "pz";
              expr.var "outx"; expr.var "outy"; expr.var "outz"])
          cmd.skip)))).

  Definition g1_scalar_mul_body : Syntax.cmd :=
    cmd.seq (cmd.call [] store_zero_name
               [expr.var "outx"; expr.var "outy"; expr.var "outz"])
    (cmd.seq (cmd.set "i" (expr.literal 256))
       (cmd.while (expr.var "i") g1_scalar_mul_loop_body)).

  Definition g1_scalar_mul
    : string * (list string * list string * Syntax.cmd) :=
    ("g1_scalar_mul",
     (["outx"; "outy"; "outz"; "scalar"; "px"; "py"; "pz"], [],
      g1_scalar_mul_body)).
End Program.

(* ================================================================== *)
(** ** 5. The program computes [smul_prog] on raw triples               *)
(* ================================================================== *)

Section Proof.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok (field_representation:=field_representation)}.
  Context (Hwidth64 : width = 64).
  Context (curve_add_name curve_double_name store_zero_name : String.string).

  Local Notation F := (F M_pos).
  Local Notation G1_F := (F * F * F)%type.
  Local Notation FElemT := (FElem (Some tight_bounds)).

  Context (g1_add_spec : G1_F -> G1_F -> G1_F)
          (g1_double_spec : G1_F -> G1_F)
          (g1_identity : G1_F).

  Definition smul_target (s : list word) (P : G1_F) : G1_F :=
    smul_prog g1_add_spec g1_double_spec g1_identity (List.map word.unsigned s) P.

  Ltac solve_get :=
    repeat (rewrite map.get_put_diff by congruence);
    first [ rewrite map.get_put_same; reflexivity | eassumption ].

  Ltac peel :=
    cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
    fold WeakestPrecondition.cmd.

  Ltac eval_dexprs :=
    cbv [WeakestPrecondition.dexprs WeakestPrecondition.dexpr list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.literal WeakestPrecondition.get dlet.dlet];
    repeat (eexists; split; [solve_get|]);
    try reflexivity.

  Lemma unsigned_small (v : Z) :
    0 <= v < 2 ^ 64 -> word.unsigned (word.of_Z v : word) = v.
  Proof. intros. apply word.unsigned_of_Z_nowrap. rewrite Hwidth64. lia. Qed.

  Lemma word_i_and_63 (v : Z) :
    0 <= v < 256 ->
    word.unsigned (word.and (word.of_Z v) (word.of_Z 63) : word) = v mod 64.
  Proof.
    intros Hv. rewrite word.unsigned_and_nowrap, !unsigned_small by lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma word_limb_addr (sp : word) (v : Z) :
    0 <= v < 256 ->
    word.add sp (word.slu (word.sru (word.of_Z v) (word.of_Z 6)) (word.of_Z 3))
    = word.add sp (word.of_Z (Z.of_nat 0 * 32 + Z.of_nat (Z.to_nat (v / 64)) * 8)).
  Proof.
    intros Hv. f_equal. apply word.unsigned_inj.
    assert (Hq : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite word.unsigned_slu by (rewrite unsigned_small, Hwidth64 by lia; lia).
    rewrite word.unsigned_sru_nowrap by (rewrite unsigned_small, Hwidth64 by lia; lia).
    rewrite !unsigned_small by lia.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    rewrite ?Z2Nat.id by lia.
    unfold word.wrap. rewrite Hwidth64. rewrite Z.mod_small by lia.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
  Qed.

  Lemma word_bit (x : word) (k : word) :
    0 <= word.unsigned k < 64 ->
    word.unsigned (word.and (word.sru x k) (word.of_Z 1) : word)
    = Z.b2z (Z.testbit (word.unsigned x) (word.unsigned k)).
  Proof.
    intros Hk. rewrite word.unsigned_and_nowrap.
    rewrite word.unsigned_sru_nowrap by (rewrite Hwidth64; lia).
    rewrite unsigned_small by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    rewrite Z.testbit_spec' by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma word_sub_1 (v : nat) :
    (0 < v <= 256)%nat ->
    word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) = (word.of_Z (Z.of_nat (v - 1)) : word).
  Proof.
    intros Hv. apply word.unsigned_inj.
    rewrite word.unsigned_sub, !unsigned_small by lia.
    unfold word.wrap. rewrite Hwidth64. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma word_of_nat_zero (v : nat) :
    (v <= 256)%nat -> word.unsigned (word.of_Z (Z.of_nat v) : word) = Z.of_nat v.
  Proof. intros. apply unsigned_small. lia. Qed.

  Lemma scalar_bit_word (s : list word) (v : nat) :
    (v < 256)%nat ->
    scalar_bit (List.map word.unsigned s) v
    = Z.testbit (word.unsigned (nth (Z.to_nat (Z.of_nat v / 64)) s (word.of_Z 0)))
                (Z.of_nat v mod 64).
  Proof.
    intros Hv. unfold scalar_bit.
    replace (Z.to_nat (Z.of_nat v / 64)) with (Nat.div v 64)
      by (rewrite <- (Nat2Z.id (Nat.div v 64)), Nat2Z.inj_div; reflexivity).
    replace (Z.of_nat v mod 64) with (Z.of_nat (Nat.modulo v 64))
      by (rewrite Nat2Z.inj_mod; reflexivity).
    f_equal.
    replace 0 with (word.unsigned (word.of_Z 0 : word)) at 1
      by apply word.unsigned_of_Z_0.
    apply map_nth.
  Qed.

  Definition loop_inv (functions : Semantics.env) (tr : Semantics.trace)
      (outx outy outz sp px py pz : word) (s : list word) (X Y Z : F)
      (R : mem -> Prop) (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 256)%nat /\
    map.get l "outx" = Some outx /\ map.get l "outy" = Some outy /\
    map.get l "outz" = Some outz /\ map.get l "scalar" = Some sp /\
    map.get l "px" = Some px /\ map.get l "py" = Some py /\
    map.get l "pz" = Some pz /\
    map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
    exists ax ay az,
      dadd_from g1_add_spec g1_double_spec (List.map word.unsigned s) (X, Y, Z) v (ax, ay, az)
      = smul_target s (X, Y, Z) /\
      (FElemT outx ax * FElemT outy ay * FElemT outz az
       * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m.

  Lemma g1_scalar_mul_body_wp functions
      (HA : CurveAddAliasedOK curve_add_name g1_add_spec functions)
      (HD : CurveDoubleInplaceOK curve_double_name g1_double_spec functions)
      (HZ : StoreZero3OK store_zero_name g1_identity functions)
      (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : F)
      (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals) :
    length s = 4%nat ->
    (FElem None outx ox0 * FElem None outy oy0 * FElem None outz oz0
     * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
    map.get l "outx" = Some outx -> map.get l "outy" = Some outy ->
    map.get l "outz" = Some outz -> map.get l "scalar" = Some sp ->
    map.get l "px" = Some px -> map.get l "py" = Some py -> map.get l "pz" = Some pz ->
    WeakestPrecondition.cmd functions
      (g1_scalar_mul_body curve_add_name curve_double_name store_zero_name) tr m l
      (fun tr' m' l' =>
         tr' = tr /\
         exists ox oy oz,
           (ox, oy, oz) = smul_target s (X, Y, Z) /\
           (FElemT outx ox * FElemT outy oy * FElemT outz oz
            * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').
  Proof.
    intros Hlen Hm Hox Hoy Hoz Hsp Hpx Hpy Hpz.
    cbv [g1_scalar_mul_body].
    (* store_zero(out) *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (HZ outx outy outz ox0 oy0 oz0
                (ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep tr m).
      ecancel_assumption. }
    cbv beta. intros tr1 m1 rets (-> & <- & Hm1).
    eexists; split; [reflexivity|].
    (* i := 256 *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    cbv [dlet.dlet].
    (* the loop *)
    eapply (Loops.while_localsmap (measure := nat)
              (loop_inv functions tr outx outy outz sp px py pz s X Y Z R)
              Wf_nat.lt_wf 256%nat).
    { (* entry *)
      cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
      do 8 (split; [solve_get|]).
      case_eq g1_identity. intros [ix iy] iz Hid. rewrite Hid in Hm1.
      exists ix, iy, iz. split.
      - unfold smul_target, smul_prog. rewrite Hid. reflexivity.
      - ecancel_assumption. }
    intros v t mv lv Hinv.
    destruct Hinv as (-> & Hv & Hlx & Hly & Hlz & Hls & Hlpx & Hlpy & Hlpz & Hli
                      & ax & ay & az & Hacc & Hmv).
    exists (word.of_Z (Z.of_nat v)). split.
    { eval_dexprs. }
    split.
    - (* loop body *)
      intros Hne.
      assert (Hv0 : (0 < v)%nat).
      { destruct v; [|lia]. exfalso. apply Hne. apply word.unsigned_of_Z_0. }
      set (v' := (v - 1)%nat).
      cbv [g1_scalar_mul_loop_body].
      (* i := i - 1 *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      cbv [Semantics.interp_binop].
      rewrite word_sub_1 by lia. fold v'.
      (* out := double(out) *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (HD outx outy outz ax ay az
                  (ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep tr mv).
        ecancel_assumption. }
      cbv beta. intros t2 m2 rets (-> & <- & Hm2).
      case_eq (g1_double_spec (ax, ay, az)). intros [dx dy] dz Hd. rewrite Hd in Hm2.
      eexists; split; [reflexivity|].
      (* a := scalar + ((i >> 6) << 3) *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      (* bit := (load(a) >> (i & 63)) & 1 *)
      assert (Hv'256 : (v' < 256)%nat) by lia.
      set (limb := Z.to_nat (Z.of_nat v' / 64)).
      assert (Hlimb : (limb < 4)%nat).
      { unfold limb. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        apply Z.div_lt_upper_bound; lia. }
      pose proof (ScalarsArray_load_limb Hwidth64 g1_add_spec g1_double_spec g1_identity sp [s] 0 limb
                    (FElemT outx dx * FElemT outy dy * FElemT outz dz
                     * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m2
                    ltac:(cbn; lia) Hlimb) as Hload.
      cbn [nth] in Hload.
      peel. peel.
      eexists; split.
      { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
             WeakestPrecondition.expr_body WeakestPrecondition.literal
             WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
        eexists; split; [solve_get|].
        eexists; split.
        { cbv [Semantics.interp_binop].
          rewrite word_limb_addr by lia. apply Hload. ecancel_assumption. }
        eexists; split; [solve_get|].
        reflexivity. }
      cbv [dlet.dlet Semantics.interp_binop].
      set (bitw := word.and
                     (word.sru (nth limb s (word.of_Z 0))
                        (word.and (word.of_Z (Z.of_nat v')) (word.of_Z 63)))
                     (word.of_Z 1) : word).
      assert (Hbit : word.unsigned bitw
                     = Z.b2z (scalar_bit (List.map word.unsigned s) v')).
      { unfold bitw. rewrite word_bit by (rewrite word_i_and_63 by lia;
                                         pose proof (Z.mod_pos_bound (Z.of_nat v') 64); lia).
        rewrite word_i_and_63 by lia. rewrite scalar_bit_word by lia. reflexivity. }
      (* if bit { out := out + P } *)
      peel.
      eexists; split; [eval_dexprs|].
      cbn [dadd_from] in Hacc.
      replace v with (S v') in Hacc by lia.
      cbn [dadd_from] in Hacc. rewrite Hd in Hacc.
      split.
      + intros Hb.
        assert (Hsb : scalar_bit (List.map word.unsigned s) v' = true).
        { destruct (scalar_bit (List.map word.unsigned s) v'); [reflexivity|].
          rewrite Hbit in Hb. cbn in Hb. congruence. }
        rewrite Hsb in Hacc.
        peel.
        eexists; split; [eval_dexprs|].
        eapply Semantics.weaken_call.
        { eapply (HA outx px outy py outz pz dx X dy Y dz Z
                    (ScalarsArray sp [s] * R)%sep tr m2).
          ecancel_assumption. }
        cbv beta. intros t3 m3 rets (-> & <- & Hm3).
        case_eq (g1_add_spec (dx, dy, dz) (X, Y, Z)). intros [sx sy] sz Hs.
        rewrite Hs in Hm3, Hacc.
        eexists; split; [reflexivity|].
        exists v'. split; [|lia].
        cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
        do 8 (split; [solve_get|]).
        exists sx, sy, sz. split; [exact Hacc|]. ecancel_assumption.
      + intros Hb.
        assert (Hsb : scalar_bit (List.map word.unsigned s) v' = false).
        { destruct (scalar_bit (List.map word.unsigned s) v'); [|reflexivity].
          rewrite Hbit in Hb. cbn in Hb. congruence. }
        rewrite Hsb in Hacc.
        peel.
        exists v'. split; [|lia].
        cbv [loop_inv]. split; [reflexivity|]. split; [lia|].
        do 8 (split; [solve_get|]).
        exists dx, dy, dz. split; [exact Hacc|]. ecancel_assumption.
    - (* exit *)
      intros Hz.
      rewrite word_of_nat_zero in Hz by exact Hv.
      assert (v = 0%nat) as -> by lia.
      cbn [dadd_from] in Hacc.
      split; [reflexivity|].
      exists ax, ay, az. split; [exact Hacc|exact Hmv].
  Qed.

  Definition spec_of_g1_scalar_mul (functions : Semantics.env) : Prop :=
    forall (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : F)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      (FElem None outx ox0 * FElem None outy oy0 * FElem None outz oz0
       * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g1_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz,
             (ox, oy, oz) = smul_target s (X, Y, Z) /\
             (FElemT outx ox * FElemT outy oy * FElemT outz oz
              * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').

  Theorem g1_scalar_mul_ok functions :
    map.get functions "g1_scalar_mul"
      = Some (snd (g1_scalar_mul curve_add_name curve_double_name store_zero_name)) ->
    CurveAddAliasedOK curve_add_name g1_add_spec functions ->
    CurveDoubleInplaceOK curve_double_name g1_double_spec functions ->
    StoreZero3OK store_zero_name g1_identity functions ->
    spec_of_g1_scalar_mul functions.
  Proof.
    intros Henv HA HD HZ outx outy outz sp px py pz ox0 oy0 oz0 X Y Z s R tr m Hlen Hm.
    unfold Semantics.call.
    do 3 eexists. split; [exact Henv|].
    destruct (map.of_list_zip ["outx"; "outy"; "outz"; "scalar"; "px"; "py"; "pz"]
                [outx; outy; outz; sp; px; py; pz]) as [l0|] eqn:Hzip.
    2: { exfalso. cbn in Hzip. discriminate Hzip. }
    exists l0. split; [reflexivity|].
    cbn in Hzip. injection Hzip as <-.
    eapply Semantics.exec.weaken.
    { eapply WeakestPreconditionProperties.sound_cmd.
      eapply (g1_scalar_mul_body_wp functions HA HD HZ outx outy outz sp px py pz
                ox0 oy0 oz0 X Y Z s R tr m); try exact Hlen; try exact Hm;
        repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same. }
    intros tr' m' l' (-> & ox & oy & oz & Hres & Hm').
    exists []. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    exists ox, oy, oz. split; [exact Hres|exact Hm'].
  Qed.
End Proof.
