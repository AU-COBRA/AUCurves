(** Bignum-style bedrock2 spec for the P-384 RCB G1 point addition.

    This file defines the bedrock2 function [P384_G1_add] and its
    WP specification [spec_of_P384_G1_add] using AUCurves' Bignum /
    [valid] / [eval ∘ from_mont] conventions. The function body
    implements the RCB complete addition formula (Algorithm 1 of
    Renes-Costello-Batina 2015) for the general a≠0 case, since P-384
    has a = -3 (mod p).

    Port of [P256_G1_Add_Spec.v]: 6 limbs of 64 bits instead of 4
    (48-byte field elements, 6 store instructions per stack constant
    at offsets 0,8,16,24,32,40), same 40-field-op function body and
    the same WP proof structure. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Array.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Bedrock.Field.Common.Tactics.

Require Import Bedrock.Curve.P384Curve_G1.
Require Import Bedrock.Curve.P384_Wired_Specs.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.

Require Import coqutil.Map.Properties.
Require Import bedrock2.Lift1Prop.
Require Import Bedrock.Util.Word.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.SeparationLogic.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section P384_G1_Add.

  (* O(n) sep frame inference instead of O(n!) permutation search.
     Inlined from BLS12_GLV_ScalarMultBedrock.v / WPTactics.v *)
  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.

  Local Ltac ecancel_assumption ::=
    first [ecancel_assumption_fast | SeparationLogic.ecancel_assumption].

  (* P-384 prime: p = 2^384 - 2^128 - 2^96 + 2^32 - 1 *)
  Local Notation m := (2^384 - 2^128 - 2^96 + 2^32 - 1)%Z.
  Local Notation n := 6%nat.
  Local Notation bw := 64.
  Local Notation prefix := "p384_coord_".
  (* a = (-3) mod m  — note: [a] is shadowed by stackalloc pointer inside proofs,
     so use the explicit expression when needed *)
  Local Notation a_val := ((-3) mod m)%Z.
  Local Notation b_val :=
    (0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef mod m)%Z.
  Local Notation three_b := (3 * b_val mod m)%Z.

  Local Notation num_bytes := 48%Z (only parsing).
  Local Definition num_bytes_def : Z := 48%Z.

  (* m' = modinv(-m, 2^bw) — the Montgomery reduction constant.
     For P-384: m ≡ 2^32 - 1 mod 2^64, and modinv(-(2^32-1), 2^64) = 2^32 + 1.
     Use the same concrete value as P384Curve_G1.m' to ensure definitional
     compatibility with P384_add_Gallina_spec. *)
  Local Notation m' := (4294967297%Z).

  (* r' = modinv(2^64, m) satisfying (2^64 * r') mod m = 1. *)
  Local Notation r' :=
    (9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209%Z).

  (* Montgomery-encoded 3b constant for P-384.
     Concrete value equals P384Curve_G1.p384_three_b_mont (same m'/three_b).
     Defined as an alias so that [Eval cbv] in the function body can reduce it. *)
  Definition P384_three_b_mont : list Z := P384Curve_G1.p384_three_b_mont.

  (* Montgomery-encoded a constant for P-384 (a = -3 mod m). *)
  Definition P384_a_mont : list Z := P384Curve_G1.p384_a_mont_list.

  (** ** Bedrock2 function definition

      The RCB complete addition formula for general a≠0.
      This has 40 field operations (vs 30 for a=0) due to the
      three extra multiplications and four extra add/sub involving a_const. *)

  Definition P384_G1_add : Syntax.func := Eval cbv in (
    let outx := "outx" in
    let outy := "outy" in
    let outz := "outz" in
    let X1 := "X1" in
    let Y1 := "Y1" in
    let Z1 := "Z1" in
    let X2 := "X2" in
    let Y2 := "Y2" in
    let Z2 := "Z2" in
    let t0 := "t0" in
    let t1 := "t1" in
    let t2 := "t2" in
    let t3 := "t3" in
    let t4 := "t4" in
    let t5 := "t5" in
    let three_b := "three_b" in
    let a_const := "a_const" in
    let add := (append prefix "add") in
    let mul := (append prefix "mul") in
    let sub := (append prefix "sub") in
    (
      [outx; outy; outz; X1; Y1; Z1; X2; Y2; Z2], [],
      bedrock_func_body:(
      stackalloc num_bytes as three_b;
      stackalloc num_bytes as a_const;
      stackalloc num_bytes as t0;
      stackalloc num_bytes as t1;
      stackalloc num_bytes as t2;
      stackalloc num_bytes as t3;
      stackalloc num_bytes as t4;
      stackalloc num_bytes as t5;
      (* Store Montgomery-encoded 3b constant (6 limbs) *)
      store(three_b, (coq:(nth 0 P384_three_b_mont 0)));
      store(three_b + coq:(8), coq:(nth 1 P384_three_b_mont 0));
      store(three_b + coq:(16), coq:(nth 2 P384_three_b_mont 0));
      store(three_b + coq:(24), coq:(nth 3 P384_three_b_mont 0));
      store(three_b + coq:(32), coq:(nth 4 P384_three_b_mont 0));
      store(three_b + coq:(40), coq:(nth 5 P384_three_b_mont 0));
      (* Store Montgomery-encoded a = -3 constant (6 limbs) *)
      store(a_const, (coq:(nth 0 P384_a_mont 0)));
      store(a_const + coq:(8), coq:(nth 1 P384_a_mont 0));
      store(a_const + coq:(16), coq:(nth 2 P384_a_mont 0));
      store(a_const + coq:(24), coq:(nth 3 P384_a_mont 0));
      store(a_const + coq:(32), coq:(nth 4 P384_a_mont 0));
      store(a_const + coq:(40), coq:(nth 5 P384_a_mont 0));
      (* RCB complete addition formula, general a≠0 case *)
      (* Steps 1-18: same as a=0 case *)
      $mul (t0, X1, X2);
      $mul (t1, Y1, Y2);
      $mul (t2, Z1, Z2);
      $add (t3, X1, Y1);
      $add (t4, X2, Y2);
      $mul (t3, t3, t4);
      $add (t4, t0, t1);
      $sub (t3, t3, t4);
      $add (t4, X1, Z1);
      $add (t5, X2, Z2);
      $mul (t4, t4, t5);
      $add (t5, t0, t2);
      $sub (t4, t4, t5);
      $add (t5, Y1, Z1);
      $add (outx, Y2, Z2);
      $mul (t5, t5, outx);
      $add (outx, t1, t2);
      $sub (t5, t5, outx);
      (* Step 19: Z3 := a_mont * t4 *)
      $mul (outz, a_const, t4);
      (* Step 20: X3_tmp := three_b_mont * t2 *)
      $mul (outx, three_b, t2);
      (* Step 21: Z3 := X3_tmp + Z3 *)
      $add (outz, outx, outz);
      (* Steps 22-24: X3, Z3, Y3 *)
      $sub (outx, t1, outz);
      $add (outz, outz, t1);
      $mul (outy, outx, outz);
      (* Steps 25-26: t1 := 3*t0 *)
      $add (t1, t0, t0);
      $add (t1, t1, t0);
      (* Step 27: t2 := a_mont * t2 *)
      $mul (t2, a_const, t2);
      (* Step 28: t4 := three_b_mont * t4 *)
      $mul (t4, three_b, t4);
      (* Step 29: t1 := t1 + t2 *)
      $add (t1, t1, t2);
      (* Step 30: t2 := t0 - t2 *)
      $sub (t2, t0, t2);
      (* Step 31: t2 := a_mont * t2 *)
      $mul (t2, a_const, t2);
      (* Step 32: t4 := t4 + t2 *)
      $add (t4, t4, t2);
      (* Steps 33-40: final accumulation *)
      $mul (t0, t1, t4);
      $add (outy, outy, t0);
      $mul (t0, t5, t4);
      $mul (outx, t3, outx);
      $sub (outx, outx, t0);
      $mul (t0, t3, t1);
      $mul (outz, t5, outz);
      $add (outz, outz, t0)
      )
    )).

  (** ** Bignum-style WP spec *)

  Local Notation valid := (WordByWordMontgomery.valid bw n m).
  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation from_mont :=
    (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation evfrom x := (eval (from_mont x)).
  Local Notation toZ x := (List.map Interface.word.unsigned x).

  Instance spec_of_P384_G1_add :
    spec_of "P384_G1_add" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2 : list Interface.word.rep)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : Interface.word.rep)
             (wold_outx wold_outy wold_outz : list Interface.word.rep)
             (t : Semantics.trace) (m0 : Interface.map.rep)
             (Rout : Interface.map.rep -> Prop),
      valid (toZ wX1) /\ valid (toZ wY1) /\ valid (toZ wZ1) /\
      valid (toZ wX2) /\ valid (toZ wY2) /\ valid (toZ wZ2) ->
      ((Bignum n pX1 wX1) * (Bignum n pX2 wX2) *
       (Bignum n pY1 wY1) * (Bignum n pY2 wY2) *
       (Bignum n pZ1 wZ1) * (Bignum n pZ2 wZ2) *
       (Bignum n poutx wold_outx) *
       (Bignum n pouty wold_outy) *
       (Bignum n poutz wold_outz) * Rout)%sep m0 ->
      WeakestPrecondition.call functions "P384_G1_add" t m0
        [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
        (fun t' m' rets =>
           t = t' /\ rets = nil /\
           exists (woutx wouty woutz : list Interface.word.rep) Rout,
             (P384_add_Gallina_spec (toZ wX1) (toZ wY1)
                (toZ wZ1) (toZ wX2) (toZ wY2) (toZ wZ2)
                (toZ woutx) (toZ wouty) (toZ woutz) /\
              valid (toZ woutx) /\ valid (toZ wouty) /\ valid (toZ woutz)) /\
             ((Bignum n pX1 wX1) * (Bignum n pX2 wX2) *
              (Bignum n pY1 wY1) * (Bignum n pY2 wY2) *
              (Bignum n pZ1 wZ1) * (Bignum n pZ2 wZ2) *
              (Bignum n poutx woutx) * (Bignum n pouty wouty) *
              (Bignum n poutz woutz) * Rout)%sep m').

  (** ** Montgomery ring infrastructure *)

  (* Montgomery parameters *)
  Local Notation r := (2 ^ bw).
  Local Notation uw := (uweight bw).
  Local Notation word_size_in_bytes := (Memory.bytes_per_word 64).

  (* Correctness lemmas for Montgomery parameters *)
  Local Lemma a_small : a_val = a_val mod m.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma three_b_small : three_b = three_b mod m.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma r'_correct : (2 ^ bw * r') mod m = 1.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma m'_correct : (m * m') mod 2 ^ bw = -1 mod 2 ^ bw.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma bw_big : 0 < bw.
  Proof. cbv; auto. Qed.

  Local Lemma m_big : 1 < m.
  Proof. cbv; auto. Qed.

  Local Lemma n_nz : n <> 0%nat.
  Proof. cbv; discriminate. Qed.

  Local Lemma m_small : m < (2 ^ bw) ^ Z.of_nat n.
  Proof. cbv; auto. Qed.

  Local Lemma n_small : Z.of_nat n < 2 ^ bw.
  Proof. cbv. auto. Qed.

  Ltac wbw_conds :=
    repeat first [ progress apply r'_correct
                 | progress apply m'_correct
                 | progress apply bw_big
                 | progress apply m_big
                 | progress apply n_nz
                 | progress apply m_small ].

  Local Notation from_mont_correct :=
    (@from_mont_correct m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation valid_mod :=
    (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation mont_add :=
    (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_sub :=
    (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_mul :=
    (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation valid_valid'_equiv :=
    (valid_valid'_equiv m bw n n_nz m_big).
  Local Notation evfrom_mod :=
    (evfrom_mod' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation eval_from_mont_inj :=
    (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_zero :=
    (mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation toZ_ofZ_eq := (toZ_ofZ_eq n n_nz n_small m).

  Local Lemma num_bytes_correct :
    num_bytes = Z.of_nat (n * Z.to_nat word_size_in_bytes).
  Proof. cbv; auto. Qed.

  Local Notation three_b_mont := P384_three_b_mont.

  Local Lemma p384_three_b_mont_valid_local :
    valid (toZ (List.map (@Interface.word.of_Z 64 BasicC64Semantics.word) three_b_mont)).
  Proof.
    (* three_b_mont = P384Curve_G1.p384_three_b_mont, concrete list Z.
       Unfold at the Z level and verify all bounds by computation. *)
    cbv [P384_three_b_mont three_b_mont P384Curve_G1.p384_three_b_mont
         WordByWordMontgomery.valid toZ List.map].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

  Local Lemma p384_a_mont_valid :
    valid P384_a_mont.
  Proof.
    (* P384_a_mont = P384Curve_G1.p384_a_mont_list, concrete list Z. *)
    cbv [P384_a_mont P384Curve_G1.p384_a_mont_list].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

  Local Lemma p384_three_b_mont_valid :
    valid three_b_mont.
  Proof.
    exact P384Curve_G1.p384_three_b_mont_valid.
  Qed.

  (** ** Arithmetic notations *)

  Notation my_mul := (my_mul m).
  Notation my_add := (my_add m).
  Notation my_sub := (my_sub m).

  Local Infix "*'" := my_mul (at level 70).
  Local Infix "+'" := my_add (at level 80).
  Local Infix "-'" := my_sub (at level 80).

  (** ** Separation logic and WP proof notation *)

  Local Open Scope string_scope.
  Local Infix "*" := sep : sep_scope.
  Delimit Scope sep_scope with sep.

  Notation msplit := Interface.map.split.

  Notation montsub a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) -
         eval (from_mont (c))) mod m).

  Notation montadd a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) +
         eval (from_mont (c))) mod m).

  Notation montmul a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) *
         eval (from_mont (c))) mod m).

  Notation S aw := (word.add (word.of_Z word_size_in_bytes) aw).

  Add Ring Mp :
    (MontgomeryRingTheory.mont_enc_ring m bw n r' m'
       r'_correct m'_correct bw_big n_nz m_small m_big).

  Local Notation wordof_Z := (@word.of_Z 64 BasicC64Semantics.word).

  (** ** Tactics for Bignum/bytes conversion *)

  Ltac unfold_Bignum_list_step H l :=
    destruct l; [unfold Bignum in H; sepsimpl_hyps; discriminate|].

  Ltac unfold_Bignum_list H l :=
    repeat unfold_Bignum_list_step H l;
    assert (Hl : l = []) by ( unfold Bignum in H; sepsimpl_hyps;
    apply length_nil;
    match goal with
    | [H : Datatypes.length _ = n|- _ ]
      => repeat apply Nat.succ_inj in H; auto
    end); rewrite Hl in H; clear Hl.

  Ltac straightline' :=
    match goal with
    | [Hminit : ?mcond (?minit)
        |- forall (_ : @word.rep _ _)
                  (_ _ : @Interface.map.rep _ _ _),
            anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] =>
        let a := (fresh "a") in
        let mStack := (fresh "mStack") in
        let mnew := (fresh "mnew") in
        let Hany := (fresh "Hany") in
        let HanyBignum := (fresh "HanyBignum") in
        let anyval := (fresh "anyval") in
        let Hsplit := (fresh "Hsplit") in
        let Hmnew := (fresh "Hmnew") in
        let R := (fresh "R") in
        intros a mStack mnew Hany Hsplit;
        destruct (anybytes_Bignum n num_bytes mStack a num_bytes_correct Hany)
          as [anyval HanyBignum];
        destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit
                   (empty_frame mcond minit Hminit)
                   (empty_frame (Bignum _ _ _) mStack HanyBignum))
          as [R Hmnew];
        clear Hany Hsplit HanyBignum
    | _ => straightline
    end.

  Ltac clear_emps_step :=
  lazymatch goal with
  | [H' : (_ * _)%sep ?mem |- _] =>
      let thisH := (fresh "H") in
      eassert (thisH : (emp _ * _)%sep mem) by ecancel_assumption;
      clear H'; sepsimpl_hyps
      end.

  Ltac get_list_from_length l :=
    (repeat (destruct l; [discriminate| ])); destruct l; [| discriminate].

  Ltac Bignum_to_Scalars l := let Hsep := (fresh "Hsep") in
  eassert (Hsep : (Bignum n _ l * _)%sep _) by ecancel_assumption;
  apply Bignum_manyScalars_R in Hsep; sepsimpl_hyps; get_list_from_length l;
  lazymatch goal with
  | [H : (many_Scalars n _ _ * _)%sep _ |- _] =>
    let Htemp := (fresh "Htemp") in
    eassert (Htemp : many_Scalars n _ _ = many_Scalars _ _ _)
      by (vm_compute n; auto);
    rewrite Htemp in H; clear Htemp;
    repeat rewrite many_Scalars_next in H;
    rewrite many_Scalars_nil in H
  | _ => fail
  end.

  (* Clear old separation logic hypotheses that are no longer needed *)
  Ltac clear_old_seps :=
    lazymatch goal with
    | H:sep _ _ ?mem |- context [?mem] =>
      repeat
        match goal with
        | H':sep _ _ ?m |- _ => assert_fails unify m mem; clear H'
        end
    end.

  (** ** Tactics for storing constants *)

  Ltac subst_vars :=
    lazymatch goal with
    | [|- WeakestPrecondition.store _ _ ?thisa _ _] =>
      try subst thisa
    end.

  Ltac handle_store_step :=
    lazymatch goal with
      | [ |- ((Scalars.scalar ?thisa _) * _)%sep _ ] =>
       try subst thisa;
       repeat (rewrite next_word'; try (rewrite word_add_0));
       ecancel_assumption
    end.

  Ltac handle_store :=
    repeat (subst_vars; eapply Scalars.store_word_of_sep;
            [handle_store_step|]; repeat straightline');
    clear_old_seps.

  (** ** Stack allocation tactics *)

  Lemma alloc_anybytes_Bignum n0 :
    forall (R : Interface.map.rep -> Prop) a0 m0 m1 m2,
      n0 = Z.of_nat (n * Z.to_nat word_size_in_bytes) ->
      msplit m0 m1 m2 -> anybytes a0 n0 m2 -> R m1 ->
      exists (l : list BasicC64Semantics.word),
        (R * (Bignum n a0 l))%sep m0.
  Proof.
    intros.
    pose proof (anybytes_Bignum n m2 n0 a0).
    apply H3 in H1; [| cbv; auto].
    destruct H1. exists x. unfold sep. exists m1. exists m2. auto.
  Qed.

  Ltac alloc_Bignum := lazymatch goal with
    | Hprec : _ ?mpre |- forall _ _ _, anybytes _ ?n0 _ ->
      msplit _ ?mpre _ -> _ =>
      let a0 := (fresh "a") in
      let mStack := (fresh "mStack") in
      let mComb := (fresh "mComb") in
      let Hany := (fresh "Hany") in
      let Hcomb := (fresh "Hcomb") in
      let Htemp := (fresh "Htemp") in
      intros a0 mStack mComb Hany Hcomb;
      assert (Htemp : n0 = Z.of_nat (n * Z.to_nat word_size_in_bytes))
        by (cbv; auto);
      destruct (alloc_anybytes_Bignum n0 _ a0 mComb mpre mStack Htemp Hcomb
                  Hany Hprec);
      clear Htemp Hprec Hany
    | _ => idtac
    end.

  Ltac straightline_stackalloc_Bignum :=
    try (alloc_Bignum); straightline.

  (** ** Montgomery arithmetic lemmas *)

  Local Lemma valid_toZ_wordofZ_three_b_mont :
    valid (toZ (List.map wordof_Z three_b_mont)).
  Proof. exact p384_three_b_mont_valid_local. Qed.

  Local Lemma valid_toZ_wordofZ_a_mont :
    valid (toZ (List.map wordof_Z P384_a_mont)).
  Proof.
    cbv [P384_a_mont P384Curve_G1.p384_a_mont_list toZ].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

  Local Notation valid' := (valid' m bw n).

  Lemma montadd_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montadd z x y -> (enc_mont m bw n z Hz)
      = mont_add (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_add_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montsub_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montsub z x y -> (enc_mont m bw n z Hz)
      = mont_sub (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_sub_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montmul_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montmul z x y -> (enc_mont m bw n z Hz)
      = mont_mul (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_mul_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Ltac assert_valid' x H' := let H := (fresh "Hvalid") in
    assert (H : valid' (toZ x)) by (apply H'; assumption).

  Ltac assertvalid' x H :=
    tryif (assert (H : valid' x) by assumption; clear H)
    then idtac
    else (assert (H : valid' x) by
            (apply valid_valid'_equiv; assumption)).

  Lemma three_b_mont_rewrite
        (H : valid' (toZ (map wordof_Z three_b_mont))) :
    ((MontgomeryCurveSpecs.three_b_mont m bw n r' m' three_b
       three_b_small r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z three_b_mont); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq three_b_mont p384_three_b_mont_valid).
    cbv [MontgomeryCurveSpecs.three_b_mont]. rewrite mont_enc_val.
    (* three_b_mont_correct: P384_three_b_mont = to_montgomerymod ... three_b_list *)
    vm_compute. reflexivity.
  Qed.

  Lemma a_mont_rewrite (H : valid' (toZ (map wordof_Z P384_a_mont))) :
    ((MontgomeryCurveSpecs.a_mont m bw n r' m' a_val a_small
       r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z P384_a_mont); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq P384_a_mont p384_a_mont_valid).
    cbv [MontgomeryCurveSpecs.a_mont]. rewrite mont_enc_val.
    vm_compute. reflexivity.
  Qed.

  (** ** Tactics for function call handling *)

  (* Normalize callee postconditions to match montmul/montadd/montsub patterns. *)
  Ltac normalize_mont_hyps :=
    repeat match goal with
    | [H : _ mod m = ((_ mod m) * (_ mod m)) mod m |- _] =>
        rewrite <- Zmult_mod in H
    | [H : _ mod m = ((_ mod m) + (_ mod m)) mod m |- _] =>
        rewrite <- Zplus_mod in H
    | [H : _ mod m = ((_ mod m) - (_ mod m)) mod m |- _] =>
        rewrite <- Zminus_mod in H
    end.

  (* Extract length from a Bignum sep hypothesis *)
  Local Lemma Bignum_length_extract :
    forall nn (px : BasicC64Semantics.word) (ws : list BasicC64Semantics.word)
           (mm : Interface.map.rep) (R : Interface.map.rep -> Prop),
    (Bignum nn px ws * R)%sep mm ->
    Datatypes.length ws = nn.
  Proof.
    intros. unfold Bignum in H. sepsimpl_hyps. assumption.
  Qed.

  Ltac solve_bignum_length :=
    first
      [ assumption
      | match goal with
        | [HB : (Bignum _ _ ?ws * _)%sep _ |- Datatypes.length ?ws = _] =>
          exact (Bignum_length_extract _ _ _ _ _ HB)
        | [HB : (_ * (Bignum _ _ ?ws * _))%sep _ |- Datatypes.length ?ws = _] =>
          let Htmp := fresh "Htmp" in
          assert (Htmp : (Bignum _ _ ws * _)%sep _) by ecancel_assumption;
          exact (Bignum_length_extract _ _ _ _ _ Htmp)
        | [HB : context[Bignum _ _ ?ws] |- Datatypes.length ?ws = _] =>
          let Htmp := fresh "Htmp" in
          assert (Htmp : (Bignum _ _ ws * _)%sep _) by ecancel_assumption;
          exact (Bignum_length_extract _ _ _ _ _ Htmp)
        end ].

  Ltac next_call :=
    lazymatch goal with
      | [H' : (_ * _)%sep _ |- _] =>
        straightline_call;
        [eauto | eauto | solve_bignum_length
        | ecancel_assumption | ecancel_assumption | ecancel_assumption | ];
        repeat straightline'; clear H'; repeat clear_emps_step;
        normalize_mont_hyps
      end.

  (** ** Defragmentation tactics *)

  Ltac defrag_in_context := lazymatch goal with
  | [
      |- exists (_ _ : @Interface.map.rep _ _ _),
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
        repeat match goal with
        | [ H : (?Rl * ((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] =>
          let Ha := (fresh "Ha") in
          let m0 := fresh "m" in
          let Htemp := fresh "Htemp" in
          let Htemp' := fresh "Htemp'" in
          let mStack := fresh "mStack" in
          assert (Ha : ((Bignum n addr aval) * (Rl * Rr))%sep mem)
            by ecancel_assumption; clear H;
          destruct Ha as [mStack [m0 [ Htemp [Htemp' ]]]];
          exists m0; exists mStack;
          split; [ eapply Bignum_anybytes;
                   [|eassumption]; cbv; reflexivity
                 | split; [apply Properties.map.split_comm; auto
                          | clear Htemp Htemp']]
        | [ H : (((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] =>
          let Ha := (fresh "Ha") in
          let m0 := fresh "m" in
          let mStack := fresh "mStack" in
          assert (Ha : ((Bignum n addr aval) * (Rr))%sep mem)
            by ecancel_assumption; clear H;
          destruct Ha as [mStack [m0 [Htemp [Htemp' ]]]];
          exists m0; exists mStack;
          split; [ eapply Bignum_anybytes;
                   [|eassumption]; cbv; reflexivity
                 | split; [apply Properties.map.split_comm; auto
                          | clear Ha]]

        | [ H : _ mem |- _ ] => apply (sep_assoc_proj2 mem) in H
        end
  end.

  Ltac defrag_in_context' := lazymatch goal with
  | [ |- exists (_ _ : @Interface.map.rep _ _ _),
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
        match goal with
        | [ H : _ mem |- _ ] => cleanup_hyp H mem
        end
      end; defrag_in_context.

  (** ** Return-value tactics *)

  Ltac this_mod' x :=
    lazymatch goal with
    | H1 : montsub x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montsub_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | H1 : montadd x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montadd_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | H1 : montmul x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montmul_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | _ => idtac
    end.

  Ltac remember_mont x := lazymatch goal with
  | H1 : valid' x |- _ =>
    let p := (fresh "p") in
    remember {| val := x; Hvalid := H1 |} as p
  end.

  (** ** WP Proof

      Phases:
        1. Unfold function, handle stackallocs for 8 temporaries
           (three_b, a_const, t0..t5), convert byte-arrays to Bignum,
           perform 12 word-stores (6 for three_b_mont, 6 for a_mont).
        2. Step through all 40 field-op function calls via do_binop_call.
        3. Defragment memory, prove the Gallina postcondition using
           BLS12_add_specs_equiv' with the P-384 a and three_b constants. *)

  Theorem P384_G1_add_func_ok :
    program_logic_goal_for_function! P384_G1_add.
  Proof.
    cbv [program_logic_goal_for spec_of_P384_G1_add].
    intros.
    eapply WeakestPreconditionProperties.start_func;
      [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func P384_G1_add].
    repeat straightline.
    (* Convert byte arrays to Bignum for each of the 8 stackallocs *)
    repeat
      (lazymatch goal with
       | Hmem : context[array ptsto _ ?ptr ?bs] |- _ =>
         lazymatch goal with
         | _ : context[Bignum 6 ptr _] |- _ => fail
         | _ =>
           let Hiff := fresh "Hiff" in
           assert (Hiff : Lift1Prop.iff1
                   (array ptsto (@word.of_Z 64 BasicC64Semantics.word 1) ptr bs)
                   (Bignum 6 ptr (ArrayCasts.bs2ws (Z.to_nat word_size_in_bytes) bs)))
           by (apply Bignum_of_bytes;
               match goal with
               | Hl : Datatypes.length bs = Z.to_nat 48 |- _ =>
                 rewrite Hl; reflexivity
               end);
           seprewrite_in Hiff Hmem; clear Hiff
         end
       end).
    (* Clear intermediate separation facts for the partial memories *)
    repeat match goal with
    | H : (_ * _)%sep ?mem |- _ =>
      lazymatch goal with
      | |- WeakestPrecondition.store _ ?m _ _ _ =>
        assert_fails unify m mem; clear H
      | |- WeakestPrecondition.cmd _ _ _ ?m _ _ =>
        assert_fails unify m mem; clear H
      | _ => fail
      end
    end.
    (* Destructure first Bignum (three_b) into 6 concrete scalars *)
    lazymatch goal with
    | |- WeakestPrecondition.store _ _ ?p _ _ =>
      lazymatch goal with
      | Hmem : context[Bignum 6 p ?wsl] |- _ =>
        let len_lem := fresh "Hlen_tb" in
        assert (len_lem : Datatypes.length wsl = 6%nat)
          by (match goal with
              | Hbs : Datatypes.length ?bs = Z.to_nat 48 |- _ =>
                lazymatch wsl with
                | ArrayCasts.bs2ws _ bs =>
                  rewrite ArrayCasts.bs2ws_length;
                    [rewrite Hbs; cbv; reflexivity
                    |cbv; discriminate
                    |rewrite Hbs; cbv; reflexivity]
                end
              end);
        let r0 := fresh "r" in
        let r1 := fresh "r" in
        let r2 := fresh "r" in
        let r3 := fresh "r" in
        let r4 := fresh "r" in
        let r5 := fresh "r" in
        let wsl_eq := fresh "wsl_eq" in
        let wsl' := fresh "wsl'" in
        remember wsl as wsl' eqn:wsl_eq;
        destruct wsl' as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|]]]]]]];
          try (simpl in len_lem; discriminate);
        clear len_lem wsl_eq
      end
    end.
    (* Phase 1a: Unfold the three_b Bignum into scalars *)
    lazymatch goal with
    | H : context[Bignum 6 ?p [r; r0; r1; r2; r3; r4]] |- _ =>
      let Hiff := fresh "Hiff" in
      pose proof (Bignum_n_Scalar 6%nat p [r; r0; r1; r2; r3; r4]) as Hiff;
      cbn [many_Scalars hd tl] in Hiff;
      seprewrite_in Hiff H; clear Hiff
    end.
    (* Perform the 6 word stores for three_b_mont *)
    repeat (eapply Scalars.store_word_of_sep;
            [ repeat match goal with
              | |- ((Scalars.scalar ?addr _) * _)%sep _ =>
                subst addr
              | _ => idtac
              end;
              repeat (rewrite next_word'; try rewrite word_add_0);
              ecancel_assumption
            | intros ? ?; repeat straightline ]).
    (* Substitute let-bindings *)
    repeat match reverse goal with
    | x := _ |- _ => subst x
    end.
    (* Rebuild the three_b Bignum from 6 scalars *)
    eassert (Hbignum3b :
      (Bignum 6 a (List.map wordof_Z P384_three_b_mont) * _)%sep _).
    { unfold Bignum; sepsimpl; [cbv; reflexivity|];
      unfold array; cbv [P384_three_b_mont List.map];
      repeat rewrite (word_add_comm _ (word.of_Z word_size_in_bytes));
      match goal with
      | [ H : (_ * _)%sep _ |- _ ] =>
        repeat (rewrite next_word' in H; try rewrite word_add_0 in H);
        ecancel_assumption
      end. }
    clear_old_seps.
    (* Phase 1b: Destructure a_const Bignum and store a_mont values *)
    lazymatch goal with
    | |- WeakestPrecondition.store _ _ ?p _ _ =>
      lazymatch goal with
      | Hmem : context[Bignum 6 p ?wsl] |- _ =>
        let len_lem := fresh "Hlen_ac" in
        assert (len_lem : Datatypes.length wsl = 6%nat)
          by (match goal with
              | Hbs : Datatypes.length ?bs = Z.to_nat 48 |- _ =>
                lazymatch wsl with
                | ArrayCasts.bs2ws _ bs =>
                  rewrite ArrayCasts.bs2ws_length;
                    [rewrite Hbs; cbv; reflexivity
                    |cbv; discriminate
                    |rewrite Hbs; cbv; reflexivity]
                end
              end);
        let s0 := fresh "s" in
        let s1 := fresh "s" in
        let s2 := fresh "s" in
        let s3 := fresh "s" in
        let s4 := fresh "s" in
        let s5 := fresh "s" in
        let wsl_eq := fresh "wsl_eq" in
        let wsl' := fresh "wsl'" in
        remember wsl as wsl' eqn:wsl_eq;
        destruct wsl' as [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|]]]]]]];
          try (simpl in len_lem; discriminate);
        clear len_lem wsl_eq
      end
    end.
    lazymatch goal with
    | H : context[Bignum 6 ?p [s; s0; s1; s2; s3; s4]] |- _ =>
      let Hiff := fresh "Hiff" in
      pose proof (Bignum_n_Scalar 6%nat p [s; s0; s1; s2; s3; s4]) as Hiff;
      cbn [many_Scalars hd tl] in Hiff;
      seprewrite_in Hiff H; clear Hiff
    end.
    (* Perform the 6 word stores for a_mont *)
    repeat (eapply Scalars.store_word_of_sep;
            [ repeat match goal with
              | |- ((Scalars.scalar ?addr _) * _)%sep _ =>
                subst addr
              | _ => idtac
              end;
              repeat (rewrite next_word'; try rewrite word_add_0);
              ecancel_assumption
            | intros ? ?; repeat straightline ]).
    repeat match reverse goal with
    | x := _ |- _ => subst x
    end.
    (* Rebuild the a_const Bignum *)
    eassert (Hbignuma :
      (Bignum 6 a0 (List.map wordof_Z P384_a_mont) * _)%sep _).
    { unfold Bignum; sepsimpl; [cbv; reflexivity|];
      unfold array; cbv [P384_a_mont List.map];
      repeat rewrite (word_add_comm _ (word.of_Z word_size_in_bytes));
      match goal with
      | [ H : (_ * _)%sep _ |- _ ] =>
        repeat (rewrite next_word' in H; try rewrite word_add_0 in H);
        ecancel_assumption
      end. }
    clear_old_seps.
    (* Bring validity of three_b_mont and a_mont Bignums into context *)
    pose proof valid_toZ_wordofZ_three_b_mont as H3b.
    pose proof valid_toZ_wordofZ_a_mont as Ha.
    (* Phase 2: Handle the 40 binop function calls *)
    Ltac do_binop_call :=
      straightline_call;
      [ (* valid x *)
      | (* valid y *)
      | (* length old_out *)
      | ecancel_assumption
      | ecancel_assumption
      | ecancel_assumption
      | (* continuation *)
      ];
      [ eassumption | eassumption | solve_bignum_length
      | repeat straightline'; normalize_mont_hyps ].
    repeat (do_binop_call; repeat straightline).
    (* Phase 3: Postcondition — defragment memory and prove Gallina spec *)
    repeat defrag_in_context'.
    repeat straightline.
    do 4 eexists.
    split; [| ecancel_assumption].
    split; [| auto].
    (* Gallina spec *)
    unfold P384_add_Gallina_spec, BLS12_add_Gallina_spec.
    (* Validity for inputs *)
    pose proof (valid_valid'_equiv) as Hvve.
    assert_valid' wX1 Hvve.
    assert_valid' wX2 Hvve.
    assert_valid' wY1 Hvve.
    assert_valid' wY2 Hvve.
    assert_valid' wZ1 Hvve.
    assert_valid' wZ2 Hvve.
    (* Extract output word lists and assert their validity *)
    lazymatch goal with
    | H : (_ * _)%sep _ |- _ =>
      lazymatch type of H with
      | context[Bignum _ poutx ?wo_x] =>
        lazymatch type of H with
        | context[Bignum _ pouty ?wo_y] =>
          lazymatch type of H with
          | context[Bignum _ poutz ?wo_z] =>
            assert_valid' wo_x Hvve;
            assert_valid' wo_y Hvve;
            assert_valid' wo_z Hvve
          end
        end
      end
    end.
    (* Assert valid' for remaining valid hypotheses *)
    repeat match goal with
    | [ H : valid ?wz |- _ ] =>
      lazymatch wz with
      | map Interface.word.unsigned ?w =>
        lazymatch goal with
        | [ _ : valid' (toZ w) |- _ ] => fail
        | _ => assert_valid' w Hvve
        end
      | List.map Interface.word.unsigned ?w =>
        lazymatch goal with
        | [ _ : valid' (toZ w) |- _ ] => fail
        | _ => assert_valid' w Hvve
        end
      end
    end.
    (* Use BLS12_add_specs_equiv' with P-384 parameters (a = (-3) mod m, a≠0) *)
    destruct (MontgomeryCurveG1Equiv.BLS12_add_specs_equiv'
                m bw n r' m'
                a_val three_b a_small three_b_small
                r'_correct m'_correct bw_big n_nz m_small m_big
                _ _ _ _ _ _ _ _ _
                Hvalid Hvalid0 Hvalid1 Hvalid2 Hvalid3 Hvalid4
                Hvalid5 Hvalid6 Hvalid7)
      as [Heq _].
    apply Heq; clear Heq.
    (* Phase 3: polynomial identity over the mont_enc ring. *)
    lazymatch goal with
    | [ |- BLS12_add_mont_spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10
            ?a11 ?a12 ?a13 ?a14 ?a15 ?ox ?oy ?oz ] =>
      this_mod' ox; this_mod' oy; this_mod' oz
    | [ |- @MontgomeryCurveSpecs.BLS12_add_mont_spec ?mx ?bwx ?nx ?r'x ?m'x
            ?ax ?tbx ?asx ?tbsx ?r'cx ?m'cx ?bwbx ?nnzx ?msx ?mbx
            ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?ox ?oy ?oz ] =>
      this_mod' ox; this_mod' oy; this_mod' oz
    | _ =>
      (* Fallback: try to match any form *)
      match goal with
      | [ H_outx : montmul ?ox _ _ |- _ ] => this_mod' ox
      | [ H_outx : montadd ?ox _ _ |- _ ] => this_mod' ox
      | [ H_outx : montsub ?ox _ _ |- _ ] => this_mod' ox
      | _ => idtac
      end;
      match goal with
      | [ H_outy : montmul ?oy _ _ |- context[?oy] ] => this_mod' oy
      | [ H_outy : montadd ?oy _ _ |- context[?oy] ] => this_mod' oy
      | [ H_outy : montsub ?oy _ _ |- context[?oy] ] => this_mod' oy
      | _ => idtac
      end;
      match goal with
      | [ H_outz : montmul ?oz _ _ |- context[?oz] ] => this_mod' oz
      | [ H_outz : montadd ?oz _ _ |- context[?oz] ] => this_mod' oz
      | [ H_outz : montsub ?oz _ _ |- context[?oz] ] => this_mod' oz
      | _ => idtac
      end
    end.
    unfold BLS12_add_mont_spec.
    (* Rewrite spec's three_b_mont to match WP's three_b bignum *)
    let Hv3b := fresh "Hv3b" in
    assert (Hv3b : valid' (toZ (List.map wordof_Z P384_three_b_mont)))
      by (apply valid_valid'_equiv; exact valid_toZ_wordofZ_three_b_mont);
    rewrite <- (three_b_mont_rewrite Hv3b).
    (* Rewrite spec's a_mont to match WP's a_const bignum *)
    let Hva := fresh "Hva" in
    assert (Hva : valid' (toZ (List.map wordof_Z P384_a_mont)))
      by (apply valid_valid'_equiv; exact valid_toZ_wordofZ_a_mont);
    rewrite <- (a_mont_rewrite Hva).
    (* Remember all input ring elements *)
    remember_mont (toZ wX1).
    remember_mont (toZ wX2).
    remember_mont (toZ wY1).
    remember_mont (toZ wY2).
    remember_mont (toZ wZ1).
    remember_mont (toZ wZ2).
    (* Close by ring equality *)
    apply pair_equal_spec; split; [apply pair_equal_spec; split; ring | ring].
  Qed.

End P384_G1_Add.
