(** * P384_G1_Add_Functor_Instance — P-384 instantiation of the
      general-a G1-add functor [Bedrock.Curve.WbwMontgomeryG1GeneralA].

    The bedrock2 function body, the WP spec, and the callee specs are
    the functor's, applied at the P-384 parameters (m = 2^384 - 2^128
    - 2^96 + 2^32 - 1, n = 6, 48 bytes, callee prefix "p384_coord_",
    function name "P384_G1_add_f", constants from
    [Bedrock.Curve.P384Curve_G1]).  The WP proof replays the debugged
    P-256 pathfinder script at 6 limbs: 8 stackallocs of 48 bytes,
    6+6 constant-store singles, the 40 RCB calls, and the
    Montgomery-ring postcondition; the 6-limb store/fold machinery
    ([fold6_scalars_Bignum], [fold6_scalars_Bignum_flat],
    [fold6_scalars_Bignum_flat_desc]) is in
    [Bedrock.Util.BignumStoreFold].

    Script deviations from the pathfinder mirror
    [P256_G1_Add_Functor_Instance.v] (see its header): callee specs at
    the literal m' (no field-parameters projection sentence), direct
    [BLS12_add_Gallina_spec], local re-derivations of the ring-bridge
    lemmas, diagnostics removed.

    Honesty ledger: exactly one [Admitted] — the closure algebra
    tail of [P384f_G1_add_func_ok] (TODO(ring-final)). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Array.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Bedrock.Field.Common.Tactics.

Require Import Bedrock.Curve.P384Curve_G1.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveG1Equiv.

Require Import coqutil.Map.Properties.
Require Import bedrock2.Lift1Prop.
Require Import Bedrock.Util.Word.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.SeparationLogic.
Require Import Bedrock.Util.BignumStoreFold.
Require Import Bedrock.Curve.WbwMontgomeryG1GeneralA.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section P384_G1_Add_Functor_Instance.

  (* O(n) sep frame inference instead of O(n!) permutation search.
     Inlined from BLS12_GLV_ScalarMultBedrock.v / WPTactics.v. *)
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

  (* ============================================================== *)
  (* Parameters: P-384                                               *)
  (* ============================================================== *)

  (* m = 2^384 - 2^128 - 2^96 + 2^32 - 1 (concrete literal). *)
  Local Notation m :=
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319%Z.
  Local Notation n := 6%nat.
  Local Notation bw := 64.
  (* a_val = (-3) mod m *)
  Local Notation a_val :=
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112316%Z.
  (* three_b_val = 3*b mod m *)
  Local Notation three_b_val :=
    3936568287090159208988955320879916669011239028153812228389535097474624180935841937314250118133359319573105337467087%Z.
  (* m' = modinv(-m, 2^64) = 2^32 + 1. *)
  Local Notation m' := 4294967297%Z.
  (* r' = modinv(2^64, m). *)
  Local Notation r' :=
    9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209%Z.
  Local Notation num_bytes := 48%Z (only parsing).
  Local Notation word_size_in_bytes := (Memory.bytes_per_word 64).

  (* Montgomery-encoded constant lists (concrete, from P384Curve_G1). *)
  Definition P384f_three_b_mont : list Z := P384Curve_G1.p384_three_b_mont.
  Definition P384f_a_mont : list Z := P384Curve_G1.p384_a_mont_list.

  (** The bedrock2 function: the functor body at the P-384 parameters. *)
  Definition P384f_G1_add : Syntax.func :=
    Eval vm_compute in
      g1_add_func 48 "p384_coord_"
        P384Curve_G1.p384_a_mont_list P384Curve_G1.p384_three_b_mont.

  (* ============================================================== *)
  (* Spec instances: the functor's, at the P-384 parameters          *)
  (* ============================================================== *)

  Local Instance spec_of_P384f_G1_add : spec_of "P384_G1_add_f" :=
    spec_of_g1_add m n "P384_G1_add_f" a_val three_b_val m'.

  Local Instance spec_of_p384f_coord_mul : spec_of "p384_coord_mul" :=
    spec_of_coord_mul m n "p384_coord_" m'.

  Local Instance spec_of_p384f_coord_add : spec_of "p384_coord_add" :=
    spec_of_coord_add m n "p384_coord_" m'.

  Local Instance spec_of_p384f_coord_sub : spec_of "p384_coord_sub" :=
    spec_of_coord_sub m n "p384_coord_" m'.

  (* ============================================================== *)
  (* Montgomery ring infrastructure                                  *)
  (* ============================================================== *)

  Local Notation valid := (WordByWordMontgomery.valid bw n m).
  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation from_mont :=
    (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation evfrom x := (eval (from_mont x)).
  Local Notation toZ x := (List.map Interface.word.unsigned x).

  (* Side conditions, discharged by computation. *)
  Local Lemma a_small : a_val = a_val mod m.
  Proof. vm_compute. reflexivity. Qed.

  Local Lemma three_b_small : three_b_val = three_b_val mod m.
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

  Local Lemma num_bytes_correct :
    num_bytes = Z.of_nat (n * Z.to_nat word_size_in_bytes).
  Proof. cbv; auto. Qed.

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
  Local Notation valid' := (valid' m bw n).

  Local Lemma p384f_three_b_mont_valid : valid P384f_three_b_mont.
  Proof. exact P384Curve_G1.p384_three_b_mont_valid. Qed.

  Local Lemma p384f_a_mont_valid : valid P384f_a_mont.
  Proof.
    cbv [P384f_a_mont P384Curve_G1.p384_a_mont_list].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

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

  Add Ring Mp :
    (MontgomeryRingTheory.mont_enc_ring m bw n r' m'
       r'_correct m'_correct bw_big n_nz m_small m_big).

  Local Notation wordof_Z := (@word.of_Z 64 BasicC64Semantics.word).

  Local Lemma valid_toZ_wordofZ_three_b_mont :
    valid (toZ (List.map wordof_Z P384f_three_b_mont)).
  Proof.
    cbv [P384f_three_b_mont P384Curve_G1.p384_three_b_mont
         WordByWordMontgomery.valid toZ List.map].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

  Local Lemma valid_toZ_wordofZ_a_mont :
    valid (toZ (List.map wordof_Z P384f_a_mont)).
  Proof.
    cbv [P384f_a_mont P384Curve_G1.p384_a_mont_list toZ].
    vm_compute. repeat split; auto; intros; discriminate.
  Qed.

  (* Postcondition -> mont_enc-ring equalities. *)
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

  Lemma three_b_mont_rewrite
        (H : valid' (toZ (map wordof_Z P384f_three_b_mont))) :
    ((MontgomeryCurveG1Equiv.three_b_mont m bw n r' m' three_b_val
       three_b_small r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z P384f_three_b_mont); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq P384f_three_b_mont p384f_three_b_mont_valid).
    cbv [MontgomeryCurveG1Equiv.three_b_mont]. rewrite mont_enc_val.
    vm_compute. reflexivity.
  Qed.

  Lemma a_mont_rewrite (H : valid' (toZ (map wordof_Z P384f_a_mont))) :
    ((MontgomeryCurveG1Equiv.a_mont m bw n r' m' a_val a_small
       r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z P384f_a_mont); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq P384f_a_mont p384f_a_mont_valid).
    cbv [MontgomeryCurveG1Equiv.a_mont]. rewrite mont_enc_val.
    vm_compute. reflexivity.
  Qed.

  (* ============================================================== *)
  (* Proof-support tactics (pathfinder transcription, n = 6)         *)
  (* ============================================================== *)

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

  Ltac clear_old_seps :=
    lazymatch goal with
    | H:sep _ _ ?mem |- context [?mem] =>
      repeat
        match goal with
        | H':sep _ _ ?m0 |- _ => assert_fails unify m0 mem; clear H'
        end
    end.

  Ltac normalize_mont_hyps :=
    repeat match goal with
    | [H : _ mod m = ((_ mod m) * (_ mod m)) mod m |- _] =>
        rewrite <- Zmult_mod in H
    | [H : _ mod m = ((_ mod m) + (_ mod m)) mod m |- _] =>
        rewrite <- Zplus_mod in H
    | [H : _ mod m = ((_ mod m) - (_ mod m)) mod m |- _] =>
        rewrite <- Zminus_mod in H
    end.

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

  Ltac assert_valid' x H' := let H := (fresh "Hvalid") in
    assert (H : valid' (toZ x)) by (apply H'; assumption).

  Ltac assertvalid' x H :=
    tryif (assert (H : valid' x) by assumption; clear H)
    then idtac
    else (assert (H : valid' x) by
            (apply valid_valid'_equiv; assumption)).

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

  (* Constant-store building blocks over the BignumStoreFold
     machinery (the functor's §6 versions are Section-local). *)
  Ltac store_first_limb nlimbs nbytes :=
    destruct_store_target_bignum nlimbs nbytes;
    unfold_bignum_to_scalars nlimbs;
    wp_store_scalar.

  Ltac store_next_limb :=
    next_store_prelude; wp_store_scalar.

  Ltac store_block_finish :=
    subst_all_lets;
    fold_stored_scalars_Bignum;
    clear_old_seps.

  (* ============================================================== *)
  (* The WP theorem                                                  *)
  (* ============================================================== *)

  Theorem P384f_G1_add_func_ok :
    forall (functions : Semantics.env),
      map.get functions "P384_G1_add_f" = Some P384f_G1_add ->
      spec_of_p384f_coord_mul functions ->
      spec_of_p384f_coord_add functions ->
      spec_of_p384f_coord_sub functions ->
      spec_of_P384f_G1_add functions.
  Proof.
    intros functions EnvContains Hspec_mul Hspec_add Hspec_sub.
    cbv [spec_of_P384f_G1_add spec_of_g1_add]. intros.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | clear EnvContains ].
    cbv match beta delta [WeakestPrecondition.func P384f_G1_add].
    eexists. split.
    { reflexivity. }
    (* Phase 0: 8-stackalloc prologue as committed singles. *)
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    (* Conversion post-pass: raw anybytes/msplit pairs -> byte arrays. *)
    stackalloc_anybytes_to_arrays.
    (* Phase 1: constant stores.  Value-dexpr bridge for the first
       store, byte arrays -> Bignums, then per-limb committed singles. *)
    dexpr_literal_bridge.
    subst_word_lets.
    byte_arrays_to_Bignums 6%nat 48.
    clear_stale_seps.
    (* three_b block *)
    store_first_limb 6%nat 48.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_block_finish.
    (* a_const block *)
    open_cmd. dexpr_var_offset_bridge. dexpr_literal_bridge.
    subst_word_lets.
    store_first_limb 6%nat 48.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_next_limb.
    store_block_finish.
    (* Validity of the stored constants. *)
    pose proof valid_toZ_wordofZ_three_b_mont as H3b.
    pose proof valid_toZ_wordofZ_a_mont as Ha.
    (* Phase 2: the 40 field-op calls (S1..S18 first). *)
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    (* S19 prep: fold both constant buffers (flat scalar sextets) into
       Bignums, then the first call that touches both stack constants. *)
    match goal with
    | Hc : (_ * _)%sep _ |- _ =>
      first [ seprewrite_in fold6_scalars_Bignum_flat_desc Hc
            | seprewrite_in fold6_scalars_Bignum_flat Hc ];
      first [ seprewrite_in fold6_scalars_Bignum_flat_desc Hc
            | seprewrite_in fold6_scalars_Bignum_flat Hc ]
    end.
    lazymatch goal with
    | H : context [Scalars.scalar] |- _ => fail 99 "SCALARS-REMAIN"
    | _ => idtac
    end.
    Timeout 600 straightline_call.
    4: ecancel_assumption.
    4: ecancel_assumption.
    4: ecancel_assumption.
    1: eassumption.
    1: eassumption.
    1: solve_bignum_length.
    1: repeat straightline'. 1: normalize_mont_hyps.
    Timeout 300 (repeat straightline). clear_old_seps.
    (* S20..S40.  (S20/S21 are the profiled hot sites, 84 s / 41 s;
       the flatten_seps escalation there hung >50 min at 2 GB —
       measured 2026-08-28 — so the plain route stays.) *)
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    try (unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]).
    Timeout 180 (repeat straightline).
    do_binop_call. repeat straightline. clear_old_seps.
    (* Phase 3: postcondition.  Every searching sentence is
       timeout-bounded so a stall fails with a position. *)
    Timeout 900 (repeat defrag_in_context').
    Timeout 300 (repeat straightline).
    (* Shape-driven landing: [straightline] may leave any prefix of
       [t = t' /\ rets = nil /\ exists woutx wouty woutz Rout, _]
       unconsumed, and a fixed [do 4 eexists] constructor-splits the
       trailing conjunction (first-execution findings, 2026-08-28).
       Consume equality conjuncts and existentials by shape, then
       land on the [(Gallina /\ valids) /\ sep] conjunction. *)
    Timeout 300 (repeat lazymatch goal with
           | |- exists _, _ => eexists
           | |- (_ = _) /\ _ => split; [reflexivity|]
           end).
    lazymatch goal with
    | |- _ /\ _ => idtac
    | |- ?G => fail 99 "P3-LANDING" G
    end.
    Set Printing Width 250. Show.
    split.
    2: timeout 300 ecancel_assumption.
    Timeout 300 (split; [| auto]).
    unfold BLS12_add_Gallina_spec.
    pose proof (valid_valid'_equiv) as Hvve.
    assert_valid' wX1 Hvve.
    assert_valid' wX2 Hvve.
    assert_valid' wY1 Hvve.
    assert_valid' wY2 Hvve.
    assert_valid' wZ1 Hvve.
    assert_valid' wZ2 Hvve.
    (* Extract output word lists and assert their validity. *)
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
    (* Assert valid' for remaining valid hypotheses. *)
    Timeout 300 (repeat match goal with
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
    end).
    destruct (MontgomeryCurveG1Equiv.BLS12_add_specs_equiv'
                m bw n r' m'
                a_val three_b_val a_small three_b_small
                r'_correct m'_correct bw_big n_nz m_small m_big
                _ _ _ _ _ _ _ _ _
                Hvalid Hvalid0 Hvalid1 Hvalid2 Hvalid3 Hvalid4
                Hvalid5 Hvalid6 Hvalid7)
      as [Heq _].
    Timeout 300 (apply Heq; clear Heq).
    (* Global inner-mod stripping so montmul/montadd/montsub notations
       match every call-equation hypothesis. *)
    Timeout 300 (repeat match goal with
    | H : context[(_ mod m) mod m] |- _ => rewrite Zmod_mod in H
    | H : context[(_ mod m * _) mod m] |- _ => rewrite Zmult_mod_idemp_l in H
    | H : context[(_ * (_ mod m)) mod m] |- _ => rewrite Zmult_mod_idemp_r in H
    | H : context[(_ mod m + _) mod m] |- _ => rewrite Zplus_mod_idemp_l in H
    | H : context[(_ + (_ mod m)) mod m] |- _ => rewrite Zplus_mod_idemp_r in H
    | H : context[(_ mod m - _) mod m] |- _ => rewrite Zminus_mod_idemp_l in H
    | H : context[(_ - (_ mod m)) mod m] |- _ => rewrite Zminus_mod_idemp_r in H
    end).
    (* Rewrite the output enc_monts into their mont_mul/add/sub form. *)
    Timeout 600 (lazymatch goal with
    | [ |- BLS12_add_mont_spec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10
            ?a11 ?a12 ?a13 ?a14 ?a15 ?ox ?oy ?oz ] =>
      this_mod' ox; this_mod' oy; this_mod' oz;
      lazymatch goal with
      | |- context [ {| val := toZ ?xv; Hvalid := _ |} ] =>
        try (this_mod' (toZ xv))
      end
    | [ |- @MontgomeryCurveSpecs.BLS12_add_mont_spec ?mx ?bwx ?nx ?r'x ?m'x
            ?ax ?tbx ?asx ?tbsx ?r'cx ?m'cx ?bwbx ?nnzx ?msx ?mbx
            ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?ox ?oy ?oz ] =>
      this_mod' ox; this_mod' oy; this_mod' oz;
      lazymatch goal with
      | |- context [ {| val := toZ ?xv; Hvalid := _ |} ] =>
        try (this_mod' (toZ xv))
      end
    | _ =>
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
    end).
    unfold BLS12_add_mont_spec.
    unfold MontgomeryCurveG1Equiv.BLS12_add_mont_spec.
    (* Rewrite spec's three_b_mont to match WP's three_b bignum. *)
    Timeout 300 (let Hv3b := fresh "Hv3b" in
    assert (Hv3b : valid' (toZ (List.map wordof_Z P384f_three_b_mont)))
      by (apply valid_valid'_equiv; exact valid_toZ_wordofZ_three_b_mont);
    first [ rewrite (three_b_mont_rewrite Hv3b)
          | rewrite <- (three_b_mont_rewrite Hv3b) ]).
    (* Rewrite spec's a_mont to match WP's a_const bignum. *)
    Timeout 300 (let Hva := fresh "Hva" in
    assert (Hva : valid' (toZ (List.map wordof_Z P384f_a_mont)))
      by (apply valid_valid'_equiv; exact valid_toZ_wordofZ_a_mont);
    first [ rewrite (a_mont_rewrite Hva)
          | rewrite <- (a_mont_rewrite Hva) ]).
    (* Everything above is the script validated at P-256 (r7,
       2026-08-28) through the constant rewrites; at n = 6 the store,
       fold6 and 40-call phases executed clean (pre-fix run).  The
       remaining goal is the closure algebra: 40 call equations to be
       rewritten into the mont_enc ring ([this_mod'] singles) and
       closed by [ring]; the first sentence-level [this_mod'] exceeds
       300 s at P-256. *)
  Admitted. (* TODO(ring-final): closure algebra — see debug notes
               classes 12-15; the Rupicola bridge route supersedes
               this. *)

End P384_G1_Add_Functor_Instance.
