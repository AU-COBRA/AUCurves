(** * P-224 instantiation of the Rupicola general-a RCB addition.

    Parallel to [CurveAddGeneralA_P256.v] /
    [CurveAddGeneralA_P256_Loaders.v], at the P-224 field
    representation [p224_frep] from
    [Bedrock.Field.Synthesis.Examples.p224_field]
    (prefix "p224_coord_", 4 limbs of 64 bits, m = 2^224 - 2^96 + 1,
    m' = 2^64 - 1).

    COMPILE-DEFERRED: this file's build needs p224_field.vo (never
    built; its [make_computed_op] synthesis is the expensive step),
    which in turn needs a rebuild of the stale p224_prime.vo
    (2026-05-22, pre-dating the 2026-08-11 stdlib install; dune
    rebuilds it on demand).  P224Curve_G1.vo is built.  The file is
    written so that it compiles unchanged once p224_field.vo is in
    place.

    §5 (port of CurveAddGeneralA_P256.v §5): feval/Montgomery-decoding
    correspondence, canonicity of valid encodings, Bignum/FElem
    transport, and [p224_curve_add_general_bignum_bridge_valid_out]
    (Qed once compiled) for the Bignum shape with valid output buffers
    on entry, which is what [spec_of_rcb_add_general] requires.

    Honesty ledger (this file): 0 Admitted.  The unconditional bridge
    [p224_curve_add_general_bignum_bridge] is not stated (not derivable
    from the FElem-level spec; comment at the end of §5b). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.Memory.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_GallinaToZ.
Require Import Bedrock.Field.Synthesis.Examples.p224_field.
Require Import Bedrock.Curve.P224Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P224_GeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p224_field_parameters
    p224_field_parameters_ok
    p224_frep
    p224_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Curve constants                                             *)
  (* ============================================================== *)

  Definition p224_m : Z := Eval vm_compute in (2^224 - 2^96 + 1).
  Definition p224_b : Z :=
    0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4.
  Definition p224_a_Z : Z := Eval vm_compute in ((-3) mod p224_m).
  Definition p224_three_b_Z : Z := Eval vm_compute in ((3 * p224_b) mod p224_m).

  Definition p224_tb0 : Z := Eval vm_compute in nth 0 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb1 : Z := Eval vm_compute in nth 1 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb2 : Z := Eval vm_compute in nth 2 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb3 : Z := Eval vm_compute in nth 3 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_ac0 : Z := Eval vm_compute in nth 0 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac1 : Z := Eval vm_compute in nth 1 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac2 : Z := Eval vm_compute in nth 2 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac3 : Z := Eval vm_compute in nth 3 P224Curve_G1.p224_a_mont_list 0.

  Definition p224_three_b_words : list word :=
    [word.of_Z p224_tb0; word.of_Z p224_tb1;
     word.of_Z p224_tb2; word.of_Z p224_tb3].
  Definition p224_a_words : list word :=
    [word.of_Z p224_ac0; word.of_Z p224_ac1;
     word.of_Z p224_ac2; word.of_Z p224_ac3].

  Example p224_three_b_words_eq :
    p224_three_b_words
    = List.map (@word.of_Z 64 word) P224Curve_G1.p224_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_a_words_eq :
    p224_a_words
    = List.map (@word.of_Z 64 word) P224Curve_G1.p224_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_three_b_mont_is_encoding :
    P224Curve_G1.p224_three_b_mont
    = MontgomeryCurveSpecs.three_b_mont_list p224_m 64 4%nat
        18446744073709551615 p224_three_b_Z.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_a_mont_is_encoding :
    P224Curve_G1.p224_a_mont_list
    = MontgomeryCurveSpecs.a_mont_list p224_m 64 4%nat
        18446744073709551615 p224_a_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_three_b_words_length :
    length p224_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_a_words_length :
    length p224_a_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition p224_three_b_felem : felem :=
    exist _ p224_three_b_words p224_three_b_words_length.
  Definition p224_a_felem : felem :=
    exist _ p224_a_words p224_a_words_length.

  Lemma p224_three_b_words_unsigned :
    List.map word.unsigned p224_three_b_words = P224Curve_G1.p224_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_a_words_unsigned :
    List.map word.unsigned p224_a_words = P224Curve_G1.p224_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_three_b_words_bounded :
    bounded_by loose_bounds p224_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma p224_a_words_bounded :
    bounded_by loose_bounds p224_a_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma p224_three_b_feval :
    feval (proj1_sig p224_three_b_felem) = F.of_Z M_pos p224_three_b_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma p224_a_feval :
    feval (proj1_sig p224_a_felem) = F.of_Z M_pos p224_a_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Hbounds_eq for p224_frep                                    *)
  (* ============================================================== *)

  Lemma p224_bounds_eq :
    loose_bounds (FieldRepresentation:=p224_frep)
    = tight_bounds (FieldRepresentation:=p224_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §3. Constant-loader bedrock2 functions (4 limbs)                *)
  (* ============================================================== *)

  Definition p224_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p224_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p224_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p224_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p224_tb3)))).

  Definition p224_a_const_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p224_ac0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p224_ac1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p224_ac2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p224_ac3)))).

  Definition p224_three_b_func : Syntax.func :=
    (["out"], [], p224_three_b_loader_body).
  Definition p224_a_const_func : Syntax.func :=
    (["out"], [], p224_a_const_loader_body).

  (** Loader-spec proofs: the 4-limb P-256 loader script
      (CurveAddGeneralA_P256_Loaders.v), verbatim modulo names. *)
  Lemma p224_three_b_loader_ok :
    forall functions,
      map.get functions "p224_three_b" = Some p224_three_b_func ->
      spec_of_three_b_loader p224_three_b_felem "p224_three_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_three_b_loader].
    intros pout outold Rout tr mem0 Hpre.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func p224_three_b_func p224_three_b_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p224_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p224_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [p224_three_b_felem p224_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  Lemma p224_a_loader_ok :
    forall functions,
      map.get functions "p224_a_const" = Some p224_a_const_func ->
      spec_of_a_loader p224_a_felem "p224_a_const" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_a_loader].
    intros pout outold Rout tr mem0 Hpre.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func p224_a_const_func p224_a_const_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p224_a_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p224_a_words_bounded
      | |- _ => idtac
      end.
    cbv [p224_a_felem p224_a_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  (* ============================================================== *)
  (* §4. The derived body at P-224, and its spec                     *)
  (* ============================================================== *)

  Definition p224_curve_add_general_func : Syntax.func :=
    rcb_add_general_body "p224_three_b" "p224_a_const".

  Lemma p224_curve_add_general_ok :
    forall functions,
      map.get functions "curve_add_general"
      = Some p224_curve_add_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_three_b_loader p224_three_b_felem "p224_three_b" functions ->
      spec_of_a_loader p224_a_felem "p224_a_const" functions ->
      spec_of_rcb_add_general p224_three_b_felem p224_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold p224_curve_add_general_func in Henv.
    Timeout 300 refine
      (rcb_add_general_correct p224_bounds_eq
         p224_three_b_felem "p224_three_b" p224_a_felem "p224_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  (* ============================================================== *)
  (* §5. Spec bridge toward the Bignum-level specification           *)
  (* ============================================================== *)

  Local Notation toZ ws := (List.map word.unsigned ws).
  Local Notation p224_valid := (WordByWordMontgomery.valid 64 4%nat p224_m).

  Definition spec_of_p224_curve_add_general_bignum
    : spec_of "curve_add_general" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2
              wold_outx wold_outy wold_outz : list word)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p224_valid (toZ wX1) /\ p224_valid (toZ wY1) /\
        p224_valid (toZ wZ1) /\ p224_valid (toZ wX2) /\
        p224_valid (toZ wY2) /\ p224_valid (toZ wZ2) ->
        (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
         Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_add_general" tr m0
          [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P224_add_Gallina_spec
                  (toZ wX1) (toZ wY1) (toZ wZ1)
                  (toZ wX2) (toZ wY2) (toZ wZ2)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p224_valid (toZ woutx)
                /\ p224_valid (toZ wouty)
                /\ p224_valid (toZ woutz)) /\
               (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
                Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (* -------------------------------------------------------------- *)
  (* §5a. Bridge ingredients (port of CurveAddGeneralA_P256.v §5a)    *)
  (* -------------------------------------------------------------- *)

  (** The Montgomery decoding as it occurs in [P224_add_Gallina_spec]:
      the [P224Curve_G1] constants (Local Definitions there, qualified
      access) rather than the literals of [p224_valid]. *)
  Local Notation G_evfrom x :=
    (@WordByWordMontgomery.eval P224Curve_G1.bw P224Curve_G1.n
       (@WordByWordMontgomery.from_montgomerymod
          P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.m P224Curve_G1.m' x)).
  Local Notation G_valid :=
    (@WordByWordMontgomery.valid P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.m).

  (** The [MontgomeryRingTheory] lemmas at the P-224 parameters
      (section-variable order: m bw n r' m' r'_correct m'_correct
      bw_big n_nz m_small m_big). *)
  Local Notation G_evfrom_mod' :=
    (MontgomeryRingTheory.evfrom_mod'
       P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.r' P224Curve_G1.m'
       P224Curve_G1.r'_correct P224Curve_G1.m'_correct P224Curve_G1.bw_big
       P224Curve_G1.n_nz P224Curve_G1.m_small P224Curve_G1.m_big).
  Local Notation G_valid_valid'_equiv :=
    (MontgomeryRingTheory.valid_valid'_equiv
       P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n
       P224Curve_G1.n_nz P224Curve_G1.m_big).
  Local Notation G_eval_from_mont_mod_inj :=
    (MontgomeryRingTheory.eval_from_mont_mod_inj
       P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.r' P224Curve_G1.m'
       P224Curve_G1.r'_correct P224Curve_G1.m'_correct P224Curve_G1.bw_big
       P224Curve_G1.n_nz P224Curve_G1.m_small P224Curve_G1.m_big).

  (** The fiat-crypto Montgomery constant of [p224_field_parameters]
      is the [P224Curve_G1] one (both are modinv(-m, 2^64) = 2^64 - 1). *)
  Lemma p224_fiat_m'_eq : @Field.m' 64 p224_field_parameters = P224Curve_G1.m'.
  Proof. Timeout 600 vm_compute. reflexivity. Qed.

  Lemma p224_M_eq : Z.pos M_pos = P224Curve_G1.m.
  Proof. Timeout 600 vm_compute. reflexivity. Qed.

  (** [feval] is the Montgomery decoding, reduced mod m. *)
  Lemma p224_feval_evfrom (ws : list word) :
    F.to_Z (feval ws) = G_evfrom (toZ ws) mod P224Curve_G1.m.
  Proof.
    Timeout 600 change (feval ws)
      with (F.of_Z M_pos
              (@WordByWordMontgomery.eval 64 4
                 (@WordByWordMontgomery.from_montgomerymod 64 4 p224_m
                    (@Field.m' 64 p224_field_parameters) (toZ ws)))).
    rewrite p224_fiat_m'_eq, F.to_Z_of_Z, ?p224_M_eq.
    Timeout 600 reflexivity.
  Qed.

  Lemma p224_valid_evfrom_mod (l : list Z) :
    G_valid l -> G_evfrom l mod P224Curve_G1.m = G_evfrom l.
  Proof.
    intros Hv. symmetry. exact (G_evfrom_mod' l Hv).
  Qed.

  Lemma p224_feval_evfrom_valid (ws : list word) :
    p224_valid (toZ ws) -> G_evfrom (toZ ws) = F.to_Z (feval ws).
  Proof.
    intros Hv. rewrite p224_feval_evfrom. symmetry.
    apply p224_valid_evfrom_mod. exact Hv.
  Qed.

  Lemma map_unsigned_inj (l1 l2 : list word) :
    List.map word.unsigned l1 = List.map word.unsigned l2 -> l1 = l2.
  Proof.
    revert l2; induction l1 as [|a l1 IH]; intros [|b l2] H;
      cbn [List.map] in H; try discriminate; [reflexivity|].
    injection H as Ha Hl.
    f_equal; [apply word.unsigned_inj; exact Ha | apply IH; exact Hl].
  Qed.

  (** Valid Montgomery encodings with the same [feval] are equal
      word lists (canonicity of the representation). *)
  Lemma p224_feval_inj (ws1 ws2 : list word) :
    p224_valid (toZ ws1) -> p224_valid (toZ ws2) ->
    feval ws1 = feval ws2 -> ws1 = ws2.
  Proof.
    intros Hv1 Hv2 Heq.
    apply (f_equal F.to_Z) in Heq.
    rewrite !p224_feval_evfrom in Heq.
    assert (Hv1g : G_valid (toZ ws1)) by exact Hv1.
    assert (Hv2g : G_valid (toZ ws2)) by exact Hv2.
    pose proof (proj1 (G_valid_valid'_equiv (toZ ws1)) Hv1g) as Hv1'.
    pose proof (proj1 (G_valid_valid'_equiv (toZ ws2)) Hv2g) as Hv2'.
    pose proof (G_eval_from_mont_mod_inj
                  (MontgomeryRingTheory.enc_mont
                     P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n (toZ ws1) Hv1')
                  (MontgomeryRingTheory.enc_mont
                     P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n (toZ ws2) Hv2')
                  Heq) as Hrec.
    apply map_unsigned_inj.
    exact (f_equal (MontgomeryRingTheory.val
                      P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n) Hrec).
  Qed.

  (** The curve constants: the [eval] of the Gallina-spec partitions
      is [F.to_Z] of the stored felems (closed, by computation). *)
  Lemma p224_a_toZ :
    @WordByWordMontgomery.eval P224Curve_G1.bw P224Curve_G1.n
      (MontgomeryCurveSpecs.a_list P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.a)
    = F.to_Z (feval (proj1_sig p224_a_felem)).
  Proof.
    rewrite p224_a_feval, F.to_Z_of_Z. Timeout 600 vm_compute. reflexivity.
  Qed.

  Lemma p224_three_b_toZ :
    @WordByWordMontgomery.eval P224Curve_G1.bw P224Curve_G1.n
      (MontgomeryCurveSpecs.three_b_list
         P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.three_b)
    = F.to_Z (feval (proj1_sig p224_three_b_felem)).
  Proof.
    rewrite p224_three_b_feval, F.to_Z_of_Z. Timeout 600 vm_compute. reflexivity.
  Qed.

  (** Memory-predicate transport, pointwise. *)
  Lemma p224_Bignum_to_FElem2 (p : word) (ws : list word) :
    p224_valid (toZ ws) ->
    Lift1Prop.impl1 (Bignum 4 p ws)
                    (Compilation2.FElem (Some tight_bounds) p (feval ws)).
  Proof.
    intros Hv mm HB.
    unfold Bignum in HB. apply sep_emp_l in HB. destruct HB as [Hlen Harr].
    change 4%nat with (felem_size_in_words (FieldRepresentation:=p224_frep)) in Hlen.
    unfold Compilation2.FElem, Lift1Prop.ex1.
    exists (exist _ ws Hlen).
    apply sep_emp_l. split; [split; [reflexivity | exact Hv] | exact Harr].
  Qed.

  Lemma p224_FElem2_to_Bignum (p : word) (v : F) (mm : BasicC64Semantics.mem) :
    Compilation2.FElem (Some tight_bounds) p v mm ->
    exists ws : list word,
      feval ws = v /\ p224_valid (toZ ws) /\ Bignum 4 p ws mm.
  Proof.
    intros HF.
    unfold Compilation2.FElem, Lift1Prop.ex1 in HF.
    destruct HF as [[ws Hlen] HF].
    apply sep_emp_l in HF. destruct HF as [[Hfe Hbd] Harr].
    exists ws.
    split; [exact Hfe|]. split; [exact Hbd|].
    unfold Bignum. apply sep_emp_l. split; [exact Hlen | exact Harr].
  Qed.

  Lemma sep_impl1_both (p p' q q' : BasicC64Semantics.mem -> Prop) :
    Lift1Prop.impl1 p p' -> Lift1Prop.impl1 q q' ->
    Lift1Prop.impl1 (p * q)%sep (p' * q')%sep.
  Proof.
    intros H1 H2 mm (m1 & m2 & Hs & Hp & Hq).
    unfold sep. exists m1, m2.
    split; [exact Hs | split; [exact (H1 _ Hp) | exact (H2 _ Hq)]].
  Qed.

  Lemma sep_intro' (P Q : BasicC64Semantics.mem -> Prop)
        (mm m1 m2 : BasicC64Semantics.mem) :
    map.split mm m1 m2 -> P m1 -> Q m2 -> (P * Q)%sep mm.
  Proof. intros Hs HP HQ. unfold sep. exists m1, m2. auto. Qed.

  (** Rebuild a left-nested sep chain from its destructed pieces
      (one [map.split] hypothesis per intermediate memory). *)
  Local Ltac rebuild_sep :=
    lazymatch goal with
    | |- sep _ _ _ => eapply sep_intro'; [eassumption | rebuild_sep | rebuild_sep]
    | |- _ => assumption
    end.

  (** Pre-transport of the nine input Bignums (all valid) to the
      [Compilation2.FElem (Some tight_bounds)] chain of
      [spec_of_rcb_add_general]. *)
  Lemma p224_pre_bridge
        (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
        (wX1 wY1 wZ1 wX2 wY2 wZ2 wox woy woz : list word)
        (R : BasicC64Semantics.mem -> Prop) :
    p224_valid (toZ wX1) -> p224_valid (toZ wY1) -> p224_valid (toZ wZ1) ->
    p224_valid (toZ wX2) -> p224_valid (toZ wY2) -> p224_valid (toZ wZ2) ->
    p224_valid (toZ wox) -> p224_valid (toZ woy) -> p224_valid (toZ woz) ->
    Lift1Prop.impl1
      (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
       Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
       Bignum 4 poutx wox * Bignum 4 pouty woy * Bignum 4 poutz woz * R)%sep
      (Compilation2.FElem (Some tight_bounds) pX1 (feval wX1)
       * Compilation2.FElem (Some tight_bounds) pY1 (feval wY1)
       * Compilation2.FElem (Some tight_bounds) pZ1 (feval wZ1)
       * Compilation2.FElem (Some tight_bounds) pX2 (feval wX2)
       * Compilation2.FElem (Some tight_bounds) pY2 (feval wY2)
       * Compilation2.FElem (Some tight_bounds) pZ2 (feval wZ2)
       * Compilation2.FElem (Some tight_bounds) poutx (feval wox)
       * Compilation2.FElem (Some tight_bounds) pouty (feval woy)
       * Compilation2.FElem (Some tight_bounds) poutz (feval woz) * R)%sep.
  Proof.
    intros.
    repeat apply sep_impl1_both;
      first [ apply p224_Bignum_to_FElem2; assumption | reflexivity ].
  Qed.

  (* -------------------------------------------------------------- *)
  (* §5b. The bridge                                                  *)
  (* -------------------------------------------------------------- *)

  (** The Bignum-level specification with the three output buffers
      required to hold valid (canonical) encodings on entry.

      [spec_of_rcb_add_general] (CurveAddGeneralA.v) requires
      [FElem (Some tight_bounds) poutx outxold] for the output buffers,
      i.e. [bounded_by tight_bounds] = [p224_valid] of their old
      contents.  [spec_of_p224_curve_add_general_bignum] above makes no
      assumption on [wold_outx]; a function that satisfies the
      FElem-level spec but misbehaves on non-canonical output buffers
      is not excluded by the hypothesis, so the bridge to the
      unconditional shape is not derivable from
      [spec_of_rcb_add_general] alone.  This variant is the derivable
      one. *)
  Definition spec_of_p224_curve_add_general_bignum_valid_out
    : spec_of "curve_add_general" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2
              wold_outx wold_outy wold_outz : list word)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p224_valid (toZ wX1) /\ p224_valid (toZ wY1) /\
        p224_valid (toZ wZ1) /\ p224_valid (toZ wX2) /\
        p224_valid (toZ wY2) /\ p224_valid (toZ wZ2) /\
        p224_valid (toZ wold_outx) /\ p224_valid (toZ wold_outy) /\
        p224_valid (toZ wold_outz) ->
        (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
         Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_add_general" tr m0
          [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P224_add_Gallina_spec
                  (toZ wX1) (toZ wY1) (toZ wZ1)
                  (toZ wX2) (toZ wY2) (toZ wZ2)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p224_valid (toZ woutx)
                /\ p224_valid (toZ wouty)
                /\ p224_valid (toZ woutz)) /\
               (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
                Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (** Bridge from the FElem-level derived spec to the Bignum shape.
      1. pre-transport ([p224_pre_bridge]); 2. the FElem-level spec at
      [X1 := feval wX1] etc.; 3. post-transport by destructing the sep
      chain, [p224_FElem2_to_Bignum] on each clause, canonicity
      ([p224_feval_inj]) for the six preserved inputs, and
      [rebuild_sep]; 4. algebra by the generic
      [rcb_general_a_gallina_to_Z] (CurveAddGeneralA_GallinaToZ.v),
      whose premises are the Montgomery-decoding identities
      ([p224_feval_evfrom_valid]) and the constant identifications. *)
  Theorem p224_curve_add_general_bignum_bridge_valid_out :
    forall functions,
      spec_of_rcb_add_general p224_three_b_felem p224_a_felem functions ->
      spec_of_p224_curve_add_general_bignum_valid_out functions.
  Proof.
    intros functions Hspec.
    unfold spec_of_p224_curve_add_general_bignum_valid_out.
    intros wX1 wY1 wZ1 wX2 wY2 wZ2 wold_outx wold_outy wold_outz
           pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz tr m0 Rout
           Hvalid Hsep.
    destruct Hvalid as (HvX1 & HvY1 & HvZ1 & HvX2 & HvY2 & HvZ2 & Hvox & Hvoy & Hvoz).
    (* 1+2: pre-transport and the FElem-level call *)
    cbv [spec_of_rcb_add_general] in Hspec.
    specialize (Hspec poutx pouty poutz pX1 pY1 pZ1 pX2 pY2 pZ2
                  (feval wX1) (feval wY1) (feval wZ1)
                  (feval wX2) (feval wY2) (feval wZ2)
                  (feval wold_outx) (feval wold_outy) (feval wold_outz)
                  Rout tr m0).
    specialize (Hspec
                  (p224_pre_bridge pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz
                     wX1 wY1 wZ1 wX2 wY2 wZ2 wold_outx wold_outy wold_outz Rout
                     HvX1 HvY1 HvZ1 HvX2 HvY2 HvZ2 Hvox Hvoy Hvoz m0 Hsep)).
    eapply WeakestPreconditionProperties.Proper_call; [ | exact Hspec ].
    intros tr' m' rets Hpost.
    cbv beta in Hpost.
    destruct Hpost as (Hrets & Htr & outx & outy & outz & Hgal & Hsep').
    clear Hspec Hsep.
    cbv beta.
    split; [exact Htr|]. split; [exact Hrets|].
    (* 3: post-transport *)
    repeat match goal with
           | H : sep _ _ _ |- _ => destruct H as (? & ? & ? & ? & ?)
           end.
    repeat match goal with
           | H : _ |- _ =>
               apply p224_FElem2_to_Bignum in H; destruct H as (? & ? & ? & ?)
           end.
    (* the six inputs are preserved: canonicity *)
    repeat match goal with
           | Hfe : feval ?ws = feval ?w,
             Hv1 : p224_valid (toZ ?ws), Hv2 : p224_valid (toZ ?w) |- _ =>
               assert (ws = w) by (apply p224_feval_inj; assumption);
               subst ws; clear Hfe
           end.
    lazymatch goal with
    | Hx : feval ?wx = outx, Hy : feval ?wy = outy, Hz : feval ?wz = outz |- _ =>
        exists wx, wy, wz
    end.
    split; [ | rebuild_sep ].
    split; [ | split; [assumption | split; assumption] ].
    (* 4: algebra, by the generic F-level lemma; the constants
       [a_val]/[three_b_val] of the derived spec unfold to
       [feval (proj1_sig p224_a_felem)] etc. by conversion. *)
    try unfold P224_add_Gallina_spec.
    Timeout 600 refine
      (rcb_general_a_gallina_to_Z (field_parameters := p224_field_parameters)
         P224Curve_G1.m P224Curve_G1.bw P224Curve_G1.n P224Curve_G1.m'
         P224Curve_G1.a P224Curve_G1.three_b p224_M_eq
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ _ _ _ _ Hgal).
    Show.
    (* Each premise is closed by the one intended term, chosen by the
       goal's shape; no tactic may fall through to a unification that
       unfolds the Montgomery code. *)
    all: timeout 60
      (lazymatch goal with
       | |- G_evfrom (toZ ?w) = F.to_Z (feval ?w) =>
           exact (p224_feval_evfrom_valid w ltac:(assumption))
       | |- G_evfrom (toZ ?w) = F.to_Z ?o =>
           lazymatch goal with
           | H : feval w = o |- _ =>
               exact (eq_trans (p224_feval_evfrom_valid w ltac:(assumption))
                               (f_equal F.to_Z H))
           end
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.a_list _ _ _) = _ =>
           exact p224_a_toZ
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.three_b_list _ _ _) = _ =>
           exact p224_three_b_toZ
       | |- ?G => fail 99 "BRIDGE-RESIDUAL" G
       end).
  Qed.

  (** The unconditional shape, NOT stated as a theorem.

      <<
      Theorem p224_curve_add_general_bignum_bridge :
        forall functions,
          spec_of_rcb_add_general p224_three_b_felem p224_a_felem functions ->
          spec_of_p224_curve_add_general_bignum functions.
      >>

      is not derivable from [spec_of_rcb_add_general]: that spec
      requires [FElem (Some tight_bounds) poutx outxold] for the three
      output buffers, i.e. canonical ([p224_valid]) old contents, and
      says nothing about a call on non-canonical output buffers, while
      [spec_of_p224_curve_add_general_bignum] assumes nothing about
      [wold_outx]/[wold_outy]/[wold_outz].  A function satisfying the
      FElem-level spec and misbehaving on non-canonical output buffers
      is a model of the hypothesis and a counter-model of the
      conclusion.  Downstream users take
      [p224_curve_add_general_bignum_bridge_valid_out] (Qed above); the
      unconditional shape would need the derivation in
      CurveAddGeneralA.v to require only [FElem None] for the outputs. *)

End P224_GeneralA.
