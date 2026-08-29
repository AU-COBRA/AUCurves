(** * P-256 instantiation of the Rupicola general-a RCB addition.

    Instantiates [CurveAddGeneralA] (the derived 40-op Renes-Costello-
    Batina complete addition with two stack-loaded curve constants) at
    the P-256 field representation [p256_frep] from
    [Bedrock.Field.Synthesis.Examples.p256_prime].

    Contents:
      §1  Montgomery-encoded curve constants a = -3 and 3b as concrete
          felems, with vm_compute proofs (length, unsigned round-trip,
          bounds, feval value).
      §2  [p256_bounds_eq] : loose_bounds = tight_bounds for
          [p256_frep].  This resolves the PORT-CHECK left open in
          CurveAddGeneralA.v: for the New-pipeline word-by-word
          Montgomery representation both bounds are the constructor
          [wordlist] of [bounds_type], so the equation holds by
          [reflexivity].
      §3  The two constant-loader bedrock2 functions "p256_three_b"
          and "p256_a_const" (bodies only; their loader-spec proofs
          are in [CurveAddGeneralA_P256_Loaders.v]).
      §4  [p256_curve_add_general_func] := the derived Rupicola body
          instantiated at P-256, and [p256_curve_add_general_ok]
          discharging [spec_of_rcb_add_general] from
          [rcb_add_general_correct].
      §5  Spec bridge: the Bignum-level specification shape
          ([spec_of_p256_curve_add_general_bignum], the shape of
          [spec_of_P256_G1_add] / [WbwMontgomeryG1GeneralA.spec_of_g1_add]
          at P-256 parameters) and the bridge from the FElem-level
          [spec_of_rcb_add_general].  §5a: feval/Montgomery-decoding
          correspondence, canonicity of valid encodings, Bignum/FElem
          transport.  §5b: [p256_curve_add_general_bignum_bridge_valid_out]
          (Qed) for the shape with valid output buffers on entry, which
          is what [spec_of_rcb_add_general] requires; the unconditional
          shape is not derivable from it (note at §5b).

    Honesty ledger (this file): 0 Admitted.  The unconditional bridge
    [p256_curve_add_general_bignum_bridge] is not stated (not derivable
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
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Curve.P256Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P256_GeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Curve constants                                             *)
  (* ============================================================== *)

  (** Field modulus and curve coefficients as Z literals. *)
  Definition p256_m : Z := Eval vm_compute in
    (2^256 - 2^224 + 2^192 + 2^96 - 1).
  Definition p256_b : Z :=
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b.
  Definition p256_a_Z : Z := Eval vm_compute in ((-3) mod p256_m).
  Definition p256_three_b_Z : Z := Eval vm_compute in ((3 * p256_b) mod p256_m).

  (** Montgomery limbs of 3b and a, from [P256Curve_G1]
      (p256_three_b_mont / p256_a_mont_list, 4 limbs of 64 bits). *)
  Definition p256_tb0 : Z := Eval vm_compute in nth 0 P256Curve_G1.p256_three_b_mont 0.
  Definition p256_tb1 : Z := Eval vm_compute in nth 1 P256Curve_G1.p256_three_b_mont 0.
  Definition p256_tb2 : Z := Eval vm_compute in nth 2 P256Curve_G1.p256_three_b_mont 0.
  Definition p256_tb3 : Z := Eval vm_compute in nth 3 P256Curve_G1.p256_three_b_mont 0.
  Definition p256_ac0 : Z := Eval vm_compute in nth 0 P256Curve_G1.p256_a_mont_list 0.
  Definition p256_ac1 : Z := Eval vm_compute in nth 1 P256Curve_G1.p256_a_mont_list 0.
  Definition p256_ac2 : Z := Eval vm_compute in nth 2 P256Curve_G1.p256_a_mont_list 0.
  Definition p256_ac3 : Z := Eval vm_compute in nth 3 P256Curve_G1.p256_a_mont_list 0.

  Definition p256_three_b_words : list word :=
    [word.of_Z p256_tb0; word.of_Z p256_tb1;
     word.of_Z p256_tb2; word.of_Z p256_tb3].
  Definition p256_a_words : list word :=
    [word.of_Z p256_ac0; word.of_Z p256_ac1;
     word.of_Z p256_ac2; word.of_Z p256_ac3].

  Example p256_three_b_words_eq :
    p256_three_b_words
    = List.map (@word.of_Z 64 word) P256Curve_G1.p256_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Example p256_a_words_eq :
    p256_a_words
    = List.map (@word.of_Z 64 word) P256Curve_G1.p256_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  (** The lists are the spec-side Montgomery encodings. *)
  Example p256_three_b_mont_is_encoding :
    P256Curve_G1.p256_three_b_mont
    = MontgomeryCurveSpecs.three_b_mont_list p256_m 64 4%nat 1 p256_three_b_Z.
  Proof. vm_compute. reflexivity. Qed.

  Example p256_a_mont_is_encoding :
    P256Curve_G1.p256_a_mont_list
    = MontgomeryCurveSpecs.a_mont_list p256_m 64 4%nat 1 p256_a_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_three_b_words_length :
    length p256_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_a_words_length :
    length p256_a_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition p256_three_b_felem : felem :=
    exist _ p256_three_b_words p256_three_b_words_length.
  Definition p256_a_felem : felem :=
    exist _ p256_a_words p256_a_words_length.

  Lemma p256_three_b_words_unsigned :
    List.map word.unsigned p256_three_b_words = P256Curve_G1.p256_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_a_words_unsigned :
    List.map word.unsigned p256_a_words = P256Curve_G1.p256_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_three_b_words_bounded :
    bounded_by loose_bounds p256_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma p256_a_words_bounded :
    bounded_by loose_bounds p256_a_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  (** feval of the stored felems: the Montgomery decoding of the limb
      lists is the curve constant. *)
  Lemma p256_three_b_feval :
    feval (proj1_sig p256_three_b_felem) = F.of_Z M_pos p256_three_b_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma p256_a_feval :
    feval (proj1_sig p256_a_felem) = F.of_Z M_pos p256_a_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Hbounds_eq for p256_frep                                    *)
  (* ============================================================== *)

  (** PORT-CHECK (CurveAddGeneralA.v instantiation plan) resolved:
      for the New-pipeline WBW representation, [loose_bounds] and
      [tight_bounds] are both the constructor [wordlist] of
      [bounds_type] (Crypto.Bedrock.Field.Synthesis.New.
      WordByWordMontgomery, [loose_bounds_eq]/[tight_bounds_eq]), so
      the equation is definitional. *)
  Lemma p256_bounds_eq :
    loose_bounds (FieldRepresentation:=p256_frep)
    = tight_bounds (FieldRepresentation:=p256_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §3. Constant-loader bedrock2 functions                          *)
  (*     Pattern: bls12_three_b (Examples/bls12_three_b.v), 4 limbs. *)
  (* ============================================================== *)

  Definition p256_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p256_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p256_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p256_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p256_tb3)))).

  Definition p256_a_const_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p256_ac0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p256_ac1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p256_ac2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p256_ac3)))).

  Definition p256_three_b_func : Syntax.func :=
    (["out"], [], p256_three_b_loader_body).
  Definition p256_a_const_func : Syntax.func :=
    (["out"], [], p256_a_const_loader_body).

  (* ============================================================== *)
  (* §4. The derived body at P-256, and its spec                     *)
  (* ============================================================== *)

  Definition p256_curve_add_general_func : Syntax.func :=
    rcb_add_general_body "p256_three_b" "p256_a_const".

  (** [spec_of_rcb_add_general] for the instantiated body, from the
      generic derivation correctness [rcb_add_general_correct].  The
      loader-spec hypotheses are discharged in
      [CurveAddGeneralA_P256_Loaders.v]. *)
  Lemma p256_curve_add_general_ok :
    forall functions,
      map.get functions "curve_add_general"
      = Some p256_curve_add_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_three_b_loader p256_three_b_felem "p256_three_b" functions ->
      spec_of_a_loader p256_a_felem "p256_a_const" functions ->
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    (* All explicit arguments of [rcb_add_general_correct] are given
       (the Hbounds_eq and marker binders are anonymous after Section
       discharge; the marker is [True]).  Only the table-membership
       obligation is left as a hole, so that any residual mismatch is
       printed instead of searched for. *)
    unfold p256_curve_add_general_func in Henv.
    Timeout 300 refine
      (rcb_add_general_correct p256_bounds_eq
         p256_three_b_felem "p256_three_b" p256_a_felem "p256_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  (* ============================================================== *)
  (* §5. Spec bridge toward the Bignum-level specification           *)
  (* ============================================================== *)

  Local Notation toZ ws := (List.map word.unsigned ws).
  Local Notation p256_valid := (WordByWordMontgomery.valid 64 4%nat p256_m).

  (** Bignum-level specification of "curve_add_general": the shape of
      [spec_of_P256_G1_add] (P256_G1_Add_Spec.v) and of
      [WbwMontgomeryG1GeneralA.spec_of_g1_add] at the P-256
      parameters, with the same ABI
      [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]. *)
  Definition spec_of_p256_curve_add_general_bignum
    : spec_of "curve_add_general" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2
              wold_outx wold_outy wold_outz : list word)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p256_valid (toZ wX1) /\ p256_valid (toZ wY1) /\
        p256_valid (toZ wZ1) /\ p256_valid (toZ wX2) /\
        p256_valid (toZ wY2) /\ p256_valid (toZ wZ2) ->
        (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
         Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_add_general" tr m0
          [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P256_add_Gallina_spec
                  (toZ wX1) (toZ wY1) (toZ wZ1)
                  (toZ wX2) (toZ wY2) (toZ wZ2)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p256_valid (toZ woutx)
                /\ p256_valid (toZ wouty)
                /\ p256_valid (toZ woutz)) /\
               (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
                Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (* -------------------------------------------------------------- *)
  (* §5a. Bridge ingredients                                          *)
  (* -------------------------------------------------------------- *)

  (** The Montgomery decoding as it occurs in [P256_add_Gallina_spec]:
      the [P256Curve_G1] constants (Local Definitions there, qualified
      access) rather than the literals of [p256_valid]. *)
  Local Notation G_evfrom x :=
    (@WordByWordMontgomery.eval P256Curve_G1.bw P256Curve_G1.n
       (@WordByWordMontgomery.from_montgomerymod
          P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m P256Curve_G1.m' x)).
  Local Notation G_valid :=
    (@WordByWordMontgomery.valid P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m).

  (** The [MontgomeryRingTheory] lemmas at the P-256 parameters
      (section-variable order: m bw n r' m' r'_correct m'_correct
      bw_big n_nz m_small m_big). *)
  Local Notation G_evfrom_mod' :=
    (MontgomeryRingTheory.evfrom_mod'
       P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.r' P256Curve_G1.m'
       P256Curve_G1.r'_correct P256Curve_G1.m'_correct P256Curve_G1.bw_big
       P256Curve_G1.n_nz P256Curve_G1.m_small P256Curve_G1.m_big).
  Local Notation G_valid_valid'_equiv :=
    (MontgomeryRingTheory.valid_valid'_equiv
       P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n
       P256Curve_G1.n_nz P256Curve_G1.m_big).
  Local Notation G_eval_from_mont_mod_inj :=
    (MontgomeryRingTheory.eval_from_mont_mod_inj
       P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.r' P256Curve_G1.m'
       P256Curve_G1.r'_correct P256Curve_G1.m'_correct P256Curve_G1.bw_big
       P256Curve_G1.n_nz P256Curve_G1.m_small P256Curve_G1.m_big).

  (** The fiat-crypto Montgomery constant of [p256_field_parameters]
      is the [P256Curve_G1] one (both are modinv(-m, 2^64) = 1). *)
  Lemma p256_fiat_m'_eq : @Field.m' 64 p256_field_parameters = P256Curve_G1.m'.
  Proof. Timeout 600 vm_compute. reflexivity. Qed.

  Lemma p256_M_eq : Z.pos M_pos = P256Curve_G1.m.
  Proof. Timeout 600 vm_compute. reflexivity. Qed.

  (** [feval] is the Montgomery decoding, reduced mod m. *)
  Lemma p256_feval_evfrom (ws : list word) :
    F.to_Z (feval ws) = G_evfrom (toZ ws) mod P256Curve_G1.m.
  Proof.
    Timeout 600 change (feval ws)
      with (F.of_Z M_pos
              (@WordByWordMontgomery.eval 64 4
                 (@WordByWordMontgomery.from_montgomerymod 64 4 p256_m
                    (@Field.m' 64 p256_field_parameters) (toZ ws)))).
    rewrite p256_fiat_m'_eq, F.to_Z_of_Z, ?p256_M_eq.
    Timeout 600 reflexivity.
  Qed.

  Lemma p256_valid_evfrom_mod (l : list Z) :
    G_valid l -> G_evfrom l mod P256Curve_G1.m = G_evfrom l.
  Proof.
    intros Hv. symmetry. exact (G_evfrom_mod' l Hv).
  Qed.

  Lemma p256_feval_evfrom_valid (ws : list word) :
    p256_valid (toZ ws) -> G_evfrom (toZ ws) = F.to_Z (feval ws).
  Proof.
    intros Hv. rewrite p256_feval_evfrom. symmetry.
    apply p256_valid_evfrom_mod. exact Hv.
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
  Lemma p256_feval_inj (ws1 ws2 : list word) :
    p256_valid (toZ ws1) -> p256_valid (toZ ws2) ->
    feval ws1 = feval ws2 -> ws1 = ws2.
  Proof.
    intros Hv1 Hv2 Heq.
    apply (f_equal F.to_Z) in Heq.
    rewrite !p256_feval_evfrom in Heq.
    assert (Hv1g : G_valid (toZ ws1)) by exact Hv1.
    assert (Hv2g : G_valid (toZ ws2)) by exact Hv2.
    pose proof (proj1 (G_valid_valid'_equiv (toZ ws1)) Hv1g) as Hv1'.
    pose proof (proj1 (G_valid_valid'_equiv (toZ ws2)) Hv2g) as Hv2'.
    pose proof (G_eval_from_mont_mod_inj
                  (MontgomeryRingTheory.enc_mont
                     P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n (toZ ws1) Hv1')
                  (MontgomeryRingTheory.enc_mont
                     P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n (toZ ws2) Hv2')
                  Heq) as Hrec.
    apply map_unsigned_inj.
    exact (f_equal (MontgomeryRingTheory.val
                      P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n) Hrec).
  Qed.

  (** The curve constants: the [eval] of the Gallina-spec partitions
      is [F.to_Z] of the stored felems (closed, by computation). *)
  Lemma p256_a_toZ :
    @WordByWordMontgomery.eval P256Curve_G1.bw P256Curve_G1.n
      (MontgomeryCurveSpecs.a_list P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.a)
    = F.to_Z (feval (proj1_sig p256_a_felem)).
  Proof.
    rewrite p256_a_feval, F.to_Z_of_Z. Timeout 600 vm_compute. reflexivity.
  Qed.

  Lemma p256_three_b_toZ :
    @WordByWordMontgomery.eval P256Curve_G1.bw P256Curve_G1.n
      (MontgomeryCurveSpecs.three_b_list
         P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.three_b)
    = F.to_Z (feval (proj1_sig p256_three_b_felem)).
  Proof.
    rewrite p256_three_b_feval, F.to_Z_of_Z. Timeout 600 vm_compute. reflexivity.
  Qed.

  (** Memory-predicate transport, pointwise. *)
  Lemma p256_Bignum_to_FElem2 (p : word) (ws : list word) :
    p256_valid (toZ ws) ->
    Lift1Prop.impl1 (Bignum 4 p ws)
                    (Compilation2.FElem (Some tight_bounds) p (feval ws)).
  Proof.
    intros Hv mm HB.
    unfold Bignum in HB. apply sep_emp_l in HB. destruct HB as [Hlen Harr].
    change 4%nat with (felem_size_in_words (FieldRepresentation:=p256_frep)) in Hlen.
    unfold Compilation2.FElem, Lift1Prop.ex1.
    exists (exist _ ws Hlen).
    apply sep_emp_l. split; [split; [reflexivity | exact Hv] | exact Harr].
  Qed.

  Lemma p256_FElem2_to_Bignum (p : word) (v : F) (mm : BasicC64Semantics.mem) :
    Compilation2.FElem (Some tight_bounds) p v mm ->
    exists ws : list word,
      feval ws = v /\ p256_valid (toZ ws) /\ Bignum 4 p ws mm.
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
  Lemma p256_pre_bridge
        (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
        (wX1 wY1 wZ1 wX2 wY2 wZ2 wox woy woz : list word)
        (R : BasicC64Semantics.mem -> Prop) :
    p256_valid (toZ wX1) -> p256_valid (toZ wY1) -> p256_valid (toZ wZ1) ->
    p256_valid (toZ wX2) -> p256_valid (toZ wY2) -> p256_valid (toZ wZ2) ->
    p256_valid (toZ wox) -> p256_valid (toZ woy) -> p256_valid (toZ woz) ->
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
      first [ apply p256_Bignum_to_FElem2; assumption | reflexivity ].
  Qed.

  (* -------------------------------------------------------------- *)
  (* §5b. The bridge                                                  *)
  (* -------------------------------------------------------------- *)

  (** The Bignum-level specification with the three output buffers
      required to hold valid (canonical) encodings on entry.

      [spec_of_rcb_add_general] (CurveAddGeneralA.v) requires
      [FElem (Some tight_bounds) poutx outxold] for the output buffers,
      i.e. [bounded_by tight_bounds] = [p256_valid] of their old
      contents.  [spec_of_p256_curve_add_general_bignum] above makes no
      assumption on [wold_outx]; a function that satisfies the
      FElem-level spec but misbehaves on non-canonical output buffers
      is not excluded by the hypothesis, so the bridge to the
      unconditional shape is not derivable from
      [spec_of_rcb_add_general] alone.  This variant is the derivable
      one. *)
  Definition spec_of_p256_curve_add_general_bignum_valid_out
    : spec_of "curve_add_general" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2
              wold_outx wold_outy wold_outz : list word)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p256_valid (toZ wX1) /\ p256_valid (toZ wY1) /\
        p256_valid (toZ wZ1) /\ p256_valid (toZ wX2) /\
        p256_valid (toZ wY2) /\ p256_valid (toZ wZ2) /\
        p256_valid (toZ wold_outx) /\ p256_valid (toZ wold_outy) /\
        p256_valid (toZ wold_outz) ->
        (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
         Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_add_general" tr m0
          [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P256_add_Gallina_spec
                  (toZ wX1) (toZ wY1) (toZ wZ1)
                  (toZ wX2) (toZ wY2) (toZ wZ2)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p256_valid (toZ woutx)
                /\ p256_valid (toZ wouty)
                /\ p256_valid (toZ woutz)) /\
               (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
                Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (** Bridge from the FElem-level derived spec to the Bignum shape.
      1. pre-transport ([p256_pre_bridge]); 2. the FElem-level spec at
      [X1 := feval wX1] etc.; 3. post-transport by destructing the sep
      chain, [p256_FElem2_to_Bignum] on each clause, canonicity
      ([p256_feval_inj]) for the six preserved inputs, and
      [rebuild_sep]; 4. algebra by the generic
      [rcb_general_a_gallina_to_Z] (CurveAddGeneralA_GallinaToZ.v),
      whose premises are the Montgomery-decoding identities
      ([p256_feval_evfrom_valid]) and the constant identifications. *)
  Theorem p256_curve_add_general_bignum_bridge_valid_out :
    forall functions,
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions ->
      spec_of_p256_curve_add_general_bignum_valid_out functions.
  Proof.
    intros functions Hspec.
    unfold spec_of_p256_curve_add_general_bignum_valid_out.
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
                  (p256_pre_bridge pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz
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
               apply p256_FElem2_to_Bignum in H; destruct H as (? & ? & ? & ?)
           end.
    (* the six inputs are preserved: canonicity *)
    repeat match goal with
           | Hfe : feval ?ws = feval ?w,
             Hv1 : p256_valid (toZ ?ws), Hv2 : p256_valid (toZ ?w) |- _ =>
               assert (ws = w) by (apply p256_feval_inj; assumption);
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
       [feval (proj1_sig p256_a_felem)] etc. by conversion. *)
    try unfold P256_add_Gallina_spec.
    Timeout 600 refine
      (rcb_general_a_gallina_to_Z (field_parameters := p256_field_parameters)
         P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m'
         P256Curve_G1.a P256Curve_G1.three_b p256_M_eq
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ _ _ _ _ Hgal).
    Show.
    (* Each premise is closed by the one intended term, chosen by the
       goal's shape; no tactic may fall through to a unification that
       unfolds the Montgomery code. *)
    all: timeout 60
      (lazymatch goal with
       | |- G_evfrom (toZ ?w) = F.to_Z (feval ?w) =>
           exact (p256_feval_evfrom_valid w ltac:(assumption))
       | |- G_evfrom (toZ ?w) = F.to_Z ?o =>
           lazymatch goal with
           | H : feval w = o |- _ =>
               exact (eq_trans (p256_feval_evfrom_valid w ltac:(assumption))
                               (f_equal F.to_Z H))
           end
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.a_list _ _ _) = _ =>
           exact p256_a_toZ
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.three_b_list _ _ _) = _ =>
           exact p256_three_b_toZ
       | |- ?G => fail 99 "BRIDGE-RESIDUAL" G
       end).
  Qed.

  (** The unconditional shape, NOT stated as a theorem.

      <<
      Theorem p256_curve_add_general_bignum_bridge :
        forall functions,
          spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions ->
          spec_of_p256_curve_add_general_bignum functions.
      >>

      is not derivable from [spec_of_rcb_add_general]: that spec
      requires [FElem (Some tight_bounds) poutx outxold] for the three
      output buffers, i.e. canonical ([p256_valid]) old contents, and
      says nothing about a call on non-canonical output buffers, while
      [spec_of_p256_curve_add_general_bignum] assumes nothing about
      [wold_outx]/[wold_outy]/[wold_outz].  A function satisfying the
      FElem-level spec and misbehaving on non-canonical output buffers
      is a model of the hypothesis and a counter-model of the
      conclusion.  Downstream users take
      [p256_curve_add_general_bignum_bridge_valid_out] (Qed above); the
      unconditional shape would need the derivation in
      CurveAddGeneralA.v to require only [FElem None] for the outputs. *)

End P256_GeneralA.
