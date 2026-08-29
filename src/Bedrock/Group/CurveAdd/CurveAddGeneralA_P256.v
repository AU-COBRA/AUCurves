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
          at P-256 parameters) and the bridge theorem from the
          FElem-level [spec_of_rcb_add_general].  The bridge statement
          compiles; its proof is Admitted with the proof path recorded.

    Honesty ledger (this file): 1 Admitted —
    [p256_curve_add_general_bignum_bridge] (§5). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import coqutil.Word.Interface.
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
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
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

  (** Bridge from the FElem-level derived spec to the Bignum shape.

      Proof path (recorded; sep plumbing deferred):
      1. Pre-transport.  From [Bignum 4 p ws] extract
         [length ws = 4 = felem_size_in_words]; then
         [Field.FElem p (exist ws Hlen)] is definitionally
         [array scalar _ p ws] (= Bignum minus the length emp;
         [P256_Bignum_Specs.p256_Bignum_to_FElem]).  With
         [bounded_by tight_bounds ws = p256_valid (toZ ws)]
         (New-pipeline [tight_bounds_eq]) this packages
         [Compilation2.FElem (Some tight_bounds) p (feval ws)].
      2. Apply the hypothesis [spec_of_rcb_add_general] at
         X1 := feval wX1 etc.; its own preconditions are exactly the
         nine packaged FElems.
      3. Post-transport.  Each output
         [FElem (Some tight_bounds) poutx outx] yields a felem
         witness [wsoutx] with [feval wsoutx = outx],
         [p256_valid (toZ wsoutx)], and the Bignum reassembled from
         the array plus the length component of the felem.
      4. Algebra.  [rcb_add_general_gallina a_val three_b_val
         (feval wX1) ... = (outx, outy, outz)] implies
         [P256_add_Gallina_spec (toZ wX1) ... (toZ wsoutx) ...]:
         both sides are the same 40-op RCB chain, the left over
         [F M_pos], the right as mod-m equations on Montgomery
         decodings; the correspondence is feval-chain pushing
         through the 40 ops (the [BLS12_add_specs_equiv'] route of
         [MontgomeryCurveG1Equiv], with [p256_three_b_feval] /
         [p256_a_feval] fixing the constants). *)
  Theorem p256_curve_add_general_bignum_bridge :
    forall functions,
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions ->
      spec_of_p256_curve_add_general_bignum functions.
  Proof.
  Admitted.

End P256_GeneralA.
