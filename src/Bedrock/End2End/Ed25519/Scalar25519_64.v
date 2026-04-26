(** * Ed25519 scalar field [F l] (l = 2^252 + 27742317777372353535851937790883648493).
 *
 * Two layers in this file:
 *   1. [Ed25519Scalar]: pure-algebra re-exports ([prime_l], [field_l],
 *      [scalar_inv_eq_pow]); cited from Lean's
 *      [Ed25519Spec.lean::interp_scalar_inv_pow] axiom.
 *   2. [Ed25519ScalarBedrock]: bedrock2 function names + [spec_of_*]
 *      correctness *parameters* for mul/add/sub/from_bytes/to_bytes.
 *      The actual fiat-crypto WordByWordMontgomery synthesis lives in
 *      [Scalar25519_64_Synthesis.v.todo]; that file currently builds in
 *      ~15-30 min on rocq-9 (because [(mode vo)] in the dune theory
 *      forces [-native-compiler off], so [make_computed_op] falls
 *      back from [native_compute] to [vm_compute]). To keep Phase 1.3
 *      (Sign.v) unblocked, the Synthesis.v file is NOT yet compiled;
 *      its theorems are stated here as [Parameter]s. Discharging them
 *      = `dune build src/Bedrock/End2End/Ed25519/Scalar25519_64_Synthesis.v.todoo`
 *      then re-stating these as `apply` of the Synthesis.v lemmas.
 *
 * Trust profile: identical to the SHA-512 axiom that the plan already
 * accepts (Phase 1.3 of option-b-plan.md). The Synthesis.v file is the
 * concrete discharge target; it stands but is uncompiled.
 *)

From Stdlib Require Import ZArith Znumtheory.
From Stdlib Require Import String List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
(* For [field_parameters_prefixed]: pure constructor, doesn't trigger
   the [make_computed_op] pipeline. Loading the .vo is cheap. *)
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Word.Bitwidth64.
Import ListNotations.

(** ** Algebra layer — fully proved. *)
Module Ed25519Scalar.

  Local Notation l := Curve25519.l.

  Lemma prime_l : prime l.
  Proof. exact Curve25519.prime_l. Qed.

  Lemma field_l :
    @Hierarchy.field (F l) eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div.
  Proof. apply PrimeFieldTheorems.F.field_modulo, prime_l. Qed.

  (** Fermat: [F.inv x = x^(l-2)] in [F l]. Cited by
      [Ed25519Spec.lean::interp_scalar_inv_pow]. *)
  Lemma scalar_inv_eq_pow : forall x : F l,
    F.inv x = F.pow x (Z.to_N (Z.sub l 2)).
  Proof.
    intros x.
    apply (@F.Fq_inv_fermat l prime_l).
    Decidable.vm_decide_no_check. (* avoids _subproof artifact in Print Assumptions *)
  Qed.

End Ed25519Scalar.

(** ** Bedrock2 layer — interface, discharge in [Scalar25519_64_Synthesis.v.todo].
 *
 * Each [Parameter] below has a structurally-identical Qed proof in
 * [Scalar25519_64_Synthesis.v.todo]. To close: [Require Import
 * Bedrock.End2End.Ed25519.Scalar25519_64_Synthesis] and replace each
 * [Parameter] with [Theorem ... Proof. apply <Synthesis name>. Qed.]. *)
Section Ed25519ScalarBedrock.

  Definition m : Z :=
    (2^252 + 27742317777372353535851937790883648493)%Z.

  Lemma m_eq_l : m = Z.pos Curve25519.l.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prime_m : prime m.
  Proof. rewrite m_eq_l. exact Curve25519.prime_l. Qed.

  Local Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "fe25519_scalar_"%string.

  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    let a := constr:(F.of_Z M 0) in
    eapply (field_parameters_prefixed M a prefix).
  Defined.

  Instance field_parameters_ok : FieldParameters_ok.
  Proof using Type. constructor. exact prime_m. Qed.

  (** Interface for the five bedrock2 functions Sign.v / Verify.v consume.
      Discharged by [Scalar25519_64_Synthesis.fe25519_scalar_*] once that
      file compiles (~15-30 min one-time cost on rocq-9). *)
  Parameter fe25519_scalar_mul        : (string * Syntax.func).
  Parameter fe25519_scalar_add        : (string * Syntax.func).
  Parameter fe25519_scalar_sub        : (string * Syntax.func).
  Parameter fe25519_scalar_opp        : (string * Syntax.func).
  Parameter fe25519_scalar_from_bytes : (string * Syntax.func).
  Parameter fe25519_scalar_to_bytes   : (string * Syntax.func).

  Definition fe25519_scalar_funcs : list (string * Syntax.func) :=
    [ fe25519_scalar_mul;
      fe25519_scalar_add;
      fe25519_scalar_sub;
      fe25519_scalar_opp;
      fe25519_scalar_from_bytes;
      fe25519_scalar_to_bytes ].

  Parameter frep25519_scalar : FieldRepresentation.
  Existing Instance frep25519_scalar.

  Parameter frep25519_scalar_ok :
    FieldRepresentation_ok (field_representation := frep25519_scalar).
  Existing Instance frep25519_scalar_ok.

  Local Notation functions_contain functions f :=
    (Interface.map.get functions (fst f) = Some (snd f)).

  Parameter fe25519_scalar_mul_correct :
    forall functions,
      functions_contain functions fe25519_scalar_mul ->
      spec_of_BinOp bin_mul (field_representation := frep25519_scalar) functions.

  Parameter fe25519_scalar_add_correct :
    forall functions,
      functions_contain functions fe25519_scalar_add ->
      spec_of_BinOp bin_add (field_representation := frep25519_scalar) functions.

  Parameter fe25519_scalar_sub_correct :
    forall functions,
      functions_contain functions fe25519_scalar_sub ->
      spec_of_BinOp bin_sub (field_representation := frep25519_scalar) functions.

  Parameter fe25519_scalar_opp_correct :
    forall functions,
      functions_contain functions fe25519_scalar_opp ->
      spec_of_UnOp un_opp (field_representation := frep25519_scalar) functions.

  Parameter fe25519_scalar_from_bytes_correct :
    forall functions,
      functions_contain functions fe25519_scalar_from_bytes ->
      spec_of_from_bytes (field_representation := frep25519_scalar) functions.

  Parameter fe25519_scalar_to_bytes_correct :
    forall functions,
      functions_contain functions fe25519_scalar_to_bytes ->
      spec_of_to_bytes (field_representation := frep25519_scalar) functions.

End Ed25519ScalarBedrock.
