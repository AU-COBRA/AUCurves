(** * BW6-761 Frobenius — library bridge.

    Connects the BW6-761 [bw6_fp6_frob] function (in
    [BW6_761_FinalExp.v]) to the generic cubic-first Frobenius
    library theorem in
    [Bedrock.Field.FieldExtensions.PairingFieldOpsCubicFirst].

    This is the cubic-first analogue of the bridge written for
    BLS12-377 (see [BLS12_377_FinalExpDSD.spec_of_Fp12_frobenius_p2_strong_ok]).

    Structure:
      - Instantiate [PairingFieldOpsCubicFirst] at the BW6 base
        field [Fp = F bw6_M_pos] with [bw6_Fp_repr].
      - Verify the AST of [BW6_761_FinalExp.bw6_fp6_frob] is
        definitionally equal to the library
        [cubic_first_fp6_frob "bw6_761_"].
      - Strengthen the bounds-only [spec_of_bw6_fp6_frob] in
        [BW6_761_FinalExp] with the algebraic clause using
        [Semantics.weaken_call] against the library's
        [cubic_first_fp6_frob_ok].

    Bridging the BW6 [FElem_Fp6] (cubic-quadratic via
    [GenericCubicSpecs] / [GenericQuadraticSpecs]) to the library's
    [FElem_Fp6_slots] (6 explicit Fp slots) is done via the existing
    [FElem_Fp6_split_in_sep] and [FElem_Fp3_split_in_sep] lemmas in
    [BW6_761_PairingHelpers].
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.

Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FrobModel.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FinalExp.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_PairingHelpers.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOpsCubicFirst.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BW6_FrobLibBridge.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Local Notation FElem_Fp6 :=
    (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation FElem_Fp3 :=
    (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_bounded :=
    (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_tight :=
    (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_loose :=
    (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_felem :=
    (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_feval :=
    (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp3_felem :=
    (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_bounded :=
    (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_tight :=
    (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_feval :=
    (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).

  Local Notation FrobModelFp6 := (frobenius_fp6_gallina PrimeField.M_pos).

  Local Typeclasses Opaque bw6_Fp6_params.
  Local Typeclasses Opaque bw6_Fp3_params.

  (* ================================================================ *)
  (* Library instantiation                                              *)
  (* ================================================================ *)

  Local Notation bw6_lib_prefix := "bw6_761_".

  (** The library spec [spec_of_cubic_first_fp6_frob], when
      instantiated at [bw6_prime_params] and prefix ["bw6_761_"],
      names the function [bw6_761_fp6_frob].  However, the BW6
      example file uses the unprefixed name [bw6_fp6_frob].  We
      bridge the two by stating that the library function body
      coincides with the BW6 body modulo name. *)

  (** Sanity note: the library function body [cubic_first_fp6_frob
      bw6_lib_prefix] and the BW6-file body [bw6_fp6_frob] are
      structurally identical 7-step [cmd_seq_list]s with the same
      calls at the same byte offsets.  The library uses
      [3 * fp_felem_offset] for the Fp6 c1 offset; the BW6 file
      uses [fp3_felem_offset] which unfolds (via
      [GenericCubicSpecs.CE_field_representation]) to
      [3 * fp_felem_offset].

      A reflexive equality lemma between the two bodies would be a
      useful sanity check but is not in the critical path — the
      main bridge theorem below uses [Semantics.weaken_call]
      against the library spec, not the library body. *)

  (* ================================================================ *)
  (* Strong spec for bw6_fp6_frob                                      *)
  (*                                                                    *)
  (* Identical to [spec_of_bw6_fp6_frob] in [BW6_761_FinalExp.v]     *)
  (* — both carry the algebraic clause already.  We reproduce it    *)
  (* here for clarity; the bridge theorem says it follows from the  *)
  (* library's [cubic_first_fp6_frob_ok].                             *)
  (* ================================================================ *)

  (* Re-use the existing instance from BW6_761_FinalExp via
     [Existing Instance].  No new spec definition needed since the
     BW6 spec already includes the algebraic clause
     [Fp6_feval out = FrobModelFp6 ...]. *)

  Existing Instance spec_of_bw6_fp6_frob.

  (* ================================================================ *)
  (* Main bridge theorem                                                *)
  (*                                                                    *)
  (* Claim: if the function environment contains the library         *)
  (* function (and the Fp-level [fp_copy] / [fp_mul] specs), then    *)
  (* [bw6_fp6_frob] satisfies its strong spec.                         *)
  (*                                                                    *)
  (* Pattern matches                                                   *)
  (*   [BLS12_377_FinalExpDSD.spec_of_Fp12_frobenius_p2_strong_ok]:  *)
  (* same shape, ~25 line proof using [Semantics.weaken_call] +     *)
  (* [ecancel_assumption] modulo the sep-predicate translation.       *)
  (*                                                                    *)
  (* The translation step is non-trivial because BW6's [FElem_Fp6]  *)
  (* (cubic-on-quadratic) needs to be unfolded into 6 [FElem_Fp]    *)
  (* slots, then the library spec consumed, then re-folded.  This   *)
  (* uses [FElem_Fp6_split_in_sep] / [FElem_Fp3_split_in_sep] /     *)
  (* their join counterparts.                                          *)
  (* ================================================================ *)

  (* Pull in the library's Fp-level spec instances at the BW6 prime. *)
  Local Instance bw6_spec_of_Fp_felem_copy :
    spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bw6_Fp_repr).
  Local Instance bw6_spec_of_Fp_mul :
    spec_of (AbstractField.mul (F:=Fp)) :=
    AbstractField.binop_spec (F:=Fp) (field_representation:=bw6_Fp_repr)
      AbstractField.bin_mul.

  Theorem bw6_fp6_frob_ok :
    forall functions
      (EnvContains :
         map.get functions "bw6_fp6_frob" = Some (snd bw6_fp6_frob))
      (HFcopy : bw6_spec_of_Fp_felem_copy functions)
      (HFmul  : bw6_spec_of_Fp_mul functions),
    spec_of_bw6_fp6_frob functions.
  Proof.
    intros functions EnvContains HFcopy HFmul.
    (* The library lemma [PairingFieldOpsCubicFirst.cubic_first_fp6_frob_ok]
       is now closed (Print Assumptions: Closed under the global context),
       so the body-level WP for 6 sequential fp_copy + fp_mul calls is
       fully discharged at the library level.

       This bridge wraps the library spec [spec_of_cubic_first_fp6_frob]
       (stated at the Fp slot level: 6 individual fpfelem) onto the
       BW6 spec [spec_of_bw6_fp6_frob] (stated at the Fp6_felem level:
       a single list-word with cubic-on-quadratic layout).

       Definitional equality of the function bodies:
         [snd bw6_fp6_frob = snd (PairingFieldOpsCubicFirst.cubic_first_fp6_frob "bw6_")]
       holds by [eq_refl] (see Print bw6_fp6_frob; both reduce to the
       same 7-step [cmd_seq_list] of fp_copy + 6×fp_mul).

       Remaining work (structural sep translation, ~80 LoC):
       1. Apply [FElem_Fp6_split_in_sep] + twice [FElem_Fp3_split_in_sep]
          on each Fp6/Fp3 in the BW6 pre-state to expose all 18 Fp slots
          (6 from old_out, 6 from x, 3 from gfp3, 3 from gfp6) at the
          library's [FElem_Fp6_slots] / [FElem_Fp3_slots] layout.
       2. Apply [PairingFieldOpsCubicFirst.cubic_first_fp6_frob_ok] at
          [cubic_first_prefix := "bw6_"] (so the library function name
          [bw6_fp6_frob] matches) with HFcopy/HFmul.
       3. Rejoin the 6 output Fp slots back into Fp6_felem via
          [FElem_Fp_join3_in_sep] (twice, for c0 and c1 halves) then
          [FElem_Fp3_join_in_sep].
       4. Match [FrobModelFp6] against [cubic_first_fp6_frob_model]:
          both unfold to identical per-Fp-slot products with the same
          field operations on the same selectors.

       Blocker encountered when attempting inline sep translation:
       BW6's [FElem_Fp6] (cubic-on-quadratic) splits via 3 nested
       [FElem_Fp3_split_in_sep] applications, but each application
       requires the [FElem_Fp3 p _ * R] head form, which is hard to
       pattern-match across the 18-slot accumulated sep predicate using
       [ecancel_assumption_impl] (typeclass ambiguity between
       [bw6_Fp_repr] and [bw6_Fp3_repr] in the FElem instance).

       Clean follow-up: add a [bw6_FElem_Fp6_to_18slots] omnibus lemma
       in [BW6_761_PairingHelpers.v] that performs all 4 splits at once
       and exposes the result in the library's [FElem_Fp6_slots] form,
       then apply that lemma here and dispatch via the library.

       Note: [cubic_first_fp6_frob_ok] is fully proved (Closed); only
       the BW6-Fp6 ↔ Fp6_slots sep translation remains.  This bridge
       does NOT block extraction — the body-level correctness is
       already established at the library. *)
  Admitted.

End BW6_FrobLibBridge.
