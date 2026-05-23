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

  (* ================================================================ *)
  (* BW6 sep <-> library sep conversion helpers                       *)
  (*                                                                  *)
  (* The library spec [spec_of_cubic_first_fp6_frob] expects memory   *)
  (* shaped as [FElem_Fp6_slots] + [FElem_Fp3_slots] at flat          *)
  (* [slot_addr p k] addresses.  The BW6 spec expects                 *)
  (* [FElem_Fp6] / [FElem_Fp3] (cubic-quadratic nested).              *)
  (*                                                                  *)
  (* These three helpers translate.  They use the existing            *)
  (* [FElem_Fp6_split_to_6_slots] / [FElem_Fp_join6_to_Fp6] in        *)
  (* [BW6_761_PairingHelpers] plus the                                *)
  (* [word.add_assoc + word.ring_morph_add + lia] address-equality   *)
  (* recipe from the library's own normalization at lines 426-449.   *)
  (* ================================================================ *)

  Lemma BW6_Fp6_to_lib_slots :
    forall p (x : Fp6_felem) R m,
      (FElem_Fp6 p x * R)%sep m ->
      (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) p
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
       * R)%sep m.
  Proof.
    intros p x R m H.
    unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots.
    pose proof (FElem_Fp6_split_to_6_slots p x R m H) as Hsplit.
    rewrite (Z.mul_0_l _), word.add_0_r.
    rewrite (Z.mul_1_l _).
    replace (word.add p (word.of_Z (3 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
      by reflexivity.
    replace (word.add p (word.of_Z (4 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
                    (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr))))
      by (rewrite <- word.add_assoc by assumption; f_equal).
    replace (word.add p (word.of_Z (5 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
                    (word.of_Z (2 * (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      by (rewrite <- word.add_assoc by assumption; f_equal).
    SeparationLogic.ecancel_assumption_impl.
  Qed.

  Lemma BW6_Fp3_to_lib_slots :
    forall p (x : Fp3_felem) R m,
      (FElem_Fp3 p x * R)%sep m ->
      (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr x)
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr x)
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr x)
       * R)%sep m.
  Proof.
    intros p x R m H.
    unfold PairingFieldOpsCubicFirst.FElem_Fp3_slots.
    pose proof (FElem_Fp3_split_in_sep p x R m H) as Hsplit.
    rewrite (Z.mul_0_l _), word.add_0_r, (Z.mul_1_l _).
    SeparationLogic.ecancel_assumption_impl.
  Qed.

  Lemma BW6_Fp6_join_from_lib_slots :
    forall p (s0 s1 s2 s3 s4 s5 : @AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr) R m,
      length s0 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      length s1 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      length s2 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      length s3 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      length s4 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      length s5 = (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) ->
      (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) p
          s0 s1 s2 s3 s4 s5 * R)%sep m ->
      (FElem_Fp6 p ((s0 ++ s1 ++ s2) ++ (s3 ++ s4 ++ s5)) * R)%sep m.
  Proof.
    intros p s0 s1 s2 s3 s4 s5 R m Hl0 Hl1 Hl2 Hl3 Hl4 Hl5 H.
    unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots in H.
    rewrite (Z.mul_0_l _), word.add_0_r in H.
    rewrite (Z.mul_1_l _) in H.
    replace (word.add p (word.of_Z (3 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
      in H by reflexivity.
    replace (word.add p (word.of_Z (4 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
                    (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr))))
      in H by (rewrite <- word.add_assoc by assumption; f_equal).
    replace (word.add p (word.of_Z (5 *
      (Memory.bytes_per_word 64 *
       Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      with (word.add (word.add p (word.of_Z (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))))
                    (word.of_Z (2 * (Memory.bytes_per_word 64 *
         Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
      in H by (rewrite <- word.add_assoc by assumption; f_equal).
    apply (FElem_Fp_join6_to_Fp6 p s0 s1 s2 s3 s4 s5 R m Hl0 Hl1 Hl2 Hl3 Hl4 Hl5).
    SeparationLogic.ecancel_assumption_impl.
  Qed.

  (** Reverse of [BW6_Fp6_to_lib_slots]: given the library 6-slot layout
      with slot values that ARE the Fp projections of an Fp6 felem [x],
      and a length witness [length x = 6n], recover [FElem_Fp6 p x]. *)
  Lemma BW6_Fp6_from_lib_slots :
    forall p (x : Fp6_felem) R m,
      length x = (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat ->
      (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) p
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x))
       * R)%sep m ->
      (FElem_Fp6 p x * R)%sep m.
  Proof.
    intros p x R m Hlx H.
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) in *.
    assert (Hl_fst : length (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x) = (3 * n)%nat) by
      (unfold qe_fst_felem; rewrite firstn_length;
       change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
         with (3 * n)%nat; lia).
    assert (Hl_snd : length (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x) = (3 * n)%nat) by
      (unfold qe_snd_felem; rewrite skipn_length;
       change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
         with (3 * n)%nat; lia).
    assert (Hl_c0_fst : length (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c0_felem; rewrite firstn_length; rewrite Hl_fst; lia).
    assert (Hl_c1_fst : length (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c1_felem; rewrite firstn_length, skipn_length; rewrite Hl_fst; lia).
    assert (Hl_c2_fst : length (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_fst_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c2_felem; rewrite skipn_length; rewrite Hl_fst; lia).
    assert (Hl_c0_snd : length (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c0_felem; rewrite firstn_length; rewrite Hl_snd; lia).
    assert (Hl_c1_snd : length (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c1_felem; rewrite firstn_length, skipn_length; rewrite Hl_snd; lia).
    assert (Hl_c2_snd : length (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (@qe_snd_felem _ _ _ _ _ _ bw6_Fp3_repr x)) = n) by
      (unfold ce_c2_felem; rewrite skipn_length; rewrite Hl_snd; lia).
    apply (BW6_Fp6_join_from_lib_slots p _ _ _ _ _ _ R m
             Hl_c0_fst Hl_c1_fst Hl_c2_fst Hl_c0_snd Hl_c1_snd Hl_c2_snd) in H.
    rewrite (Fp6_concat_proj_eq x Hlx) in H.
    exact H.
  Qed.

  (** Reverse of [BW6_Fp3_to_lib_slots]: same idea for Fp3. *)
  Lemma BW6_Fp3_from_lib_slots :
    forall p (x : Fp3_felem) R m,
      length x = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat ->
      (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p
          (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr x)
          (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr x)
          (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr x)
       * R)%sep m ->
      (FElem_Fp3 p x * R)%sep m.
  Proof.
    intros p x R m Hlx H.
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) in *.
    assert (Hl_c0 : length (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr x) = n) by
      (unfold ce_c0_felem; rewrite firstn_length; rewrite Hlx; lia).
    assert (Hl_c1 : length (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr x) = n) by
      (unfold ce_c1_felem; rewrite firstn_length, skipn_length; rewrite Hlx; lia).
    assert (Hl_c2 : length (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr x) = n) by
      (unfold ce_c2_felem; rewrite skipn_length; rewrite Hlx; lia).
    unfold PairingFieldOpsCubicFirst.FElem_Fp3_slots in H.
    rewrite (Z.mul_0_l _), word.add_0_r, (Z.mul_1_l _) in H.
    rewrite <- (Fp3_concat_proj_eq x Hlx).
    apply (FElem_Fp_join3_in_sep p _ _ _ R m Hl_c0 Hl_c1 Hl_c2).
    use_sep_assumption; cancel.
  Qed.

  (* ============================================================== *)
  (* Bridge theorem (BLS12-377-style: take library spec as hypothesis) *)
  (*                                                                  *)
  (* Caller workflow:                                                  *)
  (*   pose proof (PairingFieldOpsCubicFirst.cubic_first_fp6_frob_ok  *)
  (*     (F_representation := bw6_Fp_repr)                            *)
  (*     (F_representation_ok := bw6_Fp_repr_ok)                       *)
  (*     "bw6_" functions EnvContains HFcopy HFmul) as Hlib.            *)
  (*   apply (bw6_fp6_frob_ok functions Hlib).                         *)
  (*                                                                  *)
  (* Structural progress (foreground MCP session 2026-05-22):         *)
  (*   - eapply Hlib closes Goal 1's call target cleanly               *)
  (*     (after specialising the 18 felem args to ce_c*_felem of       *)
  (*     qe_*_felem of x/old_out and ce_c*_felem of gfp3/gfp6).        *)
  (*   - Remaining work: 3-way sep translation                        *)
  (*     (FElem_Fp6 px x + 2× FElem_Fp3 → _slots form via sep_comm    *)
  (*     rotations + the existing BW6_Fp6_to_lib_slots /              *)
  (*     BW6_Fp3_to_lib_slots helpers), + 6-way Fp_bounded unfold of  *)
  (*     Fp6_bounded Fp6_tight x, + post translation (existential     *)
  (*     packing via BW6_Fp6_join_from_lib_slots).                    *)
  (* ============================================================== *)

  Theorem bw6_fp6_frob_ok :
    forall functions
      (Hlib :
         PairingFieldOpsCubicFirst.spec_of_cubic_first_fp6_frob
           (F_representation := bw6_Fp_repr) "bw6_" "" functions),
    spec_of_bw6_fp6_frob functions.
  Proof.
    intros functions Hlib.
    unfold spec_of_bw6_fp6_frob.
    intros pout px p_gfp3 p_gfp6 old_out x gfp3 gfp6 Rr tr mem
           [Hbx [Hbgfp3 [Hbgfp6 Hmem]]].
    (* 1. Destructure bounds via cbn into 12 atomic Fp_bounded facts. *)
    cbn [AbstractField.bounded_by AbstractField.tight_bounds
         bw6_Fp6_repr bw6_Fp3_repr
         QE_field_representation CE_field_representation] in Hbx, Hbgfp3, Hbgfp6.
    destruct Hbx as [Hbx_c0 Hbx_c1].
    destruct Hbx_c0 as [Hbxc0c0 [Hbxc0c1 Hbxc0c2]].
    destruct Hbx_c1 as [Hbxc1c0 [Hbxc1c1 Hbxc1c2]].
    destruct Hbgfp3 as [Hbg3c0 [Hbg3c1 Hbg3c2]].
    destruct Hbgfp6 as [Hbg6c0 [Hbg6c1 Hbg6c2]].
    (* 2. Pose named slot felems for the 18 Fp slot arguments. *)
    pose (slot_x_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_o_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_g3_0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g3_1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g3_2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g6_0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g6_1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g6_2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    (* 3. Convert Hmem to library sep shape via 4 [assert + use_sep_assumption;
       cancel + apply] rounds. *)
    apply BW6_Fp6_to_lib_slots in Hmem.
    assert (Hpx :
      (FElem_Fp6 px x ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (FElem_Fp3 p_gfp3 gfp3 ⋆ (FElem_Fp3 p_gfp6 gfp6 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp6_to_lib_slots in Hpx.
    assert (Hgfp3 :
      (FElem_Fp3 p_gfp3 gfp3 ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (PairingFieldOpsCubicFirst.FElem_Fp6_slots
              (F_representation := bw6_Fp_repr) px
              slot_x_c0c0 slot_x_c0c1 slot_x_c0c2
              slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
            ⋆ (FElem_Fp3 p_gfp6 gfp6 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp3_to_lib_slots in Hgfp3.
    assert (Hgfp6 :
      (FElem_Fp3 p_gfp6 gfp6 ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (PairingFieldOpsCubicFirst.FElem_Fp6_slots
              (F_representation := bw6_Fp_repr) px
              slot_x_c0c0 slot_x_c0c1 slot_x_c0c2
              slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
            ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots
                 (F_representation := bw6_Fp_repr) p_gfp3
                 slot_g3_0 slot_g3_1 slot_g3_2 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp3_to_lib_slots in Hgfp6.
    (* 4. Apply Hlib via Semantics.weaken_call. *)
    unfold spec_of_cubic_first_fp6_frob in Hlib.
    specialize (Hlib pout px p_gfp3 p_gfp6
      slot_o_c0c0 slot_o_c0c1 slot_o_c0c2 slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
      slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
      slot_g3_0 slot_g3_1 slot_g3_2
      slot_g6_0 slot_g6_1 slot_g6_2
      Rr tr mem).
    change (PairingFieldOpsCubicFirst.cubic_first_fp6_frob_name "bw6_" "")
      with "bw6_fp6_frob" in Hlib.
    eapply Semantics.weaken_call.
    { apply Hlib. clear Hlib.
      unfold Fp6_slots_tight, Fp3_slots_tight.
      split; [|split; [|split]].
      - split; [exact Hbxc0c0|].
        split; [exact Hbxc0c1|].
        split; [exact Hbxc0c2|].
        split; [exact Hbxc1c0|].
        split; [exact Hbxc1c1|exact Hbxc1c2].
      - split; [exact Hbg3c0|].
        split; [exact Hbg3c1|exact Hbg3c2].
      - split; [exact Hbg6c0|].
        split; [exact Hbg6c1|exact Hbg6c2].
      - use_sep_assumption; cancel. }
    (* 5. Destructure post. *)
    intros tr' mem' rets Hpost.
    cbn beta in Hpost.
    destruct Hpost as [Hrets [Htreq [O0 [O1 [O2 [O3 [O4 [O5
                       [Hbloose [Hfeval Hmem']]]]]]]]]].
    subst tr' rets.
    split; [reflexivity|].
    split; [reflexivity|].
    exists ((O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    (* 6. Three remaining sub-goals: bounds, algebraic, sep.

       All three depend on length witnesses:
         - length Oi = felem_size_in_words (from Bignum.Bignum in Hmem')
         - length x / gfp3 / gfp6 (from original Hmem via Bignum)

       Bounds: Fp6_bounded Fp6_loose ((O0++O1++O2)++(O3++O4++O5))
         cbn-unfolds to 6 conjuncts of form
           bounded_by loose_bounds (ce_c0_felem (qe_fst_felem concat)) ...
         Each ce_ci (qe_? concat) = Oi reduces via firstn/skipn lemmas
         under length witnesses; then HO0..HO5 discharge.

       Algebraic: Fp6_feval ((O0++O1++O2)++(O3++O4++O5)) =
         FrobModelFp6 (Fp6_feval x) (Fp3_feval gfp3) (Fp3_feval gfp6).
         Bridge:
           - Fp6_feval (concat) = feval_Fp6_slots O0..O5 [concat-proj-eq
             + length witness, mirrors Fp6_concat_proj_eq]
           - Fp6_feval x = feval_Fp6_slots slot_x_c0c0..slot_x_c1c2
             [same, from length x witness]
           - Fp3_feval gfp3 = feval_Fp3_slots slot_g3_0..slot_g3_2
             [same, length gfp3 witness]
           - same for gfp6
           - cubic_first_fp6_frob_model = FrobModelFp6 [reflexivity:
             both bodies are identical fp3_mk-of-F.mul cascades; verified
             by side-by-side comparison]

       Sep: Hmem' has library shape with output as FElem_Fp6_slots pout
         O0..O5.
         - BW6_Fp6_join_from_lib_slots produces FElem_Fp6 pout (concat)
           given 6 length witnesses (length Oi = fp_size_in_words each).
         - FElem_Fp6_join_from_proj_slots (PairingHelpers) converts the
           input slots back to FElem_Fp6 px x (under length x witness).
         - FElem_Fp3_join_from_proj_slots × 2 for gfp3, gfp6.
         - Final ecancel.

       Estimated: 150-200 LoC, mechanical once length witnesses are
       extracted via Bignum.Bignum_to_bytes applied to FElem_Fp atoms
       inside Hmem' / Hmem. *)
    (* === MCP-verified length extraction + sep partial reverse (2026-05-22) ===

       Sequence verified in MCP this session:

         1. Extract length witnesses from Hmem (copy via [pose proof]
            then destruct through sep):
              pose proof Hmem as HmemC.
              destruct HmemC as [? [? [_ [_ HmemCrest]]]].
              destruct HmemCrest as [? [? [_ [HFx HmemCrest2]]]].
              destruct HmemCrest2 as [? [? [_ [HFg3 HmemCrest3]]]].
              destruct HmemCrest3 as [? [? [_ [HFg6 _]]]].
              assert (Hlen_x : length x = felem_size_in_words_Fp6)
                by apply (GenericSplitJoin.generic_FElem_length _ _ _ HFx).
              (* similarly Hlen_gfp3, Hlen_gfp6 *)

         2. Extract length(Oi) witnesses from Hmem' (post-call mem):
              pose proof Hmem' as Htmp.
              unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots in Htmp.
              destruct Htmp as [? [? [_ [Htmp_pout _]]]].
              (* Then destruct Htmp_pout 5x to get HF_O0..HF_O5 *)
              assert (HlO0 : length O0 = felem_size_in_words_Fp)
                by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O0).
              (* similarly HlO1..HlO5 *)

         3. Sep reverse for pout output (verified in MCP):
              apply (BW6_Fp6_join_from_lib_slots pout O0 O1 O2 O3 O4 O5
                       _ _ HlO0 HlO1 HlO2 HlO3 HlO4 HlO5) in Hmem'.
              (* now Hmem' has FElem_Fp6 pout ((O0++O1++O2)++(O3++O4++O5)) *)

       Remaining: convert FElem_Fp6_slots px / FElem_Fp3_slots p_gfp3 /
       FElem_Fp3_slots p_gfp6 back to FElem_Fp6 / FElem_Fp3.  This needs
       a reverse-direction helper `BW6_Fp6_from_lib_slots` (mirror of
       `BW6_Fp6_to_lib_slots`) that converts the address-normalized
       library 6-slot form back to the BW6 nested Fp6_felem, under the
       length witness on x.  The forward helper does
       `FElem_Fp6 → FElem_Fp6_slots`; the reverse adds a `length x = 6n`
       hypothesis and inverts via `FElem_Fp6_join_from_proj_slots` from
       PairingHelpers (which is already proved, but for the
       address-normalized 6-FElem form, not directly for the library's
       `FElem_Fp6_slots`).  ~30 LoC to write the 3 reverse helpers + use them.

       Algebraic (Fp6_feval (concat) = FrobModelFp6 ...) bridges via
       Fp6_concat_proj_eq + reflexivity on the literal model equality.
       Bounds reduce via firstn_app_sharp/skipn_app_sharp + 2-step
       skipn_skipn for ce_c2.  Total remaining: ~80-100 LoC. *)
    (* Extract length witnesses for x, gfp3, gfp6 from Hmem (still has Fp6/Fp3 atoms
       for these — only pout was converted by the first apply BW6_Fp6_to_lib_slots). *)
    pose proof Hmem as Hmem_lengths.
    destruct Hmem_lengths as [? [? [_ [_ Hrest]]]].
    destruct Hrest as [? [? [_ [HFx Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HFg3 Hrest3]]]].
    destruct Hrest3 as [? [? [_ [HFg6 _]]]].
    assert (Hlen_x : length x = (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFx) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr)
        with (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    assert (Hlen_g3 : length gfp3 = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFg3) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    assert (Hlen_g6 : length gfp6 = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFg6) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    clear HFx HFg3 HFg6.
    (* Extract length witnesses for the 6 output slots O0..O5. *)
    pose proof Hmem' as HmemX.
    unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots in HmemX.
    destruct HmemX as [? [? [_ [HmemX_pout _]]]].
    destruct HmemX_pout as [? [? [_ [HF_O0 Hrest1]]]].
    destruct Hrest1 as [? [? [_ [HF_O1 Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HF_O2 Hrest3]]]].
    destruct Hrest3 as [? [? [_ [HF_O3 Hrest4]]]].
    destruct Hrest4 as [? [? [_ [HF_O4 HF_O5]]]].
    assert (HlO0 : length O0 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O0).
    assert (HlO1 : length O1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O1).
    assert (HlO2 : length O2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O2).
    assert (HlO3 : length O3 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O3).
    assert (HlO4 : length O4 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O4).
    assert (HlO5 : length O5 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O5).
    clear HF_O0 HF_O1 HF_O2 HF_O3 HF_O4 HF_O5.
    (* 6 concrete projection equalities for the CONCAT. *)
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) in *.
    set (CONCAT := (O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    assert (HlenC : length CONCAT = (6 * n)%nat).
    { subst CONCAT. rewrite !app_length. lia. }
    assert (Hfst : @qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O0 ++ O1 ++ O2).
    { unfold qe_fst_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite firstn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.firstn_O, app_nil_r.
      apply List.firstn_all2. rewrite !app_length, HlO0, HlO1, HlO2. lia. }
    assert (Hsnd : @qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O3 ++ O4 ++ O5).
    { unfold qe_snd_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite skipn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.skipn_O.
      rewrite skipn_all2 by (rewrite !app_length, HlO0, HlO1, HlO2; lia).
      reflexivity. }
    assert (Hc0fst : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O0).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO0, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1fst : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O1).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia.
      rewrite app_nil_l.
      rewrite firstn_app, HlO1, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2fst : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O2).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO1, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O1) by lia. rewrite app_nil_l.
      reflexivity. }
    assert (Hc0snd : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O3).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO3, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1snd : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O4).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite firstn_app, HlO4, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2snd : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O5).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO4, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O4) by lia. rewrite app_nil_l.
      reflexivity. }
    unfold Fp6_slots_loose in Hbloose.
    destruct Hbloose as [HbO0 [HbO1 [HbO2 [HbO3 [HbO4 HbO5]]]]].
    split; [|split].
    - (* Bounds: 6 conjuncts via the slot equalities. *)
      cbn [AbstractField.bounded_by AbstractField.loose_bounds
           bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      rewrite Hfst, Hsnd, Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      exact (conj (conj HbO0 (conj HbO1 HbO2)) (conj HbO3 (conj HbO4 HbO5))).
    - (* Algebraic: bridge Fp6_feval CONCAT through feval_Fp6_slots and Hfeval. *)
      cbn [AbstractField.feval bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      unfold GenericQuadraticSpecs.QE_feval, GenericCubicSpecs.CE_feval.
      rewrite Hfst, Hsnd.
      cbn [AbstractField.feval bw6_Fp3_repr CE_field_representation].
      unfold GenericCubicSpecs.CE_feval.
      rewrite Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      change (feval O0, feval O1, feval O2, (feval O3, feval O4, feval O5))
        with (feval_Fp6_slots O0 O1 O2 O3 O4 O5).
      rewrite Hfeval.
      unfold cubic_first_fp6_frob_model, FrobModelFp6, frobenius_fp6_gallina,
             cubic_first_frob_fp3_c0, cubic_first_frob_fp3_c1,
             frobenius_fp3_c0_gallina, frobenius_fp3_c1_gallina,
             fp6_mk, fp6_c0, fp6_c1, fp3_mk, fp3_a0, fp3_a1, fp3_a2,
             feval_Fp6_slots, feval_Fp3_slots.
      reflexivity.
    - (* Sep: convert pout output via BW6_Fp6_join_from_lib_slots; convert px / gfp3 / gfp6
         inputs back via BW6_Fp6_from_lib_slots / BW6_Fp3_from_lib_slots (the new reverse
         helpers, using the length witnesses Hlen_x, Hlen_g3, Hlen_g6). *)
      apply (BW6_Fp6_join_from_lib_slots pout O0 O1 O2 O3 O4 O5 _ _
               HlO0 HlO1 HlO2 HlO3 HlO4 HlO5) in Hmem'.
      assert (Hmem_px :
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) px
           slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp3
                 slot_g3_0 slot_g3_1 slot_g3_2
               ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6
                    slot_g6_0 slot_g6_1 slot_g6_2 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem'.
      apply (BW6_Fp6_from_lib_slots px x _ _ Hlen_x) in Hmem_px.
      assert (Hmem_g3 :
        (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp3
           slot_g3_0 slot_g3_1 slot_g3_2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (FElem_Fp6 px x
               ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6
                    slot_g6_0 slot_g6_1 slot_g6_2 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem_px.
      apply (BW6_Fp3_from_lib_slots p_gfp3 gfp3 _ _ Hlen_g3) in Hmem_g3.
      assert (Hmem_g6 :
        (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6
           slot_g6_0 slot_g6_1 slot_g6_2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (FElem_Fp6 px x
               ⋆ (FElem_Fp3 p_gfp3 gfp3 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem_g3.
      apply (BW6_Fp3_from_lib_slots p_gfp6 gfp6 _ _ Hlen_g6) in Hmem_g6.
      use_sep_assumption; cancel.
  Qed.

  (* ============================================================== *)
  (* Bridge for [bw6_fp6_frob_p2] — pi^2 variant.                    *)
  (*                                                                  *)
  (* Same as [bw6_fp6_frob_ok] but at the library suffix ["_p2"].    *)
  (* The body of BW6's [bw6_fp6_frob_p2] (in BW6_761_FinalExp.v)     *)
  (* uses gamma var names matching the library's defaults so the     *)
  (* same library theorem applies modulo the function NAME suffix.   *)
  (* The algebraic model [FrobModelFp6_p2] is definitionally equal   *)
  (* to [FrobModelFp6] (see [frobenius_fp6_p2_unfold] in              *)
  (* BW6_761_FrobModel.v) — the final [reflexivity] closes via       *)
  (* unfolding both models to the same fp3_mk-of-F.mul cascade.      *)
  (* ============================================================== *)
  Theorem bw6_fp6_frob_p2_ok :
    forall functions
      (Hlib :
         PairingFieldOpsCubicFirst.spec_of_cubic_first_fp6_frob
           (F_representation := bw6_Fp_repr) "bw6_" "_p2" functions),
    spec_of_bw6_fp6_frob_p2 functions.
  Proof.
    intros functions Hlib.
    unfold spec_of_bw6_fp6_frob_p2.
    intros pout px p_gfp3_p2 p_gfp6_p2 old_out x gfp3 gfp6 Rr tr mem
           [Hbx [Hbgfp3 [Hbgfp6 Hmem]]].
    cbn [AbstractField.bounded_by AbstractField.tight_bounds
         bw6_Fp6_repr bw6_Fp3_repr
         QE_field_representation CE_field_representation] in Hbx, Hbgfp3, Hbgfp6.
    destruct Hbx as [Hbx_c0 Hbx_c1].
    destruct Hbx_c0 as [Hbxc0c0 [Hbxc0c1 Hbxc0c2]].
    destruct Hbx_c1 as [Hbxc1c0 [Hbxc1c1 Hbxc1c2]].
    destruct Hbgfp3 as [Hbg3c0 [Hbg3c1 Hbg3c2]].
    destruct Hbgfp6 as [Hbg6c0 [Hbg6c1 Hbg6c2]].
    pose (slot_x_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_o_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_g3_0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g3_1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g3_2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr gfp3).
    pose (slot_g6_0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g6_1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g6_2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    apply BW6_Fp6_to_lib_slots in Hmem.
    assert (Hpx :
      (FElem_Fp6 px x ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (FElem_Fp3 p_gfp3_p2 gfp3 ⋆ (FElem_Fp3 p_gfp6_p2 gfp6 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp6_to_lib_slots in Hpx.
    assert (Hgfp3 :
      (FElem_Fp3 p_gfp3_p2 gfp3 ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (PairingFieldOpsCubicFirst.FElem_Fp6_slots
              (F_representation := bw6_Fp_repr) px
              slot_x_c0c0 slot_x_c0c1 slot_x_c0c2
              slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
            ⋆ (FElem_Fp3 p_gfp6_p2 gfp6 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp3_to_lib_slots in Hgfp3.
    assert (Hgfp6 :
      (FElem_Fp3 p_gfp6_p2 gfp6 ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (PairingFieldOpsCubicFirst.FElem_Fp6_slots
              (F_representation := bw6_Fp_repr) px
              slot_x_c0c0 slot_x_c0c1 slot_x_c0c2
              slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
            ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots
                 (F_representation := bw6_Fp_repr) p_gfp3_p2
                 slot_g3_0 slot_g3_1 slot_g3_2 ⋆ Rr))))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp3_to_lib_slots in Hgfp6.
    unfold spec_of_cubic_first_fp6_frob in Hlib.
    specialize (Hlib pout px p_gfp3_p2 p_gfp6_p2
      slot_o_c0c0 slot_o_c0c1 slot_o_c0c2 slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
      slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
      slot_g3_0 slot_g3_1 slot_g3_2
      slot_g6_0 slot_g6_1 slot_g6_2
      Rr tr mem).
    change (PairingFieldOpsCubicFirst.cubic_first_fp6_frob_name "bw6_" "_p2")
      with "bw6_fp6_frob_p2" in Hlib.
    eapply Semantics.weaken_call.
    { apply Hlib. clear Hlib.
      unfold Fp6_slots_tight, Fp3_slots_tight.
      split; [|split; [|split]].
      - split; [exact Hbxc0c0|]. split; [exact Hbxc0c1|]. split; [exact Hbxc0c2|].
        split; [exact Hbxc1c0|]. split; [exact Hbxc1c1|exact Hbxc1c2].
      - split; [exact Hbg3c0|]. split; [exact Hbg3c1|exact Hbg3c2].
      - split; [exact Hbg6c0|]. split; [exact Hbg6c1|exact Hbg6c2].
      - use_sep_assumption; cancel. }
    intros tr' mem' rets Hpost.
    cbn beta in Hpost.
    destruct Hpost as [Hrets [Htreq [O0 [O1 [O2 [O3 [O4 [O5
                       [Hbloose [Hfeval Hmem']]]]]]]]]].
    subst tr' rets.
    pose proof Hmem as Hmem_lengths.
    destruct Hmem_lengths as [? [? [_ [_ Hrest]]]].
    destruct Hrest as [? [? [_ [HFx Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HFg3 Hrest3]]]].
    destruct Hrest3 as [? [? [_ [HFg6 _]]]].
    assert (Hlen_x : length x = (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFx) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr)
        with (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    assert (Hlen_g3 : length gfp3 = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFg3) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    assert (Hlen_g6 : length gfp6 = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFg6) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    clear HFx HFg3 HFg6.
    pose proof Hmem' as HmemX.
    unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots in HmemX.
    destruct HmemX as [? [? [_ [HmemX_pout _]]]].
    destruct HmemX_pout as [? [? [_ [HF_O0 Hrest1]]]].
    destruct Hrest1 as [? [? [_ [HF_O1 Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HF_O2 Hrest3]]]].
    destruct Hrest3 as [? [? [_ [HF_O3 Hrest4]]]].
    destruct Hrest4 as [? [? [_ [HF_O4 HF_O5]]]].
    assert (HlO0 : length O0 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O0).
    assert (HlO1 : length O1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O1).
    assert (HlO2 : length O2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O2).
    assert (HlO3 : length O3 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O3).
    assert (HlO4 : length O4 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O4).
    assert (HlO5 : length O5 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O5).
    clear HF_O0 HF_O1 HF_O2 HF_O3 HF_O4 HF_O5.
    split; [reflexivity|].
    split; [reflexivity|].
    exists ((O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) in *.
    set (CONCAT := (O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    assert (HlenC : length CONCAT = (6 * n)%nat).
    { subst CONCAT. rewrite !app_length. lia. }
    assert (Hfst : @qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O0 ++ O1 ++ O2).
    { unfold qe_fst_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite firstn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.firstn_O, app_nil_r.
      apply List.firstn_all2. rewrite !app_length, HlO0, HlO1, HlO2. lia. }
    assert (Hsnd : @qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O3 ++ O4 ++ O5).
    { unfold qe_snd_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite skipn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.skipn_O.
      rewrite skipn_all2 by (rewrite !app_length, HlO0, HlO1, HlO2; lia).
      reflexivity. }
    assert (Hc0fst : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O0).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO0, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1fst : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O1).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia. rewrite app_nil_l.
      rewrite firstn_app, HlO1, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2fst : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O2).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO1, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O1) by lia. rewrite app_nil_l.
      reflexivity. }
    assert (Hc0snd : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O3).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO3, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1snd : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O4).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite firstn_app, HlO4, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2snd : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O5).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO4, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O4) by lia. rewrite app_nil_l.
      reflexivity. }
    unfold Fp6_slots_loose in Hbloose.
    destruct Hbloose as [HbO0 [HbO1 [HbO2 [HbO3 [HbO4 HbO5]]]]].
    split; [|split].
    - cbn [AbstractField.bounded_by AbstractField.loose_bounds
           bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      rewrite Hfst, Hsnd, Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      exact (conj (conj HbO0 (conj HbO1 HbO2)) (conj HbO3 (conj HbO4 HbO5))).
    - cbn [AbstractField.feval bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      unfold GenericQuadraticSpecs.QE_feval, GenericCubicSpecs.CE_feval.
      rewrite Hfst, Hsnd.
      cbn [AbstractField.feval bw6_Fp3_repr CE_field_representation].
      unfold GenericCubicSpecs.CE_feval.
      rewrite Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      change (feval O0, feval O1, feval O2, (feval O3, feval O4, feval O5))
        with (feval_Fp6_slots O0 O1 O2 O3 O4 O5).
      rewrite Hfeval.
      unfold cubic_first_fp6_frob_model,
             frobenius_fp6_p2_gallina, frobenius_fp6_gallina,
             cubic_first_frob_fp3_c0, cubic_first_frob_fp3_c1,
             frobenius_fp3_c0_gallina, frobenius_fp3_c1_gallina,
             fp6_mk, fp6_c0, fp6_c1, fp3_mk, fp3_a0, fp3_a1, fp3_a2,
             feval_Fp6_slots, feval_Fp3_slots.
      reflexivity.
    - apply (BW6_Fp6_join_from_lib_slots pout O0 O1 O2 O3 O4 O5 _ _
               HlO0 HlO1 HlO2 HlO3 HlO4 HlO5) in Hmem'.
      assert (Hmem_px :
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) px
           slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp3_p2
                 slot_g3_0 slot_g3_1 slot_g3_2
               ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6_p2
                    slot_g6_0 slot_g6_1 slot_g6_2 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem'.
      apply (BW6_Fp6_from_lib_slots px x _ _ Hlen_x) in Hmem_px.
      assert (Hmem_g3 :
        (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp3_p2
           slot_g3_0 slot_g3_1 slot_g3_2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (FElem_Fp6 px x
               ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6_p2
                    slot_g6_0 slot_g6_1 slot_g6_2 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem_px.
      apply (BW6_Fp3_from_lib_slots p_gfp3_p2 gfp3 _ _ Hlen_g3) in Hmem_g3.
      assert (Hmem_g6 :
        (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6_p2
           slot_g6_0 slot_g6_1 slot_g6_2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (FElem_Fp6 px x
               ⋆ (FElem_Fp3 p_gfp3_p2 gfp3 ⋆ Rr))))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem_g3.
      apply (BW6_Fp3_from_lib_slots p_gfp6_p2 gfp6 _ _ Hlen_g6) in Hmem_g6.
      use_sep_assumption; cancel.
  Qed.

  (* ============================================================== *)
  (* Bridge for [bw6_fp6_frob_p3] — pi^3 variant.                    *)
  (*                                                                  *)
  (* pi^3 has a different body from p1/p2: 3 fp_copy + 3 fp_mul with *)
  (* a single Fp scalar (= gamma_fp6_p3.c0).  Uses the library's     *)
  (* [cubic_first_fp6_frob_p3_ok] theorem (added to                  *)
  (* PairingFieldOpsCubicFirst.v).  Signature: 3 pointers instead of *)
  (* 4 (no gfp3).  Algebraic model:                                   *)
  (*   FrobModelFp6_p3 (Fp6_feval x) (fp3_a0 _ (Fp3_feval gfp6))     *)
  (* matches library's [cubic_first_fp6_frob_p3_model x g] where g  *)
  (* = Fp_feval (ce_c0_felem gfp6) by definition.                     *)
  (* ============================================================== *)
  Theorem bw6_fp6_frob_p3_ok :
    forall functions
      (Hlib :
         PairingFieldOpsCubicFirst.spec_of_cubic_first_fp6_frob_p3
           (F_representation := bw6_Fp_repr) "bw6_" functions),
    spec_of_bw6_fp6_frob_p3 functions.
  Proof.
    intros functions Hlib.
    unfold spec_of_bw6_fp6_frob_p3.
    intros pout px p_gfp6_p3 old_out x gfp6 Rr tr mem
           [Hbx [Hbgfp6 Hmem]].
    cbn [AbstractField.bounded_by AbstractField.tight_bounds
         bw6_Fp6_repr bw6_Fp3_repr
         QE_field_representation CE_field_representation] in Hbx, Hbgfp6.
    destruct Hbx as [Hbx_c0 Hbx_c1].
    destruct Hbx_c0 as [Hbxc0c0 [Hbxc0c1 Hbxc0c2]].
    destruct Hbx_c1 as [Hbxc1c0 [Hbxc1c1 Hbxc1c2]].
    destruct Hbgfp6 as [Hbg6c0 [Hbg6c1 Hbg6c2]].
    pose (slot_x_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_x_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr x)).
    pose (slot_o_c0c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c0c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_o_c1c2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr
            (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr old_out)).
    pose (slot_g_0 := @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g_1 := @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    pose (slot_g_2 := @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr gfp6).
    apply BW6_Fp6_to_lib_slots in Hmem.
    assert (Hpx :
      (FElem_Fp6 px x ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (FElem_Fp3 p_gfp6_p3 gfp6 ⋆ Rr)))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp6_to_lib_slots in Hpx.
    assert (Hg :
      (FElem_Fp3 p_gfp6_p3 gfp6 ⋆
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots
           (F_representation := bw6_Fp_repr) pout
           slot_o_c0c0 slot_o_c0c1 slot_o_c0c2
           slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
         ⋆ (PairingFieldOpsCubicFirst.FElem_Fp6_slots
              (F_representation := bw6_Fp_repr) px
              slot_x_c0c0 slot_x_c0c1 slot_x_c0c2
              slot_x_c1c0 slot_x_c1c1 slot_x_c1c2 ⋆ Rr)))%sep mem)
      by (use_sep_assumption; cancel).
    apply BW6_Fp3_to_lib_slots in Hg.
    unfold spec_of_cubic_first_fp6_frob_p3 in Hlib.
    specialize (Hlib pout px p_gfp6_p3
      slot_o_c0c0 slot_o_c0c1 slot_o_c0c2 slot_o_c1c0 slot_o_c1c1 slot_o_c1c2
      slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
      slot_g_0 slot_g_1 slot_g_2
      Rr tr mem).
    change (PairingFieldOpsCubicFirst.cubic_first_fp6_frob_p3_name "bw6_")
      with "bw6_fp6_frob_p3" in Hlib.
    eapply Semantics.weaken_call.
    { apply Hlib. clear Hlib.
      unfold Fp6_slots_tight, Fp3_slots_tight.
      split; [|split].
      - split; [exact Hbxc0c0|]. split; [exact Hbxc0c1|]. split; [exact Hbxc0c2|].
        split; [exact Hbxc1c0|]. split; [exact Hbxc1c1|exact Hbxc1c2].
      - split; [exact Hbg6c0|]. split; [exact Hbg6c1|exact Hbg6c2].
      - use_sep_assumption; cancel. }
    intros tr' mem' rets Hpost.
    cbn beta in Hpost.
    destruct Hpost as [Hrets [Htreq [O0 [O1 [O2 [O3 [O4 [O5
                       [Hbloose [Hfeval Hmem']]]]]]]]]].
    subst tr' rets.
    pose proof Hmem as Hmem_lengths.
    destruct Hmem_lengths as [? [? [_ [_ Hrest]]]].
    destruct Hrest as [? [? [_ [HFx Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HFg HFrr]]]].
    assert (Hlen_x : length x = (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFx) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr)
        with (6 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    assert (Hlen_g : length gfp6 = (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat).
    { pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFg) as Htmp.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)%nat in Htmp.
      exact Htmp. }
    clear HFx HFg HFrr.
    pose proof Hmem' as HmemX.
    unfold PairingFieldOpsCubicFirst.FElem_Fp6_slots in HmemX.
    destruct HmemX as [? [? [_ [HmemX_pout _]]]].
    destruct HmemX_pout as [? [? [_ [HF_O0 Hrest1]]]].
    destruct Hrest1 as [? [? [_ [HF_O1 Hrest2]]]].
    destruct Hrest2 as [? [? [_ [HF_O2 Hrest3]]]].
    destruct Hrest3 as [? [? [_ [HF_O3 Hrest4]]]].
    destruct Hrest4 as [? [? [_ [HF_O4 HF_O5]]]].
    assert (HlO0 : length O0 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O0).
    assert (HlO1 : length O1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O1).
    assert (HlO2 : length O2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O2).
    assert (HlO3 : length O3 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O3).
    assert (HlO4 : length O4 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O4).
    assert (HlO5 : length O5 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)
      by apply (GenericSplitJoin.generic_FElem_length _ _ _ HF_O5).
    clear HF_O0 HF_O1 HF_O2 HF_O3 HF_O4 HF_O5.
    split; [reflexivity|].
    split; [reflexivity|].
    exists ((O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr) in *.
    set (CONCAT := (O0 ++ O1 ++ O2) ++ (O3 ++ O4 ++ O5)).
    assert (HlenC : length CONCAT = (6 * n)%nat).
    { subst CONCAT. rewrite !app_length. lia. }
    assert (Hfst : @qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O0 ++ O1 ++ O2).
    { unfold qe_fst_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite firstn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.firstn_O, app_nil_r.
      apply List.firstn_all2. rewrite !app_length, HlO0, HlO1, HlO2. lia. }
    assert (Hsnd : @qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr CONCAT = O3 ++ O4 ++ O5).
    { unfold qe_snd_felem. subst CONCAT.
      change (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr)
        with (3 * n)%nat.
      rewrite skipn_app.
      rewrite !app_length, HlO0, HlO1, HlO2.
      replace (3 * n - (n + (n + n)))%nat with 0%nat by lia.
      rewrite List.skipn_O.
      rewrite skipn_all2 by (rewrite !app_length, HlO0, HlO1, HlO2; lia).
      reflexivity. }
    assert (Hc0fst : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O0).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO0, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1fst : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O1).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia. rewrite app_nil_l.
      rewrite firstn_app, HlO1, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2fst : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O0 ++ O1 ++ O2) = O2).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO0, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O0) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO1, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O1) by lia. rewrite app_nil_l.
      reflexivity. }
    assert (Hc0snd : @ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O3).
    { unfold ce_c0_felem. fold n.
      rewrite firstn_app, HlO3, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc1snd : @ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O4).
    { unfold ce_c1_felem. fold n.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite firstn_app, HlO4, Nat.sub_diag, List.firstn_O, app_nil_r.
      apply List.firstn_all2. lia. }
    assert (Hc2snd : @ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr (O3 ++ O4 ++ O5) = O5).
    { unfold ce_c2_felem. fold n.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- skipn_skipn.
      rewrite skipn_app, HlO3, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O3) by lia. rewrite app_nil_l.
      rewrite skipn_app, HlO4, Nat.sub_diag, List.skipn_O.
      rewrite (skipn_all2 O4) by lia. rewrite app_nil_l.
      reflexivity. }
    unfold Fp6_slots_loose in Hbloose.
    destruct Hbloose as [HbO0 [HbO1 [HbO2 [HbO3 [HbO4 HbO5]]]]].
    split; [|split].
    - cbn [AbstractField.bounded_by AbstractField.loose_bounds
           bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      rewrite Hfst, Hsnd, Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      exact (conj (conj HbO0 (conj HbO1 HbO2)) (conj HbO3 (conj HbO4 HbO5))).
    - (* Algebraic: bridge through Hfeval and identify model bodies *)
      cbn [AbstractField.feval bw6_Fp6_repr bw6_Fp3_repr
           QE_field_representation CE_field_representation].
      unfold GenericQuadraticSpecs.QE_feval, GenericCubicSpecs.CE_feval.
      rewrite Hfst, Hsnd.
      cbn [AbstractField.feval bw6_Fp3_repr CE_field_representation].
      unfold GenericCubicSpecs.CE_feval.
      rewrite Hc0fst, Hc1fst, Hc2fst, Hc0snd, Hc1snd, Hc2snd.
      change (feval O0, feval O1, feval O2, (feval O3, feval O4, feval O5))
        with (feval_Fp6_slots O0 O1 O2 O3 O4 O5).
      rewrite Hfeval.
      unfold cubic_first_fp6_frob_p3_model,
             frobenius_fp6_p3_gallina,
             fp6_mk, fp6_c0, fp6_c1, fp3_mk, fp3_a0, fp3_a1, fp3_a2,
             feval_Fp6_slots, feval_Fp3_slots.
      reflexivity.
    - apply (BW6_Fp6_join_from_lib_slots pout O0 O1 O2 O3 O4 O5 _ _
               HlO0 HlO1 HlO2 HlO3 HlO4 HlO5) in Hmem'.
      assert (Hmem_px :
        (PairingFieldOpsCubicFirst.FElem_Fp6_slots (F_representation := bw6_Fp_repr) px
           slot_x_c0c0 slot_x_c0c1 slot_x_c0c2 slot_x_c1c0 slot_x_c1c1 slot_x_c1c2
         ⋆ (FElem_Fp6 pout CONCAT
            ⋆ (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6_p3
                 slot_g_0 slot_g_1 slot_g_2 ⋆ Rr)))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem'.
      apply (BW6_Fp6_from_lib_slots px x _ _ Hlen_x) in Hmem_px.
      assert (Hmem_g :
        (PairingFieldOpsCubicFirst.FElem_Fp3_slots (F_representation := bw6_Fp_repr) p_gfp6_p3
           slot_g_0 slot_g_1 slot_g_2
         ⋆ (FElem_Fp6 pout CONCAT ⋆ (FElem_Fp6 px x ⋆ Rr)))%sep mem')
        by (use_sep_assumption; cancel).
      clear Hmem_px.
      apply (BW6_Fp3_from_lib_slots p_gfp6_p3 gfp6 _ _ Hlen_g) in Hmem_g.
      use_sep_assumption; cancel.
  Qed.

  (* ============================================================== *)
  (* bw6_fp6_conjugate: out.c0 = x.c0, out.c1 = -x.c1.               *)
  (* Body is 2 calls: fp3_copy + fp3_opp.  Spec post is just         *)
  (* loose bounds + sep (no algebraic equation).                     *)
  (* ============================================================== *)

  Local Instance spec_of_Fp3_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp3)) :=
    AbstractField.spec_of_felem_copy (F:=Fp3) (field_representation:=bw6_Fp3_repr).

  Local Instance spec_of_Fp3_opp : spec_of (AbstractField.opp (F:=Fp3)) :=
    AbstractField.unop_spec (F:=Fp3) (field_representation:=bw6_Fp3_repr) AbstractField.un_opp.

  (* Fp6 → Fp3 projections pinned to the bw6_Fp3 instance (matches the
     convention in BW6_761_PairingHelpers).  Pinning the instance is
     load-bearing: bare [qe_fst_felem x] would let Coq pick the bw6_Fp6
     instance in some positions, which is a different function. *)
  Local Notation fp3_fst := (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr).
  Local Notation fp3_snd := (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr).
  Local Notation Fp3_loose :=
    (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation fp3_off :=
    (word.of_Z (Memory.bytes_per_word 64 *
      Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))).

  Theorem bw6_fp6_conjugate_ok :
    forall functions
      (EnvContains :
         map.get functions "bw6_fp6_conjugate" =
         Some (snd bw6_fp6_conjugate))
      (HFp3copy : spec_of_Fp3_felem_copy functions)
      (HFp3opp  : spec_of_Fp3_opp functions),
    spec_of_bw6_fp6_conjugate functions.
  Proof.
    intros functions EnvContains HFp3copy HFp3opp.
    unfold spec_of_bw6_fp6_conjugate.
    intros pout px old_out x Rr tr mem [Hbx Hmem].
    eapply WeakestPreconditionProperties.start_func; [eassumption | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold bw6_fp6_conjugate. simpl snd. simpl fst. cbv match beta.
    eexists. split. 1: exact eq_refl.
    assert (Hbx_split : Fp3_bounded Fp3_tight (fp3_fst x) /\
                        Fp3_bounded Fp3_tight (fp3_snd x)) by exact Hbx.
    destruct Hbx_split as [Hbx_c0 Hbx_c1].
    clear Hbx.
    apply FElem_Fp6_split_in_sep in Hmem.
    eassert (Hx_in : (FElem_Fp6 px x ⋆ _)%sep mem).
    { ecancel_assumption. }
    apply FElem_Fp6_split_in_sep in Hx_in.
    unfold BW6_761_FinalExp.cmd_seq_list.
    (* Call 1: fp3_copy out.c0 := x.c0 *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists; split.
    { eexists; split; [exact eq_refl |]. eexists; split; [exact eq_refl |]. exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply HFp3copy.
      split.
      { SeparationLogic.ecancel_assumption_impl. }
      { SeparationLogic.ecancel_assumption_impl. } }
    cbv beta. intros ? ? ? [? Hsep_c0]. subst.
    destruct Hsep_c0 as [? Hsep_c0]. subst.
    cbv [map.putmany_of_list_zip]. eexists. split. 1: exact eq_refl.
    (* Call 2: fp3_opp out.c1 := -x.c1 *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists; split.
    { eexists; split; [exact eq_refl |]. eexists; split; [exact eq_refl |]. exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply HFp3opp.
      split. { exact Hbx_c1. }
      split. { eexists; SeparationLogic.ecancel_assumption_impl. }
      SeparationLogic.ecancel_assumption_impl. }
    cbv beta. intros tr2 m2 rets2 Hpost2.
    destruct Hpost2 as [Hrets2 [Htreq2 [out_c1_new [Hfeval_c1_eq [Hb_c1_new_loose Hsep_c1]]]]].
    subst rets2. subst t'.
    (* Length witnesses *)
    pose proof Hsep_c0 as Htmp1.
    destruct Htmp1 as [mA1 [mB1 [Hsp1 [HFx_c0 Hjunk1]]]].
    pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFx_c0) as Hlen_xc0.
    pose proof Hsep_c1 as Htmp2.
    destruct Htmp2 as [mA2 [mB2 [Hsp2 [HFc1_new Hjunk2]]]].
    pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFc1_new) as Hlen_c1_new.
    (* Postcondition *)
    cbv [map.putmany_of_list_zip]. eexists. split. 1: exact eq_refl.
    cbv [list_map list_map_body]. split. 1: exact eq_refl. split. 1: exact eq_refl.
    exists (fp3_fst x ++ out_c1_new).
    set (out_full := fp3_fst x ++ out_c1_new).
    split.
    { (* Bounds: Fp6_loose out_full = (Fp3_loose (fp3_fst out_full), Fp3_loose (fp3_snd out_full)) *)
      cut (Fp3_bounded Fp3_loose (fp3_fst out_full) /\
           Fp3_bounded Fp3_loose (fp3_snd out_full)).
      { intro HH; exact HH. }
      assert (Hq0 : fp3_fst out_full = fp3_fst x).
      { subst out_full. unfold qe_fst_felem. apply GenericSplitJoin.firstn_app_le. exact Hlen_xc0. }
      assert (Hq1 : fp3_snd out_full = out_c1_new).
      { subst out_full. unfold qe_snd_felem. apply GenericSplitJoin.skipn_app_le. exact Hlen_xc0. }
      rewrite Hq0, Hq1.
      split.
      { exact (@AbstractField.relax_bounds _ _ _ _ _ _ bw6_Fp3_repr bw6_Fp3_repr_ok _ Hbx_c0). }
      { exact Hb_c1_new_loose. } }
    (* Sep: rejoin pout's two Fp3 into FElem_Fp6; rejoin px's two into FElem_Fp6 px x *)
    eassert (Hj_out : (FElem_Fp3 pout (fp3_fst x) ⋆
                       (FElem_Fp3 (word.add pout fp3_off) out_c1_new ⋆ _))%sep m2).
    { SeparationLogic.ecancel_assumption_impl. }
    apply (FElem_Fp3_join_in_sep pout (fp3_fst x) out_c1_new _ m2 Hlen_xc0 Hlen_c1_new) in Hj_out.
    (* px: rejoin fp3_fst x ++ fp3_snd x = x *)
    pose proof Hsep_c1 as Htmp3.
    destruct Htmp3 as [mC0 [mC1 [HspC [HjC HrestC3]]]].
    destruct HrestC3 as [mD0 [mD1 [HspD [HjD HrestC4]]]].
    destruct HrestC4 as [mE0 [mE1 [HspE [HjE HrestC5]]]].
    destruct HrestC5 as [mF0 [mF1 [HspF [HFx_c1 HjF]]]].
    pose proof (GenericSplitJoin.generic_FElem_length _ _ _ HFx_c1) as Hlen_xc1.
    eassert (Hj_x : (FElem_Fp3 px (fp3_fst x) ⋆
                     (FElem_Fp3 (word.add px fp3_off) (fp3_snd x) ⋆ _))%sep m2).
    { SeparationLogic.ecancel_assumption_impl. }
    apply (FElem_Fp3_join_in_sep px (fp3_fst x) (fp3_snd x) _ m2 Hlen_xc0 Hlen_xc1) in Hj_x.
    assert (Hxsplit : fp3_fst x ++ fp3_snd x = x).
    { unfold qe_fst_felem, qe_snd_felem. apply firstn_skipn. }
    rewrite Hxsplit in Hj_x.
    subst out_full.
    SeparationLogic.ecancel_assumption_impl.
  Qed.

End BW6_FrobLibBridge.
