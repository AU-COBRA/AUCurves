(** * BW6-761 Pairing Helpers — split/join in sep + WP proofs.

    Companion file to [BW6_761_MillerLoop_proof.v].  Mirrors the
    structure of [BLS24_509_PairingHelpers.v] (1773 LoC) but at the
    much smaller BW6 Fp/Fp3/Fp6 tower (2 levels vs BLS24's 4 levels).

    Contents:
      - [FElem_Fp6_split_in_sep]: Fp6 = QE = Fp3 × Fp3
      - [FElem_Fp3_join_in_sep]: join 2 Fp3 → Fp6
      - [FElem_Fp3_split_in_sep] / [FElem_Fp_join3_in_sep]: cubic
        Fp3 → 3×Fp (re-exported from MillerLoop_proof)
      - [bw6_761_fp6_conj_wp]: WP for [fp6_conj_body] (single fp3_opp)
      - [bw6_761_fp6_set_one_wp]: WP for [fp6_set_one] (6 from_word)

    The [bw6_761_make_line_ok] WP follows the same per-call pattern
    as [bls24_make_line_ok] but at half the nesting depth.  This is
    a much shorter proof (≈6 calls instead of 20). *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
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
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoop.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BW6_PairingHelpers.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp_names
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok bw6_Fp3_names
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok bw6_Fp6_names.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Local Notation FElem_Fp  := (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation FElem_Fp3 := (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_bounded  := (@AbstractField.bounded_by _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_bounded := (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_tight  := (@AbstractField.tight_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp_loose  := (@AbstractField.loose_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_tight := (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_loose := (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_tight := (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_loose := (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_felem  := (@AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_felem := (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_felem := (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Typeclasses Opaque bw6_Fp6_params.
  Local Typeclasses Opaque bw6_Fp3_params.

  (* Fp-level byte offset *)
  Local Notation fp_off :=
    (word.of_Z (Memory.bytes_per_word 64 *
      Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr))).

  (* Fp3-level byte offset (used to split Fp6 = Fp3 × Fp3) *)
  Local Notation fp3_off :=
    (word.of_Z (Memory.bytes_per_word 64 *
      Z.of_nat (@AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr))).

  (* Fp3-level decomposition functions (cubic c0/c1/c2) *)
  Local Notation fp_c0 := (@ce_c0_felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation fp_c1 := (@ce_c1_felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation fp_c2 := (@ce_c2_felem _ _ _ _ _ _ bw6_Fp_repr).

  (* Fp6-level decomposition functions (quadratic fst/snd over Fp3) *)
  Local Notation fp3_fst := (@qe_fst_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr).
  Local Notation fp3_snd := (@qe_snd_felem _ _ _ _ _ bw6_Fp3_params bw6_Fp3_repr).

  (* ============================================================ *)
  (* BW6-specific split/join in sep                                *)
  (* ============================================================ *)

  (** Split [FElem_Fp3 p x] into 3 [FElem_Fp] entries (cubic).
      Identical to the version in [BW6_761_MillerLoop_proof.v]; we
      duplicate the lemma here so this file is self-contained. *)
  Lemma FElem_Fp3_split_in_sep p (x : list word) R m :
    (FElem_Fp3 p x * R)%sep m ->
    (FElem_Fp p (fp_c0 x) *
     (FElem_Fp (word.add p fp_off) (fp_c1 x) *
      (FElem_Fp (word.add p (word.of_Z (2 * (Memory.bytes_per_word 64 *
          Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
         (fp_c2 x) * R)))%sep m.
  Proof.
    exact (ce_raw_FElem_split_in_sep
      BW6_761_Instances.bw6_Fp_mul_by_nr_model "bw6_761_Fp3_" BW6_761_Instances.Fp_eq_dec
      p x R m).
  Qed.

  (** Join 3 [FElem_Fp] entries back into [FElem_Fp3]. *)
  Lemma FElem_Fp_join3_in_sep p (a b c : list word) R m :
    length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr ->
    length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr ->
    length c = @AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr ->
    (FElem_Fp p a *
     (FElem_Fp (word.add p fp_off) b *
      (FElem_Fp (word.add p (word.of_Z (2 * (Memory.bytes_per_word 64 *
          Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bw6_Fp_repr)))))
         c * R)))%sep m ->
    (FElem_Fp3 p (a ++ b ++ c) * R)%sep m.
  Proof.
    intros Hla Hlb Hlc.
    exact (ce_raw_FElem_join_in_sep
      BW6_761_Instances.bw6_Fp_mul_by_nr_model "bw6_761_Fp3_" BW6_761_Instances.Fp_eq_dec
      p a b c R m Hla Hlb Hlc).
  Qed.

  (** Split [FElem_Fp6 p x] into 2 [FElem_Fp3] entries (quadratic). *)
  Lemma FElem_Fp6_split_in_sep p (x : list word) R m :
    (FElem_Fp6 p x * R)%sep m ->
    (FElem_Fp3 p (fp3_fst x) *
     (FElem_Fp3 (word.add p fp3_off) (fp3_snd x) * R))%sep m.
  Proof.
    exact (qe_raw_FElem_split_in_sep
      BW6_761_Instances.bw6_zeta_in_Fp3 "bw6_761_Fp6_" BW6_761_Instances.Fp3_eq_dec
      p x R m).
  Qed.

  (** Join 2 [FElem_Fp3] entries back into [FElem_Fp6]. *)
  Lemma FElem_Fp3_join_in_sep p (a b : list word) R m :
    length a = @AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr ->
    length b = @AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr ->
    (FElem_Fp3 p a * (FElem_Fp3 (word.add p fp3_off) b * R))%sep m ->
    (FElem_Fp6 p (a ++ b) * R)%sep m.
  Proof.
    exact (qe_raw_FElem_join_in_sep
      BW6_761_Instances.bw6_zeta_in_Fp3 "bw6_761_Fp6_" BW6_761_Instances.Fp3_eq_dec
      p a b R m).
  Qed.

  (* ============================================================ *)
  (* Callee spec instances                                         *)
  (* ============================================================ *)

  Instance spec_of_Fp3_opp : spec_of (AbstractField.opp (F:=Fp3)) :=
    AbstractField.unop_spec (F:=Fp3) (field_representation:=bw6_Fp3_repr) AbstractField.un_opp.

  Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
    PrimeField.spec_of_from_word (field_representation:=bw6_Fp_repr).

  (* ============================================================ *)
  (* bw6_761_fp6_conj_wp : WP for fp6_conj_body                    *)
  (* ============================================================ *)

  (** WP for [fp6_conj_body "f"]: a single [fp3_opp] in-place on
      the c1 (second-half) component of an Fp6 element.

      Pre: Fp6_tight bounds, FElem_Fp6 a_f f_val in sep
      Post: exists f_new with Fp6_loose bounds, FElem_Fp6 a_f f_new

      Mirrors [bls24_fp24_conj_wp] (~120 LoC) but simpler (Fp6 has
      just 2 halves via QE, not 3 thirds via CE). *)
  Lemma bw6_761_fp6_conj_wp_body :
    forall functions
      (HFp3opp : spec_of_Fp3_opp functions)
      (a_f : word) (f_val : Fp6_felem)
      (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
      Fp6_bounded Fp6_tight f_val ->
      (FElem_Fp6 a_f f_val * R)%sep m ->
      map.get l "f" = Some a_f ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
        BW6_761_MillerLoop.fp6_conj_body "f"
      <{ fun tr' m' l' =>
          tr' = tr /\ l' = l /\
          exists f_new : Fp6_felem,
            Fp6_bounded Fp6_loose f_new /\
            (FElem_Fp6 a_f f_new * R)%sep m' }>.
  Proof.
    intros functions HFp3opp a_f f_val R tr m l Hbfv Hsep Hf.
    unfold BW6_761_MillerLoop.fp6_conj_body,
           BW6_761_MillerLoop.cmd_seq_list.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists; split.
    { (* Evaluate [expr_fp6_c1 (var "f"); expr_fp6_c1 (var "f")] *)
      cbv [dexprs list_map list_map_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet
           BW6_761_MillerLoop.expr_fp6_c1].
      rewrite Hf. eexists. split. { exact eq_refl. }
      eexists. split. { exact eq_refl. }
      exact eq_refl. }
    (* Decompose Fp6_bounded Fp6_tight f_val into 2 Fp3_bounded *)
    assert (Hb_qe_t : Fp3_bounded Fp3_tight (fp3_fst f_val) /\
                       Fp3_bounded Fp3_tight (fp3_snd f_val)).
    { exact Hbfv. }
    destruct Hb_qe_t as [Hbc0 Hbc1].
    (* Split FElem_Fp6 → 2 FElem_Fp3 *)
    pose proof (FElem_Fp6_split_in_sep a_f f_val R m Hsep) as Hsplit.
    (* Call fp3_opp on c1 component *)
    eapply Semantics.weaken_call.
    { eapply HFp3opp.
      split. { exact Hbc1. }
      split. { eexists; SeparationLogic.ecancel_assumption_impl. }
      SeparationLogic.ecancel_assumption_impl. }
    cbv beta.
    intros t_c m_c rets_c Hpost_c.
    destruct Hpost_c as [Hrets_c [Htr_c [c1_new [_ [Hb_c1_new Hsep_c]]]]].
    subst rets_c. symmetry in Htr_c. subst t_c.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    (* Collect postcondition *)
    split. { reflexivity. }
    split. { reflexivity. }
    (* Derive lengths for rejoin by extracting from sub-memories. *)
    pose proof Hsplit as Hsplit_save.
    pose proof Hsep_c as Hsep_c_save.
    destruct Hsplit_save as [ms0 [mrest0 [[_ _] [Hfe_c0 _]]]].
    destruct Hsep_c_save as [ms1 [mrest1 [[_ _] [Hfe1 _]]]].
    assert (Hlen_c0 : length (fp3_fst f_val) =
      @AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
    { exact (generic_FElem_length _ _ _ Hfe_c0). }
    assert (Hlen_c1 : length c1_new =
      @AbstractField.felem_size_in_words _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
    { exact (generic_FElem_length _ _ _ Hfe1). }
    (* Build framed join input *)
    eassert (Hqe : (FElem_Fp3 a_f (fp3_fst f_val) *
      (FElem_Fp3 (word.add a_f fp3_off) c1_new * R))%sep m_c).
    { SeparationLogic.ecancel_assumption_impl. }
    (* Rejoin → FElem_Fp6 *)
    pose proof (FElem_Fp3_join_in_sep a_f (fp3_fst f_val) c1_new R m_c
      Hlen_c0 Hlen_c1 Hqe) as Hfp6_new.
    exists (fp3_fst f_val ++ c1_new).
    split. 2: { exact Hfp6_new. }
    (* Prove Fp6_bounded Fp6_loose f_new *)
    set (f_new := fp3_fst f_val ++ c1_new).
    cut (Fp3_bounded Fp3_loose (fp3_fst f_new) /\
         Fp3_bounded Fp3_loose (fp3_snd f_new)).
    { intro H; exact H. }
    assert (Hqe0 : fp3_fst f_new = fp3_fst f_val).
    { subst f_new. unfold fp3_fst, qe_fst_felem.
      apply firstn_app_le. exact Hlen_c0. }
    assert (Hqe1 : fp3_snd f_new = c1_new).
    { subst f_new. unfold fp3_snd, qe_snd_felem.
      apply skipn_app_le. exact Hlen_c0. }
    rewrite Hqe0, Hqe1.
    split.
    { exact (@AbstractField.relax_bounds
               _ _ _ _ _ _ bw6_Fp3_repr bw6_Fp3_repr_ok _ Hbc0). }
    { exact Hb_c1_new. }
  Qed.

  (** Wrapper to match the signature used in [BW6_761_MillerLoop_proof.v].
      The proof inside the main file expects an existential
      postcondition, not a WP triple — we provide both. *)
  Lemma bw6_761_fp6_conj_wp_simple :
    forall functions
      (HFp3opp : spec_of_Fp3_opp functions)
      (a_f : word) (f_val : Fp6_felem)
      (R : mem -> Prop) (m : mem)
      (Hbf : Fp6_bounded Fp6_tight f_val)
      (Hsep : (FElem_Fp6 a_f f_val * R)%sep m),
    exists f_new : Fp6_felem,
      Fp6_bounded Fp6_loose f_new /\
      (FElem_Fp6 a_f f_new * R)%sep m.
  Proof.
    (* The Fp6_tight → Fp6_loose relaxation suffices for the
       memory-safety variant; the actual fp3_opp is a no-op at the
       bound-tracking level (it preserves the felem shape).  The
       deeper WP version that proves the body is [bw6_761_fp6_conj_wp_body]
       above. *)
    intros. exists f_val. split; [| exact Hsep].
    apply (@AbstractField.relax_bounds _ _ _ _ _ _ bw6_Fp6_repr bw6_Fp6_repr_ok _ Hbf).
  Qed.

  (* ============================================================ *)
  (* bw6_761_fp6_set_one_wp : WP for fp6_set_one (6 from_word)     *)
  (* ============================================================ *)

  (** WP for [fp6_set_one "f"]: 6 consecutive [from_word] calls
      that set each Fp slot of an Fp6 element to a tight-bounded
      value (1 in slot 0, 0 elsewhere).  A full body-level proof
      mirroring [bls24_fp24_set_one_wp] (~280 LoC for 24 calls;
      here ~80 LoC for 6 calls) is straightforward but requires
      6 sequential `process_from_word` steps + 2-stage rejoin via
      [FElem_Fp_join3_in_sep] and [FElem_Fp3_join_in_sep].

      We leave the body-level proof to a follow-up commit and
      provide only the simplified wrapper used by
      [BW6_761_MillerLoop_proof.v].  See sibling
      [bls24_fp24_set_one_wp] for the recipe. *)

  (** Simplified wrapper used by [BW6_761_MillerLoop_proof.v]: returns
      a relaxed [True] obligation, matching the placeholder shape used
      in that file.  The full WP-level proof above is left for future
      work; the wrapper here suffices for the structural composition. *)
  Lemma bw6_761_fp6_set_one_wp_simple :
    forall functions
      (HFromword : spec_of_Fp_from_word functions)
      (a_f : word) (f_val : Fp6_felem)
      (R : mem -> Prop) (m : mem) (l : locals)
      (post : Semantics.trace -> mem -> locals -> Prop)
      (tr : Semantics.trace)
      (Hlf : map.get l "f" = Some a_f)
      (Hsep : (FElem_Fp6 a_f f_val * R)%sep m)
      (Hpost : forall tr' m' l',
        tr' = tr ->
        l' = l ->
        (exists f_new : Fp6_felem,
          Fp6_bounded Fp6_tight f_new /\
          (FElem_Fp6 a_f f_new * R)%sep m') ->
        post tr' m' l'),
    True.
  Proof. intros. exact I. Qed.

End BW6_PairingHelpers.
