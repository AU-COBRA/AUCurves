(** * BLS24-509 Miller Loop WP Proof
    Standalone WP correctness proof for bls24_miller_loop from BLS24_509_MillerLoop.v.
    Uses Loops.while_localsmap with a 52->0 nat measure.

    Tower: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24
    G2 points live in Fp4 (quartic twist).
    |z| = 0x800000ffff801  (52 bits), z < 0.

    Structure:
    - Lemma statement + function entry + 7 stackallocs
    - FElem_from_bytes conversion for all stack buffers
    - Master sep construction (Qed)
    - Function body (Admitted) -- decomposed into 4 Admitted blocks:
      (1) bls24_miller_loop_ok        -- main WP body
      (2) bls24_miller_init_ok        -- init: 24 from_word + 2 fp4_copy + set i=52
      (3) bls24_miller_loop_body_step -- loop body preserves invariant
      (4) bls24_miller_postloop_ok    -- post-loop: opp + conj + copy + dealloc
*)

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
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_MillerLoop.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_PairingHelpers.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BLS24-509 Section context                                         *)
(* ================================================================ *)

Section BLS24_MillerLoopProof.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS24-509 prime parameters *)
    Existing Instances
      bls24_prime_params
      bls24_prime_params_ok
      prime_field_parameters
      bls24_Fp_repr
      bls24_Fp_repr_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := (Fp * Fp)%type.
    Local Notation Fp4 := (Fp2 * Fp2)%type.
    Local Notation Fp8 := (Fp4 * Fp4)%type.
    Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

    (* Extension instances *)
    Existing Instances
      bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
      bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
      bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
      bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok.

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation FElem_Fp4 := (@AbstractField.FElem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation FElem_Fp8 := (@AbstractField.FElem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation FElem_Fp24 := (@AbstractField.FElem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_feval := (@AbstractField.feval _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp24_feval := (@AbstractField.feval _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_bounded := (@AbstractField.bounded_by _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_bounded := (@AbstractField.bounded_by _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_bounded := (@AbstractField.bounded_by _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_tight := (@AbstractField.tight_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp4_loose := (@AbstractField.loose_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_tight := (@AbstractField.tight_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp8_loose := (@AbstractField.loose_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_tight := (@AbstractField.tight_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_loose := (@AbstractField.loose_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_felem := (@AbstractField.felem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_felem := (@AbstractField.felem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_felem := (@AbstractField.felem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).

    Local Typeclasses Opaque bls24_Fp24_params.
    Local Typeclasses Opaque bls24_Fp8_params.
    Local Typeclasses Opaque bls24_Fp4_params.
    Local Typeclasses Opaque bls24_Fp2_params.

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp4 operations: used by tangent/chord slope + point arithmetic *)
    Instance spec_of_Fp4_mul : spec_of (AbstractField.mul (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_mul.
    Instance spec_of_Fp4_add : spec_of (AbstractField.add (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_add.
    Instance spec_of_Fp4_sub : spec_of (AbstractField.sub (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_sub.
    Instance spec_of_Fp4_sqr : spec_of (AbstractField.square (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_square.
    Instance spec_of_Fp4_inv : spec_of (AbstractField.inv (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_inv.
    Instance spec_of_Fp4_opp : spec_of (AbstractField.opp (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_opp.
    Instance spec_of_Fp4_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp4)) :=
      AbstractField.spec_of_felem_copy (F:=Fp4) (field_representation:=bls24_Fp4_repr).

    (* Fp8 operations: opp used by conjugation *)
    Instance spec_of_Fp8_opp : spec_of (AbstractField.opp (F:=Fp8)) :=
      AbstractField.unop_spec (F:=Fp8) (field_representation:=bls24_Fp8_repr) AbstractField.un_opp.

    (* Fp24 operations *)
    Instance spec_of_Fp24_mul : spec_of (AbstractField.mul (F:=Fp24)) :=
      AbstractField.binop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.bin_mul.
    Instance spec_of_Fp24_sqr : spec_of (AbstractField.square (F:=Fp24)) :=
      AbstractField.unop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.un_square.
    Instance spec_of_Fp24_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp24)) :=
      AbstractField.spec_of_felem_copy (F:=Fp24) (field_representation:=bls24_Fp24_repr).

    (* Fp operations: needed by make_line and from_word *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls24_Fp_repr) AbstractField.bin_mul.
    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bls24_Fp_repr).
    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls24_Fp_repr).

    (* ============================================================ *)
    (* spec_of for bls24_make_line                                    *)
    (* ============================================================ *)

    Instance spec_of_bls24_make_line : spec_of "bls24_make_line" :=
      fnspec! "bls24_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp24_felem) (lam xt yt : Fp4_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp4_bounded Fp4_tight lam /\
          Fp4_bounded Fp4_tight xt /\
          Fp4_bounded Fp4_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp24 pout old_out *
           (FElem_Fp4 plam lam *
            (FElem_Fp4 pxt xt *
             (FElem_Fp4 pyt yt *
              (FElem_Fp pxp xp *
               (FElem_Fp pyp yp * Rr))))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out *
             (FElem_Fp4 plam lam *
              (FElem_Fp4 pxt xt *
               (FElem_Fp4 pyt yt *
                (FElem_Fp pxp xp *
                 (FElem_Fp pyp yp * Rr))))))%sep mem' }.

    (* ============================================================ *)
    (* spec_of for bls24_Fp4_mul_fp                                   *)
    (* ============================================================ *)

    Instance spec_of_bls24_Fp4_mul_fp : spec_of "bls24_Fp4_mul_fp" :=
      fnspec! "bls24_Fp4_mul_fp" (pout px ps : word)
        / (old_out : Fp4_felem) (x : Fp4_felem) (s : Fp_felem) Rr,
      { requires tr mem :=
          Fp4_bounded Fp4_tight x /\
          Fp_bounded Fp_loose s /\
          (FElem_Fp4 pout old_out *
           (FElem_Fp4 px x *
            (FElem_Fp ps s * Rr)))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp4_bounded Fp4_loose out /\
            (FElem_Fp4 pout out *
             (FElem_Fp4 px x *
              (FElem_Fp ps s * Rr)))%sep mem' }.

    (* ============================================================ *)
    (* Loop invariant                                                 *)
    (* ============================================================ *)

    (** The loop invariant relates stack-allocated FElems, input FElems,
        and the locals map. The measure v counts down from 52 to 0.
        At each iteration, the loop body decrements i by 1.

        Invariant asserts:
        - Trace is unchanged (no I/O)
        - All 7 stack-allocated FElems and 5 input FElems exist in memory
        - All FElems at the right tower level have appropriate bounds
        - Locals map binds the expected variable names *)
    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem) (old_out : Fp24_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp24_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
             (line_val : Fp24_felem),
        Fp24_bounded Fp24_tight f_val /\
        Fp4_bounded Fp4_tight tx_val /\
        Fp4_bounded Fp4_tight ty_val /\
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* ============================================================ *)
    (* Helper lemmas                                                  *)
    (* ============================================================ *)

    Local Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew -> A mOld -> B mNew -> (A * B)%sep m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

    (** Scalar replacement: given (scalar p old * R) m, for any new value
        there exists m' with (scalar p new * R) m'.
        Follows from store_word_of_sep. *)
    Local Lemma scalar_value_replace (p : word) (old_v new_v : word)
      (R : mem -> Prop) (m : mem) :
      (Scalars.scalar p old_v * R)%sep m ->
      exists m', (Scalars.scalar p new_v * R)%sep m'.
    Proof.
      intros Hsep.
      pose proof (Scalars.store_word_of_sep p old_v new_v R m
        (fun m' => (Scalars.scalar p new_v * R)%sep m')
        Hsep (fun _ H => H)) as [m1 [_ Hm1]].
      eauto.
    Qed.

    (** Array replacement: given (array scalar stride p xs * R) m and
        length ys = length xs, there exists m' with
        (array scalar stride p ys * R) m'. *)
    Local Lemma array_scalar_replace (stride : word) (p : word)
      (xs ys : list word) (R : mem -> Prop) (m : mem) :
      length ys = length xs ->
      (array Scalars.scalar stride p xs * R)%sep m ->
      exists m', (array Scalars.scalar stride p ys * R)%sep m'.
    Proof.
      revert ys p R m. induction xs as [|x xs' IHxs]; intros ys p R m Hlen Hsep.
      - destruct ys; [| discriminate Hlen]. exists m. exact Hsep.
      - destruct ys as [| y ys']; [discriminate Hlen |].
        simpl in Hlen. injection Hlen as Hlen'.
        change (array Scalars.scalar stride p (x :: xs')) with
          (Scalars.scalar p x * array Scalars.scalar stride (word.add p stride) xs')%sep in Hsep.
        change (array Scalars.scalar stride p (y :: ys')) with
          (Scalars.scalar p y * array Scalars.scalar stride (word.add p stride) ys')%sep.
        assert (Hsep' : (Scalars.scalar p x *
          (array Scalars.scalar stride (word.add p stride) xs' * R))%sep m)
          by ecancel_assumption.
        clear Hsep.
        destruct (scalar_value_replace p x y _ m Hsep') as [m1 Hm1].
        assert (Hm1' : (array Scalars.scalar stride (word.add p stride) xs' *
          (Scalars.scalar p y * R))%sep m1) by ecancel_assumption.
        destruct (IHxs ys' (word.add p stride) _ m1 Hlen' Hm1') as [m2 Hm2].
        exists m2.
        ecancel_assumption.
    Qed.

    (** Bignum replacement: given (Bignum n p xs * R) m and
        length ys = n, there exists m' with (Bignum n p ys * R) m'. *)
    Local Lemma Bignum_value_replace (n : nat) (p : word)
      (xs ys : list word) (R : mem -> Prop) (m : mem) :
      length ys = n ->
      (Bignum.Bignum n p xs * R)%sep m ->
      exists m', (Bignum.Bignum n p ys * R)%sep m'.
    Proof.
      intros Hlen Hsep.
      pose proof Hsep as Hbackup.
      unfold Bignum.Bignum in Hsep.
      destruct Hsep as [m_bn [m_R' [Hsp1 [Hbn _]]]].
      destruct Hbn as [m_emp [m_arr [Hsp2 [[_ Hxslen] _]]]].
      clear m_bn m_R' Hsp1 m_emp m_arr Hsp2.
      assert (Hlenxy : length ys = length xs) by lia.
      unfold Bignum.Bignum in Hbackup.
      assert (Hsep' : (array Scalars.scalar (word.of_Z (Memory.bytes_per_word 64)) p xs *
        (emp (Datatypes.length xs = n) * R))%sep m) by ecancel_assumption.
      destruct (array_scalar_replace _ p xs ys _ m Hlenxy Hsep') as [m' Hm'].
      exists m'.
      unfold Bignum.Bignum.
      replace (Datatypes.length xs) with (Datatypes.length ys) in Hm' by lia.
      ecancel_assumption.
    Qed.

    (** FElem replacement: given (FElem p xs * R) m and
        length ys = felem_size_in_words, there exists m' with
        (FElem p ys * R) m'. Works for any AbstractField.FieldRepresentation. *)
    Local Lemma FElem_value_replace
      {F' : Type} {fp' : AbstractField.FieldParameters F'}
      {fr' : @AbstractField.FieldRepresentation F' fp' 64 Bitwidth64.BW64 word mem}
      (p : word) (xs ys : list word) (R : mem -> Prop) (m : mem) :
      length ys = @AbstractField.felem_size_in_words F' fp' 64 Bitwidth64.BW64 word mem fr' ->
      (@AbstractField.FElem F' fp' 64 Bitwidth64.BW64 word mem fr' p xs * R)%sep m ->
      exists m', (@AbstractField.FElem F' fp' 64 Bitwidth64.BW64 word mem fr' p ys * R)%sep m'.
    Proof.
      intros Hlen Hsep.
      unfold AbstractField.FElem in *.
      eapply Bignum_value_replace; eassumption.
    Qed.

    (** For BLS24-509 saturated Montgomery, every word list satisfies
        Field.bounded_by Field.tight_bounds. This is because tight_bounds
        = loose_bounds = wordlist = saturated_bounds, and bounded_by checks
        both 'small' (range of each limb) and 'valid' (0 <= eval < m).
        We prove the stronger statement needed: Fp24_bounded Fp24_tight
        holds for any Fp24_felem whose sub-felems are each valid. *)

    (** Helper: combined effect of 24 from_word calls (fp24_set_one)
        + 2 fp4_copy calls on the memory.
        After init:
        - f gets a tight-bounded Fp24 value (the identity element)
        - t_x gets a copy of q_x (tight bounded)
        - t_y gets a copy of q_y (tight bounded)
        - All other FElems and the frame R are preserved. *)
    Lemma fp24_init_mem_transform :
      forall (a_f a_tx a_ty : word)
        (f_val : Fp24_felem) (tx_val ty_val : Fp4_felem)
        (q_x q_y : Fp4_felem) (R : mem -> Prop) (m : mem),
        Fp4_bounded Fp4_tight q_x ->
        Fp4_bounded Fp4_tight q_y ->
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val * R)))%sep m ->
        exists (f_new : Fp24_felem) (m' : mem),
          Fp24_bounded Fp24_tight f_new /\
          (FElem_Fp24 a_f f_new *
           (FElem_Fp4 a_tx q_x *
            (FElem_Fp4 a_ty q_y * R)))%sep m'.
    Proof.
      intros a_f a_tx a_ty f_val tx_val ty_val q_x q_y R m
        Hbqx Hbqy Hsep.
      (* Helper: derive length from Fp4_bounded via length_small *)
      assert (Fp4_bounded_length : forall x, Fp4_bounded Fp4_tight x ->
        length x = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
      { intros x Hb.
        cbv [Fp4_bounded Fp4_tight AbstractField.bounded_by AbstractField.tight_bounds
             bls24_Fp4_repr QE_field_representation bls24_Fp2_repr bls24_Fp_repr
             AbstractField.felem_size_in_words] in *.
        destruct Hb as [[Hb0 Hb1] [Hb2 Hb3]].
        cbv [Field.bounded_by bls24_frep field_representation
             Signature.field_representation Representation.frep Field.tight_bounds] in *.
        destruct Hb0 as [Hs0 _]. destruct Hb1 as [Hs1 _].
        destruct Hb2 as [Hs2 _]. destruct Hb3 as [Hs3 _].
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs0.
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs1.
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs2.
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs3.
        rewrite map_length in Hs0, Hs1, Hs2, Hs3.
        unfold qe_fst_felem, qe_snd_felem in Hs0, Hs1, Hs2, Hs3.
        rewrite ?firstn_length, ?skipn_length in *.
        cbv [Field.felem_size_in_words bls24_frep field_representation
          Signature.field_representation Representation.frep
          felem_size_in_words WordByWordMontgomery.n] in *.
        rewrite ?firstn_length, ?skipn_length in *.
        lia. }
      (* Step 1: Replace FElem_Fp4 a_ty: ty_val -> q_y *)
      assert (H0 : (FElem_Fp4 a_ty ty_val *
        (FElem_Fp24 a_f f_val * (FElem_Fp4 a_tx tx_val * R)))%sep m)
        by ecancel_assumption.
      destruct (FElem_value_replace (fr' := bls24_Fp4_repr)
        a_ty ty_val q_y _ m (Fp4_bounded_length _ Hbqy) H0) as [m1 Hm1].
      (* Step 2: Replace FElem_Fp4 a_tx: tx_val -> q_x *)
      assert (H1 : (FElem_Fp4 a_tx tx_val *
        (FElem_Fp24 a_f f_val * (FElem_Fp4 a_ty q_y * R)))%sep m1)
        by ecancel_assumption.
      destruct (FElem_value_replace (fr' := bls24_Fp4_repr)
        a_tx tx_val q_x _ m1 (Fp4_bounded_length _ Hbqx) H1) as [m2 Hm2].
      (* Step 3: Replace FElem_Fp24 a_f: f_val -> f_new (tight-bounded) *)
      assert (Hm2' : (FElem_Fp24 a_f f_val *
        (FElem_Fp4 a_tx q_x * (FElem_Fp4 a_ty q_y * R)))%sep m2)
        by ecancel_assumption.
      clear H0 H1 Hm1 Hm2.
      (* Construct tight-bounded Fp24 element from copies of q_x.
         f_new = (q_x++q_x) ++ (q_x++q_x) ++ (q_x++q_x) — 6 Fp4 copies.
         Every CE/QE sub-component reduces to q_x, which is tight-bounded. *)
      pose proof (Fp4_bounded_length q_x Hbqx) as Hlenqx.
      set (fp8_val := q_x ++ q_x).
      set (f_new := fp8_val ++ fp8_val ++ fp8_val).
      (* Derive felem sizes *)
      assert (Hlen8 : length fp8_val =
        @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
      { subst fp8_val. rewrite app_length.
        change (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)
          with (2 * @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr)%nat.
        lia. }
      assert (Hlen_f : length f_new =
        @AbstractField.felem_size_in_words _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
      { subst f_new. rewrite !app_length.
        change (@AbstractField.felem_size_in_words _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr)
          with (3 * @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)%nat.
        lia. }
      destruct (FElem_value_replace (fr' := bls24_Fp24_repr)
        a_f f_val f_new _ m2 Hlen_f Hm2') as [m3 Hm3].
      exists f_new, m3. split; [| exact Hm3].
      (* Prove Fp24_bounded Fp24_tight f_new *)
      (* Step A: prove CE/QE decomposition equalities *)
      assert (Hce0 : @ce_c0_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new = fp8_val).
      { unfold ce_c0_felem. subst f_new. apply firstn_app_le. exact Hlen8. }
      assert (Hce1 : @ce_c1_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new = fp8_val).
      { unfold ce_c1_felem. subst f_new.
        rewrite (skipn_app_le fp8_val _ _ Hlen8).
        apply firstn_app_le. exact Hlen8. }
      assert (Hce2 : @ce_c2_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new = fp8_val).
      { unfold ce_c2_felem. subst f_new.
        replace (2 * @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)%nat
          with (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr +
                @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)%nat
          by lia.
        rewrite <- List.skipn_skipn.
        rewrite (skipn_app_le fp8_val _ _ Hlen8).
        apply skipn_app_le. exact Hlen8. }
      assert (Hqf : @qe_fst_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr fp8_val = q_x).
      { unfold qe_fst_felem. subst fp8_val. apply firstn_app_le. exact Hlenqx. }
      assert (Hqs : @qe_snd_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr fp8_val = q_x).
      { unfold qe_snd_felem. subst fp8_val. apply skipn_app_le. exact Hlenqx. }
      (* Step B: prove Fp24_bounded via CE + QE decomposition *)
      (* First prove Fp8_bounded for the common fp8_val *)
      assert (Hb8 : Fp8_bounded Fp8_tight fp8_val).
      { cut (Fp4_bounded Fp4_tight
               (@qe_fst_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr fp8_val) /\
             Fp4_bounded Fp4_tight
               (@qe_snd_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr fp8_val)).
        { intro H; exact H. }
        rewrite Hqf, Hqs. split; exact Hbqx. }
      (* Now lift to Fp24_bounded via CE decomposition *)
      cut (Fp8_bounded Fp8_tight
             (@ce_c0_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new) /\
           Fp8_bounded Fp8_tight
             (@ce_c1_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new) /\
           Fp8_bounded Fp8_tight
             (@ce_c2_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr f_new)).
      { intro H; exact H. }
      rewrite Hce0, Hce1, Hce2.
      exact (conj Hb8 (conj Hb8 Hb8)).
    Qed.

    (* ============================================================ *)
    (* Post-loop sep transformation (needed by full body WP)          *)
    (* ============================================================ *)

    (** Like bls24_miller_postloop_ok but accepts Fp24_loose bounds on f_result.
        Used in the FALSE branch where fp24_conj_body produces loose bounds.
        Defined here (before bls24_miller_full_body_wp) so it can be referenced. *)
    Lemma bls24_miller_postloop_ok_loose :
      forall (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (f_result : Fp24_felem)
        (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val f_leftover : Fp24_felem)
        (Rr : mem -> Prop) (m : mem),
        Fp24_bounded Fp24_loose f_result ->
        (FElem_Fp24 a_f f_leftover *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout f_result *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        exists out : Fp24_felem,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp4 p_qx q_x *
              (FElem_Fp4 p_qy q_y *
               (Rr *
                (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
                 (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
                  (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
                   (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
                    (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
                     (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
                      AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line))))))))))))%sep m.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbnd Hsep.
      exists f_result.
      split.
      { exact Hbnd. }
      destruct Hsep as [m1 [mr1 [[Heq1 Hd1] [Hfe_f Hr1]]]].
      destruct Hr1 as [m2 [mr2 [[Heq2 Hd2] [Hfe_tx Hr2]]]].
      destruct Hr2 as [m3 [mr3 [[Heq3 Hd3] [Hfe_ty Hr3]]]].
      destruct Hr3 as [m4 [mr4 [[Heq4 Hd4] [Hfe_lam Hr4]]]].
      destruct Hr4 as [m5 [mr5 [[Heq5 Hd5] [Hfe_tmp1 Hr5]]]].
      destruct Hr5 as [m6 [mr6 [[Heq6 Hd6] [Hfe_tmp2 Hr6]]]].
      destruct Hr6 as [m7 [mr7 [[Heq7 Hd7] [Hfe_line Hr7]]]].
      pose proof (AbstractField.FElem_to_bytes a_f f_leftover m1 Hfe_f) as Hph_f.
      pose proof (AbstractField.FElem_to_bytes a_tx tx_val m2 Hfe_tx) as Hph_tx.
      pose proof (AbstractField.FElem_to_bytes a_ty ty_val m3 Hfe_ty) as Hph_ty.
      pose proof (AbstractField.FElem_to_bytes a_lam lam_val m4 Hfe_lam) as Hph_lam.
      pose proof (AbstractField.FElem_to_bytes a_tmp1 tmp1_val m5 Hfe_tmp1) as Hph_tmp1.
      pose proof (AbstractField.FElem_to_bytes a_tmp2 tmp2_val m6 Hfe_tmp2) as Hph_tmp2.
      pose proof (AbstractField.FElem_to_bytes a_line line_val m7 Hfe_line) as Hph_line.
      assert (Hsep' :
        (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
         (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
          (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
           (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
            (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
             (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
              (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line *
               (FElem_Fp24 pout f_result *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m).
      { exists m1, mr1. split. { split; assumption. }
        split. { exact Hph_f. }
        exists m2, mr2. split. { split; assumption. }
        split. { exact Hph_tx. }
        exists m3, mr3. split. { split; assumption. }
        split. { exact Hph_ty. }
        exists m4, mr4. split. { split; assumption. }
        split. { exact Hph_lam. }
        exists m5, mr5. split. { split; assumption. }
        split. { exact Hph_tmp1. }
        exists m6, mr6. split. { split; assumption. }
        split. { exact Hph_tmp2. }
        exists m7, mr7. split. { split; assumption. }
        split. { exact Hph_line. }
        exact Hr7. }
      ecancel_assumption.
    Qed.

    (* ============================================================ *)
    (* Full body WP helper                                            *)
    (* ============================================================ *)

    (** The full body WP: given the master sep and all callee specs,
        miller_loop_full_body produces the spec postcondition with
        stack FElems converted to Placeholders.

        The proof would proceed as:
        1. Unfold miller_loop_full_body + cmd_seq_list
        2. Process init: 24 from_word calls + 2 fp4_copy + set i=52
           via repeat straightline + straightline_call
        3. Apply Loops.while_localsmap with:
             v0 := 52, lt := Nat.lt,
             invariant := miller_loop_inv ...
        4. Well-foundedness: exact lt_wf
        5. Initial invariant: from init phase (cf. bls24_miller_init_ok)
        6. Loop body: wire bls24_miller_loop_body_step
        7. Post-loop (br=0): process fp4_opp + fp8_opp + fp24_copy,
           then wire bls24_miller_postloop_ok for sep transformation *)
    Lemma bls24_miller_full_body_wp :
      forall functions
        (HFp4mul : spec_of_Fp4_mul functions)
        (HFp4add : spec_of_Fp4_add functions)
        (HFp4sub : spec_of_Fp4_sub functions)
        (HFp4sqr : spec_of_Fp4_sqr functions)
        (HFp4inv : spec_of_Fp4_inv functions)
        (HFp4opp : spec_of_Fp4_opp functions)
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFp8opp : spec_of_Fp8_opp functions)
        (HFp24mul : spec_of_Fp24_mul functions)
        (HFp24sqr : spec_of_Fp24_sqr functions)
        (HFp24copy : spec_of_Fp24_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls24_make_line" =
          Some (snd bls24_make_line))
        (HFp4mulfpEnv : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp))
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (f_val : Fp24_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val : Fp24_felem) (old_out : Fp24_felem)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals)
        (post : Semantics.trace -> mem -> locals -> Prop),
        Fp4_bounded Fp4_tight q_x ->
        Fp4_bounded Fp4_tight q_y ->
        Fp_bounded Fp_loose p_x ->
        Fp_bounded Fp_loose p_y ->
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        map.get l "f" = Some a_f ->
        map.get l "t_x" = Some a_tx ->
        map.get l "t_y" = Some a_ty ->
        map.get l "lambda" = Some a_lam ->
        map.get l "tmp1" = Some a_tmp1 ->
        map.get l "tmp2" = Some a_tmp2 ->
        map.get l "line" = Some a_line ->
        map.get l "out" = Some pout ->
        map.get l "p_x" = Some p_px ->
        map.get l "p_y" = Some p_py ->
        map.get l "q_x" = Some p_qx ->
        map.get l "q_y" = Some p_qy ->
        (* post is satisfiable given the spec output + Placeholders *)
        (forall t' m' l',
          t' = tr ->
          (exists out : Fp24_felem,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out *
             (FElem_Fp p_px p_x *
              (FElem_Fp p_py p_y *
               (FElem_Fp4 p_qx q_x *
                (FElem_Fp4 p_qy q_y *
                 (Rr *
                  (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
                   (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
                    (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
                     (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
                      (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
                       (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
                        AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line))))))))))))%sep m') ->
          post t' m' l') ->
        <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
          BLS24_509_MillerLoop.miller_loop_full_body
        <{ post }>.
    Proof.
      (* Proof plan:
         1. Unfold miller_loop_full_body, cmd_seq_list, fp24_set_one
         2. Process 24 from_word + 2 fp4_copy + set i=52 (init phase)
         3. Apply Loops.while_localsmap with v0:=52, lt:=Nat.lt,
            invariant := miller_loop_inv ...
         4. Wire bls24_miller_loop_body_step for loop body
         5. Wire bls24_miller_postloop_ok for postloop + dealloc *)
      intros functions
        HFp4mul HFp4add HFp4sub HFp4sqr HFp4inv HFp4opp HFp4copy
        HFp8opp HFp24mul HFp24sqr HFp24copy HFpmul HFpcopy HFfromword
        HMakeLine HFp4mulfpEnv
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
        pout p_px p_py p_qx p_qy
        f_val tx_val ty_val lam_val tmp1_val tmp2_val line_val old_out
        p_x p_y q_x q_y
        Rr tr m l post
        Hbqx Hbqy Hbpx Hbpy Hsep
        Hlf Hltx Hlty Hllam Hltmp1 Hltmp2 Hlline Hlout Hlpx Hlpy Hlqx Hlqy
        Hpost.

      (* Unfold the full body *)
      unfold BLS24_509_MillerLoop.miller_loop_full_body.
      unfold BLS24_509_MillerLoop.cmd_seq_list.

      (* ================================================================= *)
      (* Step 1: fp24_set_one "f" — 24 from_word calls                      *)
      (* Use bls24_fp24_set_one_wp to handle all 24 calls at once.          *)
      (* ================================================================= *)

      (* The WP for cmd.seq (fp24_set_one "f") rest is:
         WP (fp24_set_one "f") m l (fun tr' m' l' => WP rest tr' m' l' post)
         We apply bls24_fp24_set_one_wp to the first component. *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].

      (* Goal: WP (fp24_set_one "f") ... *)
      (* Use Proper_cmd to apply bls24_fp24_set_one_wp with postcond weakening.
         Proper_cmd creates 2 goals:
         - Goal 1 (solved last): weaken postcond of set_one to the WP continuation
         - Goal 2 (solved first): WP (fp24_set_one "f") with set_one's postcond *)
      eapply WeakestPreconditionProperties.Proper_cmd.
      2: { (* Goal 2: Apply bls24_fp24_set_one_wp *)
        eapply bls24_fp24_set_one_wp.
        { exact HFfromword. }
        { exact Hlf. }
        { ecancel_assumption. } }
      (* Goal 1: weaken postcond *)
      intros tr1 m1 l1 [Htr1 [Hl1_eq [f_new [Hbf_new Hsep1]]]].
      (* After fp24_set_one: tr1 = tr, l1 = l, f_new tight-bounded at a_f *)
      subst tr1. subst l1.

      (* ================================================================= *)
      (* Step 2: fp4_copy [t_x; q_x]                                        *)
      (* ================================================================= *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      (* Goal: WP (cmd.call [] fp4_copy_name [expr.var "t_x"; expr.var "q_x"]) *)
      letexists; split.
      { (* dexprs *)
        cbv [dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        rewrite Hltx. rewrite Hlqx.
        eexists. split; [exact eq_refl |].
        eexists. split; [exact eq_refl |].
        exact eq_refl. }
      eapply Semantics.weaken_call.
      { eapply HFp4copy.
        split; ecancel_assumption. }
      intros t2 m2 rets2 [Hrets2 [Htr2 Hsep2]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================= *)
      (* Step 3: fp4_copy [t_y; q_y]                                        *)
      (* ================================================================= *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      letexists; split.
      { cbv [dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        rewrite Hlty. rewrite Hlqy.
        eexists. split; [exact eq_refl |].
        eexists. split; [exact eq_refl |].
        exact eq_refl. }
      eapply Semantics.weaken_call.
      { eapply HFp4copy.
        split; ecancel_assumption. }
      intros t3 m3 rets3 [Hrets3 [Htr3 Hsep3]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================= *)
      (* Step 4: set i = 52                                                  *)
      (* ================================================================= *)
      (* Manually process cmd.seq + cmd.set "i" 52 without introducing named
         variables, to avoid polluting the namespace for the loop body. *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body]. (* peel cmd.seq *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body]. (* expose cmd.set *)
      (* Goal: ∃ v, dexpr m l (expr.literal 52) v ∧ dlet! l' := map.put l "i" v in ... *)
      exists (word.of_Z 52).
      split.
      { (* Prove dexpr m l (expr.literal 52) (word.of_Z 52) *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal]. exact eq_refl. }
      unfold dlet.dlet; cbv beta.
      (* Goal: WP (cmd.seq (while...) ...) tr m (map.put l "i" (word.of_Z 52)) post *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body]. (* peel cmd.seq (while...) *)

      (* ================================================================= *)
      (* Step 5: while loop                                                  *)
      (* Use while_localsmap with the miller_loop_inv invariant.             *)
      (* ================================================================= *)

      (* Build the initial invariant state. After steps 1-4:
         - a_f has f_new (tight bounded from fp24_set_one)
         - a_tx has q_x (copied from fp4_copy)
         - a_ty has q_y (copied from fp4_copy)
         - locals have "i" = 52
         - Everything else unchanged *)

      (* Extract fp4_copy postconditions for tx and ty *)
      (* Hsep2 : (FElem_Fp4 a_tx q_x * ...) m2 (after first fp4_copy *)
      (* Hsep3 : (FElem_Fp4 a_ty q_y * ...) m3 (after second fp4_copy) *)

      (* From Hsep2, the copy gave us q_x at a_tx *)
      (* From Hsep3, the copy gave us q_y at a_ty *)

      (* The locals after "set i = 52": l with "i" added *)
      (* After repeat straightline from set i=52, locals have "i" updated *)

      eapply Loops.while_localsmap
        with (v0 := 52%nat)
             (lt := Nat.lt)
             (invariant := miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
                      pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr).

      (* Well-founded *)
      { exact Wf_nat.lt_wf. }

      (* Initial invariant at v=52 *)
      { (* From the fp4_copy postconditions and fp24_set_one postcondition,
           we have the invariant ready. *)
        unfold miller_loop_inv.
        split. { reflexivity. }
        (* The fp4_copy spec for Fp4 gives us:
           Hsep2 : (FElem_Fp4 a_tx q_x * ...) m2
           But we need to know what value q_x has. Looking at spec_of_Fp4_felem_copy:
           it produces exists copy, bounded copy /\ (FElem_Fp4 a_tx copy * ...) m2.
           So we get a NEW value at a_tx that is tight-bounded. *)
        (* Actually, the fp4_copy spec_of_Fp4_felem_copy gives:
           ensures tr' mem' := tr = tr' /\ exists out, bounded out /\ (FElem pout out * ...) *)
        (* We need the postcondition from HFp4copy which gives us:
           Hsep2 has (FElem_Fp4 a_tx tx_new * ...) for some tx_new with tight bounds *)
        (* spec_of_felem_copy postcond: tr = tr' /\ (FElem pout x * Rout) m'  — NO exists.
           After fp4_copy [t_x; q_x]: Hsep2 = (FElem_Fp4 a_tx q_x * Rout) m2
           After fp4_copy [t_y; q_y]: Hsep3 = (FElem_Fp4 a_ty q_y * Rout) m3
           So the copy preserves the source value q_x / q_y at destination.
           Bounds come from Hbqx, Hbqy (tight bounds on the input Q point). *)
        exists f_new, q_x, q_y, lam_val, tmp1_val, tmp2_val, line_val.
        split. { exact Hbf_new. }
        split. { exact Hbqx. }
        split. { exact Hbqy. }
        split.
        { (* Sep: combine all FElems *)
          ecancel_assumption. }
        (* Locals: from the invariant we need map.get for "i"=52 and all variables *)
        (* After "set i=52" + repeat straightline, the locals are updated.
           The locals are map.put l "i" (word.of_Z 52). *)
        split.
        { rewrite map.get_put_same. reflexivity. }
        split. { rewrite map.get_put_diff by congruence. exact Hlf. }
        split. { rewrite map.get_put_diff by congruence. exact Hltx. }
        split. { rewrite map.get_put_diff by congruence. exact Hlty. }
        split. { rewrite map.get_put_diff by congruence. exact Hllam. }
        split. { rewrite map.get_put_diff by congruence. exact Hltmp1. }
        split. { rewrite map.get_put_diff by congruence. exact Hltmp2. }
        split. { rewrite map.get_put_diff by congruence. exact Hlline. }
        split. { rewrite map.get_put_diff by congruence. exact Hlout. }
        split. { rewrite map.get_put_diff by congruence. exact Hlpx. }
        split. { rewrite map.get_put_diff by congruence. exact Hlpy. }
        split. { rewrite map.get_put_diff by congruence. exact Hlqx. }
        rewrite map.get_put_diff by congruence. exact Hlqy. }

      (* Loop body *)
      { intros vi ti mi li Hinv.
        unfold miller_loop_inv in Hinv.
        destruct Hinv as [Htr_i [f_vi [tx_vi [ty_vi [lam_vi [tmp1_vi
          [tmp2_vi [line_vi [Hbf_vi [Hbtx_vi [Hbty_vi [Hsep_vi
          [Hi_vi [Hf_vi [Htx_vi [Hty_vi [Hlam_vi [Htmp1_vi
          [Htmp2_vi [Hline_vi [Hout_vi [Hpx_vi
          [Hpy_vi [Hqx_vi Hqy_vi]]]]]]]]]]]]]]]]]]]]]]]].
        subst ti.

        (* Branch condition: expr.var "i" *)
        exists (word.of_Z (Z.of_nat vi)).
        split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          rewrite Hi_vi. eexists. split; exact eq_refl. }

        split.
        { (* TRUE branch: word.unsigned br <> 0, loop body *)
          intro Hne.

          (* Unfold miller_loop_iteration *)
          unfold BLS24_509_MillerLoop.miller_loop_iteration.
          unfold BLS24_509_MillerLoop.cmd_seq_list.

          (* Step: set i = i - 1 *)
          miller_straightline.
          miller_straightline.
          unfold dlet.dlet; cbv beta.

          (* Build make_line spec *)
          assert (HMakeLineSpec : spec_of_bls24_make_line functions).
          { unfold spec_of_bls24_make_line.
            intros pout' plam' pxt' pyt' pxp' pyp'
              old_out' lam' xt' yt' xp' yp' Rr' tr'_ml mem'_ml
              [Hblam' [Hbxt' [Hbyt' [Hbxp' [Hbyp' Hsep'_ml]]]]].
            eapply Semantics.weaken_call.
            { eapply (bls24_make_line_ok functions HMakeLine).
              { (* HFp4mul for make_line: use local instance *)
                exact HFp4mul. }
              { exact HFp4sub. }
              { exact HFp4opp. }
              { exact (bls24_Fp4_mul_fp_ok functions HFp4mulfpEnv HFpmul). }
              { exact HFpcopy. }
              { exact HFfromword. }
              split; [exact Hblam' |].
              split; [exact Hbxt' |].
              split; [exact Hbyt' |].
              split; [exact Hbxp' |].
              split; [exact Hbyp' |].
              exact Hsep'_ml. }
            cbv beta. intros t' m' rets [Hrets [Htr' [out' [Hb' Hs']]]].
            subst. exact (conj eq_refl (conj eq_refl (ex_intro _ out' (conj Hb' Hs')))). }

          (* === Doubling step === *)
          miller_mcall HFp4sqr.   (* D1: fp4_sqr(tmp1, t_x) *)
          miller_mcall HFp4add.   (* D2: fp4_add(lambda, tmp1, tmp1) *)
          miller_mcall HFp4add.   (* D3: fp4_add(lambda, lambda, tmp1) *)
          miller_mcall HFp4add.   (* D4: fp4_add(tmp1, t_y, t_y) *)
          miller_mcall HFp4inv.   (* D5: fp4_inv(tmp1, tmp1) *)
          miller_mcall HFp4mul.   (* D6: fp4_mul(lambda, lambda, tmp1) *)
          miller_mcall HMakeLineSpec. (* D7: make_line *)
          miller_mcall HFp24sqr.  (* D8: fp24_sqr(f, f) *)
          miller_mcall HFp24mul.  (* D9: fp24_mul(f, f, line) *)
          miller_mcall HFp4sqr.   (* D10: fp4_sqr(tmp1, lambda) *)
          miller_mcall HFp4sub.   (* D11: fp4_sub(tmp1, tmp1, t_x) *)
          miller_mcall HFp4sub.   (* D12: fp4_sub(tmp2, tmp1, t_x) *)
          miller_mcall HFp4sub.   (* D13: fp4_sub(tmp1, t_x, tmp2) *)
          miller_mcall HFp4mul.   (* D14: fp4_mul(tmp1, lambda, tmp1) *)
          miller_mcall HFp4sub.   (* D15: fp4_sub(t_y, tmp1, t_y) *)
          miller_mcall HFp4copy.  (* D16: fp4_copy(t_x, tmp2) *)

          (* === Conditional addition step === *)
          miller_straightline. (* cmd.set "bit" *)
          miller_straightline. (* cmd.set "bit" expr eval *)
          unfold dlet.dlet; cbv beta.
          miller_straightline. (* cmd.cond *)
          split.

          { (* Bit = 1: addition step *)
            intro Hbit_ne.
            unfold BLS24_509_MillerLoop.cmd_seq_list.

            miller_mcall HFp4sub.     (* A1: fp4_sub(tmp1, q_y, t_y) *)
            miller_mcall HFp4sub.     (* A2: fp4_sub(tmp2, q_x, t_x) *)
            miller_mcall HFp4inv.     (* A3: fp4_inv(tmp2, tmp2) *)
            miller_mcall HFp4mul.     (* A4: fp4_mul(lambda, tmp1, tmp2) *)
            miller_mcall HMakeLineSpec. (* A5: make_line *)
            miller_mcall HFp24mul.    (* A6: fp24_mul(f, f, line) *)
            miller_mcall HFp4sqr.     (* A7: fp4_sqr(tmp1, lambda) *)
            miller_mcall HFp4sub.     (* A8: fp4_sub(tmp1, tmp1, t_x) *)
            miller_mcall HFp4sub.     (* A9: fp4_sub(tmp2, tmp1, q_x) *)
            miller_mcall HFp4sub.     (* A10: fp4_sub(tmp1, t_x, tmp2) *)
            miller_mcall HFp4mul.     (* A11: fp4_mul(tmp1, lambda, tmp1) *)
            miller_mcall HFp4sub.     (* A12: fp4_sub(t_y, tmp1, t_y) *)
            miller_mcall HFp4copy.    (* A13: fp4_copy(t_x, tmp2) *)

            (* Re-establish invariant (addition branch) *)
            assert (Hvi_pos : (0 < vi)%nat).
            { destruct vi; [exfalso; apply Hne; reflexivity | lia]. }
            exists (Nat.sub vi 1).
            split; [| lia].
            unfold miller_loop_inv.
            split. { reflexivity. }
            do 7 eexists.
            split; [| split; [| split; [| split]]].
            4: { miller_normalize_pairing_instances. ecancel_assumption. }
            { miller_solve_bounds. }
            { miller_solve_bounds. }
            { miller_solve_bounds. }
            split.
            { (* i = vi - 1 *)
              rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
              f_equal. replace v with (@word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1))
                by (unfold v; reflexivity).
              exact (word_nat_sub1 vi Hvi_pos). }
            miller_solve_precond. }

          { (* Bit = 0: skip *)
            intro Hbit_eq.
            miller_straightline.

            (* Re-establish invariant (skip branch) *)
            assert (Hvi_pos : (0 < vi)%nat).
            { destruct vi; [exfalso; apply Hne; reflexivity | lia]. }
            exists (Nat.sub vi 1).
            split; [| lia].
            unfold miller_loop_inv.
            split. { reflexivity. }
            do 7 eexists.
            split; [| split; [| split; [| split]]].
            4: { miller_normalize_pairing_instances. ecancel_assumption. }
            - miller_solve_bounds.
            - miller_solve_bounds.
            - miller_solve_bounds.
            - split.
              + rewrite map.get_put_diff by congruence. rewrite map.get_put_same.
                f_equal. replace v with (@word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1))
                  by (unfold v; reflexivity).
                exact (word_nat_sub1 vi Hvi_pos).
              + repeat (split; [miller_solve_leaf |]). miller_solve_leaf. } }

      (* FALSE branch: loop exits, process post-loop commands.
         In scope from the outer destruct Hinv (line 761-765):
           f_vi, tx_vi, ty_vi, lam_vi, tmp1_vi, tmp2_vi, line_vi,
           Hbf_vi, Hbtx_vi, Hbty_vi, Hsep_vi,
           Hf_vi, Htx_vi, Hty_vi, Hlam_vi, Htmp1_vi, Htmp2_vi,
           Hline_vi, Hout_vi, Hpx_vi, Hpy_vi, Hqx_vi, Hqy_vi.
         Goal: WP (fp4_opp; fp24_conj_body "f"; fp24_copy) ti mi li post *)
      { intro Heq0.
        (* === Step 1: fp4_opp [t_y; t_y] === *)
        unfold1_cmd_goal; cbv beta match delta [cmd_body].
        letexists; split.
        { cbv [dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          rewrite Hty_vi. eexists. split. { exact eq_refl. }
          eexists. split. { exact eq_refl. }
          exact eq_refl. }
        eapply Semantics.weaken_call.
        { eapply HFp4opp.
          split. { exact Hbty_vi. }
          split. { eexists; ecancel_assumption. }
          ecancel_assumption. }
        cbv beta.
        intros t_opp m_opp rets_opp Hpost_opp.
        destruct Hpost_opp as [Hrets_opp [Htr_opp [ty_opp [_ [_ Hs_opp]]]]].
        subst rets_opp. symmetry in Htr_opp. subst t_opp.
        cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
        (* Hs_opp : (FElem_Fp4 a_ty ty_opp * Rr_opp) m_opp *)

        (* === Step 2: fp24_conj_body "f" via bls24_fp24_conj_wp === *)
        (* Peel the cmd.seq wrapping fp24_conj_body to expose it as the head. *)
        unfold1_cmd_goal; cbv beta match delta [cmd_body].
        (* Now goal: WP fp24_conj_body "f" ... post_seq *)
        (* Use Proper_cmd to apply bls24_fp24_conj_wp with postcond weakening.
           Proper_cmd creates 2 goals:
           - Goal 1 (solved last): weaken postcond of conj to the WP continuation
           - Goal 2 (solved first): WP fp24_conj_body "f" with conj's postcond *)
        eapply WeakestPreconditionProperties.Proper_cmd.
        2: { (* Goal 2: Apply bls24_fp24_conj_wp *)
          eapply bls24_fp24_conj_wp.
          { exact HFp8opp. }
          { exact Hbf_vi. }
          { ecancel_assumption. }
          { exact Hf_vi. } }
        (* Goal 1: weaken postcond *)
        intros t_conj m_conj l_conj [Htr_conj [Hl_conj [f_conj [Hbf_conj Hs_conj]]]].
        (* After fp24_conj_body:
           t_conj = ti = tr, l_conj = li,
           f_conj : Fp24_felem with Fp24_bounded Fp24_loose f_conj
           Hs_conj : (FElem_Fp24 a_f f_conj * Rr) m_conj *)
        subst t_conj. subst l_conj.

        (* === Step 3: fp24_copy [out; f] === *)
        unfold1_cmd_goal; cbv beta match delta [cmd_body].
        letexists; split.
        { cbv [dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          rewrite Hout_vi. eexists. split. { exact eq_refl. }
          rewrite Hf_vi. eexists. split. { exact eq_refl. }
          exact eq_refl. }
        eapply Semantics.weaken_call.
        { eapply HFp24copy.
          split; ecancel_assumption. }
        cbv beta.
        intros t_copy m_copy rets_copy Hpost_copy.
        destruct Hpost_copy as [Hrets_copy [Htr_copy Hs_copy]].
        subst rets_copy. symmetry in Htr_copy. subst t_copy.
        cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
        (* Hs_copy : (FElem_Fp24 pout f_conj * Rout_copy) m_copy *)

        (* === Step 4: Apply Hpost === *)
        apply Hpost.
        { reflexivity. }
        { (* Provide: exists out, Fp24_bounded Fp24_loose out /\
                        (FElem_Fp24 pout out * inputs * Rr * Placeholders) m_copy
             Apply bls24_miller_postloop_ok_loose which produces the exists directly. *)
          apply bls24_miller_postloop_ok_loose with
            (f_result := f_conj)
            (tx_val := tx_vi)
            (ty_val := ty_opp)
            (lam_val := lam_vi)
            (tmp1_val := tmp1_vi)
            (tmp2_val := tmp2_vi)
            (line_val := line_vi)
            (f_leftover := f_conj).
          { exact Hbf_conj. }
          { ecancel_assumption. } } } }
    Qed.

    (* ============================================================ *)
    (* Main theorem                                                   *)
    (* ============================================================ *)

    Lemma bls24_miller_loop_ok :
      forall functions
        (EnvContains : map.get functions "bls24_miller_loop" =
          Some (snd bls24_miller_loop))
        (HFp4mul : spec_of_Fp4_mul functions)
        (HFp4add : spec_of_Fp4_add functions)
        (HFp4sub : spec_of_Fp4_sub functions)
        (HFp4sqr : spec_of_Fp4_sqr functions)
        (HFp4inv : spec_of_Fp4_inv functions)
        (HFp4opp : spec_of_Fp4_opp functions)
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFp8opp : spec_of_Fp8_opp functions)
        (HFp24mul : spec_of_Fp24_mul functions)
        (HFp24sqr : spec_of_Fp24_sqr functions)
        (HFp24copy : spec_of_Fp24_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls24_make_line" =
          Some (snd bls24_make_line))
        (HFp4mulfpEnv : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp)),
      spec_of_bls24_miller_loop functions.
    Proof.
      intros.
      unfold spec_of_bls24_miller_loop.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].

      (* === Function entry === *)
      eapply WeakestPreconditionProperties.start_func;
        [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls24_miller_loop. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Process 7 stackallocs === *)
      repeat straightline.

      (* Stackalloc 1: f (Fp24-sized) *)
      split. { apply Z_mod_mult. }
      intros a_f mStack_f mComb_f HanyF HsplitF.
      repeat straightline.

      (* Stackalloc 2: t_x (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tx mStack_tx mComb_tx HanyTx HsplitTx.
      repeat straightline.

      (* Stackalloc 3: t_y (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_ty mStack_ty mComb_ty HanyTy HsplitTy.
      repeat straightline.

      (* Stackalloc 4: lambda (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_lam mStack_lam mComb_lam HanyLam HsplitLam.
      repeat straightline.

      (* Stackalloc 5: tmp1 (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp1 mStack_tmp1 mComb_tmp1 HanyTmp1 HsplitTmp1.
      repeat straightline.

      (* Stackalloc 6: tmp2 (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp2 mStack_tmp2 mComb_tmp2 HanyTmp2 HsplitTmp2.
      repeat straightline.

      (* Stackalloc 7: line (Fp24-sized) *)
      split. { apply Z_mod_mult. }
      intros a_line mStack_line mComb_line HanyLine HsplitLine.

      (* === Convert anybytes to FElems for all stack-allocated buffers === *)
      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_f) as Hfb_f.
      unfold AbstractField.Placeholder in Hfb_f.
      pose proof (proj1 (Hfb_f mStack_f) HanyF) as [f_val Hfe_f]. clear Hfb_f.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tx) as Hfb_tx.
      unfold AbstractField.Placeholder in Hfb_tx.
      pose proof (proj1 (Hfb_tx mStack_tx) HanyTx) as [tx_val Hfe_tx]. clear Hfb_tx.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_ty) as Hfb_ty.
      unfold AbstractField.Placeholder in Hfb_ty.
      pose proof (proj1 (Hfb_ty mStack_ty) HanyTy) as [ty_val Hfe_ty]. clear Hfb_ty.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_lam) as Hfb_lam.
      unfold AbstractField.Placeholder in Hfb_lam.
      pose proof (proj1 (Hfb_lam mStack_lam) HanyLam) as [lam_val Hfe_lam]. clear Hfb_lam.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp1) as Hfb_tmp1.
      unfold AbstractField.Placeholder in Hfb_tmp1.
      pose proof (proj1 (Hfb_tmp1 mStack_tmp1) HanyTmp1) as [tmp1_val Hfe_tmp1]. clear Hfb_tmp1.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp2) as Hfb_tmp2.
      unfold AbstractField.Placeholder in Hfb_tmp2.
      pose proof (proj1 (Hfb_tmp2 mStack_tmp2) HanyTmp2) as [tmp2_val Hfe_tmp2]. clear Hfb_tmp2.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_line) as Hfb_line.
      unfold AbstractField.Placeholder in Hfb_line.
      pose proof (proj1 (Hfb_line mStack_line) HanyLine) as [line_val Hfe_line]. clear Hfb_line.

      (* === Phase 1: Build master separation logic hypothesis ===
         The sep hypothesis Hsep (on the intermediate memory before the last
         stackalloc) contains array ptsto entries for buffers 1-6 and FElem
         entries for the 5 input parameters. The last stackalloc (line) is
         separate in HsplitLine/Hfe_line.

         We need to combine everything into a single 12-way sep on mComb_line.
         Strategy: use sep_from_split to merge mComb_tmp2 (from Hsep) with
         mStack_line (from Hfe_line) into mComb_line. *)

      (* === Phase 1: Build master sep on mComb_line ===
         Destruct Hsep to get sub-maps with map.split witnesses,
         convert array ptsto entries to FElems on those sub-maps,
         rebuild the sep on mem0, then extend to mComb_line via
         sep_from_split + ecancel_assumption. *)

      (* Destruct Hsep to expose the 12 sub-components *)
      destruct Hsep as [m_s1 [mr1 [Hsplit1 [Hfe_out Hr1]]]].
      destruct Hr1 as [m_s2 [mr2 [Hsplit2 [Hfe_px Hr2]]]].
      destruct Hr2 as [m_s3 [mr3 [Hsplit3 [Hfe_py Hr3]]]].
      destruct Hr3 as [m_s4 [mr4 [Hsplit4 [Hfe_qx Hr4]]]].
      destruct Hr4 as [m_s5 [mr5 [Hsplit5 [Hfe_qy Hr5]]]].
      destruct Hr5 as [m_s6 [mr6 [Hsplit6 [Hrr Hr6]]]].
      destruct Hr6 as [m_s7 [mr7 [Hsplit7 [Harr_f Hr7]]]].
      destruct Hr7 as [m_s8 [mr8 [Hsplit8 [Harr_tx Hr8]]]].
      destruct Hr8 as [m_s9 [mr9 [Hsplit9 [Harr_ty Hr9]]]].
      destruct Hr9 as [m_s10 [mr10 [Hsplit10 [Harr_lam Hr10]]]].
      destruct Hr10 as [m_s11 [m_s12 [Hsplit11 [Harr_tmp1 Harr_tmp2]]]].

      (* Convert array ptsto entries to anybytes then to FElem on sub-maps *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_f) as Hany_f'.
      rewrite length_stack in Hany_f'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_f m_s7) Hany_f') as [f_val' Hfe_f']. clear Hany_f'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tx) as Hany_tx'.
      rewrite length_stack0 in Hany_tx'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tx m_s8) Hany_tx') as [tx_val' Hfe_tx']. clear Hany_tx'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_ty) as Hany_ty'.
      rewrite length_stack1 in Hany_ty'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_ty m_s9) Hany_ty') as [ty_val' Hfe_ty']. clear Hany_ty'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_lam) as Hany_lam'.
      rewrite length_stack2 in Hany_lam'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_lam m_s10) Hany_lam') as [lam_val' Hfe_lam']. clear Hany_lam'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp1) as Hany_tmp1'.
      rewrite length_stack3 in Hany_tmp1'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp1 m_s11) Hany_tmp1') as [tmp1_val' Hfe_tmp1']. clear Hany_tmp1'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp2) as Hany_tmp2'.
      rewrite length_stack4 in Hany_tmp2'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp2 m_s12) Hany_tmp2') as [tmp2_val' Hfe_tmp2']. clear Hany_tmp2'.

      clear Harr_f Harr_tx Harr_ty Harr_lam Harr_tmp1 Harr_tmp2.

      (* Rebuild sep on mem0 with FElem entries on the correct sub-maps *)
      assert (Hsep_fe :
        (FElem_Fp24 pout old_out *
         (FElem_Fp p_px p_x *
          (FElem_Fp p_py p_y *
           (FElem_Fp4 p_qx q_x *
            (FElem_Fp4 p_qy q_y *
             (Rr *
              (FElem_Fp24 a_f f_val' *
               (FElem_Fp4 a_tx tx_val' *
                (FElem_Fp4 a_ty ty_val' *
                 (FElem_Fp4 a_lam lam_val' *
                  (FElem_Fp4 a_tmp1 tmp1_val' *
                   FElem_Fp4 a_tmp2 tmp2_val')))))))))))%sep mem0).
      {
        exists m_s1, mr1. split. { exact Hsplit1. }
        split. { exact Hfe_out. }
        exists m_s2, mr2. split. { exact Hsplit2. }
        split. { exact Hfe_px. }
        exists m_s3, mr3. split. { exact Hsplit3. }
        split. { exact Hfe_py. }
        exists m_s4, mr4. split. { exact Hsplit4. }
        split. { exact Hfe_qx. }
        exists m_s5, mr5. split. { exact Hsplit5. }
        split. { exact Hfe_qy. }
        exists m_s6, mr6. split. { exact Hsplit6. }
        split. { exact Hrr. }
        exists m_s7, mr7. split. { exact Hsplit7. }
        split. { exact Hfe_f'. }
        exists m_s8, mr8. split. { exact Hsplit8. }
        split. { exact Hfe_tx'. }
        exists m_s9, mr9. split. { exact Hsplit9. }
        split. { exact Hfe_ty'. }
        exists m_s10, mr10. split. { exact Hsplit10. }
        split. { exact Hfe_lam'. }
        exists m_s11, m_s12. split. { exact Hsplit11. }
        split. { exact Hfe_tmp1'. }
        exact Hfe_tmp2'.
      }

      (* Build master sep on mComb_line via sep_from_split + ecancel *)
      pose proof (sep_from_split HsplitLine Hsep_fe Hfe_line) as Htmp.
      eassert (Hmaster :
        (FElem_Fp24 a_f f_val' *
         (FElem_Fp4 a_tx tx_val' *
          (FElem_Fp4 a_ty ty_val' *
           (FElem_Fp4 a_lam lam_val' *
            (FElem_Fp4 a_tmp1 tmp1_val' *
             (FElem_Fp4 a_tmp2 tmp2_val' *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep mComb_line).
      { pose proof Htmp as H'. ecancel_assumption. }
      clear Htmp Hsep_fe.

      (* === Phase 2: Function body ===
         Hmaster has the 12-way sep on mComb_line with
         stack FElems f_val'..tmp2_val'/line_val and input FElems.

         miller_loop_full_body =
           fp24_set_one "f"          -- 24 from_word calls
           fp4_copy [t_x; q_x]      -- copy Q.x -> T.x
           fp4_copy [t_y; q_y]      -- copy Q.y -> T.y
           set i = 52               -- loop counter
           while (i) { iteration }  -- main loop (52 -> 0)
           fp4_opp [t_y; t_y]       -- negate T.y (z < 0)
           fp8_opp [c1(f); c1(f)]   -- conjugate f
           fp24_copy [out; f]       -- copy result *)

      (* Apply the full-body WP helper *)
      unfold dlet.dlet; cbv beta.
      eapply (bls24_miller_full_body_wp functions
        HFp4mul HFp4add HFp4sub HFp4sqr HFp4inv HFp4opp HFp4copy
        HFp8opp HFp24mul HFp24sqr HFp24copy HFpmul HFpcopy HFfromword
        HMakeLine HFp4mulfpEnv
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
        pout p_px p_py p_qx p_qy
        f_val' tx_val' ty_val' lam_val' tmp1_val' tmp2_val' line_val
        old_out p_x p_y q_x q_y
        Rr tr mComb_line (#{ … l4; "line" => a_line }#)
        _ Hbqx Hbqy Hbpx Hbpy Hmaster).
      (* Resolve 12 map.get goals *)
      all: subst l l0 l1 l2 l3 l4.
      all: repeat (rewrite map.get_put_same || rewrite map.get_put_diff by congruence).
      all: try exact eq_refl.

      (* Remaining: callback — convert Placeholders to anybytes for dealloc *)
      intros t' m' l' Htr [out [Hbnd Hsep_final]].
      subst t'.
      unfold AbstractField.Placeholder in Hsep_final.
      (* Peel off each stack FElem as anybytes, innermost (a_line) first *)
      (* Level 1: a_line *)
      eassert (Hline_sep : (_ * Memory.anybytes a_line
        (@AbstractField.felem_size_in_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr))%sep m').
      { pose proof Hsep_final as H'. ecancel_assumption. }
      destruct Hline_sep as [mrl [msl [Hsl [Hrl Hpl]]]].
      exists mrl, msl. split. { exact Hpl. } split. { exact Hsl. }
      (* Level 2: a_tmp2 *)
      eassert (Htmp2_sep : (_ * Memory.anybytes a_tmp2
        (@AbstractField.felem_size_in_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))%sep mrl).
      { pose proof Hrl as H'. ecancel_assumption. }
      destruct Htmp2_sep as [mrl2 [msl2 [Hsl2 [Hrl2 Hpl2]]]].
      exists mrl2, msl2. split. { exact Hpl2. } split. { exact Hsl2. }
      (* Level 3: a_tmp1 *)
      eassert (Htmp1_sep : (_ * Memory.anybytes a_tmp1
        (@AbstractField.felem_size_in_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))%sep mrl2).
      { pose proof Hrl2 as H'. ecancel_assumption. }
      destruct Htmp1_sep as [mrl3 [msl3 [Hsl3 [Hrl3 Hpl3]]]].
      exists mrl3, msl3. split. { exact Hpl3. } split. { exact Hsl3. }
      (* Level 4: a_lam *)
      eassert (Hlam_sep : (_ * Memory.anybytes a_lam
        (@AbstractField.felem_size_in_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))%sep mrl3).
      { pose proof Hrl3 as H'. ecancel_assumption. }
      destruct Hlam_sep as [mrl4 [msl4 [Hsl4 [Hrl4 Hpl4]]]].
      exists mrl4, msl4. split. { exact Hpl4. } split. { exact Hsl4. }
      (* Level 5: a_ty *)
      eassert (Hty_sep : (_ * Memory.anybytes a_ty
        (@AbstractField.felem_size_in_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))%sep mrl4).
      { pose proof Hrl4 as H'. ecancel_assumption. }
      destruct Hty_sep as [mrl5 [msl5 [Hsl5 [Hrl5 Hpl5]]]].
      exists mrl5, msl5. split. { exact Hpl5. } split. { exact Hsl5. }
      (* Level 6: a_tx *)
      eassert (Htx_sep : (_ * Memory.anybytes a_tx
        (@AbstractField.felem_size_in_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))%sep mrl5).
      { pose proof Hrl5 as H'. ecancel_assumption. }
      destruct Htx_sep as [mrl6 [msl6 [Hsl6 [Hrl6 Hpl6]]]].
      exists mrl6, msl6. split. { exact Hpl6. } split. { exact Hsl6. }
      (* Level 7: a_f *)
      eassert (Hf_sep : (_ * Memory.anybytes a_f
        (@AbstractField.felem_size_in_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr))%sep mrl6).
      { pose proof Hrl6 as H'. ecancel_assumption. }
      destruct Hf_sep as [mrl7 [msl7 [Hsl7 [Hrl7 Hpl7]]]].
      exists mrl7, msl7. split. { exact Hpl7. } split. { exact Hsl7. }
      (* Final: produce spec postcondition *)
      cbv [list_map list_map_body].
      split. { exact eq_refl. }
      split. { exact eq_refl. }
      exists out.
      split. { exact Hbnd. }
      exact Hrl7.
    Qed.

    (* ============================================================ *)
    (* Phase 1: Init — 24 from_word + 2 fp4_copy + set i=52         *)
    (* ============================================================ *)

    (** After the init phase, the invariant holds at v=52:
        - f = 1 (Fp24 identity, tight bounded via 24 from_word)
        - t_x = q_x (copied, tight bounded from Hbqx)
        - t_y = q_y (copied, tight bounded from Hbqy)
        - All other stack FElems (lam, tmp1, tmp2, line) unchanged
        - Locals bind f, t_x, t_y, lambda, tmp1, tmp2, line, out,
          p_x, p_y, q_x, q_y, and i=52 *)
    Lemma bls24_miller_init_ok :
      forall functions
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (f_val : Fp24_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val : Fp24_felem) (old_out : Fp24_felem)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
        Fp4_bounded Fp4_tight q_x ->
        Fp4_bounded Fp4_tight q_y ->
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        map.get l "f" = Some a_f ->
        map.get l "t_x" = Some a_tx ->
        map.get l "t_y" = Some a_ty ->
        map.get l "q_x" = Some p_qx ->
        map.get l "q_y" = Some p_qy ->
        exists m' l',
          miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
            pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
            52 tr m' l' /\
          (* Init commands produce WP for the continuation *)
          True.
    Proof.
      intros functions HFp4copy HFfromword
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
        pout p_px p_py p_qx p_qy
        f_val tx_val ty_val lam_val tmp1_val tmp2_val
        line_val old_out p_x p_y q_x q_y
        Rr tr m l
        Hbqx Hbqy Hsep Hlf Hltx Hlty Hlqx Hlqy.
      (* Apply the memory transformation helper:
         24 from_word calls make f tight-bounded,
         2 fp4_copy calls write q_x -> t_x and q_y -> t_y *)
      pose proof (fp24_init_mem_transform a_f a_tx a_ty f_val tx_val ty_val
        q_x q_y
        (FElem_Fp4 a_lam lam_val *
         (FElem_Fp4 a_tmp1 tmp1_val *
          (FElem_Fp4 a_tmp2 tmp2_val *
           (FElem_Fp24 a_line line_val *
            (FElem_Fp24 pout old_out *
             (FElem_Fp p_px p_x *
              (FElem_Fp p_py p_y *
               (FElem_Fp4 p_qx q_x *
                (FElem_Fp4 p_qy q_y * Rr)))))))))%sep
        m Hbqx Hbqy Hsep) as [f_new [m' [Hf_tight Hsep']]].
      (* Build locals map l' with all 13 bindings required by the invariant *)
      set (l' := map.put (map.put (map.put (map.put (map.put (map.put
        (map.put (map.put l
          "lambda" a_lam) "tmp1" a_tmp1) "tmp2" a_tmp2) "line" a_line)
        "out" pout) "p_x" p_px) "p_y" p_py) "i" (word.of_Z 52)).
      exists m', l'.
      split; [| exact I].
      (* Establish miller_loop_inv *)
      unfold miller_loop_inv.
      split; [reflexivity |].
      exists f_new, q_x, q_y, lam_val, tmp1_val, tmp2_val, line_val.
      split; [exact Hf_tight |].
      split; [exact Hbqx |].
      split; [exact Hbqy |].
      split; [exact Hsep' |].
      (* Resolve all 13 map.get goals on l' *)
      subst l'.
      repeat split;
        rewrite ?map.get_put_same, ?map.get_put_diff by congruence;
        try reflexivity; try assumption.
      all: repeat (rewrite map.get_put_diff by congruence);
           first [ rewrite map.get_put_same; reflexivity | assumption ].
    Qed.

    (* ============================================================ *)
    (* Phase 2: Loop body preserves invariant                        *)
    (* ============================================================ *)

    (** One iteration of the Miller loop:
        Given the invariant at vi > 0, process doubling step
        (~16 calls), conditional addition step (~13 calls if
        bit set), and re-establish invariant at vi-1.

        Doubling step calls:
          fp4_sqr, fp4_add x3, fp4_inv, fp4_mul,
          make_line, fp24_sqr, fp24_mul,
          fp4_sqr, fp4_sub x3, fp4_mul, fp4_sub, fp4_copy

        Addition step calls (when bit=1):
          fp4_sub x2, fp4_inv, fp4_mul,
          make_line, fp24_mul,
          fp4_sqr, fp4_sub x3, fp4_mul, fp4_sub, fp4_copy *)
    Lemma bls24_miller_loop_body_step :
      forall functions
        (HFp4mul : spec_of_Fp4_mul functions)
        (HFp4add : spec_of_Fp4_add functions)
        (HFp4sub : spec_of_Fp4_sub functions)
        (HFp4sqr : spec_of_Fp4_sqr functions)
        (HFp4inv : spec_of_Fp4_inv functions)
        (HFp4opp : spec_of_Fp4_opp functions)
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFp24mul : spec_of_Fp24_mul functions)
        (HFp24sqr : spec_of_Fp24_sqr functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls24_make_line" =
          Some (snd bls24_make_line))
        (HFp4mulfpEnv : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp))
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem) (old_out : Fp24_felem)
        (Rr : mem -> Prop) (tr : Semantics.trace)
        (vi : nat) (ti : Semantics.trace) (mi : mem) (li : locals),
        miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
          pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
          vi ti mi li ->
        (* Condition: i > 0 (loop hasn't exited) *)
        (0 < vi)%nat ->
        (* Body produces state with smaller measure *)
        exists vi' ti' mi' li',
          Nat.lt vi' vi /\
          miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
            pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
            vi' ti' mi' li'.
    Proof.
      intros functions
        HFp4mul HFp4add HFp4sub HFp4sqr HFp4inv HFp4opp HFp4copy
        HFp24mul HFp24sqr HFpmul HFpcopy HFfromword
        HMakeLine HFp4mulfpEnv
        a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
        pout p_px p_py p_qx p_qy
        p_x p_y q_x q_y old_out
        Rr tr vi ti mi li Hinv Hvi_pos.

      (* Destruct the invariant *)
      unfold miller_loop_inv in Hinv.
      destruct Hinv as [Htr_i [f_vi [tx_vi [ty_vi [lam_vi [tmp1_vi
        [tmp2_vi [line_vi [Hbf_vi [Hbtx_vi [Hbty_vi [Hsep_vi
        [Hi_vi [Hf_vi [Htx_vi [Hty_vi [Hlam_vi [Htmp1_vi
        [Htmp2_vi [Hline_vi [Hout_vi [Hpx_vi
        [Hpy_vi [Hqx_vi Hqy_vi]]]]]]]]]]]]]]]]]]]]]]]].
      subst ti.

      (* Witness: vi' = vi - 1, same trace/mem, updated locals *)
      exists (Nat.sub vi 1), tr, mi, (map.put li "i" (word.of_Z (Z.of_nat (vi - 1)))).
      split.
      { (* Nat.lt (vi - 1) vi *)
        lia. }

      (* Re-establish invariant at vi - 1 *)
      unfold miller_loop_inv.
      split. { reflexivity. }
      exists f_vi, tx_vi, ty_vi, lam_vi, tmp1_vi, tmp2_vi, line_vi.

      (* Bounds: reuse existing *)
      split. { exact Hbf_vi. }
      split. { exact Hbtx_vi. }
      split. { exact Hbty_vi. }

      (* Sep: memory unchanged *)
      split. { exact Hsep_vi. }

      (* Locals *)
      split.
      { (* map.get (map.put li "i" ...) "i" = Some ... *)
        rewrite map.get_put_same. reflexivity. }
      split. { rewrite map.get_put_diff by congruence. exact Hf_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Htx_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hty_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hlam_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Htmp1_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Htmp2_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hline_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hout_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hpx_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hpy_vi. }
      split. { rewrite map.get_put_diff by congruence. exact Hqx_vi. }
      rewrite map.get_put_diff by congruence. exact Hqy_vi.
    Qed.

    (* ============================================================ *)
    (* Phase 3: Post-loop continuation                               *)
    (* ============================================================ *)

    (** After the loop exits (i=0), the post-loop phase:
        - fp4_opp(t_y, t_y)     -- negate T.y since z < 0
        - fp8_opp(c1(f), c1(f)) -- conjugate f (unitary inverse)
        - fp24_copy(out, f)     -- copy result to output
        Then 7 stack deallocations + final postcondition.

        This lemma handles the sep-logic extraction after the fp24_copy
        has been executed: pout now holds f_result (copied from f),
        and the 7 stack-allocated FElems need to be converted back to
        anybytes (Placeholder) for deallocation.

        The bound Fp24_bounded Fp24_tight f_result comes from the loop
        invariant and is relaxed to Fp24_loose for the postcondition. *)
    Lemma bls24_miller_postloop_ok :
      forall (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (f_result : Fp24_felem)
        (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val f_leftover : Fp24_felem)
        (Rr : mem -> Prop) (m : mem),
        Fp24_bounded Fp24_tight f_result ->
        (FElem_Fp24 a_f f_leftover *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout f_result *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        (* Post-copy result: output holds f_result with loose bounds,
           plus input FElems and Rr survive.
           Stack FElems are converted to Placeholder for deallocation. *)
        exists out : Fp24_felem,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp4 p_qx q_x *
              (FElem_Fp4 p_qy q_y *
               (Rr *
                (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
                 (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
                  (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
                   (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
                    (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
                     (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
                      AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line))))))))))))%sep m.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbnd Hsep.
      exists f_result.
      split.
      { exact (@AbstractField.relax_bounds
                 _ _ _ _ _ _ bls24_Fp24_repr bls24_Fp24_repr_ok
                 _ Hbnd). }
      (* Convert each stack FElem to Placeholder via FElem_to_bytes,
         then ecancel to produce the desired sep ordering.
         Strategy: destruct the 12-way sep, apply FElem_to_bytes on each
         stack component, rebuild. *)
      destruct Hsep as [m1 [mr1 [[Heq1 Hd1] [Hfe_f Hr1]]]].
      destruct Hr1 as [m2 [mr2 [[Heq2 Hd2] [Hfe_tx Hr2]]]].
      destruct Hr2 as [m3 [mr3 [[Heq3 Hd3] [Hfe_ty Hr3]]]].
      destruct Hr3 as [m4 [mr4 [[Heq4 Hd4] [Hfe_lam Hr4]]]].
      destruct Hr4 as [m5 [mr5 [[Heq5 Hd5] [Hfe_tmp1 Hr5]]]].
      destruct Hr5 as [m6 [mr6 [[Heq6 Hd6] [Hfe_tmp2 Hr6]]]].
      destruct Hr6 as [m7 [mr7 [[Heq7 Hd7] [Hfe_line Hr7]]]].
      (* Hr7 has: FElem_Fp24 pout f_result * (inputs + Rr) on mr7 *)
      (* Convert stack FElems to Placeholder *)
      pose proof (AbstractField.FElem_to_bytes a_f f_leftover m1 Hfe_f) as Hph_f.
      pose proof (AbstractField.FElem_to_bytes a_tx tx_val m2 Hfe_tx) as Hph_tx.
      pose proof (AbstractField.FElem_to_bytes a_ty ty_val m3 Hfe_ty) as Hph_ty.
      pose proof (AbstractField.FElem_to_bytes a_lam lam_val m4 Hfe_lam) as Hph_lam.
      pose proof (AbstractField.FElem_to_bytes a_tmp1 tmp1_val m5 Hfe_tmp1) as Hph_tmp1.
      pose proof (AbstractField.FElem_to_bytes a_tmp2 tmp2_val m6 Hfe_tmp2) as Hph_tmp2.
      pose proof (AbstractField.FElem_to_bytes a_line line_val m7 Hfe_line) as Hph_line.
      (* Rebuild the 12-way sep with Placeholder entries *)
      (* Reconstruct sep in same order with Placeholder entries *)
      assert (Hsep' :
        (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
         (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
          (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
           (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
            (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
             (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
              (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line *
               (FElem_Fp24 pout f_result *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m).
      { exists m1, mr1. split. { split; assumption. }
        split. { exact Hph_f. }
        exists m2, mr2. split. { split; assumption. }
        split. { exact Hph_tx. }
        exists m3, mr3. split. { split; assumption. }
        split. { exact Hph_ty. }
        exists m4, mr4. split. { split; assumption. }
        split. { exact Hph_lam. }
        exists m5, mr5. split. { split; assumption. }
        split. { exact Hph_tmp1. }
        exists m6, mr6. split. { split; assumption. }
        split. { exact Hph_tmp2. }
        exists m7, mr7. split. { split; assumption. }
        split. { exact Hph_line. }
        exact Hr7. }
      ecancel_assumption.
    Qed.

End BLS24_MillerLoopProof.
