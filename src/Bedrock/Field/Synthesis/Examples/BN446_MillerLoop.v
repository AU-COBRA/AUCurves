(** * BN446 Miller Loop WP Proof
    Standalone WP correctness proof for bn446_miller_loop from BN446_Pairing.v.
    Uses Loops.while_localsmap with a 65->0 nat measure.

    Key differences from BN254 (BN254_MillerLoop.v):
    - beta = -1, xi = (3, 1)
    - 65 iterations (66-bit 6u+2 parameter, MSB consumed at init) instead of 64
    - u6p2 stored as 2-word array (16 bytes) on stack; bit extraction loads indexed word
    - No conjugation after loop (positive u)
    - 8 stackallocs (7 FElems + 1 u6p2 array of 16 bytes)
    - Fp = 4 words (not 6)
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BN446_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BN446 Section context                                             *)
(* ================================================================ *)

Section BN446_MillerLoop.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BN446 prime parameters *)
    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn446_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn446_mul"; PrimeField.add := "bn446_add";
      PrimeField.sub := "bn446_sub"; PrimeField.opp := "bn446_opp";
      PrimeField.square := "bn446_square"; PrimeField.scmula24 := "bn446_scmula24";
      PrimeField.inv := "bn446_inv"; PrimeField.from_bytes := "bn446_from_bytes";
      PrimeField.to_bytes := "bn446_to_bytes"; PrimeField.select_znz := "bn446_select_znz";
      PrimeField.felem_copy := "bn446_felem_copy"; PrimeField.from_word := "bn446_from_word";
      PrimeField.from_list := "bn446_from_list";
    |}.

    Instance bn446_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn446. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bn446_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn446_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn446_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn446_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn446_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn446_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn446_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn446_frep |}.

    Instance bn446_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn446_Fp_rep] in *.
      cbv [Field.bounded_by bn446_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn446_Fp2_".
    Let fp6_prefix := "bn446_Fp6_".
    Let fp12_prefix := "bn446_Fp12_".

    (* beta = -1 for BN446 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn446_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (3, 1) for BN446 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn446_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 2.
    Let bn446_xi_im : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bn446_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bn446_beta "bn446_".
    Instance bn446_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bn446_beta "bn446_".
    Instance bn446_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_".

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn446_Fp12_params'.
    Local Typeclasses Opaque bn446_Fp6_params'.
    Local Typeclasses Opaque bn446_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_add.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_square.

    Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_inv.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bn446_Fp2_rep').

    (* Fp12 operations *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.bin_mul.

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.un_square.

    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn446_Fp12_rep').

    (* Fp operations needed by make_line *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bn446_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bn446_Fp_rep).

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bn446_Fp_rep).

    (* spec_of for bn446_make_line -- needed by straightline_call *)
    Instance spec_of_bn446_make_line : spec_of "bn446_make_line" :=
      fnspec! "bn446_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp12_felem) (lam xt yt : Fp2_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight lam /\
          Fp2_bounded Fp2_tight xt /\
          Fp2_bounded Fp2_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp2 plam lam ⋆
            (FElem_Fp2 pxt xt ⋆
             (FElem_Fp2 pyt yt ⋆
              (FElem_Fp pxp xp ⋆
               (FElem_Fp pyp yp ⋆ Rr)))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp2 plam lam ⋆
              (FElem_Fp2 pxt xt ⋆
               (FElem_Fp2 pyt yt ⋆
                (FElem_Fp pxp xp ⋆
                 (FElem_Fp pyp yp ⋆ Rr)))))) mem' }.

    (* ============================================================ *)
    (* D1: bn446_miller_loop spec and proof                          *)
    (* ============================================================ *)

    Instance spec_of_bn446_miller_loop : spec_of "bn446_miller_loop" :=
      fnspec! "bn446_miller_loop" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight q_x /\
          Fp2_bounded Fp2_tight q_y /\
          Fp_bounded Fp_loose p_x /\
          Fp_bounded Fp_loose p_y /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    (* u6p2 value: |6u+2| for BN446 is 66 bits, stored as [lo, hi].
       The MSB (bit 65) initializes T=Q; we iterate bits 64 down to 0.
       Bit extraction: idx = i >> 6, addr = u6p2 + (idx << 3),
         word = load(addr), bit = (word >> (i & 63)) & 1. *)
    Local Definition u6p2_limbs : list word :=
      [word.of_Z BN446_Pairing.bn446_6u2_lo; word.of_Z BN446_Pairing.bn446_6u2_hi].

    (* Loop invariant for the Miller loop.
       The measure v counts down from 65 to 0. At each iteration, the
       loop body decrements i by 1, so v = word.unsigned(i).
       The invariant asserts:
       - The trace is unchanged (no I/O)
       - All 7 stack-allocated FElems, the u6p2 array, and 5 input FElems exist in memory
         with appropriate bounds
       - The locals map binds the expected variable names *)
    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line a_u6p2 : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) (old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp12_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp2_felem)
             (line_val : Fp12_felem),
        (v <= 112)%nat /\
        Fp12_bounded Fp12_tight f_val /\
        Fp2_bounded Fp2_tight tx_val /\
        Fp2_bounded Fp2_tight ty_val /\
        (FElem_Fp12 a_f f_val ⋆
         (FElem_Fp2 a_tx tx_val ⋆
          (FElem_Fp2 a_ty ty_val ⋆
           (FElem_Fp2 a_lam lam_val ⋆
            (FElem_Fp2 a_tmp1 tmp1_val ⋆
             (FElem_Fp2 a_tmp2 tmp2_val ⋆
              (FElem_Fp12 a_line line_val ⋆
               (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆
                (FElem_Fp12 pout old_out ⋆
                 (FElem_Fp p_px p_x ⋆
                  (FElem_Fp p_py p_y ⋆
                   (FElem_Fp2 p_qx q_x ⋆
                    (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "u6p2" = Some a_u6p2 /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* Helper lemmas *)
    Local Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew -> A mOld -> B mNew -> (A ⋆ B) m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    Local Notation fp_felem_offset_val :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep)).

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split bn446_beta
        fp2_prefix p x m1 Hfp2) as [ma [mb [[Heq2 Hd2] [Ha Hb]]]].
      subst m1.
      pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd) as [Hd_a Hd_b].
      exists ma, (map.putmany mb m2).
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_r. split; [exact Hd2 | exact Hd_a]. }
      split; [exact Ha |].
      exists mb, m2.
      split; [split; [reflexivity | exact Hd_b] |].
      split; [exact Hb | exact HR].
    Qed.

    Lemma FElem_Fp_join_in_sep p (a b : Fp_felem) R m :
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep ->
      (FElem_Fp p a ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) b ⋆ R)) m ->
      (FElem_Fp2 p (a ++ b) ⋆ R) m.
    Proof.
      intros Hla Hlb [ma [mr1 [[Heq1 Hd1] [Ha Hr1]]]].
      destruct Hr1 as [mb [mr2 [[Heq2 Hd2] [Hb HR]]]].
      subst mr1.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ab Hd_ar].
      assert (Hjoin : (FElem_Fp p a ⋆
        FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) b) (map.putmany ma mb)).
      { exists ma, mb. split; [split; [reflexivity | exact Hd_ab] |].
        split; [exact Ha | exact Hb]. }
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join bn446_beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    (* u6p2: convert anybytes 16 at addr a into two scalars in a sep.
       Mechanical: split anybytes 16 into two anybytes 8, then use anybytes_to_scalar. *)
    Local Lemma anybytes16_to_2scalars (a : word) (R : mem -> Prop) (m : mem) :
      (Memory.anybytes a 16 ⋆ R) m ->
      exists w0 w1, (scalar a w0 ⋆ (scalar (word.add a (word.of_Z 8)) w1 ⋆ R)) m.
    Proof.
      intro Hsep.
      destruct Hsep as [m_any [m_R [[Hm Hdisj] [Hany HR]]]].
      apply Array.anybytes_to_array_1 in Hany.
      destruct Hany as [bs [Harr Hlen]].
      change (Z.to_nat 16) with 16%nat in Hlen.
      pose proof (List.firstn_skipn 8 bs) as Hsplit.
      rewrite <- Hsplit in Harr.
      apply Array.bytearray_append in Harr.
      destruct Harr as [m1 [m2 [[Hm12 Hd12] [Harr1 Harr2]]]].
      assert (Hlen1 : List.length (List.firstn 8 bs) = 8%nat).
      { rewrite List.length_firstn. lia. }
      assert (Hlen2 : List.length (List.skipn 8 bs) = 8%nat).
      { rewrite List.length_skipn. lia. }
      apply Array.array_1_to_anybytes in Harr1.
      rewrite Hlen1 in Harr1.
      apply Array.array_1_to_anybytes in Harr2.
      rewrite Hlen2 in Harr2.
      change (Z.of_nat 8) with 8 in *.
      change 8 with (Memory.bytes_per_word 64) in Harr1 at 1.
      apply anybytes_to_scalar in Harr1.
      destruct Harr1 as [w0 Hsc0].
      rewrite Hlen1 in Harr2. change (Z.of_nat 8) with 8 in Harr2.
      assert (Harr2' : Memory.anybytes (word.add a (word.of_Z 8)) (Memory.bytes_per_word 64) m2).
      { exact Harr2. }
      apply anybytes_to_scalar in Harr2'.
      destruct Harr2' as [w1 Hsc1].
      exists w0, w1.
      exists m1, (map.putmany m2 m_R).
      assert (Hd1R : map.disjoint m1 m_R).
      { subst m_any. apply (proj1 (map.disjoint_putmany_l m1 m2 m_R)) in Hdisj. tauto. }
      assert (Hd2R : map.disjoint m2 m_R).
      { subst m_any. apply (proj1 (map.disjoint_putmany_l m1 m2 m_R)) in Hdisj. tauto. }
      split.
      { split.
        - subst m_any. rewrite map.putmany_assoc. exact Hm.
        - apply map.disjoint_putmany_r. split; [exact Hd12 | exact Hd1R]. }
      split; [exact Hsc0 |].
      exists m2, m_R.
      split.
      { split; [reflexivity | exact Hd2R]. }
      split; [exact Hsc1 | exact HR].
    Qed.

    (* u6p2 store lemma: process 2 stores to stack-allocated u6p2 array.
       Converts anybytes 16 -> array scalar [lo; hi] after both stores complete. *)
    Local Lemma u6p2_stores_wp :
      forall call t (m : mem) l (a_u6p2 : word) R
             (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "u6p2" = Some a_u6p2 ->
        (Memory.anybytes a_u6p2 16 ⋆ R) m ->
        (forall m', (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆ R) m' ->
          post t m' l) ->
        WeakestPrecondition.cmd call
          (BN446_Pairing.store_6u2_limbs) t m l post.
    Proof.
      intros call t m l a_u6p2 R post Hget Hany Hpost.
      pose proof (anybytes16_to_2scalars a_u6p2 R m Hany) as [w0 [w1 Hsep2]].
      unfold BN446_Pairing.store_6u2_limbs, BN446_Pairing.cmd_seq_list.
      (* First store: cmd.store word (expr.var "u6p2") (expr.literal lo) *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        rewrite Hget. eexists. split; exact eq_refl. }
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal dlet.dlet].
        split; exact eq_refl. }
      unfold store.
      eapply Scalars.store_word_of_sep.
      { ecancel_assumption. }
      intros m1 Hsep1.
      (* Second store: cmd.store word (u6p2+8) (expr.literal hi) *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      exists (word.add a_u6p2 (word.of_Z 8)). split.
      { unfold DEXPR, WeakestPrecondition.dexpr.
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        rewrite Hget.
        eexists. split; [exact eq_refl |]. cbv [Semantics.interp_binop]. exact eq_refl. }
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal dlet.dlet].
        split; exact eq_refl. }
      unfold store.
      eapply Scalars.store_word_of_sep.
      { ecancel_assumption. }
      intros m2 Hsep_final.
      apply Hpost.
      cbv [array u6p2_limbs].
      ecancel_assumption.
    Qed.

    (* u6p2 array to anybytes: convert 2-word scalar array back to anybytes 16.
       This is needed for stack deallocation. *)
    Local Lemma array_scalar2_to_anybytes16 :
      forall (a : word) (ws : list word) (m : mem),
      length ws = 2%nat ->
      array scalar (word.of_Z 8) a ws m ->
      Memory.anybytes a 16 m.
    Proof.
      intros a ws m Hlen Harr.
      destruct ws as [|w0 ws']; [simpl in Hlen; discriminate |].
      destruct ws' as [|w1 ws'']; [simpl in Hlen; discriminate |].
      destruct ws'' as [| w2 ws3]; [| simpl in Hlen; discriminate].
      assert (Hbn : Bignum.Bignum 2 a [w0; w1] m).
      { unfold Bignum.Bignum. exists map.empty, m.
        split. { split.
          { apply (proj2 (Properties.map.split_empty_l m m)). reflexivity. }
          { apply Properties.map.disjoint_empty_l. } }
        split. { split; [reflexivity | reflexivity]. }
        { exact Harr. } }
      pose proof (proj1 (Bignum.Bignum_to_bytes 2 a [w0; w1] m) Hbn) as Hbn2.
      destruct Hbn2 as [m_e [m_a [Hspl [[He Hlen_bs] Harr_ptsto]]]].
      subst m_e. apply Properties.map.split_empty_l in Hspl. subst m_a.
      apply (Array.array_1_to_anybytes) in Harr_ptsto.
      rewrite Hlen_bs in Harr_ptsto.
      change (Z.of_nat (2 * Z.to_nat (Memory.bytes_per_word 64))) with 16
        in Harr_ptsto.
      exact Harr_ptsto.
    Qed.

    (* u6p2 array load lemma: load from 2-word u6p2 array at symbolic index *)
    Local Lemma u6p2_array_load (a_u6p2 i_val : word) (m : mem) (R : mem -> Prop)
      (Hsep : (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆ R) m) :
      let idx := Z.to_nat (word.unsigned (word.sru i_val (word.of_Z 6))) in
      let addr := word.add a_u6p2 (word.slu (word.sru i_val (word.of_Z 6)) (word.of_Z 3)) in
      (idx < length u6p2_limbs)%nat ->
      Memory.load access_size.word m addr = Some (nth idx u6p2_limbs (word.of_Z 0)).
    Proof.
      intros idx addr Hbound.
      pose proof (Scalars.array_load_of_sep a_u6p2 addr idx u6p2_limbs
        (word.of_Z 8) access_size.word R m Hsep) as Hload.
      assert (Haddr : addr = word.add a_u6p2
        (word.of_Z (word.unsigned (word.of_Z (width:=64) 8) * Z.of_nat idx))).
      { subst addr idx. f_equal.
        apply word.unsigned_inj.
        rewrite word.unsigned_slu_shamtZ by lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        rewrite word.unsigned_of_Z.
        unfold word.wrap. f_equal.
        rewrite Z2Nat.id
          by (pose proof (word.unsigned_range (word.sru i_val (word.of_Z 6))); lia).
        change (word.unsigned (word.of_Z (width:=64) 8)) with 8.
        lia. }
      rewrite Hload by assumption.
      f_equal. unfold Scalars.truncate_word, Scalars.truncate_Z.
      apply word.unsigned_inj. rewrite word.unsigned_of_Z.
      unfold word.wrap. rewrite Z.land_ones by lia.
      pose proof (word.unsigned_range (nth idx u6p2_limbs (word.of_Z 0))).
      rewrite Zmod_mod. rewrite Z.mod_small by lia. reflexivity.
    Qed.

    (* Tactics -- aliases to generic versions from BLS12_MillerGeneric *)
    Local Ltac snd_from_word_ecancel H := BLS12_MillerGeneric.miller_snd_from_word_ecancel H.
    Local Ltac normalize_pairing_instances := BLS12_MillerGeneric.miller_normalize_pairing_instances.
    Local Ltac resolve_map_get := BLS12_MillerGeneric.miller_resolve_map_get.
    Local Ltac eval_expr_abstract := BLS12_MillerGeneric.miller_eval_expr_abstract.
    Local Ltac miller_straightline := BLS12_MillerGeneric.miller_straightline.
    Local Ltac eval_dexprs_abstract := BLS12_MillerGeneric.miller_eval_dexprs_abstract.
    Local Ltac solve_miller_bounds := BLS12_MillerGeneric.miller_solve_bounds.
    Local Ltac wp_miller_call spec_hyp :=
      repeat miller_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ let H := fresh "Hcallee" in
        pose proof spec_hyp as H;
        eapply H;
        first
        [ wp_binop_precond solve_miller_bounds
        | wp_unop_precond solve_miller_bounds
        | ecancel_assumption_with_copy
        | split; ecancel_assumption_with_copy
        | repeat (first
            [ solve_miller_bounds
            | ecancel_assumption_with_copy
            | split ])
        ]
      | cbv beta; wp_postcall_auto
      ];
      try (unfold dlet.dlet; cbv beta);
      match goal with
      | Hrem : exists _, _ /\ _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hfeval := fresh "Hfeval" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hfeval [Hbound Hsep]]];
        try clear Hfeval
      | Hrem : exists _, _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hbound Hsep]]
      end.

    (* Word subtraction -- from generic *)
    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

    Lemma bn446_miller_loop_ok :
      forall functions
        (EnvContains : map.get functions "bn446_miller_loop" =
          Some (snd bn446_miller_loop))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2add : spec_of_Fp2_add functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bn446_make_line" =
          Some (snd bn446_make_line))
        (HFp2mulfpEnv : map.get functions "bn446_Fp2_mul_fp" =
          Some (snd bn446_Fp2_mul_fp))
        (HMakeLineOk : spec_of_bn446_make_line functions),
      spec_of_bn446_miller_loop functions.
    Proof.
      intros.
      unfold spec_of_bn446_miller_loop.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
      (* === Function entry === *)
      eapply WeakestPreconditionProperties.start_func;
        [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn446_miller_loop. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Process 8 stackallocs === *)
      repeat straightline.

      (* Stackalloc 1: f (Fp12-sized) *)
      split. { apply Z_mod_mult. }
      intros a_f mStack_f mComb_f HanyF HsplitF.
      repeat straightline.

      (* Stackalloc 2: t_x (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tx mStack_tx mComb_tx HanyTx HsplitTx.
      repeat straightline.

      (* Stackalloc 3: t_y (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_ty mStack_ty mComb_ty HanyTy HsplitTy.
      repeat straightline.

      (* Stackalloc 4: lambda (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_lam mStack_lam mComb_lam HanyLam HsplitLam.
      repeat straightline.

      (* Stackalloc 5: tmp1 (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp1 mStack_tmp1 mComb_tmp1 HanyTmp1 HsplitTmp1.
      repeat straightline.

      (* Stackalloc 6: tmp2 (Fp2-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp2 mStack_tmp2 mComb_tmp2 HanyTmp2 HsplitTmp2.
      repeat straightline.

      (* Stackalloc 7: line (Fp12-sized) *)
      split. { apply Z_mod_mult. }
      intros a_line mStack_line mComb_line HanyLine HsplitLine.
      (* Don't use repeat straightline here -- it may consume the u6p2 stackalloc *)
      straightline. (* cmd.seq *)

      (* Stackalloc 8: u6p2 (16 bytes = 2 words) *)
      split. { cbv. reflexivity. }
      intros a_u6p2 mStack_u6p2 mComb_u6p2 HanyU6p2 HsplitU6p2.

      (* Convert anybytes to FElems for all stack-allocated FElem buffers *)
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep'
        wordok mapok a_f) as Hfb_f.
      unfold AbstractField.Placeholder in Hfb_f.
      pose proof (proj1 (Hfb_f mStack_f) HanyF) as [f_val Hfe_f]. clear Hfb_f.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tx) as Hfb_tx.
      unfold AbstractField.Placeholder in Hfb_tx.
      pose proof (proj1 (Hfb_tx mStack_tx) HanyTx) as [tx_val Hfe_tx]. clear Hfb_tx.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_ty) as Hfb_ty.
      unfold AbstractField.Placeholder in Hfb_ty.
      pose proof (proj1 (Hfb_ty mStack_ty) HanyTy) as [ty_val Hfe_ty]. clear Hfb_ty.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_lam) as Hfb_lam.
      unfold AbstractField.Placeholder in Hfb_lam.
      pose proof (proj1 (Hfb_lam mStack_lam) HanyLam) as [lam_val Hfe_lam]. clear Hfb_lam.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tmp1) as Hfb_tmp1.
      unfold AbstractField.Placeholder in Hfb_tmp1.
      pose proof (proj1 (Hfb_tmp1 mStack_tmp1) HanyTmp1) as [tmp1_val Hfe_tmp1]. clear Hfb_tmp1.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tmp2) as Hfb_tmp2.
      unfold AbstractField.Placeholder in Hfb_tmp2.
      pose proof (proj1 (Hfb_tmp2 mStack_tmp2) HanyTmp2) as [tmp2_val Hfe_tmp2]. clear Hfb_tmp2.

      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep'
        wordok mapok a_line) as Hfb_line.
      unfold AbstractField.Placeholder in Hfb_line.
      pose proof (proj1 (Hfb_line mStack_line) HanyLine) as [line_val Hfe_line]. clear Hfb_line.

      (* === Build master separation logic hypothesis === *)

      (* Destruct Hsep to expose the sub-components *)
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

      (* f buffer (Fp12) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_f) as Hany_f'.
      match goal with H : Datatypes.length stack = _ |- _ => rewrite H in Hany_f' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep'
        wordok mapok a_f) as Hfb_f'.
      unfold AbstractField.Placeholder in Hfb_f'.
      pose proof (proj1 (Hfb_f' m_s7) Hany_f') as [f_val' Hfe_f']. clear Hfb_f' Hany_f'.

      (* tx buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tx) as Hany_tx'.
      match goal with H : Datatypes.length stack0 = _ |- _ => rewrite H in Hany_tx' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tx) as Hfb_tx'.
      unfold AbstractField.Placeholder in Hfb_tx'.
      pose proof (proj1 (Hfb_tx' m_s8) Hany_tx') as [tx_val' Hfe_tx']. clear Hfb_tx' Hany_tx'.

      (* ty buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_ty) as Hany_ty'.
      match goal with H : Datatypes.length stack1 = _ |- _ => rewrite H in Hany_ty' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_ty) as Hfb_ty'.
      unfold AbstractField.Placeholder in Hfb_ty'.
      pose proof (proj1 (Hfb_ty' m_s9) Hany_ty') as [ty_val' Hfe_ty']. clear Hfb_ty' Hany_ty'.

      (* lam buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_lam) as Hany_lam'.
      match goal with H : Datatypes.length stack2 = _ |- _ => rewrite H in Hany_lam' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_lam) as Hfb_lam'.
      unfold AbstractField.Placeholder in Hfb_lam'.
      pose proof (proj1 (Hfb_lam' m_s10) Hany_lam') as [lam_val' Hfe_lam']. clear Hfb_lam' Hany_lam'.

      (* tmp1 buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp1) as Hany_tmp1'.
      match goal with H : Datatypes.length stack3 = _ |- _ => rewrite H in Hany_tmp1' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tmp1) as Hfb_tmp1'.
      unfold AbstractField.Placeholder in Hfb_tmp1'.
      pose proof (proj1 (Hfb_tmp1' m_s11) Hany_tmp1') as [tmp1_val' Hfe_tmp1']. clear Hfb_tmp1' Hany_tmp1'.

      (* tmp2 buffer (Fp2) *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp2) as Hany_tmp2'.
      match goal with H : Datatypes.length stack4 = _ |- _ => rewrite H in Hany_tmp2' end.
      pose proof (@AbstractField.FElem_from_bytes _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep'
        wordok mapok a_tmp2) as Hfb_tmp2'.
      unfold AbstractField.Placeholder in Hfb_tmp2'.
      pose proof (proj1 (Hfb_tmp2' m_s12) Hany_tmp2') as [tmp2_val' Hfe_tmp2']. clear Hfb_tmp2' Hany_tmp2'.

      clear Harr_f Harr_tx Harr_ty Harr_lam Harr_tmp1 Harr_tmp2.

      (* Now rebuild sep on mem0 with FElem entries on the CORRECT sub-maps *)
      eassert (Hsep_fe :
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp p_px p_x ⋆
          (FElem_Fp p_py p_y ⋆
           (FElem_Fp2 p_qx q_x ⋆
            (FElem_Fp2 p_qy q_y ⋆
             (Rr ⋆
              (FElem_Fp12 a_f f_val' ⋆
               (FElem_Fp2 a_tx tx_val' ⋆
                (FElem_Fp2 a_ty ty_val' ⋆
                 (FElem_Fp2 a_lam lam_val' ⋆
                  (FElem_Fp2 a_tmp1 tmp1_val' ⋆
                   FElem_Fp2 a_tmp2 tmp2_val'))))))))))) mem0).
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

      (* Build master sep on mComb_line (before u6p2 stackalloc) *)
      eassert (Hmaster_pre :
        (FElem_Fp12 a_f f_val' ⋆
         (FElem_Fp2 a_tx tx_val' ⋆
          (FElem_Fp2 a_ty ty_val' ⋆
           (FElem_Fp2 a_lam lam_val' ⋆
            (FElem_Fp2 a_tmp1 tmp1_val' ⋆
             (FElem_Fp2 a_tmp2 tmp2_val' ⋆
              (FElem_Fp12 a_line line_val ⋆
               (FElem_Fp12 pout old_out ⋆
                (FElem_Fp p_px p_x ⋆
                 (FElem_Fp p_py p_y ⋆
                  (FElem_Fp2 p_qx q_x ⋆
                   (FElem_Fp2 p_qy q_y ⋆ Rr)))))))))))) mComb_line).
      {
        pose proof (sep_from_split HsplitLine Hsep_fe Hfe_line) as Htmp.
        pose proof Htmp as H'. ecancel_assumption.
      }

      (* Build master sep on mComb_u6p2, adding u6p2 anybytes *)
      eassert (Hmaster :
        (FElem_Fp12 a_f f_val' ⋆
         (FElem_Fp2 a_tx tx_val' ⋆
          (FElem_Fp2 a_ty ty_val' ⋆
           (FElem_Fp2 a_lam lam_val' ⋆
            (FElem_Fp2 a_tmp1 tmp1_val' ⋆
             (FElem_Fp2 a_tmp2 tmp2_val' ⋆
              (FElem_Fp12 a_line line_val ⋆
               (Memory.anybytes a_u6p2 16 ⋆
                (FElem_Fp12 pout old_out ⋆
                 (FElem_Fp p_px p_x ⋆
                  (FElem_Fp p_py p_y ⋆
                   (FElem_Fp2 p_qx q_x ⋆
                    (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))) mComb_u6p2).
      {
        pose proof (sep_from_split HsplitU6p2 Hmaster_pre HanyU6p2) as Htmp.
        pose proof Htmp as H'. ecancel_assumption.
      }

      (* === Phase 2: Process init calls + loop + dealloc === *)

      unfold BN446_Pairing.miller_loop_full_body.
      unfold BN446_Pairing.cmd_seq_list.
      unfold BN446_Pairing.fp12_set_one.
      unfold BN446_Pairing.expr_fp12_c0, BN446_Pairing.expr_fp12_c1,
             BN446_Pairing.expr_fp6_c0, BN446_Pairing.expr_fp6_c1,
             BN446_Pairing.expr_fp6_c2, BN446_Pairing.expr_fp_snd.

      (* Offset notations *)
      Local Notation fp_felem_offset :=
        (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep)).
      Local Notation fp6_felem_offset :=
        (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep')).
      Local Notation fp6_c1_off :=
        (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix).
      Local Notation fp6_c2_off :=
        (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix).

      (* Split FElem_Fp12 a_f -> 6 FElem_Fp2 *)
      eassert (Hf_sep : (FElem_Fp12 a_f f_val' ⋆ _) mComb_u6p2).
      { pose proof Hmaster as H'. ecancel_assumption. }

      destruct Hf_sep as [m_f12 [m_f12_rest [Hsplit_f12 [Hfe_f12 Hf12_rest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bn446_beta bn446_xi_re bn446_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_f f_val' m_f12 Hfe_f12)
        as Hf12_split.

      destruct Hf12_split as [m_d0 [m_d1 [Hsplit_d0d1 [Hfe_d0 Hfe_d1]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bn446_beta bn446_xi_re bn446_xi_im
        fp6_prefix fp2_prefix a_f _ m_d0 Hfe_d0)
        as [m_c00 [m_c01_02 [Hsplit_c00 [Hfe_c00 Hc01_02]]]].
      destruct Hc01_02 as [m_c01 [m_c02 [Hsplit_c01_02 [Hfe_c01 Hfe_c02]]]].

      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bn446_beta bn446_xi_re bn446_xi_im
        fp6_prefix fp2_prefix
        (word.add a_f (word.of_Z fp6_felem_offset)) _ m_d1 Hfe_d1)
        as [m_c10 [m_c11_12 [Hsplit_c10 [Hfe_c10 Hc11_12]]]].
      destruct Hc11_12 as [m_c11 [m_c12 [Hsplit_c11_12 [Hfe_c11 Hfe_c12]]]].

      destruct Hsplit_c00 as [Heq_c00 Hd_c00'].
      destruct Hsplit_c01_02 as [Heq_c01_02 Hd_c01_02'].
      destruct Hsplit_c10 as [Heq_c10 Hd_c10'].
      destruct Hsplit_c11_12 as [Heq_c11_12 Hd_c11_12'].
      destruct Hsplit_d0d1 as [Heq_d0d1 Hd_d0d1].
      destruct Hsplit_f12 as [Heq_f12 Hd_f12'].

      (* Normalize FElem types *)
      change (Fp2_field_parameters bn446_beta fp2_prefix)
        with bn446_Fp2_params' in Hfe_c00, Hfe_c01, Hfe_c02, Hfe_c10, Hfe_c11, Hfe_c12.
      change (Fp2_field_representation bn446_beta fp2_prefix)
        with bn446_Fp2_rep' in Hfe_c00, Hfe_c01, Hfe_c02, Hfe_c10, Hfe_c11, Hfe_c12.

      subst m_c01_02 m_c11_12 m_d0 m_d1 m_f12.
      rewrite ?map.putmany_assoc in Heq_f12.
      split_all_disjointness.

      (* Build expanded sep on mComb_u6p2 with 6 Fp2 sub-components of f *)
      eassert (Hsep_expanded :
        (FElem_Fp2 a_f (c0_felem (d0_felem f_val')) ⋆
         (FElem_Fp2 (word.add a_f fp6_c1_off) (c1_felem (d0_felem f_val')) ⋆
          (FElem_Fp2 (word.add a_f fp6_c2_off) (c2_felem (d0_felem f_val')) ⋆
           (FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem f_val')) ⋆
            (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off)
               (c1_felem (d1_felem f_val')) ⋆
             (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off)
                (c2_felem (d1_felem f_val')) ⋆
              (FElem_Fp2 a_tx tx_val' ⋆
               (FElem_Fp2 a_ty ty_val' ⋆
                (FElem_Fp2 a_lam lam_val' ⋆
                 (FElem_Fp2 a_tmp1 tmp1_val' ⋆
                  (FElem_Fp2 a_tmp2 tmp2_val' ⋆
                   (FElem_Fp12 a_line line_val ⋆
                    (Memory.anybytes a_u6p2 16 ⋆
                     (FElem_Fp12 pout old_out ⋆
                      (FElem_Fp p_px p_x ⋆
                       (FElem_Fp p_py p_y ⋆
                        (FElem_Fp2 p_qx q_x ⋆
                         (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))))))))
        mComb_u6p2).
      { subst mComb_u6p2.
        rewrite <- ?map.putmany_assoc.
        exists m_c00, (map.putmany m_c01 (map.putmany m_c02
          (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c00 |].
        exists m_c01, (map.putmany m_c02
          (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c01 |].
        exists m_c02, (map.putmany m_c10 (map.putmany m_c11 (map.putmany m_c12 m_f12_rest))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c02 |].
        exists m_c10, (map.putmany m_c11 (map.putmany m_c12 m_f12_rest)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c10 |].
        exists m_c11, (map.putmany m_c12 m_f12_rest).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c11 |].
        exists m_c12, m_f12_rest.
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_c12 |].
        exact Hf12_rest. }

      (* === Phase 2: Process 12 from_word calls === *)
      eassert (Hpair1 : (FElem_Fp2 a_f (c0_felem (d0_felem f_val')) ⋆ _) mComb_u6p2).
      { pose proof Hsep_expanded as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair1.

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d0_felem f_val'))) _ tr).
           exact Hpair1. }
      intros t_fw1 m_fw1 rets_fw1 [Hrets_fw1 [Htr_fw1 [fw1 [_ [Hb_fw1 Hsep_fw1]]]]].
      subst rets_fw1. symmetry in Htr_fw1. subst t_fw1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 2: from_word(a_f.d0.c0 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw1. }
      intros t_fw2 m_fw2 rets_fw2 [Hrets_fw2 [Htr_fw2 [fw2 [_ [Hb_fw2 Hsep_fw2]]]]].
      subst rets_fw2. symmetry in Htr_fw2. subst t_fw2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 3-4: from_word on c1(d0) fst/snd --- *)
      repeat straightline.
      eassert (Hpair2 : (FElem_Fp2 (word.add a_f fp6_c1_off) (c1_felem (d0_felem f_val')) ⋆ _) m_fw2).
      { pose proof Hsep_fw2 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair2.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d0_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair2. }
      intros t_fw3 m_fw3 rets_fw3 [Hrets_fw3 [Htr_fw3 [fw3 [_ [Hb_fw3 Hsep_fw3]]]]].
      subst rets_fw3. symmetry in Htr_fw3. subst t_fw3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw3. }
      intros t_fw4 m_fw4 rets_fw4 [Hrets_fw4 [Htr_fw4 [fw4 [_ [Hb_fw4 Hsep_fw4]]]]].
      subst rets_fw4. symmetry in Htr_fw4. subst t_fw4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 5-6: from_word on c2(d0) fst/snd --- *)
      repeat straightline.
      eassert (Hpair3 : (FElem_Fp2 (word.add a_f fp6_c2_off) (c2_felem (d0_felem f_val')) ⋆ _) m_fw4).
      { pose proof Hsep_fw4 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair3.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d0_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair3. }
      intros t_fw5 m_fw5 rets_fw5 [Hrets_fw5 [Htr_fw5 [fw5 [_ [Hb_fw5 Hsep_fw5]]]]].
      subst rets_fw5. symmetry in Htr_fw5. subst t_fw5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d0_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw5. }
      intros t_fw6 m_fw6 rets_fw6 [Hrets_fw6 [Htr_fw6 [fw6 [_ [Hb_fw6 Hsep_fw6]]]]].
      subst rets_fw6. symmetry in Htr_fw6. subst t_fw6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 7-8: from_word on c0(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair4 : (FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem f_val')) ⋆ _) m_fw6).
      { pose proof Hsep_fw6 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair4.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair4. }
      intros t_fw7 m_fw7 rets_fw7 [Hrets_fw7 [Htr_fw7 [fw7 [_ [Hb_fw7 Hsep_fw7]]]]].
      subst rets_fw7. symmetry in Htr_fw7. subst t_fw7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw7. }
      intros t_fw8 m_fw8 rets_fw8 [Hrets_fw8 [Htr_fw8 [fw8 [_ [Hb_fw8 Hsep_fw8]]]]].
      subst rets_fw8. symmetry in Htr_fw8. subst t_fw8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 9-10: from_word on c1(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair5 : (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off) (c1_felem (d1_felem f_val')) ⋆ _) m_fw8).
      { pose proof Hsep_fw8 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair5.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair5. }
      intros t_fw9 m_fw9 rets_fw9 [Hrets_fw9 [Htr_fw9 [fw9 [_ [Hb_fw9 Hsep_fw9]]]]].
      subst rets_fw9. symmetry in Htr_fw9. subst t_fw9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw9. }
      intros t_fw10 m_fw10 rets_fw10 [Hrets_fw10 [Htr_fw10 [fw10 [_ [Hb_fw10 Hsep_fw10]]]]].
      subst rets_fw10. symmetry in Htr_fw10. subst t_fw10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Calls 11-12: from_word on c2(d1) fst/snd --- *)
      repeat straightline.
      eassert (Hpair6 : (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off) (c2_felem (d1_felem f_val')) ⋆ _) m_fw10).
      { pose proof Hsep_fw10 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hpair6.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d1_felem f_val'))) _ tr).
           normalize_pairing_instances. exact Hpair6. }
      intros t_fw11 m_fw11 rets_fw11 [Hrets_fw11 [Htr_fw11 [fw11 [_ [Hb_fw11 Hsep_fw11]]]]].
      subst rets_fw11. symmetry in Htr_fw11. subst t_fw11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d1_felem f_val'))) _ tr).
           snd_from_word_ecancel Hsep_fw11. }
      intros t_fw12 m_fw12 rets_fw12 [Hrets_fw12 [Htr_fw12 [fw12 [_ [Hb_fw12 Hsep_fw12]]]]].
      subst rets_fw12. symmetry in Htr_fw12. subst t_fw12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Step 1: Extract Fp-level lengths from FElem predicates === *)
      Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep).
      Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
      Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep').
      Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).
      Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bn446_pf_params bn446_Fp_rep).

      pose proof fun p v m (H : FElem_Fp p v m) =>
        @QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bn446_pf_params bn446_Fp_rep p v m H
        as FpLen.

      assert (Hlen_fw1 : length fw1 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw1 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw2 : length fw2 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw2 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw3 : length fw3 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw3 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw4 : length fw4 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw4 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw5 : length fw5 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw5 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw6 : length fw6 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw6 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw7 : length fw7 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw7 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw8 : length fw8 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw8 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw9 : length fw9 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw9 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw10 : length fw10 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw10 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw11 : length fw11 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw11 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw12 : length fw12 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw12 ⋆ _) m_fw12) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      clear FpLen.

      (* === Step 2: Chain-join Fp pairs into Fp2 === *)

      (* Join d0.c0: fw1 + fw2 *)
      eassert (Hsep_j1 : (FElem_Fp _ fw1 ⋆ (FElem_Fp _ fw2 ⋆ _)) m_fw12).
      { pose proof Hsep_fw12 as H'. ecancel_assumption. }
      apply FElem_Fp_join_in_sep in Hsep_j1; [| exact Hlen_fw1 | exact Hlen_fw2].

      (* Join d0.c1: fw3 + fw4 *)
      eassert (Hsep_j2 : (FElem_Fp _ fw3 ⋆ (FElem_Fp _ fw4 ⋆ _)) m_fw12).
      { pose proof Hsep_j1 as H'. ecancel_assumption. }
      eassert (Hsep_j2' : (FElem_Fp _ fw3 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw4 ⋆ _)) m_fw12).
      { exact Hsep_j2. }
      apply FElem_Fp_join_in_sep in Hsep_j2'; [| exact Hlen_fw3 | exact Hlen_fw4].

      (* Join d0.c2: fw5 + fw6 *)
      eassert (Hsep_j3 : (FElem_Fp _ fw5 ⋆ (FElem_Fp _ fw6 ⋆ _)) m_fw12).
      { pose proof Hsep_j2' as H'. ecancel_assumption. }
      eassert (Hsep_j3' : (FElem_Fp _ fw5 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw6 ⋆ _)) m_fw12).
      { exact Hsep_j3. }
      apply FElem_Fp_join_in_sep in Hsep_j3'; [| exact Hlen_fw5 | exact Hlen_fw6].

      (* Join d1.c0: fw7 + fw8 *)
      eassert (Hsep_j4 : (FElem_Fp _ fw7 ⋆ (FElem_Fp _ fw8 ⋆ _)) m_fw12).
      { pose proof Hsep_j3' as H'. ecancel_assumption. }
      eassert (Hsep_j4' : (FElem_Fp _ fw7 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw8 ⋆ _)) m_fw12).
      { exact Hsep_j4. }
      apply FElem_Fp_join_in_sep in Hsep_j4'; [| exact Hlen_fw7 | exact Hlen_fw8].

      (* Join d1.c1: fw9 + fw10 *)
      eassert (Hsep_j5 : (FElem_Fp _ fw9 ⋆ (FElem_Fp _ fw10 ⋆ _)) m_fw12).
      { pose proof Hsep_j4' as H'. ecancel_assumption. }
      eassert (Hsep_j5' : (FElem_Fp _ fw9 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw10 ⋆ _)) m_fw12).
      { exact Hsep_j5. }
      apply FElem_Fp_join_in_sep in Hsep_j5'; [| exact Hlen_fw9 | exact Hlen_fw10].

      (* Join d1.c2: fw11 + fw12 *)
      eassert (Hsep_j6 : (FElem_Fp _ fw11 ⋆ (FElem_Fp _ fw12 ⋆ _)) m_fw12).
      { pose proof Hsep_j5' as H'. ecancel_assumption. }
      eassert (Hsep_j6' : (FElem_Fp _ fw11 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw12 ⋆ _)) m_fw12).
      { exact Hsep_j6. }
      apply FElem_Fp_join_in_sep in Hsep_j6'; [| exact Hlen_fw11 | exact Hlen_fw12].

      (* === Steps 3-6: Join Fp2->Fp6->Fp12 and rebuild sep === *)

      eassert (Hsep_d0_ext :
        ((FElem_Fp2 a_f (fw1 ++ fw2) ⋆
          (FElem_Fp2 (word.add a_f fp6_c1_off) (fw3 ++ fw4) ⋆
           FElem_Fp2 (word.add a_f fp6_c2_off) (fw5 ++ fw6))) ⋆ _) m_fw12).
      { pose proof Hsep_j6' as H'. ecancel_assumption_impl. }
      destruct Hsep_d0_ext as [m_d0_3 [m_d0_rest [Hsplit_d0 [Hfe_d0_3 Hd0_rest]]]].

      eassert (Hd1_3_ext :
        ((FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset)) (fw7 ++ fw8) ⋆
          (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c1_off) (fw9 ++ fw10) ⋆
           FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset)) fp6_c2_off) (fw11 ++ fw12))) ⋆ _) m_d0_rest).
      { pose proof Hd0_rest as H'. ecancel_assumption_impl. }
      destruct Hd1_3_ext as [m_d1_3 [m_rest [Hsplit_d1 [Hfe_d1_3 Hrest]]]].

      (* Length facts for Fp2 *)
      assert (Hlen_d0c0_fp2 : length (fw1 ++ fw2) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw1, Hlen_fw2. reflexivity. }
      assert (Hlen_d0c1_fp2 : length (fw3 ++ fw4) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw3, Hlen_fw4. reflexivity. }
      assert (Hlen_d0c2_fp2 : length (fw5 ++ fw6) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw5, Hlen_fw6. reflexivity. }
      assert (Hlen_d1c0_fp2 : length (fw7 ++ fw8) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
      assert (Hlen_d1c1_fp2 : length (fw9 ++ fw10) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw9, Hlen_fw10. reflexivity. }
      assert (Hlen_d1c2_fp2 : length (fw11 ++ fw12) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw11, Hlen_fw12. reflexivity. }

      (* Build Fp6 for d0 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bn446_pf_params bn446_beta bn446_xi_re bn446_xi_im bn446_Fp_rep fp6_prefix fp2_prefix
        a_f (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) m_d0_3
        Hlen_d0c0_fp2 Hlen_d0c1_fp2 Hlen_d0c2_fp2 Hfe_d0_3)
        as Hfe_d0'.

      (* Build Fp6 for d1 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bn446_pf_params bn446_beta bn446_xi_re bn446_xi_im bn446_Fp_rep fp6_prefix fp2_prefix
        (word.add a_f (word.of_Z fp6_felem_offset))
        (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) m_d1_3
        Hlen_d1c0_fp2 Hlen_d1c1_fp2 Hlen_d1c2_fp2 Hfe_d1_3)
        as Hfe_d1'.

      (* Build Fp12 from d0 and d1 *)
      assert (Hlen_d0_fp6 : length ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw1, Hlen_fw2, Hlen_fw3, Hlen_fw4, Hlen_fw5, Hlen_fw6.
        reflexivity. }
      assert (Hlen_d1_fp6 : length ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_fw9, Hlen_fw10, Hlen_fw11, Hlen_fw12.
        reflexivity. }

      (* Build 2-way Fp6 sep *)
      destruct Hsplit_d0 as [Heq_d0 Hd_d0].
      destruct Hsplit_d1 as [Heq_d1 Hd_d1].
      set (m_fp12_j := map.putmany m_d0_3 m_d1_3).
      assert (Hsep_2fp6 : (FElem_Fp6 a_f ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ⋆
        FElem_Fp6 (word.add a_f (word.of_Z fp6_felem_offset))
          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))) m_fp12_j).
      { subst m_fp12_j. exists m_d0_3, m_d1_3.
        split; [split; [reflexivity |] |].
        { subst m_d0_rest.
          exact (proj1 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0)). }
        split; [exact Hfe_d0' | exact Hfe_d1']. }

      pose proof (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _
        wordok mapok bn446_pf_params bn446_Fp_rep bn446_beta bn446_xi_re bn446_xi_im fp12_prefix fp6_prefix fp2_prefix
        a_f ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
        ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) m_fp12_j
        Hlen_d0_fp6 Hlen_d1_fp6 Hsep_2fp6)
        as Hfe_fp12_j.

      (* Rebuild full sep *)
      set (f_new := ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ++
                     ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))).
      eassert (Hsep_rejoined :
        (FElem_Fp12 a_f f_new ⋆
         (FElem_Fp2 a_tx tx_val' ⋆
          (FElem_Fp2 a_ty ty_val' ⋆
           (FElem_Fp2 a_lam lam_val' ⋆
            (FElem_Fp2 a_tmp1 tmp1_val' ⋆
             (FElem_Fp2 a_tmp2 tmp2_val' ⋆
              (FElem_Fp12 a_line line_val ⋆
               (Memory.anybytes a_u6p2 16 ⋆
                (FElem_Fp12 pout old_out ⋆
                 (FElem_Fp p_px p_x ⋆
                  (FElem_Fp p_py p_y ⋆
                   (FElem_Fp2 p_qx q_x ⋆
                    (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))) m_fw12).
      { subst m_fw12 m_d0_rest m_fp12_j.
        exists (map.putmany m_d0_3 m_d1_3), m_rest.
        split; [split |].
        { rewrite map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { exact (proj2 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0)). }
          { exact Hd_d1. } }
        split; [exact Hfe_fp12_j | exact Hrest]. }

      (* === fp2_copy: copy q_x -> a_tx === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp2copy.
           pose proof Hsep_rejoined as Htmp_copy.
           split; ecancel_assumption_impl. }
      intros t_c1 m_c1 rets_c1 Hpost_c1.
      destruct Hpost_c1 as [Hrets_c1 [Htr_c1 Hsep_c1]].
      subst rets_c1. symmetry in Htr_c1. subst t_c1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === fp2_copy: copy q_y -> a_ty === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp2copy.
           pose proof Hsep_c1 as Htmp_copy2.
           split; ecancel_assumption_impl. }
      intros t_c2 m_c2 rets_c2 Hpost_c2.
      destruct Hpost_c2 as [Hrets_c2 [Htr_c2 Hsep_c2]].
      subst rets_c2. symmetry in Htr_c2. subst t_c2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Process store_6u2_limbs + set i === *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eapply u6p2_stores_wp.
      { repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence].
        exact eq_refl. }
      { ecancel_assumption. }
      intros m_stores Hsep_stores.
      repeat straightline.

      eapply Loops.while_localsmap
        with (v0 := 112%nat)
             (lt := Nat.lt)
             (invariant := miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line a_u6p2
                      pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr).

      (* well_founded *)
      { exact lt_wf. }

      (* Initial invariant *)
      { unfold miller_loop_inv.
        split; [reflexivity |].
        eexists f_new, _, _, lam_val', tmp1_val', tmp2_val', line_val.
        (* v <= 65 *)
        split. { lia. }
        (* Bounds *)
        split.
        { (* Fp12_bounded Fp12_tight f_new -- from 12 from_word tight bounds *)
          subst f_new.
          change Fp12_bounded with
            (fun (b : @AbstractField.bounds _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep')
                 (felem : list word) =>
              @AbstractField.bounded_by _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep' b (d0_felem felem) /\
              @AbstractField.bounded_by _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep' b (d1_felem felem));
            cbv beta.
          rewrite (@DodecicFieldExtensions.d0_felem_app _ _ _ _
            bn446_pf_params bn446_Fp_rep bn446_beta bn446_xi_re bn446_xi_im fp6_prefix fp2_prefix
            ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
            ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))
            Hlen_d0_fp6).
          rewrite (@DodecicFieldExtensions.d1_felem_app _ _ _ _
            bn446_pf_params bn446_Fp_rep bn446_beta bn446_xi_re bn446_xi_im fp6_prefix fp2_prefix
            ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
            ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))
            Hlen_d0_fp6).
          change (@AbstractField.bounded_by _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep') with
            (fun (b : @AbstractField.bounds _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep')
                 (felem : list word) =>
              Fp2_bounded b (c0_felem felem) /\
              Fp2_bounded b (c1_felem felem) /\
              Fp2_bounded b (c2_felem felem));
            cbv beta.
          rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2).
          rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
          rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
          rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2).
          rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
          rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _
            bn446_pf_params bn446_beta bn446_Fp_rep fp2_prefix
            (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
          change Fp2_bounded with
            (fun (b : @AbstractField.bounds _ _ _ _ _ _ bn446_Fp_rep)
                 (ws : list word) =>
              Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws));
            cbv beta.
          unfold fst_felem, snd_felem,
            QuadraticFieldExtensionsSpecs.fst_felem,
            QuadraticFieldExtensionsSpecs.snd_felem.
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw1).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw1).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw3).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw3).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw5).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw5).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw7).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw7).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw9).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw9).
          rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw11).
          rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw11).
          split.
          { split.
            { split; [exact Hb_fw1 | exact Hb_fw2]. }
            split.
            { split; [exact Hb_fw3 | exact Hb_fw4]. }
            { split; [exact Hb_fw5 | exact Hb_fw6]. } }
          { split.
            { split; [exact Hb_fw7 | exact Hb_fw8]. }
            split.
            { split; [exact Hb_fw9 | exact Hb_fw10]. }
            { split; [exact Hb_fw11 | exact Hb_fw12]. } } }
        split.
        { exact Hbqx. }
        split.
        { exact Hbqy. }
        split.
        { (* Sep -- the current sep matches the invariant (with u6p2 array) *)
          ecancel_assumption. }
        (* Locals: map.get for each variable *)
        repeat split; repeat straightline. }

      (* Loop body *)
      { intros vi ti mi li Hinv.
        unfold miller_loop_inv in Hinv.
        destruct Hinv as [Htr_i [f_vi [tx_vi [ty_vi [lam_vi [tmp1_vi
          [tmp2_vi [line_vi [Hvi_bound [Hbf_vi [Hbtx_vi [Hbty_vi [Hsep_vi
          [Hi_vi [Hf_vi [Htx_vi [Hty_vi [Hlam_vi [Htmp1_vi
          [Htmp2_vi [Hline_vi [Hu6p2_vi [Hout_vi [Hpx_vi
          [Hpy_vi [Hqx_vi Hqy_vi]]]]]]]]]]]]]]]]]]]]]]]]]].
        subst ti.

        (* Evaluate branch condition: expr.var "i" *)
        exists (word.of_Z (Z.of_nat vi)).
        split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          rewrite Hi_vi.
          exists (word.of_Z (Z.of_nat vi)).
          split; exact eq_refl. }
        split.
        { (* TRUE branch: word.unsigned br <> 0, loop body *)
          intro Hne.

          unfold BN446_Pairing.miller_loop_iteration.
          unfold BN446_Pairing.cmd_seq_list.

          (* Process set i = i - 1 *)
          miller_straightline. (* cmd.seq *)
          miller_straightline. (* cmd.set "i" -- updates locals *)
          unfold dlet.dlet; cbv beta.

          (* Process set "word" = load(u6p2 + (i/64)*8)
             This involves a memory load that needs special handling.
             We need to:
             1. Extract the u6p2 array from the sep
             2. Prove the load succeeds via u6p2_array_load
             3. Introduce the loaded value *)
          miller_straightline. (* cmd.seq *)

          (* cmd.set "word" (expr.load access_size.word addr_expr) *)
          unfold1_cmd_goal; cbv beta match delta [cmd_body].
          letexists. split.
          { (* Evaluate load expression: provide the load result directly *)
            eassert (Harr_sep : (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆ _) mi).
            { pose proof Hsep_vi as H'. ecancel_assumption. }
            pose proof (u6p2_array_load a_u6p2 v mi _ Harr_sep) as Hload.
            cbv beta zeta in Hload.
            assert (Hbound_load : (Z.to_nat (word.unsigned (word.sru v (word.of_Z 6))) < Datatypes.length u6p2_limbs)%nat).
            { cbv [u6p2_limbs]. simpl length.
              enough (word.unsigned (word.sru v (word.of_Z 6)) < 2) by lia.
              rewrite word.unsigned_sru_nowrap.
              { rewrite word.unsigned_of_Z. change (word.wrap 6) with 6.
                rewrite Z.shiftr_div_pow2 by lia.
                pose proof (word.unsigned_range v).
                assert (word.unsigned v < 128).
                { assert (Hv_eq : v = @word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1)).
                  { subst v. apply word.unsigned_inj. reflexivity. }
                  rewrite Hv_eq. rewrite word.unsigned_sub.
                  rewrite !word.unsigned_of_Z. unfold word.wrap.
                  assert (0 < vi)%nat by (destruct vi; [exfalso; apply Hne; reflexivity | lia]).
                  rewrite (Z.mod_small (Z.of_nat vi) (2^64)) by lia.
                  rewrite (Z.mod_small 1 (2^64)) by lia.
                  rewrite Z.mod_small by lia. lia. }
                apply Z.div_lt_upper_bound; lia. }
              { rewrite word.unsigned_of_Z. change (word.wrap 6) with 6. lia. } }
            specialize (Hload Hbound_load).
            unfold DEXPR, WeakestPrecondition.dexpr.
            cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get WeakestPrecondition.literal
                 WeakestPrecondition.load dlet.dlet].
            eexists. split. { resolve_map_get. }
            eexists. split. { resolve_map_get. }
            cbv [Semantics.interp_binop].
            eexists. split. { exact Hload. }
            exact eq_refl. }
          unfold dlet.dlet; cbv beta.

          (* Process set "bit" = (word >> (i%64)) & 1 *)
          miller_straightline. (* cmd.seq *)
          miller_straightline. (* cmd.set "bit" *)
          unfold dlet.dlet; cbv beta.

          (* After set: locals have "i", "word", "bit" added.
             Now process ~30 function calls + conditional + invariant. *)

          (* === Doubling step === *)

          (* Use the make_line spec hypothesis *)
          set (HMakeLineSpec := HMakeLineOk).

          (* Helper tactic for make_line calls *)
          Local Ltac handle_make_line :=
            eexists;
            split;
            [ cbv [dexprs list_map list_map_body
                   WeakestPrecondition.expr WeakestPrecondition.expr_body
                   WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
              repeat match goal with
                | |- _ /\ _ => split
                | |- exists _, _ => eexists
                | |- map.get _ _ = Some _ => resolve_map_get
                | |- @eq _ _ _ => exact eq_refl
                | |- True => exact I
              end
            | straightline_call ].

          Local Ltac solve_word_nat :=
            repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence];
            f_equal;
            apply Properties.word.unsigned_inj;
            rewrite word.unsigned_of_Z;
            match goal with |- word.unsigned ?w = ?rhs =>
              let u := eval cbv beta iota delta [word.unsigned Naive.unsigned] in
                (word.unsigned w) in
              change (word.unsigned w) with u
            end;
            cbv [word.wrap];
            Z.to_euclidean_division_equations; nia.

          Local Ltac solve_miller_mapget :=
            match goal with
            | |- map.get _ "i" = Some _ =>
              repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence];
              first
              [ exact eq_refl
              | assumption
              | (f_equal; rewrite <- word.ring_morph_sub; f_equal; lia)
              | (f_equal; rewrite word_nat_sub1 by lia; reflexivity)
              | (f_equal;
                 match goal with
                 | |- ?lhs = word.of_Z (Z.of_nat (?n - 1)) =>
                   replace lhs with (@word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1))
                     by reflexivity;
                   exact (word_nat_sub1 n ltac:(lia))
                 end) ]
            | |- map.get _ _ = Some _ =>
              repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence];
              first
              [ exact eq_refl
              | assumption
              | match goal with
                | H : map.get _ ?k = Some _ |- map.get _ ?k = Some _ => exact H
                end ]
            end.

          Local Ltac solve_miller_leaf :=
            first
            [ eexists; normalize_pairing_instances; ecancel_assumption_with_copy
            | normalize_pairing_instances; ecancel_assumption_with_copy
            | solve_miller_bounds
            | solve_miller_mapget
            ].

          Local Ltac solve_miller_precond :=
            match goal with
            | |- _ /\ _ => split; [| solve_miller_precond]; solve_miller_leaf
            | _ => solve_miller_leaf
            end.

          Local Ltac solve_miller_locals :=
            solve_miller_precond.

          Local Ltac mcall spec :=
            try miller_straightline;
            unfold1_cmd_goal; cbv beta match delta [cmd_body];
            letexists; split; [solve [eval_dexprs_abstract] |];
            eapply Semantics.weaken_call;
            [ eapply spec; solve_miller_precond
            | cbv beta; intros ? ? ? [? [? ?]]; subst;
              cbv [map.putmany_of_list_zip];
              eexists; split; [exact eq_refl |]
            ];
            try match goal with
            | Hrem : exists _, _ /\ _ /\ _ |- _ =>
              destruct Hrem as [?vout [?Hfe [?Hb ?Hs]]]; try clear Hfe
            | Hrem : exists _, _ /\ _ |- _ =>
              destruct Hrem as [?vout [?Hb ?Hs]]
            end.

          (* === Doubling step === *)
          mcall HFp2sqr.   (* D1: fp2_sqr(tmp1, t_x) *)
          mcall HFp2add.   (* D2: fp2_add(lambda, tmp1, tmp1) *)
          mcall HFp2add.   (* D3: fp2_add(lambda, lambda, tmp1) *)
          mcall HFp2add.   (* D4: fp2_add(tmp1, t_y, t_y) *)
          mcall HFp2inv.   (* D5: fp2_inv(tmp1, tmp1) *)
          mcall HFp2mul.   (* D6: fp2_mul(lambda, lambda, tmp1) *)
          mcall HMakeLineSpec. (* D7: make_line *)
          mcall HFp12sqr.  (* D8: fp12_sqr(f, f) *)
          mcall HFp12mul.  (* D9: fp12_mul(f, f, line) *)
          mcall HFp2sqr.   (* D10: fp2_sqr(tmp1, lambda) *)
          mcall HFp2sub.   (* D11: fp2_sub(tmp1, tmp1, t_x) *)
          mcall HFp2sub.   (* D12: fp2_sub(tmp2, tmp1, t_x) *)
          mcall HFp2sub.   (* D13: fp2_sub(tmp1, t_x, tmp2) *)
          mcall HFp2mul.   (* D14: fp2_mul(tmp1, lambda, tmp1) *)
          mcall HFp2sub.   (* D15: fp2_sub(t_y, tmp1, t_y) *)
          mcall HFp2copy.  (* D16: fp2_copy(t_x, tmp2) *)

          (* === Conditional: cond on "bit" === *)
          miller_straightline. (* cmd.cond *)
          split.

          { (* Bit = 1 (word.unsigned v <> 0): addition step *)
            intro Hbit_ne.
            unfold BN446_Pairing.cmd_seq_list.

            mcall HFp2sub.  (* A1 *)
            mcall HFp2sub.  (* A2 *)
            mcall HFp2inv.  (* A3 *)
            mcall HFp2mul.  (* A4 *)
            mcall HMakeLineSpec. (* A5 *)
            mcall HFp12mul. (* A6 *)
            mcall HFp2sqr.  (* A7 *)
            mcall HFp2sub.  (* A8 *)
            mcall HFp2sub.  (* A9 *)
            mcall HFp2sub.  (* A10 *)
            mcall HFp2mul.  (* A11 *)
            mcall HFp2sub.  (* A12 *)
            mcall HFp2copy. (* A13 *)

            (* Re-establish invariant (addition branch) *)
            assert (Hvi_pos : (0 < vi)%nat).
            { destruct vi; [exfalso; apply Hne; reflexivity | lia]. }

            exists (Nat.sub vi 1).
            split; [ | lia].
            unfold miller_loop_inv.
            split. { exact eq_refl. }
            do 7 eexists.
            split; [| split; [| split; [| split; [| split]]]].
            5: { normalize_pairing_instances. ecancel_assumption. }
            { lia. }
            { solve_miller_bounds. }
            { solve_miller_bounds. }
            { solve_miller_bounds. }
            (* Handle "i" separately, rest via solve_miller_precond *)
            split.
            { repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence].
              f_equal. replace v with (@word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1))
                by (unfold v; reflexivity).
              exact (word_nat_sub1 vi Hvi_pos). }
            solve_miller_precond. }

          { (* Bit = 0: skip -- nothing changed, reuse doubling step's sep *)
            intro Hbit_eq.
            miller_straightline. (* cmd.skip *)

            (* Re-establish invariant (skip branch) *)
            assert (Hvi_pos : (0 < vi)%nat).
            { destruct vi; [exfalso; apply Hne; reflexivity | lia]. }
            exists (Nat.sub vi 1).
            split; [ | lia].
            unfold miller_loop_inv.
            split. { exact eq_refl. }
            do 7 eexists.
            split; [| split; [| split; [| split; [| split]]]].
            5: normalize_pairing_instances; ecancel_assumption.
            - lia.
            - solve_miller_bounds.
            - solve_miller_bounds.
            - solve_miller_bounds.
            - split.
              + repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence].
                f_equal. replace v with (@word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1))
                  by (unfold v; reflexivity).
                exact (word_nat_sub1 vi Hvi_pos).
              + repeat (split; [solve_miller_leaf |]). solve_miller_leaf. } }
        { (* FALSE branch: word.unsigned br = 0, postcondition *)
          intro Heq0.

          (* The post-loop goal is the WP for:
             cmd.call fp12_copy [out; f] + 8 deallocs
             No conjugation for BN446. *)

          (* Provide arguments for the copy call *)
          exists [pout; a_f].
          split.
          { cbv [dexprs list_map list_map_body
                 WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get].
            rewrite Hout_vi. rewrite Hf_vi.
            eexists. split; [exact eq_refl |].
            eexists. split; [exact eq_refl |].
            exact eq_refl. }

          (* fp12_copy(out, f) via Semantics.call *)
          eapply Semantics.weaken_call.
          1: { eapply HFp12copy.
               split; ecancel_assumption. }
          intros t_cp m_cp ? [Hrets_cp Hsep_cp].
          subst.
          destruct Hsep_cp as [Htr_cp Hsep_cp'].
          symmetry in Htr_cp. subst t_cp.

          (* Process return value *)
          exists li.
          split. { cbv [map.putmany_of_list_zip]. exact eq_refl. }

          (* === Stack deallocation (8 levels) + final postcondition === *)

          (* --- Dealloc level 1: u6p2 (16 bytes) --- *)
          eassert (Hu6p2_sep : (_ ⋆ array scalar (word.of_Z 8) a_u6p2 u6p2_limbs) m_cp).
          { pose proof Hsep_cp' as H'. ecancel_assumption. }
          destruct Hu6p2_sep as [m_rest_u6p2 [m_u6p2 [[Heq_u6p2 Hd_u6p2] [Hrest_u6p2 Hu6p2]]]].
          exists m_rest_u6p2, m_u6p2.
          split. { exact (array_scalar2_to_anybytes16 _ _ _ (eq_refl : length u6p2_limbs = 2%nat) Hu6p2). }
          split. { split; [exact Heq_u6p2 | exact Hd_u6p2]. }

          (* --- Dealloc level 2: line (Fp12-sized) --- *)
          eassert (Hline_sep : (_ ⋆ FElem_Fp12 a_line line_vi) m_rest_u6p2).
          { pose proof Hrest_u6p2 as H'. ecancel_assumption. }
          destruct Hline_sep as [m_rest_line [m_line [[Heq_line Hd_line] [Hrest_line Hfline]]]].
          exists m_rest_line, m_line.
          split. { exact (AbstractField.FElem_to_bytes a_line line_vi m_line Hfline). }
          split. { split; [exact Heq_line | exact Hd_line]. }

          (* --- Dealloc level 3: tmp2 (Fp2-sized) --- *)
          eassert (Htmp2_sep : (_ ⋆ FElem_Fp2 a_tmp2 tmp2_vi) m_rest_line).
          { pose proof Hrest_line as H'. ecancel_assumption. }
          destruct Htmp2_sep as [m_rest_tmp2 [m_tmp2 [[Heq_tmp2 Hd_tmp2] [Hrest_tmp2 Hftmp2]]]].
          exists m_rest_tmp2, m_tmp2.
          split. { exact (AbstractField.FElem_to_bytes a_tmp2 tmp2_vi m_tmp2 Hftmp2). }
          split. { split; [exact Heq_tmp2 | exact Hd_tmp2]. }

          (* --- Dealloc level 4: tmp1 (Fp2-sized) --- *)
          eassert (Htmp1_sep : (_ ⋆ FElem_Fp2 a_tmp1 tmp1_vi) m_rest_tmp2).
          { pose proof Hrest_tmp2 as H'. ecancel_assumption. }
          destruct Htmp1_sep as [m_rest_tmp1 [m_tmp1 [[Heq_tmp1 Hd_tmp1] [Hrest_tmp1 Hftmp1]]]].
          exists m_rest_tmp1, m_tmp1.
          split. { exact (AbstractField.FElem_to_bytes a_tmp1 tmp1_vi m_tmp1 Hftmp1). }
          split. { split; [exact Heq_tmp1 | exact Hd_tmp1]. }

          (* --- Dealloc level 5: lambda (Fp2-sized) --- *)
          eassert (Hlam_sep : (_ ⋆ FElem_Fp2 a_lam lam_vi) m_rest_tmp1).
          { pose proof Hrest_tmp1 as H'. ecancel_assumption. }
          destruct Hlam_sep as [m_rest_lam [m_lam [[Heq_lam Hd_lam] [Hrest_lam Hflam]]]].
          exists m_rest_lam, m_lam.
          split. { exact (AbstractField.FElem_to_bytes a_lam lam_vi m_lam Hflam). }
          split. { split; [exact Heq_lam | exact Hd_lam]. }

          (* --- Dealloc level 6: t_y (Fp2-sized) --- *)
          eassert (Hty_sep : (_ ⋆ FElem_Fp2 a_ty ty_vi) m_rest_lam).
          { pose proof Hrest_lam as H'. ecancel_assumption. }
          destruct Hty_sep as [m_rest_ty [m_ty [[Heq_ty Hd_ty] [Hrest_ty Hfty]]]].
          exists m_rest_ty, m_ty.
          split. { exact (AbstractField.FElem_to_bytes a_ty ty_vi m_ty Hfty). }
          split. { split; [exact Heq_ty | exact Hd_ty]. }

          (* --- Dealloc level 7: t_x (Fp2-sized) --- *)
          eassert (Htx_sep : (_ ⋆ FElem_Fp2 a_tx tx_vi) m_rest_ty).
          { pose proof Hrest_ty as H'. ecancel_assumption. }
          destruct Htx_sep as [m_rest_tx [m_tx [[Heq_tx Hd_tx] [Hrest_tx Hftx]]]].
          exists m_rest_tx, m_tx.
          split. { exact (AbstractField.FElem_to_bytes a_tx tx_vi m_tx Hftx). }
          split. { split; [exact Heq_tx | exact Hd_tx]. }

          (* --- Dealloc level 8: f (Fp12-sized) --- *)
          eassert (Hf_sep : (_ ⋆ FElem_Fp12 a_f f_vi) m_rest_tx).
          { pose proof Hrest_tx as H'. ecancel_assumption. }
          destruct Hf_sep as [m_rest_f [m_f [[Heq_f Hd_f] [Hrest_f Hff]]]].
          exists m_rest_f, m_f.
          split. { exact (AbstractField.FElem_to_bytes a_f f_vi m_f Hff). }
          split. { split; [exact Heq_f | exact Hd_f]. }

          (* --- Final postcondition --- *)
          cbv [list_map list_map_body].
          split. { exact eq_refl. }
          split. { exact eq_refl. }
          exists f_vi.
          split. { pose proof (@DodecicFieldExtensionsSpecs.Fp12_field_representation_ok
                     _ _ _ _ bn446_pf_params bn446_Fp_rep bn446_Fp_rep_ok bn446_beta
                     bn446_xi_re bn446_xi_im fp12_prefix fp6_prefix fp2_prefix) as Hfp12_ok.
                   exact (@AbstractField.relax_bounds _ _ _ _ _ _ _ Hfp12_ok _ Hbf_vi). }
          exact Hrest_f. }
      }
    Qed.

End BN446_MillerLoop.
