(** * BN254 Miller Loop WP Proof
    Standalone WP correctness proof for bn254_miller_loop from BN254_Pairing.v.
    Uses Loops.while_localsmap with a 64->0 nat measure.

    Key differences from BLS12-377 (BLS12_377_MillerLoop.v):
    - beta = -1, xi = (9, 1)
    - 64 iterations (65-bit 6u+2 parameter, MSB consumed at init) instead of 65
    - u6p2 stored as 1-word (8 bytes) on stack; bit extraction is a single load
    - No conjugation after loop (positive u)
    - 8 stackallocs (7 FElems + 1 u6p2 word of 8 bytes)
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
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Override ecancel_fast with the original ecancel_assumption to avoid
   divergence on large sep contexts (the while loop body has 15+ atoms). *)
Local Ltac ecancel_assumption ::= SeparationLogic.ecancel_assumption.

(* ================================================================ *)
(* BN254 Section context                                             *)
(* ================================================================ *)

Section BN254_MillerLoopOptimal.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BN254 prime parameters *)
    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul"; PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub"; PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square"; PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv"; PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes"; PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy"; PrimeField.from_word := "bn254_from_word";
      PrimeField.from_list := "bn254_from_list";
    |}.

    Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bn254_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_Fp_rep] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn254_Fp2_".
    Let fp6_prefix := "bn254_Fp6_".
    Let fp12_prefix := "bn254_Fp12_".

    (* beta = -1 for BN254 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (9, 1) for BN254 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bn254_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bn254_beta "bn254_".
    Instance bn254_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bn254_beta "bn254_".
    Instance bn254_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn254_Fp6_params' _ _ _ _ bn254_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn254_Fp12_params'.
    Local Typeclasses Opaque bn254_Fp6_params'.
    Local Typeclasses Opaque bn254_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_add.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_square.

    Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_inv.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bn254_Fp2_rep').

    (* Fp12 operations *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.bin_mul.

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.un_square.

    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn254_Fp12_rep').

    (* Fp operations needed by make_line *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bn254_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bn254_Fp_rep).

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bn254_Fp_rep).

    (* spec_of for bn254_make_line -- needed by straightline_call *)
    Instance spec_of_bn254_make_line_corrected : spec_of "bn254_make_line_corrected" :=
      fnspec! "bn254_make_line_corrected" (pout plam pxt pyt pxp pyp : word)
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
    (* D1: bn254_miller_loop spec and proof                          *)
    (* ============================================================ *)

    Instance spec_of_bn254_miller_loop_optimal : spec_of "bn254_miller_loop_optimal" :=
      fnspec! "bn254_miller_loop_optimal" (pout p_px p_py p_qx p_qy : word)
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

    (* u6p2 value: |6u+2| low 64 bits = 0x9D797039BE763BA8.
       The MSB (bit 64) initializes T=Q; we iterate bits 63 down to 0. *)
    Local Definition u6p2_word : word := word.of_Z 0x9D797039BE763BA8.

    (* Loop invariant for the Miller loop.
       The measure v counts down from 64 to 0. At each iteration, the
       loop body decrements i by 1, so v = word.unsigned(i).
       The invariant asserts:
       - The trace is unchanged (no I/O)
       - All 7 stack-allocated FElems, the u6p2 scalar, and 5 input FElems exist in memory
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
        (v <= 64)%nat /\
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
               (scalar a_u6p2 u6p2_word ⋆
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
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep)).

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split bn254_beta
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
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
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
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join bn254_beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    (* u6p2 store lemma: process single store to stack-allocated u6p2.
       Converts anybytes 8 -> scalar after the store completes. *)
    Local Lemma u6p2_store_wp :
      forall call t (m : mem) l (a_u6p2 : word) R
             (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "u6p2" = Some a_u6p2 ->
        (Memory.anybytes a_u6p2 8 ⋆ R) m ->
        (forall m', (scalar a_u6p2 u6p2_word ⋆ R) m' ->
          post t m' l) ->
        WeakestPrecondition.cmd call
          (BN254_Pairing.store_6u2_limbs) t m l post.
    Proof.
      intros call t m l a_u6p2 R post Hget Hany Hpost.
      (* Convert anybytes 8 to a scalar *)
      change 8 with (Memory.bytes_per_word 64) in Hany.
      destruct Hany as [m_any [m_R [[Hm Hdisj] [Hany' HR]]]].
      apply anybytes_to_scalar in Hany'.
      destruct Hany' as [w0 Hsc0].
      (* Unfold store_6u2_limbs into a single store *)
      unfold BN254_Pairing.store_6u2_limbs.
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
      { subst m. exists m_any, m_R.
        split; [split; [reflexivity | exact Hdisj] |].
        split; [exact Hsc0 | exact HR]. }
      intros m1 Hsep1.
      apply Hpost.
      exact Hsep1.
    Qed.

    (* u6p2 scalar to anybytes: convert scalar back to anybytes 8.
       This is needed for stack deallocation. *)
    Local Lemma scalar_to_anybytes8 :
      forall (a : word) (w : word) (m : mem),
      scalar a w m ->
      Memory.anybytes a 8 m.
    Proof.
      intros a w m Hsc.
      apply scalar_to_anybytes in Hsc.
      exact Hsc.
    Qed.

    (* u6p2 load lemma: load from single-word u6p2 *)
    Local Lemma u6p2_scalar_load (a_u6p2 : word) (m : mem) (R : mem -> Prop)
      (Hsep : (scalar a_u6p2 u6p2_word ⋆ R) m) :
      Memory.load access_size.word m a_u6p2 = Some u6p2_word.
    Proof.
      eapply Scalars.load_word_of_sep.
      ecancel_assumption.
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

    Local Lemma sep_from_split_ext (P Q : mem -> Prop) (mC mPrev mStack : mem) :
      map.split mC mPrev mStack -> P mPrev -> Q mStack -> (Q ⋆ P) mC.
    Proof.
      intros [Heq Hd] HP HQ. subst mC.
      exists mStack, mPrev.
      split. { split. { apply map.putmany_comm. exact Hd. } exact (proj1 (map.disjoint_comm _ _) Hd). }
      exact (conj HQ HP).
    Qed.

    (* ============================================================ *)
    (* fp12_set_one_wp: reusable WP lemma for the fp12_set_one      *)
    (* initialization block.                                         *)
    (*                                                                *)
    (* Encapsulates the 12 from_word calls + Fp12→Fp decomposition + *)
    (* Fp→Fp12 recomposition into a single WP property.              *)
    (* Eliminates ~300 lines of repeated proof per Miller loop.      *)
    (* ============================================================ *)

    Local Notation fp_felem_offset_s1 :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep)).
    Local Notation fp6_felem_offset_s1 :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bn254_Fp6_params' _ _ _ _ bn254_Fp6_rep')).
    Local Notation fp6_c1_off_s1 :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bn254_pf_params bn254_beta bn254_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off_s1 :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bn254_pf_params bn254_beta bn254_Fp_rep fp2_prefix).

    Lemma fp12_set_one_wp :
      forall (e : map.rep (map := Semantics.env))
        (HFfromword : spec_of_Fp_from_word e)
        (a_f : word) (old_f : Fp12_felem) (R : mem -> Prop) tr mem_init l,
        map.get l "f" = Some a_f ->
        (FElem_Fp12 a_f old_f ⋆ R) mem_init ->
        WeakestPrecondition.cmd e
          (BN254_Pairing.fp12_set_one "f") tr mem_init l
          (fun t m' l' =>
            t = tr /\ l' = l /\
            exists f_one : Fp12_felem,
              Fp12_bounded Fp12_tight f_one /\
              (FElem_Fp12 a_f f_one ⋆ R) m').
    Proof.
      intros e HFfromword a_f old_f R tr mem_init l Hget Hsep.
      unfold BN254_Pairing.fp12_set_one, BN254_Pairing.cmd_seq_list.
      unfold BN254_Pairing.expr_fp12_c0, BN254_Pairing.expr_fp12_c1,
             BN254_Pairing.expr_fp6_c0, BN254_Pairing.expr_fp6_c1,
             BN254_Pairing.expr_fp6_c2, BN254_Pairing.expr_fp_snd.

      (* === Split FElem_Fp12 → 6 FElem_Fp2 === *)
      destruct Hsep as [m_f12 [m_rest [Hsplit_f12 [Hfe_f12 Hrest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bn254_beta bn254_xi_re bn254_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_f old_f m_f12 Hfe_f12)
        as [m_d0 [m_d1 [Hsd [Hfd0 Hfd1]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bn254_beta bn254_xi_re bn254_xi_im
        fp6_prefix fp2_prefix a_f _ m_d0 Hfd0)
        as [m00 [m0r [Hs0 [Hf00 H0r]]]].
      destruct H0r as [m01 [m02 [Hs01 [Hf01 Hf02]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bn254_beta bn254_xi_re bn254_xi_im
        fp6_prefix fp2_prefix (word.add a_f (word.of_Z fp6_felem_offset_s1)) _ m_d1 Hfd1)
        as [m10 [m1r [Hs1 [Hf10 H1r]]]].
      destruct H1r as [m11 [m12 [Hs11 [Hf11 Hf12]]]].
      destruct Hs0 as [? ?]. destruct Hs01 as [? ?].
      destruct Hs1 as [? ?]. destruct Hs11 as [? ?].
      destruct Hsd as [? ?]. destruct Hsplit_f12 as [? ?]. subst.
      change (Fp2_field_parameters bn254_beta fp2_prefix) with bn254_Fp2_params' in *.
      change (Fp2_field_representation bn254_beta fp2_prefix) with bn254_Fp2_rep' in *.
      split_all_disjointness.

      (* Build expanded sep with 6 FElem_Fp2 + R on combined memory *)
      eassert (Hsep_exp :
        (FElem_Fp2 a_f (c0_felem (d0_felem old_f)) ⋆
         (FElem_Fp2 (word.add a_f fp6_c1_off_s1) (c1_felem (d0_felem old_f)) ⋆
          (FElem_Fp2 (word.add a_f fp6_c2_off_s1) (c2_felem (d0_felem old_f)) ⋆
           (FElem_Fp2 (word.add a_f (word.of_Z fp6_felem_offset_s1)) (c0_felem (d1_felem old_f)) ⋆
            (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset_s1)) fp6_c1_off_s1) (c1_felem (d1_felem old_f)) ⋆
             (FElem_Fp2 (word.add (word.add a_f (word.of_Z fp6_felem_offset_s1)) fp6_c2_off_s1) (c2_felem (d1_felem old_f)) ⋆
              R)))))) (map.putmany (map.putmany (map.putmany m00 (map.putmany m01 m02)) (map.putmany m10 (map.putmany m11 m12))) m_rest)).
      { rewrite <- ?map.putmany_assoc.
        exists m00, (map.putmany m01 (map.putmany m02 (map.putmany m10 (map.putmany m11 (map.putmany m12 m_rest))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf00 |].
        exists m01, (map.putmany m02 (map.putmany m10 (map.putmany m11 (map.putmany m12 m_rest)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf01 |].
        exists m02, (map.putmany m10 (map.putmany m11 (map.putmany m12 m_rest))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf02 |].
        exists m10, (map.putmany m11 (map.putmany m12 m_rest)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf10 |].
        exists m11, (map.putmany m12 m_rest).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf11 |].
        exists m12, m_rest.
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf12 | exact Hrest]. }

      (* === 6 pairs of from_word calls === *)
      (* The Hsep_exp sep is on a putmany chain. Rename for ecancel_assumption. *)
      set (mem_exp := (map.putmany (map.putmany (map.putmany m00 (map.putmany m01 m02)) (map.putmany m10 (map.putmany m11 m12))) m_rest)) in Hsep_exp.

      (* === Process 12 from_word calls using wp_call_step === *)
      (* Split each Fp2 and process its two from_word calls *)

      (* Use old-style manual from_word pattern (wp_call_step interacts
         poorly with ecancel_fast's override of ecancel_assumption) *)
      Local Ltac do_from_word HFfw Hsep_prev :=
        repeat straightline;
        eapply Semantics.weaken_call;
        [ eapply HFfw; pose proof Hsep_prev as H'; ecancel_assumption
        | cbv beta; intros ? ? ? ?;
          repeat match goal with H : _ /\ _ |- _ => destruct H end;
          try subst;
          cbv [map.putmany_of_list_zip];
          try (eexists; split; [ exact eq_refl | ]);
          repeat straightline ].

      Local Ltac do_from_word_pair HFfw split_lemma :=
        eassert (_ : (FElem_Fp2 _ _ ⋆ _) _) by ecancel_assumption;
        match goal with H : (FElem_Fp2 _ _ ⋆ _) _ |- _ =>
          apply split_lemma in H;
          do_from_word HFfw H;
          match goal with Hs : (_ ⋆ _) _ |- _ =>
            do_from_word HFfw Hs
          end
        end.

      (* Process all 6 pairs of from_word calls.
         After each do_from_word, the postcondition sep Hpost is the last
         hypothesis introduced. We use Ltac to name it explicitly. *)
      Local Ltac fw_pair HFfw split_lemma :=
        let Hp := fresh "Hp" in
        eassert (Hp : (FElem_Fp2 _ _ ⋆ _) _) by ecancel_assumption;
        apply split_lemma in Hp;
        (* fst half *)
        repeat straightline;
        eapply Semantics.weaken_call;
        [ eapply HFfw; exact Hp
        | cbv beta;
          let Hs := fresh "Hsep_fw" in
          intros ? ? ? Hs;
          repeat match goal with H : _ /\ _ |- _ => destruct H end;
          try subst; cbv [map.putmany_of_list_zip];
          try (eexists; split; [ exact eq_refl | ]); repeat straightline ];
        (* snd half — use named Hsep_fw from fst half postcondition *)
        repeat straightline;
        eapply Semantics.weaken_call;
        [ eapply HFfw;
          (* Find the most recent sep hypothesis and use it for ecancel *)
          multimatch goal with Hs : (_ ⋆ _) _ |- _ =>
            let H' := fresh in pose proof Hs as H'; SeparationLogic.ecancel_assumption end
        | cbv beta;
          intros ? ? ? ?;
          repeat match goal with H : _ /\ _ |- _ => destruct H end;
          try subst; cbv [map.putmany_of_list_zip];
          try (eexists; split; [ exact eq_refl | ]); repeat straightline ].

      (* All 6 pairs *)
      do 6 (fw_pair HFfromword FElem_Fp2_split_in_sep).
    Qed.

    Lemma bn254_miller_loop_optimal_ok :
      forall functions
        (EnvContains : map.get functions "bn254_miller_loop_optimal" =
          Some (snd bn254_miller_loop_optimal))
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
        (HMakeLine : map.get functions "bn254_make_line_corrected" =
          Some (snd bn254_make_line_corrected))
        (HFp2mulfpEnv : map.get functions "bn254_Fp2_mul_fp" =
          Some (snd bn254_Fp2_mul_fp))
        (HMakeLineOk : spec_of_bn254_make_line_corrected functions)
        (* Frobenius correction callee hypotheses *)
        (HLoadG1 : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn254_load_gamma1" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out, Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ R) m'))
        (HLoadQ1Y : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn254_load_q1_y_const" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out, Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ R) m'))
        (HLoadG1P2 : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn254_load_gamma1_p2" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out, Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ R) m'))
        (HFp2conj : forall pout px (old_out : Fp2_felem) (x : Fp2_felem) R tr m,
          Fp2_bounded Fp2_tight x ->
          (FElem_Fp2 pout old_out ⋆ (FElem_Fp2 px x ⋆ R)) m ->
          Semantics.call functions "bn254_Fp2_conjugate" tr m [pout; px]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out, Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ (FElem_Fp2 px x ⋆ R)) m'))
        (HFp2mulfp : forall pout px ps
          (old_out : Fp2_felem) (x : Fp2_felem) (s : Fp_felem) R tr m,
          Fp2_bounded Fp2_tight x ->
          Fp_bounded Fp_loose s ->
          (FElem_Fp2 pout old_out ⋆ (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ R))) m ->
          Semantics.call functions "bn254_Fp2_mul_fp" tr m [pout; px; ps]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out, Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ R))) m')),
      spec_of_bn254_miller_loop_optimal functions.
    Proof.
      intros functions EnvContains HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2opp HFp2copy HFp12mul HFp12sqr HFp12copy HFpmul HFpcopy HFfromword HMakeLine HMulFp HMakeLineOk HLoadG1 HLoadQ1Y HLoadG1P2 HFp2conj HFp2mulfp.
      unfold spec_of_bn254_miller_loop_optimal.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn254_miller_loop_optimal. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      repeat straightline.

      (* === Process 13 stackallocs === *)
      split. { apply Z_mod_mult. }
      intros a_f mStack_f mComb_f HanyF HsplitF.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tx mStack_tx mComb_tx HanyTx HsplitTx.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_ty mStack_ty mComb_ty HanyTy HsplitTy.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_lam mStack_lam mComb_lam HanyLam HsplitLam.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp1 mStack_tmp1 mComb_tmp1 HanyTmp1 HsplitTmp1.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp2 mStack_tmp2 mComb_tmp2 HanyTmp2 HsplitTmp2.
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_line mStack_line mComb_line HanyLine HsplitLine.
      straightline.
      split. { cbv. reflexivity. }
      intros a_u6p2 mStack_u6p2 mComb_u6p2 HanyU6p2 HsplitU6p2.
      straightline.
      split. { apply Z_mod_mult. }
      intros a_q1x mStack_q1x mComb_q1x HanyQ1x HsplitQ1x.
      straightline.
      split. { apply Z_mod_mult. }
      intros a_q1y mStack_q1y mComb_q1y HanyQ1y HsplitQ1y.
      straightline.
      split. { apply Z_mod_mult. }
      intros a_cg1 mStack_cg1 mComb_cg1 HanyCg1 HsplitCg1.
      straightline.
      split. { apply Z_mod_mult. }
      intros a_cgy mStack_cgy mComb_cgy HanyCgy HsplitCgy.
      straightline.
      split. { apply Z_mod_mult. }
      intros a_cg1p2 mStack_cg1p2 mComb_cg1p2 HanyCg1p2 HsplitCg1p2.

      (* === Convert anybytes to FElems === *)
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep' wordok mapok a_f) as Hfb_f.
      unfold AbstractField.Placeholder in Hfb_f.
      pose proof (proj1 (Hfb_f mStack_f) HanyF) as [f_val Hfe_f]. clear Hfb_f.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_tx) as Hfb_tx.
      unfold AbstractField.Placeholder in Hfb_tx.
      pose proof (proj1 (Hfb_tx mStack_tx) HanyTx) as [tx_val Hfe_tx]. clear Hfb_tx.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_ty) as Hfb_ty.
      unfold AbstractField.Placeholder in Hfb_ty.
      pose proof (proj1 (Hfb_ty mStack_ty) HanyTy) as [ty_val Hfe_ty]. clear Hfb_ty.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_lam) as Hfb_lam.
      unfold AbstractField.Placeholder in Hfb_lam.
      pose proof (proj1 (Hfb_lam mStack_lam) HanyLam) as [lam_val Hfe_lam]. clear Hfb_lam.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_tmp1) as Hfb_tmp1.
      unfold AbstractField.Placeholder in Hfb_tmp1.
      pose proof (proj1 (Hfb_tmp1 mStack_tmp1) HanyTmp1) as [tmp1_val Hfe_tmp1]. clear Hfb_tmp1.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_tmp2) as Hfb_tmp2.
      unfold AbstractField.Placeholder in Hfb_tmp2.
      pose proof (proj1 (Hfb_tmp2 mStack_tmp2) HanyTmp2) as [tmp2_val Hfe_tmp2]. clear Hfb_tmp2.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep' wordok mapok a_line) as Hfb_line.
      unfold AbstractField.Placeholder in Hfb_line.
      pose proof (proj1 (Hfb_line mStack_line) HanyLine) as [line_val Hfe_line]. clear Hfb_line.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_q1x) as Hfb_q1x.
      unfold AbstractField.Placeholder in Hfb_q1x.
      pose proof (proj1 (Hfb_q1x mStack_q1x) HanyQ1x) as [q1x_val Hfe_q1x]. clear Hfb_q1x.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_q1y) as Hfb_q1y.
      unfold AbstractField.Placeholder in Hfb_q1y.
      pose proof (proj1 (Hfb_q1y mStack_q1y) HanyQ1y) as [q1y_val Hfe_q1y]. clear Hfb_q1y.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_cg1) as Hfb_cg1.
      unfold AbstractField.Placeholder in Hfb_cg1.
      pose proof (proj1 (Hfb_cg1 mStack_cg1) HanyCg1) as [cg1_val Hfe_cg1]. clear Hfb_cg1.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_cgy) as Hfb_cgy.
      unfold AbstractField.Placeholder in Hfb_cgy.
      pose proof (proj1 (Hfb_cgy mStack_cgy) HanyCgy) as [cgy_val Hfe_cgy]. clear Hfb_cgy.
      pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep' wordok mapok a_cg1p2) as Hfb_cg1p2.
      unfold AbstractField.Placeholder in Hfb_cg1p2.
      pose proof (proj1 (Hfb_cg1p2 mStack_cg1p2) HanyCg1p2) as [cg1p2_val Hfe_cg1p2]. clear Hfb_cg1p2.

      (* === Build master sep on mComb_cg1p2 === *)
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitF Hsep Hfe_f) as Hext_f.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitTx Hext_f Hfe_tx) as Hext_tx.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitTy Hext_tx Hfe_ty) as Hext_ty.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitLam Hext_ty Hfe_lam) as Hext_lam.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitTmp1 Hext_lam Hfe_tmp1) as Hext_tmp1.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitTmp2 Hext_tmp1 Hfe_tmp2) as Hext_tmp2.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitLine Hext_tmp2 Hfe_line) as Hext_line.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitU6p2 Hext_line HanyU6p2) as Hext_u6p2.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitQ1x Hext_u6p2 Hfe_q1x) as Hext_q1x.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitQ1y Hext_q1x Hfe_q1y) as Hext_q1y.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitCg1 Hext_q1y Hfe_cg1) as Hext_cg1.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitCgy Hext_cg1 Hfe_cgy) as Hext_cgy.
      pose proof (sep_from_split_ext _ _ _ _ _ HsplitCg1p2 Hext_cgy Hfe_cg1p2) as Hsep_all.
      clear Hext_f Hext_tx Hext_ty Hext_lam Hext_tmp1 Hext_tmp2 Hext_line Hext_u6p2 Hext_q1x Hext_q1y Hext_cg1 Hext_cgy.

      (* Hsep_all : (FElem_Fp2 a_cg1p2 cg1p2_val ⋆
                     (FElem_Fp2 a_cgy cgy_val ⋆
                      (FElem_Fp2 a_cg1 cg1_val ⋆
                       (FElem_Fp2 a_q1y q1y_val ⋆
                        (FElem_Fp2 a_q1x q1x_val ⋆
                         (anybytes a_u6p2 8 ⋆
                          (FElem_Fp12 a_line line_val ⋆
                           (FElem_Fp2 a_tmp2 tmp2_val ⋆
                            (FElem_Fp2 a_tmp1 tmp1_val ⋆
                             (FElem_Fp2 a_lam lam_val ⋆
                              (FElem_Fp2 a_ty ty_val ⋆
                               (FElem_Fp2 a_tx tx_val ⋆
                                (FElem_Fp12 a_f f_val ⋆
                                 (FElem_Fp12 pout old_out ⋆
                                  (FElem_Fp p_px p_x ⋆
                                   (FElem_Fp p_py p_y ⋆
                                    (FElem_Fp2 p_qx q_x ⋆
                                     (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))))))))
                   mComb_cg1p2 *)

      (* === Unfold the body === *)
      unfold BN254_Pairing.miller_loop_optimal_full_body, BN254_Pairing.cmd_seq_list.

      (* === Phase 1: fp12_set_one via helper lemma === *)
      straightline. (* split cmd.seq to isolate fp12_set_one *)
      eapply WeakestPreconditionProperties.Proper_cmd; cycle 1.
      { eapply fp12_set_one_wp.
        - exact HFfromword.
        - subst l11. repeat (first [apply map.get_put_same | rewrite map.get_put_diff by discriminate]). reflexivity.
        - pose proof Hsep_all as H'. ecancel_assumption. }
      intros t_so m_so l_so [Ht_so [Hl_so [f_one [Hb_fone Hsep_so]]]].
      subst t_so l_so.

      (* === Phase 2: fp2_copy t_x q_x + fp2_copy t_y q_y === *)
      wp_call_step HFp2copy.
      wp_call_step HFp2copy.

      (* === Phase 3: store_6u2_limbs + set i = 64 === *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eapply u6p2_store_wp.
      { repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence].
        exact eq_refl. }
      { ecancel_assumption. }
      intros m_stores Hsep_stores.
      repeat straightline.

      (* === Phase 4: while loop === *)
      eapply Loops.while_localsmap
        with (v0 := 64%nat)
             (lt := Nat.lt)
             (invariant := miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line a_u6p2
                      pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out
                      (* Rr' includes original Rr + 5 extra Fp2 stack FElems *)
                      (FElem_Fp2 a_q1x q1x_val ⋆
                       (FElem_Fp2 a_q1y q1y_val ⋆
                        (FElem_Fp2 a_cg1 cg1_val ⋆
                         (FElem_Fp2 a_cgy cgy_val ⋆
                          (FElem_Fp2 a_cg1p2 cg1p2_val ⋆ Rr))))) tr).

      (* well_founded *)
      { exact lt_wf. }

      (* Initial invariant *)
      { unfold miller_loop_inv.
        split; [reflexivity |].
        do 7 eexists.
        split. { lia. }
        split. { exact Hb_fone. }
        split. { exact Hbqx. }
        split. { exact Hbqy. }
        split. { ecancel_assumption. }
        repeat split; repeat straightline. }

      (* Loop body *)
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

          unfold BN254_Pairing.miller_loop_iteration_corrected.
          unfold BN254_Pairing.cmd_seq_list.

          (* Process set i = i - 1 *)
          miller_straightline. (* cmd.seq *)
          miller_straightline. (* cmd.set "i" -- updates locals *)
          unfold dlet.dlet; cbv beta.

          (* Process set "word" = load(u6p2)
             This involves a memory load from the single-word u6p2 on stack.
             We need to:
             1. Extract the u6p2 scalar from the sep
             2. Prove the load succeeds via load_word_of_sep
             3. Introduce the loaded value *)
          miller_straightline. (* cmd.seq *)

          (* cmd.set "word" (expr.load access_size.word (expr.var "u6p2")) *)
          unfold1_cmd_goal; cbv beta match delta [cmd_body].
          letexists. split.
          { (* Evaluate load expression *)
            eassert (Hsc_sep : (scalar a_u6p2 u6p2_word ⋆ _) mi).
            { pose proof Hsep_vi as H'. ecancel_assumption. }
            pose proof (u6p2_scalar_load a_u6p2 mi _ Hsc_sep) as Hload.
            unfold DEXPR, WeakestPrecondition.dexpr.
            cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
            eexists. split. { resolve_map_get. }
            eexists. split. { exact Hload. }
            exact eq_refl. }
          unfold dlet.dlet; cbv beta.

          (* Process set "bit" = (word >> i) & 1 *)
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
            unfold BN254_Pairing.cmd_seq_list.

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
             No conjugation for BN254. *)

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


      (* === Phase 5: Frobenius corrections === *)
      unfold BN254_Pairing.frob_corrections_body, BN254_Pairing.cmd_seq_list.
      unfold BN254_Pairing.expr_fp12_c0, BN254_Pairing.expr_fp12_c1,
             BN254_Pairing.expr_fp6_c0, BN254_Pairing.expr_fp6_c1,
             BN254_Pairing.expr_fp6_c2, BN254_Pairing.expr_fp_snd.

      (* 3 loaders + 2 conjugates + 2 muls + 4 slope calls + 1 make_line + 1 fp12_mul
         + 7 point arithmetic + 1 fp2_mul_fp + 4 slope + 1 make_line + 1 fp12_mul = 27 calls *)
      wp_call_step HLoadG1.          (* load gamma1 → const_g1 *)
      wp_call_step HLoadQ1Y.         (* load q1_y_const → const_g_y *)
      wp_call_step HLoadG1P2.        (* load gamma1_p2 → const_g1p2 *)
      wp_call_step HFp2conj.         (* conjugate q_x → tmp1 *)
      wp_call_step HFp2mul.          (* mul tmp1 const_g1 → q1_x *)
      wp_call_step HFp2conj.         (* conjugate q_y → tmp1 *)
      wp_call_step HFp2mul.          (* mul tmp1 const_g_y → q1_y *)
      wp_call_step HFp2sub.          (* sub q1_y t_y → tmp1 *)
      wp_call_step HFp2sub.          (* sub q1_x t_x → tmp2 *)
      wp_call_step HFp2inv.          (* inv tmp2 → tmp2 *)
      wp_call_step HFp2mul.          (* mul tmp1 tmp2 → lambda *)
      wp_call_step HMakeLineOk.      (* make_line_corrected → line *)
      wp_call_step HFp12mul.         (* mul f line → f *)
      wp_call_step HFp2sqr.          (* sqr lambda → tmp1 *)
      wp_call_step HFp2sub.          (* sub tmp1 t_x → tmp1 *)
      wp_call_step HFp2sub.          (* sub tmp1 q1_x → tmp2 *)
      wp_call_step HFp2sub.          (* sub t_x tmp2 → tmp1 *)
      wp_call_step HFp2mul.          (* mul lambda tmp1 → tmp1 *)
      wp_call_step HFp2sub.          (* sub tmp1 t_y → t_y *)
      wp_call_step HFp2copy.         (* copy t_x tmp2 *)
      wp_call_step HFp2mulfp.        (* mul_fp q_x const_g1p2 → q1_x *)
      wp_call_step HFp2sub.          (* sub q_y t_y → tmp1 *)
      wp_call_step HFp2sub.          (* sub q1_x t_x → tmp2 *)
      wp_call_step HFp2inv.          (* inv tmp2 → tmp2 *)
      wp_call_step HFp2mul.          (* mul tmp1 tmp2 → lambda *)
      wp_call_step HMakeLineOk.      (* make_line_corrected → line *)
      wp_call_step HFp12mul.         (* mul f line → f *)

      (* === Phase 6: fp12_copy out f === *)
      wp_call_step HFp12copy.

      (* === Phase 7: 13-level stack deallocation === *)
      (* Each level: extract FElem from sep, convert to anybytes, provide map.split *)
      Local Ltac dealloc_fp2 :=
        match goal with
        | |- exists _ _, Memory.anybytes ?a _ _ /\ _ =>
          eassert (_ : (_ ⋆ FElem_Fp2 a _) _) by ecancel_assumption;
          match goal with H : (_ ⋆ FElem_Fp2 a _) _ |- _ =>
            destruct H as [? [? [[? ?] [? ?]]]];
            eexists _, _;
            split; [eapply AbstractField.FElem_to_bytes; eassumption|];
            split; [split; [eassumption | eassumption]|]
          end
        end.
      Local Ltac dealloc_fp12 :=
        match goal with
        | |- exists _ _, Memory.anybytes ?a _ _ /\ _ =>
          eassert (_ : (_ ⋆ FElem_Fp12 a _) _) by ecancel_assumption;
          match goal with H : (_ ⋆ FElem_Fp12 a _) _ |- _ =>
            destruct H as [? [? [[? ?] [? ?]]]];
            eexists _, _;
            split; [eapply AbstractField.FElem_to_bytes; eassumption|];
            split; [split; [eassumption | eassumption]|]
          end
        end.
      Local Ltac dealloc_u6p2 :=
        match goal with
        | |- exists _ _, Memory.anybytes ?a 8 _ /\ _ =>
          eassert (_ : (_ ⋆ scalar a _) _) by ecancel_assumption;
          match goal with H : (_ ⋆ scalar a _) _ |- _ =>
            destruct H as [? [? [[? ?] [? ?]]]];
            eexists _, _;
            split; [eapply scalar_to_anybytes8; eassumption|];
            split; [split; [eassumption | eassumption]|]
          end
        end.

      (* 13 dealloc levels in reverse allocation order:
         const_g1p2, const_g_y, const_g1, q1_y, q1_x (5 new Fp2)
         u6p2 (8 bytes), line (Fp12), tmp2, tmp1, lambda, t_y, t_x (Fp2)
         f (Fp12) *)
      do 5 dealloc_fp2.     (* const_g1p2, const_g_y, const_g1, q1_y, q1_x *)
      dealloc_u6p2.          (* u6p2 *)
      dealloc_fp12.          (* line *)
      do 5 dealloc_fp2.     (* tmp2, tmp1, lambda, t_y, t_x *)
      dealloc_fp12.          (* f *)

      (* Final postcondition *)
      cbv [list_map list_map_body get].
      split. { exact eq_refl. }
      split. { exact eq_refl. }
      eexists. split.
      { (* Fp12_bounded Fp12_loose *)
        pose proof (@DodecicFieldExtensionsSpecs.Fp12_field_representation_ok
          _ _ _ _ bn254_pf_params bn254_Fp_rep bn254_Fp_rep_ok bn254_beta
          bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix) as Hfp12_ok.
        eapply (@AbstractField.relax_bounds _ _ _ _ _ _ _ Hfp12_ok).
        eassumption. }
      ecancel_assumption.
    Qed.

End BN254_MillerLoopOptimal.
