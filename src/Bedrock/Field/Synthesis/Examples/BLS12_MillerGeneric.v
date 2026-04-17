(** * Generic Miller Loop WP Proof Infrastructure
    Shared definitions, lemmas, and Ltac tactics for BLS12-family
    Miller loop proofs. Instantiated by BLS12_MillerLoop.v (381)
    and BLS12_377_MillerLoop.v (377).

    Provides:
    - Extension field instances and operation specs (parameterized Section)
    - Generic loop invariant definition (with extra_sep for u6p2 array)
    - Helper lemmas (sep_from_split, FElem_Fp2_split_in_sep, etc.)
    - Shared Ltac tactics (resolve_map_get, eval_expr_abstract, mcall, etc.)
    - Make_line and miller_loop spec definitions
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
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* Section: parameterized definitions and lemmas                     *)
(* ================================================================ *)

Section MillerGeneric.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Context {pf_params : PrimeFieldParameters}.
    Existing Instance pf_params.
    Context {pf_params_ok : PrimeFieldParameters_ok}.
    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Context {Fp_rep : AbstractField.FieldRepresentation (F:=Fp)}.
    Context {Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

    Variable beta : F PrimeField.M_pos.
    Variable xi_re xi_im : F PrimeField.M_pos.
    Variable func_prefix : string.

    Let fp2_prefix := (func_prefix ++ "Fp2_")%string.
    Let fp6_prefix := (func_prefix ++ "Fp6_")%string.
    Let fp12_prefix := (func_prefix ++ "Fp12_")%string.

    Instance gen_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params beta func_prefix.
    Instance gen_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep beta func_prefix.
    Instance gen_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params beta xi_re xi_im func_prefix.
    Instance gen_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep beta xi_re xi_im func_prefix.
    Instance gen_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params beta xi_re xi_im func_prefix.
    Instance gen_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep beta xi_re xi_im func_prefix.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ gen_Fp2_params _ _ _ _ gen_Fp2_rep).
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ gen_Fp2_params _ _ _ _ gen_Fp2_rep).
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ gen_Fp2_params _ _ _ _ gen_Fp2_rep).
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).
    Local Notation Fp2_felem := (@AbstractField.felem _ gen_Fp2_params _ _ _ _ gen_Fp2_rep).
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ gen_Fp12_params _ _ _ _ gen_Fp12_rep).

    Local Typeclasses Opaque gen_Fp12_params.
    Local Typeclasses Opaque gen_Fp6_params.
    Local Typeclasses Opaque gen_Fp2_params.

    (* Rep-ok instances *)
    Instance gen_Fp12_rep_ok :
      @AbstractField.FieldRepresentation_ok _ gen_Fp12_params _ _ _ _ gen_Fp12_rep :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok beta xi_re xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    Instance gen_Fp2_rep_ok :
      @AbstractField.FieldRepresentation_ok _ gen_Fp2_params _ _ _ _ gen_Fp2_rep :=
      QuadraticFieldExtensionsSpecs.Fp2_field_representation_ok beta fp2_prefix.

    (* Spec definitions *)
    Variable miller_func_name : string.
    Variable make_line_func_name : string.

    Definition spec_of_make_line : spec_of make_line_func_name :=
      fnspec! make_line_func_name (pout plam pxt pyt pxp pyp : word)
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

    Definition spec_of_miller_loop : spec_of miller_func_name :=
      fnspec! miller_func_name (pout p_px p_py p_qx p_qy : word)
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

    (* Generic loop invariant, parameterized by extra_sep and extra_local_gets *)
    Variable extra_sep : word -> mem -> Prop.
    Variable extra_local_gets : word -> locals -> Prop.

    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line a_extra : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) (old_out : Fp12_felem)
      (bit_count : nat)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp12_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp2_felem)
             (line_val : Fp12_felem),
        (v <= bit_count)%nat /\
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
               (extra_sep a_extra ⋆
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
        extra_local_gets a_extra l /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* === Helper lemmas === *)

    Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew ->
      A mOld ->
      B mNew ->
      (A ⋆ B) m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    Local Notation fp_felem_offset_val :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ Fp_rep)).

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split beta
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
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ Fp_rep ->
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
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

End MillerGeneric.

(* ================================================================ *)
(* Top-level Ltac tactics (shared between 381 and 377)               *)
(* ================================================================ *)

(* Resolve map.get on abstract locals using hypotheses *)
Ltac miller_resolve_map_get :=
  match goal with
  | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
    first
    [ unify k k';
      rewrite map.get_put_same; exact eq_refl
    | rewrite map.get_put_diff by congruence;
      miller_resolve_map_get ]
  | |- map.get ?m ?k = Some ?e =>
    first
    [ assumption
    | match goal with
      | H : map.get m k = Some _ |- _ => exact H
      end ]
  end.

(* Evaluate a single expression with abstract locals *)
Ltac miller_eval_expr_abstract :=
  cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
       WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
  repeat (first
    [ exact eq_refl
    | eexists; split; [miller_resolve_map_get |]
    | eexists; split; [exact eq_refl |]
    ]).

(* Process cmd.seq/set/skip/cond with abstract locals *)
Ltac miller_straightline :=
  match goal with
  | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    letexists; split; [solve [miller_eval_expr_abstract] |]
  | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | |- WeakestPrecondition.cmd _ (cmd.cond _ _ _) _ _ _ _ =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    letexists; split; [solve [miller_eval_expr_abstract] |]
  end.

(* Evaluate dexprs with abstract locals *)
Ltac miller_eval_dexprs_abstract :=
  cbv [dexprs list_map list_map_body
       WeakestPrecondition.expr WeakestPrecondition.expr_body
       WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
  repeat (first
    [ exact eq_refl
    | eexists; split; [miller_resolve_map_get |]
    | eexists; split; [exact eq_refl |]
    ]).

(* Solve bounds: generic version using eapply + typeclasses eauto *)
Ltac miller_solve_bounds :=
  first
  [ eassumption
  | match goal with
    | H : ?P ?b1 ?x |- ?P ?b2 ?x => exact H
    end
  | match goal with
    | H : ?bounded ?tight ?x |- ?bounded ?loose ?x =>
      eapply AbstractField.relax_bounds; [| exact H]; typeclasses eauto
    end
  ].

Ltac miller_normalize_pairing_instances := idtac.

Ltac miller_snd_from_word_ecancel H :=
  let H' := fresh "H" in
  pose proof H as H';
  ecancel_assumption_impl.

Ltac miller_solve_mapget :=
  match goal with
  | |- map.get _ "i" = Some _ =>
    repeat first [rewrite map.get_put_same | rewrite map.get_put_diff by congruence];
    first
    [ exact eq_refl
    | assumption
    | (f_equal; rewrite <- word.ring_morph_sub; f_equal; lia)
    | (f_equal; match goal with
       | |- ?lhs = word.of_Z (Z.of_nat (?n - 1)) =>
         replace lhs with (@word.sub 64 _ (word.of_Z (Z.of_nat n)) (word.of_Z 1))
           by reflexivity;
         rewrite <- word.ring_morph_sub; f_equal; zify; lia
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

Ltac miller_solve_leaf :=
  first
  [ eexists; miller_normalize_pairing_instances; ecancel_assumption_with_copy
  | miller_normalize_pairing_instances; ecancel_assumption_with_copy
  | miller_solve_bounds
  | miller_solve_mapget
  ].

Ltac miller_solve_precond :=
  match goal with
  | |- _ /\ _ => split; [| miller_solve_precond]; miller_solve_leaf
  | _ => miller_solve_leaf
  end.

(* mcall: process one function call in the miller loop body *)
Ltac miller_mcall spec :=
  try miller_straightline;
  unfold1_cmd_goal; cbv beta match delta [cmd_body];
  letexists; split; [solve [miller_eval_dexprs_abstract] |];
  eapply Semantics.weaken_call;
  [ eapply spec; miller_solve_precond
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
