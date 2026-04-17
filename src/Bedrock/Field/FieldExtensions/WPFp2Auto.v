(** * High-level WP tactics for Fp2 field extension proofs.

    Automates the common patterns in Fp2 WP proofs:
    - Fp2 FElem splitting into Fp halves
    - Fp-level function calls with automatic sep frame construction
    - Fp2 FElem joining for stack deallocation
    - Final postcondition assembly

    Reduces ~280-line proofs to ~30 lines. *)

From Stdlib Require Import ZArith.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

Import Separation SeparationLogic.

(** *** Tactic 1: wp_fp2_split

    Given H : FElem ptr felem mem (at Fp2 level),
    splits into two Fp-level FElem hypotheses + disjointness.

    Produces: m_fst, m_snd, Hfst : FElem ptr fst_felem m_fst,
              Hsnd : FElem (ptr+off) snd_felem m_snd,
              disjointness facts. Substs the mem equation. *)

Ltac wp_fp2_split beta fp2_prefix H :=
  let m1 := fresh "m" in let m2 := fresh "m" in
  let Hsep := fresh "Hsep" in
  let H1 := fresh "Hfe" in let H2 := fresh "Hfe" in
  let Heq := fresh "Heq" in let Hd := fresh "Hd" in
  pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _ ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix _ _ _ H)
    as [m1 [m2 [Hsep [H1 H2]]]];
  destruct Hsep as [Heq Hd]; subst;
  split_all_disjointness.

(** *** Tactic 2: wp_fp2_copy

    Handles one Fp-level felem_copy call.
    After repeat straightline leaves us at Semantics.call,
    applies weaken_call + the copy spec + build_sep_reorder. *)

Ltac wp_fp2_copy HFcopy :=
  eapply Semantics.weaken_call;
  [ let H := fresh "Hcallee" in
    pose proof HFcopy as H;
    eapply H;
    split; [build_sep_reorder | build_sep_reorder]
  | wp_postcall_auto ];
  try split_all_disjointness.

(** *** Tactic 3: wp_fp2_binop

    Handles one Fp-level binop (sub/add) call.
    Requires an existing sep hypothesis Hsep covering
    the needed FElem regions. *)

Ltac wp_fp2_binop HFop :=
  eapply Semantics.weaken_call;
  [ let H := fresh "Hcallee" in
    pose proof HFop as H;
    eapply H;
    wp_binop_precond ltac:(first [eassumption | assumption])
  | wp_postcall_auto ].

(** *** Tactic 4: wp_fp2_build_sep

    After two copy calls, builds the master sep hypothesis
    from the current putmany chain.
    Takes Heq_m0_out which relates the pre-copy memory to the output memory. *)

Ltac wp_fp2_build_master_sep Heq_m0_out :=
  (* Derive cross-disjointness via the memory equation *)
  let H1 := fresh "Hd_cross" in
  assert (H1 : map.disjoint _ _) by map_disjoint_auto;
  rewrite Heq_m0_out in H1; split_all_disjointness;
  (* May need a second cross-disjointness *)
  try (let H2 := fresh "Hd_cross" in
       assert (H2 : map.disjoint _ _) by map_disjoint_auto;
       rewrite Heq_m0_out in H2; split_all_disjointness);
  (* Build the mem equation and sep *)
  let Hmem := fresh "Hmem_eq" in
  assert (Hmem : _ = _) by
    (subst; rewrite ?map.putmany_assoc; try rewrite Heq_m0_out;
     rewrite <- ?map.putmany_assoc; reflexivity);
  let Hsep := fresh "Hsep" in
  assert Hsep by (rewrite Hmem; build_sep_reorder).

(** *** Tactic 5: wp_fp2_destruct_postcall

    Destructs a nested sep postcondition into named maps. *)

Ltac wp_fp2_destruct_postcall H :=
  let rec go H :=
    lazymatch type of H with
    | (_ * _)%sep _ =>
      let m1 := fresh "m" in let m2 := fresh "m" in
      let Heq := fresh "Heq" in let Hd := fresh "Hd" in
      let H1 := fresh "Hf" in let H2 := fresh "Hrest" in
      destruct H as [m1 [m2 [[Heq Hd] [H1 H2]]]];
      try subst; go H2
    | _ => idtac
    end
  in go H; split_all_disjointness.

(** *** Tactic 6: wp_fp2_join

    Joins two Fp FElem halves back into an Fp2 FElem.
    Takes the two FElem hypotheses and produces an Fp2-level FElem. *)

Ltac wp_fp2_join prime_params F_repr beta fp2_prefix ptr Hfst Hsnd m_fst m_snd :=
  let Hlen_fst := fresh "Hlen" in let Hlen_snd := fresh "Hlen" in
  pose proof (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _ prime_params F_repr _ _ _ Hfst) as Hlen_fst;
  pose proof (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _ prime_params F_repr _ _ _ Hsnd) as Hlen_snd;
  let Hjoin := fresh "Hjoin" in
  assert (Hjoin : (@AbstractField.FElem _ _ _ _ _ _ F_repr ptr _ ⋆
    @AbstractField.FElem _ _ _ _ _ _ F_repr _ _) (map.putmany m_fst m_snd))
    by (exists m_fst, m_snd; split; [split; [reflexivity | map_disjoint_auto] |];
        split; [exact Hfst | exact Hsnd]);
  let Hfp2 := fresh "Hfp2" in
  pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _ ltac:(exact _) ltac:(exact _) prime_params F_repr beta fp2_prefix
    ptr _ _ (map.putmany m_fst m_snd) Hlen_fst Hlen_snd Hjoin) as Hfp2.
