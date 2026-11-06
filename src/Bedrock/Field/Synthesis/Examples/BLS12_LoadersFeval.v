(** * Functional specifications of the BLS12-381 Frobenius constant loaders.

    For each constant loader of [BLS12_Pairing.v] this file proves a WP
    lemma whose postcondition also fixes the field value written:

      Fp2_feval out = K

    where K is the Gallina constant of [BLS12_FrobConstants.v]
    (frob_gamma1_p2 = xi^((p^2-1)/3), frob_gamma2_p2 = xi^(2((p^2-1)/3)),
     frob_coeff_fp12_p2_c1 = xi^((p^2-1)/6), frob_gamma1 = xi^((p-1)/3),
     frob_gamma2 = xi^(2((p-1)/3)), frob_coeff_fp12_c1 = xi^((p-1)/6)).

    The first three extend [bls12_load_gamma1_p2_ok],
    [bls12_load_gamma2_p2_ok], [bls12_load_w_frob_p2_c1_ok] of
    [BLS12_PairingHelpers.v]; the p-loaders (gamma1, gamma2, w_frob_c1),
    which had no WP lemma, get one here.  The section header and the store
    tactic are copied from [BLS12_PairingHelpers.v] (they are Local there).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobDecode.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.


Section BLS12_LoadersFeval.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-381 prime parameters *)
    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bls12_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_Fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bls12_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls12_beta "bls12_") in exact v).
    Instance bls12_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls12_beta "bls12_") in exact v).
    Instance bls12_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).

    (* Fp-level offset within Fp2 *)
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).

    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).

    (* ============================================================ *)
    (* Compatibility: function body identity                         *)
    (* ============================================================ *)

    (* The function body defined here (via bls12_pf_params) must equal
       the imported one from BLS12_Pairing (via bls12_prime_params).
       Both define M_pos = Z.to_pos bls12_prime.m and the same function names,
       so the bodies are convertible. *)

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Lemma Fp2_feval_pair (ws : list word) (a b : Fp) :
      Fp_feval (fst_felem ws) = a -> Fp_feval (snd_felem ws) = b ->
      Fp2_feval ws = (a, b).
    Proof.
      intros Ha Hb.
      change Fp2_feval with (fun ws =>
        (Fp_feval (fst_felem ws), Fp_feval (snd_felem ws))).
      cbv beta. rewrite Ha, Hb. reflexivity.
    Qed.
    Local Definition conj3_rot {A B C : Prop} (c : C) (a : A) (b : B) : A /\ B /\ C :=
      conj a (conj b c).

    Local Ltac normalize_word_addr_in H :=
      repeat (rewrite <- Properties.word.add_assoc in H);
      repeat (rewrite <- word.ring_morph_add in H);
      repeat match type of H with
      | context [word.of_Z (?a + ?b)] =>
        let v := eval cbv in (a + b) in
        change (a + b) with v in H
      end.

    (* Helper: swap conjunction for proving sep before bounded *)
    Local Definition conj_swap {A B : Prop} (b : B) (a : A) : A /\ B := conj a b.

    (* Helper: fold scalars + Rr back into (Bignum * Rr) for postcondition *)
    (* Eliminates emp from Bignum unfolding: proves (Bignum n p vs * R) m
       from (array scalar step p vs * R) m when length vs = n *)
    Local Lemma Bignum_of_array_sep n p (vs : list word) R m :
      length vs = n ->
      (array Scalars.scalar (word.of_Z (Memory.bytes_per_word 64)) p vs ⋆ R) m ->
      (Bignum.Bignum n p vs ⋆ R) m.
    Proof.
      intros Hlen Hsep.
      unfold Bignum.Bignum.
      destruct Hsep as [m1 [m2 [[Heq Hd] [Ha HR]]]].
      exists m1, m2.
      split. { split; [exact Heq | exact Hd]. }
      split; [|exact HR].
      exists map.empty, m1.
      split. { split.
        - symmetry. apply Properties.map.putmany_empty_l.
        - apply Properties.map.disjoint_empty_l. }
      split.
      - cbv [emp]. exact (conj eq_refl Hlen).
      - exact Ha.
    Qed.

    (* Store step for solve_store_fp2_constant: find the scalar at the
       store address by syntax in the flattened hypothesis and move it to
       the front with [seps_nth_to_head].  Through [straightline], the
       rebound [ecancel_assumption] (WPTactics.ecancel_assumption_fast)
       took 10 s or more per store here. *)
    Local Ltac find_scalar_at addr l :=
      lazymatch l with
      | cons (Scalars.scalar ?a _) ?tl =>
          match constr:(Set) with
          | _ => let _ := match constr:(Set) with _ => constr_eq a addr end in constr:(O)
          | _ => let n := find_scalar_at addr tl in constr:(S n)
          end
      | cons _ ?tl => let n := find_scalar_at addr tl in constr:(S n)
      end.

    Local Ltac nth_atom i l :=
      lazymatch i with
      | O => lazymatch l with cons ?h _ => h end
      | S ?j => lazymatch l with cons _ ?tl => nth_atom j tl end
      end.

    Local Ltac remove_atom i l :=
      lazymatch i with
      | O => lazymatch l with cons _ ?tl => tl end
      | S ?j => lazymatch l with
                | cons ?h ?tl => let r := remove_atom j tl in constr:(cons h r)
                end
      end.

    Local Ltac pick_scalar_assumption :=
      lazymatch goal with
      | |- (Scalars.scalar ?addr _ ⋆ _)%sep ?m =>
        match goal with
        | H : (_ ⋆ _)%sep m |- _ =>
          let H' := fresh in pose proof H as H';
          flatten_seps_in H';
          lazymatch type of H' with
          | seps ?L _ =>
            let i := find_scalar_at addr L in
            let t := nth_atom i L in
            let r := remove_atom i L in
            apply (proj2 (seps_nth_to_head i L m)) in H';
            change ((t ⋆ seps r)%sep m) in H';
            cbv [seps] in H';
            exact H'
          end
        end
      end.

    Local Ltac store_fp2_step :=
      lazymatch goal with
      | |- store access_size.word _ ?a _ _ =>
          try (is_var a; subst a);
          eapply Scalars.store_word_of_sep; [solve [pick_scalar_assumption] |]
      | |- _ => straightline
      end.

    (* Shared tactic for C3-C5 store-only constant loaders.
       After the function-specific setup (start_func, unfold, eexists, split),
       this tactic:
       1. Decomposes FElem_Fp2 into 12 scalar predicates
       2. Processes 12 cmd.store via repeat straightline
       3. Reconstructs FElem_Fp2 from the updated scalars *)

    Local Ltac solve_store_fp2_constant_feval loaded_eq loaded_def dec_re dec_im :=
      (* Phase 1: Decompose FElem_Fp2 into 12 scalars *)
      match goal with Hsep : (FElem_Fp2 _ _ ⋆ ?RR) _ |- _ =>
        let m_out := fresh "m_out" in let m_rr := fresh "m_rr" in
        let Hout := fresh "Hout" in let Hrr := fresh "Hrr" in
        let Hd := fresh "Hd" in
        destruct Hsep as [m_out [m_rr [[?Heq Hd] [Hout Hrr]]]]; subst;
        unfold FElem_Fp2, AbstractField.FElem, Bignum.Bignum in Hout;
        let me := fresh in let ma := fresh in let Hms := fresh in
        let Hlen := fresh "Hlen" in let Ha := fresh "Ha" in
        destruct Hout as [me [ma [Hms [[?Hme Hlen] Ha]]]];
        subst me; apply Properties.map.split_empty_l in Hms; subst ma;
        (* Destruct old_out into 12 elements *)
        match type of Hlen with length ?x = _ =>
          let do_dest y := (let w := fresh "w" in
            destruct y as [|w y]; [simpl in Hlen; discriminate | ]) in
          do_dest x; do_dest x; do_dest x; do_dest x; do_dest x; do_dest x;
          do_dest x; do_dest x; do_dest x; do_dest x; do_dest x; do_dest x;
          (destruct x; [| simpl in Hlen; discriminate]); clear Hlen
        end;
        (* Unfold array, normalize addresses *)
        cbn [Array.array Scalars.scalar] in Ha;
        change (Memory.bytes_per_word 64) with 8 in Ha;
        normalize_word_addr_in Ha;
        (* Build combined sep *)
        let P := type of Ha in
        let Pcurried := match P with ?PP m_out => PP end in
        let Hcomb := fresh "Hcomb" in
        assert (Hcomb : (Pcurried ⋆ RR) (map.putmany m_out m_rr)) by
          (exists m_out, m_rr;
           split; [split; [reflexivity | exact Hd] |];
           split; [exact Ha | exact Hrr]);
        clear Ha Hrr Hd
      end;
      (* Phase 2: Process 12 stores *)
      repeat store_fp2_step;
      (* Phase 3: Close postcondition *)
      eexists (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: []);
      apply conj3_rot;
      [ (* Sep: prove via Bignum_of_array_sep to avoid emp issues *)
        unfold AbstractField.FElem;
        apply Bignum_of_array_sep;
        [ cbn [length]; exact eq_refl | ];
        change (@AbstractField.felem_size_in_words
          _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep') with 12%nat;
        change (Memory.bytes_per_word 64) with 8;
        cbn [Array.array Scalars.scalar];
        repeat rewrite <- Properties.word.add_assoc;
        repeat rewrite <- word.ring_morph_add;
        repeat match goal with
        | |- context [word.of_Z (?a + ?b)] =>
          let v := eval cbv in (a + b) in change (a + b) with v
        end;
        repeat match goal with x := _ |- _ => subst x end;
        ecancel_assumption
      | (* feval: decode the stored words, then the xi-power equation *)
        rewrite <- loaded_eq; unfold loaded_def;
        apply Fp2_feval_pair; [exact dec_re | exact dec_im]
      | (* Bounded: concrete values, vm_compute + split *)
        vm_compute; repeat split;
        first [exact eq_refl | discriminate | exact I]
      ].

    Lemma bls12_load_gamma1_p2_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_gamma1_p2" =
          Some (snd bls12_load_gamma1_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma1_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_gamma1_p2 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_gamma1_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.gamma1_p2_loaded_eq BLS12_381_Frob.gamma1_p2_loaded
        BLS12_381_FrobDecode.decode_gamma1_p2 BLS12_381_FrobDecode.decode_zero.
    Qed.

    Lemma bls12_load_gamma2_p2_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_gamma2_p2" =
          Some (snd bls12_load_gamma2_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma2_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_gamma2_p2 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_gamma2_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.gamma2_p2_loaded_eq BLS12_381_Frob.gamma2_p2_loaded
        BLS12_381_FrobDecode.decode_gamma2_p2 BLS12_381_FrobDecode.decode_zero.
    Qed.

    Lemma bls12_load_w_frob_p2_c1_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_w_frob_p2_c1" =
          Some (snd bls12_load_w_frob_p2_c1)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_w_frob_p2_c1" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_coeff_fp12_p2_c1 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_w_frob_p2_c1. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.w_frob_p2_c1_loaded_eq BLS12_381_Frob.w_frob_p2_c1_loaded
        BLS12_381_FrobDecode.decode_w_frob_p2_c1 BLS12_381_FrobDecode.decode_zero.
    Qed.

    Lemma bls12_load_gamma1_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_gamma1" =
          Some (snd bls12_load_gamma1)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma1" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_gamma1 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_gamma1. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.gamma1_loaded_eq BLS12_381_Frob.gamma1_loaded
        BLS12_381_FrobDecode.decode_zero BLS12_381_FrobDecode.decode_gamma1_im.
    Qed.

    Lemma bls12_load_gamma2_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_gamma2" =
          Some (snd bls12_load_gamma2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_gamma2 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_gamma2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.gamma2_loaded_eq BLS12_381_Frob.gamma2_loaded
        BLS12_381_FrobDecode.decode_gamma2 BLS12_381_FrobDecode.decode_zero.
    Qed.

    Lemma bls12_load_w_frob_c1_feval_ok :
      forall functions
        (EnvContains : map.get functions "bls12_load_w_frob_c1" =
          Some (snd bls12_load_w_frob_c1)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_w_frob_c1" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_feval out = BLS12_381_Frob.frob_coeff_fp12_c1 /\
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_load_w_frob_c1. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant_feval BLS12_381_Frob.w_frob_c1_loaded_eq BLS12_381_Frob.w_frob_c1_loaded
        BLS12_381_FrobDecode.decode_w_frob_c1_re BLS12_381_FrobDecode.decode_w_frob_c1_im.
    Qed.

End BLS12_LoadersFeval.
