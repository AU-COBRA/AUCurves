(** * BLS12-377 Pairing Helper WP Proofs
    Standalone WP correctness proofs for pairing helper functions
    defined in BLS12_377_Pairing.v:
    - C1: bls377_Fp2_mul_fp (multiply Fp2 by Fp scalar)
    - C3: bls377_load_gamma1_p2
    - C4: bls377_load_gamma2_p2
    - C5: bls377_load_w_frob_p2_c1
    - C2: bls377_make_line
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
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BLS12-377 Section context — mirrors BLS12_377_Pairing.v              *)
(* ================================================================ *)

Section BLS12_377_PairingHelpers.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-377 prime parameters *)
    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul";
      PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub";
      PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square";
      PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv";
      PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes";
      PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy";
      PrimeField.from_word := "bls377_from_word";
      PrimeField.from_list := "bls377_from_list";
    |}.

    Instance bls377_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bls377_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_Fp_rep] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls377_Fp2_".
    Let fp6_prefix := "bls377_Fp6_".
    Let fp12_prefix := "bls377_Fp12_".

    (* β = -1 for BLS12-377 (p ≡ 3 mod 4) *)
    Let bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).

    (* ξ = 1+u for BLS12-377 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls377_xi_re : F PrimeField.M_pos := @F.zero PrimeField.M_pos.
    Let bls377_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bls377_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls377_beta "bls377_") in exact v).
    Instance bls377_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls377_beta "bls377_") in exact v).
    Instance bls377_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls377_Fp6_params' _ _ _ _ bls377_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls377_Fp_rep).

    (* Fp-level offset within Fp2 *)
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep)).

    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).

    (* ============================================================ *)
    (* Compatibility: function body identity                         *)
    (* ============================================================ *)

    (* The function body defined here (via bls377_pf_params) must equal
       the imported one from BLS12_377_Pairing (via bls377_prime_params).
       Both define M_pos = Z.to_pos bls12_377_prime.m and the same function names,
       so the bodies are convertible. *)

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls377_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bls377_Fp_rep).

    Instance spec_of_Fp_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
      AbstractField.unop_spec (F:=Fp) (field_parameters:=prime_field_parameters)
        (field_representation:=bls377_Fp_rep) AbstractField.un_opp.

    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls377_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls377_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bls377_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bls377_Fp2_rep').

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls377_Fp_rep).

    Local Typeclasses Opaque bls377_Fp12_params'.
    Local Typeclasses Opaque bls377_Fp6_params'.
    Local Typeclasses Opaque bls377_Fp2_params'.

    (* ============================================================ *)
    (* Helper: split FElem_Fp2 in a sep into two FElem_Fp entries   *)
    (* ============================================================ *)

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split bls377_beta
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

    (* Reverse: join two FElem_Fp back into FElem_Fp2 in a sep *)
    Lemma FElem_Fp_join_in_sep p (a b : Fp_felem) R m :
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep ->
      (FElem_Fp p a ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset)) b ⋆ R)) m ->
      (FElem_Fp2 p (a ++ b) ⋆ R) m.
    Proof.
      intros Hla Hlb [ma [mr1 [[Heq1 Hd1] [Ha Hr1]]]].
      destruct Hr1 as [mb [mr2 [[Heq2 Hd2] [Hb HR]]]].
      subst mr1.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ab Hd_ar].
      assert (Hjoin : (FElem_Fp p a ⋆
        FElem_Fp (word.add p (word.of_Z fp_felem_offset)) b) (map.putmany ma mb)).
      { exists ma, mb. split; [split; [reflexivity | exact Hd_ab] |].
        split; [exact Ha | exact Hb]. }
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join bls377_beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    (* ============================================================ *)
    (* C1: bls377_Fp2_mul_fp — multiply Fp2 by Fp scalar             *)
    (* ============================================================ *)

    (* Gallina model: scale each Fp component by s *)
    Local Definition fp2_mul_fp_model (x : Fp2) (s : Fp) : Fp2 :=
      (@F.mul PrimeField.M_pos (fst x) s,
       @F.mul PrimeField.M_pos (snd x) s).

    Instance spec_of_bls377_Fp2_mul_fp : spec_of "bls377_Fp2_mul_fp" :=
      fnspec! "bls377_Fp2_mul_fp" (pout px ps : word)
        / (old_out x : Fp2_felem) (s : Fp_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight x /\
          Fp_bounded Fp_loose s /\
          (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ (FElem_Fp2 pout old_out ⋆ Rr))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp2_feval out = fp2_mul_fp_model (Fp2_feval x) (Fp_feval s) /\
            Fp2_bounded Fp2_tight out /\
            (FElem_Fp2 pout out ⋆ (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ Rr))) mem' }.

    Lemma bls377_Fp2_mul_fp_ok :
      forall functions
        (EnvContains : map.get functions "bls377_Fp2_mul_fp" =
          Some (snd bls377_Fp2_mul_fp))
        (HFmul : spec_of_Fp_mul functions),
      spec_of_bls377_Fp2_mul_fp functions.
    Proof.
      intros.
      unfold spec_of_bls377_Fp2_mul_fp.
      intros pout px ps old_out x s Rr tr mem0 [Hbx [Hbs Hsep]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_Fp2_mul_fp. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      (* Step through: cmd.seq -> cmd.call arg evaluation *)
      straightline. straightline. straightline.
      (* Now at: call functions "bls377_mul" tr mem0 args postcondition *)

      (* === Decompose precondition sep === *)
      destruct Hsep as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]].
      destruct Hr1 as [m_s [m_r2 [[Heq1 Hd1] [Hfs Hr2]]]].
      destruct Hr2 as [m_out [m_rr [[Heq2 Hd2] [Hfe_out Hrr]]]].
      subst m_r1 m_r2 mem0.

      (* Split Fp2 FElems into Fp halves *)
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        wordok mapok bls377_pf_params bls377_Fp_rep bls377_beta fp2_prefix
        px x m_x Hfx)
        as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        wordok mapok bls377_pf_params bls377_Fp_rep bls377_beta fp2_prefix
        pout old_out m_out Hfe_out)
        as [m_o1 [m_o2 [Hsep_o [Ho1 Ho2]]]].

      (* Decompose Fp2 bounded_by into 2 Fp bounded_by *)
      change (@AbstractField.bounded_by _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep')
        with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ bls377_Fp_rep b
          (fst_felem ws)
          /\ @AbstractField.bounded_by _ _ _ _ _ _ bls377_Fp_rep b
          (snd_felem ws)) in Hbx.
      destruct Hbx as [Hbx1 Hbx2].

      (* Derive pairwise disjointness *)
      destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_o as [Heq_o Hd_o12].
      subst m_x m_out.
      split_all_disjointness.

      (* Build master 6-way sep *)
      set (combined_mem :=
        map.putmany (map.putmany m_x1 m_x2)
          (map.putmany m_s (map.putmany (map.putmany m_o1 m_o2) m_rr))).
      assert (Hcm : combined_mem =
        map.putmany m_x1 (map.putmany m_x2
          (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr))))).
      { unfold combined_mem. rewrite !map.putmany_assoc. reflexivity. }
      assert (Hsep6 :
        (FElem_Fp px (fst_felem x) ⋆
         (FElem_Fp (word.add px (word.of_Z fp_felem_offset)) (snd_felem x) ⋆
          (FElem_Fp ps s ⋆
           (FElem_Fp pout (fst_felem old_out) ⋆
            (FElem_Fp (word.add pout (word.of_Z fp_felem_offset)) (snd_felem old_out) ⋆ Rr)))))
        combined_mem).
      { rewrite Hcm.
        exists m_x1, (map.putmany m_x2 (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx1 |].
        exists m_x2, (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx2 |].
        exists m_s, (map.putmany m_o1 (map.putmany m_o2 m_rr)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfs |].
        exists m_o1, (map.putmany m_o2 m_rr).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho1 |].
        exists m_o2, m_rr.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Ho2 | exact Hrr]. }

      (* === Call 1: bls377_mul(out, x, s) — fst halves === *)
      eapply Semantics.weaken_call.
      1: { pose proof HFmul as HFmul1.
           unfold spec_of_Fp_mul, AbstractField.binop_spec in HFmul1.
           eapply (HFmul1 pout px ps
             (fst_felem old_out) (fst_felem x) s _ tr).
           split; [apply (@AbstractField.relax_bounds _ _ _ _ _ _
             bls377_Fp_rep bls377_Fp_rep_ok); exact Hbx1 |].
           split; [exact Hbs |].
           split; [eexists; pose proof Hsep6 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep6 as H'; ecancel_assumption |].
           pose proof Hsep6 as H'. ecancel_assumption. }

      (* Process postcondition of call 1 *)
      intros t1 m1 rets1 [Hrets1 [Htr1 [out1 [Hfeval1 [Hbound1 Hsep1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }
      (* Process cmd.seq continuation to second call *)
      straightline. straightline. straightline.

      (* === Call 2: bls377_mul(out+off, x+off, s) — snd halves === *)
      eapply Semantics.weaken_call.
      1: { pose proof HFmul as HFmul2.
           unfold spec_of_Fp_mul, AbstractField.binop_spec in HFmul2.
           eapply (HFmul2
             (word.add pout (word.of_Z fp_felem_offset))
             (word.add px (word.of_Z fp_felem_offset))
             ps
             (snd_felem old_out) (snd_felem x) s _ tr).
           split; [apply (@AbstractField.relax_bounds _ _ _ _ _ _
             bls377_Fp_rep bls377_Fp_rep_ok); exact Hbx2 |].
           split; [exact Hbs |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           pose proof Hsep1 as H'. ecancel_assumption. }

      (* Process postcondition of call 2 *)
      intros t2 m2 rets2 [Hrets2 [Htr2 [out2 [Hfeval2 [Hbound2 Hsep2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip].
      exists (#{ "out" => pout; "x" => px; "s" => ps }#).
      split. { exact eq_refl. }
      cbv [list_map get]. split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Final postcondition === *)
      (* Get lengths for Fp2_raw_FElem_join *)
      assert (Hlen_out1 : length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep).
      { destruct Hsep1 as [mc [_ [_ [Hfc _]]]].
        exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls377_pf_params bls377_Fp_rep _ _ _ Hfc). }
      assert (Hlen_out2 : length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep).
      { destruct Hsep2 as [mc [_ [_ [Hfc _]]]].
        exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls377_pf_params bls377_Fp_rep _ _ _ Hfc). }
      assert (Hlen_x1 : length (fst_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep).
      { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls377_pf_params bls377_Fp_rep _ _ _ Hx1). }
      assert (Hlen_x2 : length (snd_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep).
      { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls377_pf_params bls377_Fp_rep _ _ _ Hx2). }

      (* Witness: concatenation of two Fp felems *)
      exists (out1 ++ out2).

      (* feval *)
      split.
      { unfold fp2_mul_fp_model.
        change Fp2_feval with (fun ws =>
          (Fp_feval (fst_felem ws), Fp_feval (snd_felem ws))).
        cbv beta.
        unfold fst_felem, snd_felem,
          QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_out1).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out1).
        rewrite Hfeval1, Hfeval2.
        cbv [bin_model AbstractField.bin_mul AbstractField.Fmul].
        reflexivity. }

      (* bounded_by tight *)
      split.
      { change Fp2_bounded with (fun b ws =>
          Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws)).
        unfold fst_felem, snd_felem,
          QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_out1).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out1).
        cbv [bin_outbounds AbstractField.bin_mul] in Hbound1, Hbound2.
        split; assumption. }

      (* sep: FElem_Fp2 pout (out1 ++ out2) * (FElem_Fp2 px x * (FElem_Fp ps s * Rr)) *)
      { (* Decompose Hsep2 to get individual maps *)
        destruct Hsep2 as [m_A [m_rest1 [[Heq_s2 Hd_s2] [HA Hrest1]]]].
        destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_r1] [HB Hrest2]]]].
        destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_r2] [HC Hrest3]]]].
        destruct Hrest3 as [m_D [m_E [[Heq_r3 Hd_DE] [HD HE]]]].
        subst m_rest1 m_rest2 m_rest3 m2.
        split_all_disjointness.
        (* Join output Fp halves into Fp2 *)
        assert (Hjoin_out :
          (FElem_Fp pout out1 ⋆
           FElem_Fp (word.add pout (word.of_Z fp_felem_offset)) out2)
          (map.putmany m_B m_A)).
        { exists m_B, m_A.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HB | exact HA]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          wordok mapok bls377_pf_params bls377_Fp_rep bls377_beta fp2_prefix
          pout out1 out2
          (map.putmany m_B m_A) Hlen_out1 Hlen_out2 Hjoin_out) as Hfp2_out.
        (* Join input Fp halves into Fp2 *)
        assert (Hjoin_x :
          (FElem_Fp px (fst_felem x) ⋆
           FElem_Fp (word.add px (word.of_Z fp_felem_offset)) (snd_felem x))
          (map.putmany m_C m_D)).
        { exists m_C, m_D.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HC | exact HD]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          wordok mapok bls377_pf_params bls377_Fp_rep bls377_beta fp2_prefix
          px (fst_felem x) (snd_felem x)
          (map.putmany m_C m_D) Hlen_x1 Hlen_x2 Hjoin_x) as Hfp2_x.
        rewrite (@QuadraticFieldExtensions.Fp2_list_decomp _ _ _ _
          bls377_pf_params bls377_Fp_rep x) in Hfp2_x.
        (* Build final sep *)
        exists (map.putmany m_B m_A),
               (map.putmany (map.putmany m_C m_D) m_E).
        split; [split |].
        { rewrite !map.putmany_assoc.
          rewrite (map.putmany_comm m_A m_B Hdj15).
          reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hfp2_out |].
        exists (map.putmany m_C m_D), m_E.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hfp2_x | exact HE]. }
    Qed.

    (* ============================================================ *)
    (* C3-C5: Frobenius constant loaders                            *)
    (* ============================================================ *)

    (* These functions store 12 words (6 real limbs + 6 zeros) to
       an Fp2 buffer. The proof strategy:
       1. Unfold FElem_Fp2 -> Bignum -> array scalar, normalize addresses
       2. Build combined sep with 12 individual scalar predicates + Rr
       3. Process 12 cmd.store via repeat straightline
       4. Reconstruct FElem_Fp2 from updated scalars (postcondition)
       Steps 1-3 are automated by solve_store_fp2_constant.
       Step 4 (postcondition + bounded_by) is admitted. *)

    (* Normalize nested word.add in a hypothesis to absolute offsets.
       Rewrites word.add (word.add p (word.of_Z a)) (word.of_Z b)
       into word.add p (word.of_Z (a + b)) via:
       1. Right-associate: (p + a) + b -> p + (a + b) via <- add_assoc
       2. Fold Z addition: word.add (of_Z a) (of_Z b) -> of_Z (a+b)
       3. Evaluate: of_Z (a+b) -> of_Z v where v = a+b *)
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

    (* Shared tactic for C3-C5 store-only constant loaders.
       After the function-specific setup (start_func, unfold, eexists, split),
       this tactic:
       1. Decomposes FElem_Fp2 into 12 scalar predicates
       2. Processes 12 cmd.store via repeat straightline
       3. Reconstructs FElem_Fp2 from the updated scalars *)
    Local Ltac solve_store_fp2_constant :=
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
      repeat straightline;
      (* Phase 3: Close postcondition *)
      eexists (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: []);
      apply conj_swap;
      [ (* Sep: prove via Bignum_of_array_sep to avoid emp issues *)
        unfold AbstractField.FElem;
        apply Bignum_of_array_sep;
        [ cbn [length]; exact eq_refl | ];
        change (@AbstractField.felem_size_in_words
          _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep') with 12%nat;
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
      | (* Bounded: concrete values, vm_compute + split *)
        vm_compute; repeat split;
        first [exact eq_refl | discriminate | exact I]
      ].

    Lemma bls377_load_gamma1_p2_ok :
      forall functions
        (EnvContains : map.get functions "bls377_load_gamma1_p2" =
          Some (snd bls377_load_gamma1_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls377_load_gamma1_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_load_gamma1_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    Lemma bls377_load_gamma2_p2_ok :
      forall functions
        (EnvContains : map.get functions "bls377_load_gamma2_p2" =
          Some (snd bls377_load_gamma2_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls377_load_gamma2_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_load_gamma2_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    Lemma bls377_load_w_frob_p2_c1_ok :
      forall functions
        (EnvContains : map.get functions "bls377_load_w_frob_p2_c1" =
          Some (snd bls377_load_w_frob_p2_c1)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls377_load_w_frob_p2_c1" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_load_w_frob_p2_c1. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    (* ============================================================ *)
    (* C2: bls377_make_line                                          *)
    (* ============================================================ *)

    (* Fp6-level offset notations (from CubicFieldExtensions) *)
    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep')).
    Local Notation Fp6_felem_size := (@AbstractField.felem_size_in_words _ bls377_Fp6_params' _ _ _ _ bls377_Fp6_rep').
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat Fp6_felem_size).

    (* Fp6 sub-component access *)
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    (* Fp12 sub-component access *)
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls377_pf_params bls377_Fp_rep).
    (* Fp6_c1/c2 offsets computed with the correct (Fp-level) representation *)
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls377_pf_params bls377_beta bls377_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls377_pf_params bls377_beta bls377_Fp_rep fp2_prefix).

    Lemma bls377_make_line_ok :
      forall functions
        (EnvContains : map.get functions "bls377_make_line" =
          Some (snd bls377_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfp : spec_of_bls377_Fp2_mul_fp functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      forall pout plam pxt pyt pxp pyp
        (old_out : @AbstractField.felem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep')
        (lam xt yt : Fp2_felem) (xp yp : Fp_felem) Rr tr mem,
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
             (FElem_Fp pyp yp ⋆ Rr)))))) mem ->
        WeakestPrecondition.call functions "bls377_make_line" tr mem
          [pout; plam; pxt; pyt; pxp; pyp]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              @AbstractField.bounded_by _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep'
                (@AbstractField.loose_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep') out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp2 plam lam ⋆
                (FElem_Fp2 pxt xt ⋆
                 (FElem_Fp2 pyt yt ⋆
                  (FElem_Fp pxp xp ⋆
                   (FElem_Fp pyp yp ⋆ Rr)))))) mem').
    Proof.
      intros functions EnvContains HFp2mul HFp2sub HFp2opp HFp2mulfp HFpcopy HFfromword
        pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0
        [Hblam [Hbxt [Hbyt [Hbxp [Hbyp Hsep]]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_make_line. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      repeat straightline.

      (* === Stackalloc tmp (Fp2-sized) === *)
      split. { apply Z_mod_mult. }
      intros a_tmp mStack mCombined HstackTmp Hm_split.

      (* Convert anybytes to FElem_Fp2 *)
      pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep'
        wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp.

      (* Decompose precondition sep *)
      destruct Hsep as [m_out [m_r1 [[Heq0 Hd0] [Hfe_out Hr1]]]].
      destruct Hr1 as [m_lam [m_r2 [[Heq1 Hd1] [Hfe_lam Hr2]]]].
      destruct Hr2 as [m_xt [m_r3 [[Heq2 Hd2] [Hfe_xt Hr3]]]].
      destruct Hr3 as [m_yt [m_r4 [[Heq3 Hd3] [Hfe_yt Hr4]]]].
      destruct Hr4 as [m_xp [m_r5 [[Heq4 Hd4] [Hfe_xp Hr5]]]].
      destruct Hr5 as [m_yp [m_rr [[Heq5 Hd5] [Hfe_yp Hrr]]]].
      subst m_r1 m_r2 m_r3 m_r4 m_r5 mem0.

      (* Split Fp12 output into Fp6 halves *)
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls377_beta bls377_xi_re bls377_xi_im
        fp12_prefix fp6_prefix fp2_prefix pout old_out m_out Hfe_out)
        as [m_fp6_0 [m_fp6_1 [Hsep_fp12 [Hfe_fp6_0 Hfe_fp6_1]]]].
      destruct Hsep_fp12 as [Heq_fp12 Hd_fp12].
      subst m_out.

      (* Split each Fp6 into 3 Fp2 components *)
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls377_beta bls377_xi_re bls377_xi_im
        fp6_prefix fp2_prefix
        pout _ m_fp6_0 Hfe_fp6_0)
        as [m_o00 [m_o01_02 [Hsep_c0 [Ho00 Ho01_02]]]].
      destruct Ho01_02 as [m_o01 [m_o02 [Hsep_o01_02 [Ho01 Ho02]]]].
      destruct Hsep_c0 as [? Hd_c0]. destruct Hsep_o01_02 as [? Hd_o01_02]. subst.

      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls377_beta bls377_xi_re bls377_xi_im
        fp6_prefix fp2_prefix
        (word.add pout (word.of_Z fp6_felem_offset)) _ m_fp6_1 Hfe_fp6_1)
        as [m_o10 [m_o11_12 [Hsep_c1 [Ho10 Ho11_12]]]].
      destruct Ho11_12 as [m_o11 [m_o12 [Hsep_o11_12 [Ho11 Ho12]]]].
      destruct Hsep_c1 as [? Hd_c1]. destruct Hsep_o11_12 as [? Hd_o11_12]. subst.

      (* Derive pairwise disjointness *)
      split_all_disjointness.
      destruct Hm_split as [Heq_comb Hd_comb].
      split_all_disjointness.
      rewrite !map.putmany_assoc in Heq_comb.

      (* The FElem types from Fp6_raw_FElem_split use
         Fp2_field_parameters/Fp2_field_representation applied to fp2_prefix.
         We define a local alias to match what the split hypotheses produce. *)
      set (FE2 := @AbstractField.FElem _
        (Fp2_field_parameters bls377_beta fp2_prefix) _ _ _ _
        (Fp2_field_representation bls377_beta fp2_prefix)).

      (* Build combined sep on mCombined with all sub-FElems *)
      assert (Hsep :
        (FE2 pout (c0_felem (d0_felem old_out)) ⋆
         (FE2 (word.add pout fp6_c1_off) (c1_felem (d0_felem old_out)) ⋆
          (FE2 (word.add pout fp6_c2_off) (c2_felem (d0_felem old_out)) ⋆
           (FE2 (word.add pout (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem old_out)) ⋆
            (FE2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
               (c1_felem (d1_felem old_out)) ⋆
             (FE2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
                (c2_felem (d1_felem old_out)) ⋆
              (FE2 plam lam ⋆
               (FE2 pxt xt ⋆
                (FE2 pyt yt ⋆
                 (FElem_Fp pxp xp ⋆
                  (FElem_Fp pyp yp ⋆
                   (Rr ⋆
                    FE2 a_tmp tmp_val))))))))))))
        mCombined).
      { subst mCombined FE2.
        rewrite <- ?map.putmany_assoc.
        exists m_o00, (map.putmany m_o01 (map.putmany m_o02
          (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
            (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
              (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho00 |].
        exists m_o01, (map.putmany m_o02
          (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
            (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
              (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho01 |].
        exists m_o02, (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho02 |].
        exists m_o10, (map.putmany m_o11 (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho10 |].
        exists m_o11, (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho11 |].
        exists m_o12, (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho12 |].
        exists m_lam, (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_lam |].
        exists m_xt, (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xt |].
        exists m_yt, (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yt |].
        exists m_xp, (map.putmany m_yp (map.putmany m_rr mStack)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xp |].
        exists m_yp, (map.putmany m_rr mStack).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yp |].
        exists m_rr, mStack.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hrr | exact Htmp_felem]. }

      (* FE2 and FElem_Fp2 are definitionally equal.
         Subst FE2 so all subsequent references use FElem_Fp2. *)
      subst FE2.
      (* Fold opaque instance names in Hsep so ecancel_assumption can
         unify Hsep's FElem terms with the specs' FElem_Fp2 terms. *)
      change (Fp2_field_parameters bls377_beta fp2_prefix)
        with bls377_Fp2_params' in Hsep.
      change (Fp2_field_representation bls377_beta fp2_prefix)
        with bls377_Fp2_rep' in Hsep.

      (* Fp2-level relax_bounds helper *)
      pose proof (@Fp2_field_representation_ok _ _ _ _ bls377_pf_params
        bls377_Fp_rep bls377_Fp_rep_ok bls377_beta fp2_prefix) as Fp2_rep_ok.

      (* === 13 call steps: 4 Fp2-level + 9 Fp-level === *)
      (* Unfold cmd_seq_list so straightline can process cmd.seq *)
      unfold BLS12_377_Pairing.cmd_seq_list.
      (* Unfold expression helpers so straightline can evaluate args *)
      unfold BLS12_377_Pairing.expr_fp12_c0, BLS12_377_Pairing.expr_fp12_c1,
             BLS12_377_Pairing.expr_fp6_c0, BLS12_377_Pairing.expr_fp6_c1,
             BLS12_377_Pairing.expr_fp6_c2, BLS12_377_Pairing.expr_fp_snd.

      (* === Call 1: fp2_mul(pout, plam, pxt) === *)
      (* out.c0.c0 = lam * x_t *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2mul as HF1.
           unfold spec_of_Fp2_mul, AbstractField.binop_spec in HF1.
           eapply (HF1 pout plam pxt
             (c0_felem (d0_felem old_out)) lam xt _ tr).
           split; [apply (@AbstractField.relax_bounds _ bls377_Fp2_params' _ _ _ _
             bls377_Fp2_rep' Fp2_rep_ok); exact Hblam |].
           split; [apply (@AbstractField.relax_bounds _ bls377_Fp2_params' _ _ _ _
             bls377_Fp2_rep' Fp2_rep_ok); exact Hbxt |].
           split; [eexists; pose proof Hsep as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep as H'; ecancel_assumption |].
           pose proof Hsep as H'. ecancel_assumption. }
      intros t1 m1 rets1 [Hrets1 [Htr1 [out1 [Hfeval1 [Hbound1 Hsep1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 2: fp2_sub(pout, pout, pyt) === *)
      (* out.c0.c0 -= y_t *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2sub as HF2.
           unfold spec_of_Fp2_sub, AbstractField.binop_spec in HF2.
           eapply (HF2 pout pout pyt
             out1 out1 yt _ tr).
           split; [cbv [bin_xbounds AbstractField.bin_sub]; exact Hbound1 |].
           split; [cbv [bin_ybounds AbstractField.bin_sub]; exact Hbyt |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           pose proof Hsep1 as H'. ecancel_assumption. }
      intros t2 m2 rets2 [Hrets2 [Htr2 [out2 [Hfeval2 [Hbound2 Hsep2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 3: fp2_mul_fp(a_tmp, plam, pxp) === *)
      (* tmp = lam * x_p *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2mulfp as HF3.
           unfold spec_of_bls377_Fp2_mul_fp in HF3.
           eapply (HF3 a_tmp plam pxp
             tmp_val lam xp _ tr).
           split; [exact Hblam |].
           split; [exact Hbxp |].
           pose proof Hsep2 as H'. ecancel_assumption. }
      intros t3 m3 rets3 [Hrets3 [Htr3 [out3 [Hfeval3 [Hbound3 Hsep3]]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 4: fp2_opp(out.c0.c1, tmp) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2opp as HF4.
           unfold spec_of_Fp2_opp, AbstractField.unop_spec in HF4.
           (* The evaluated arg address is word.add pout (word.of_Z (bytes_per_word * Fp2_felem_size))
              which equals word.add pout fp6_c1_off definitionally.
              We use subst args to let Coq's unification handle it. *)
           subst args.
           eapply (HF4
             (word.add pout fp6_c1_off)
             a_tmp
             (c1_felem (d0_felem old_out)) out3 _ tr).
           split; [cbv [un_xbounds AbstractField.un_opp]; exact Hbound3 |].
           split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
           pose proof Hsep3 as H'. ecancel_assumption. }
      intros t4 m4 rets4 [Hrets4 [Htr4 [out4 [Hfeval4 [Hbound4 Hsep4]]]]].
      subst rets4. symmetry in Htr4. subst t4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 5-12: from_word / fp_copy at Fp level === *)
      (* Strategy: for each call, use ecancel to rearrange the running
         sep so the target FElem_Fp2 is first, then apply
         FElem_Fp2_split_in_sep to get FElem_Fp entries. *)

      (* --- Call 5: from_word(out.c0.c2 fst, 0) --- *)
      repeat straightline.
      (* Split out.c0.c2 FElem_Fp2 into two FElem_Fp *)
      eassert (Hsep4_split5 :
        (FElem_Fp2 (word.add pout fp6_c2_off)
           (c2_felem (d0_felem old_out)) ⋆ _) m4).
      { pose proof Hsep4 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep4_split5.
      (* Hsep4_split5 : (FElem_Fp (pout+c2off) fst *
                          (FElem_Fp (pout+c2off+fpoff) snd * R5)) m4 *)
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d0_felem old_out))) _ tr).
           exact Hsep4_split5. }
      intros t5 m5' rets5 [Hrets5 [Htr5 [fw5 [Hfeval5 [Hbound5 Hsep5]]]]].
      subst rets5. symmetry in Htr5. subst t5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 6: from_word(out.c0.c2 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d0_felem old_out))) _ tr).
           (* The goal address comes from straightline and uses expanded
              offsets. We need to match it with the opaque fp6_c2_off in Hsep5.
              Strategy: change the goal address to match the hypothesis form. *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout fp6_c2_off) (word.of_Z fp_felem_offset))
               (snd_felem (c2_felem (d0_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep5 as H'. ecancel_assumption. }
      intros t6 m6' rets6 [Hrets6 [Htr6 [fw6 [Hfeval6 [Hbound6 Hsep6]]]]].
      subst rets6. symmetry in Htr6. subst t6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 7: from_word(out.c1.c0 fst, 0) --- *)
      repeat straightline.
      eassert (Hsep6_split7 :
        (FElem_Fp2 (word.add pout (word.of_Z fp6_felem_offset))
           (c0_felem (d1_felem old_out)) ⋆ _) m6').
      { pose proof Hsep6 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep6_split7.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d1_felem old_out))) _ tr).
           exact Hsep6_split7. }
      intros t7 m7' rets7 [Hrets7 [Htr7 [fw7 [Hfeval7 [Hbound7 Hsep7]]]]].
      subst rets7. symmetry in Htr7. subst t7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 8: from_word(out.c1.c0 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d1_felem old_out))) _ tr).
           (* Address normalization: change goal address to match hypothesis form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout (word.of_Z fp6_felem_offset)) (word.of_Z fp_felem_offset))
               (snd_felem (c0_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep7 as H'. ecancel_assumption. }
      intros t8 m8' rets8 [Hrets8 [Htr8 [fw8 [Hfeval8 [Hbound8 Hsep8]]]]].
      subst rets8. symmetry in Htr8. subst t8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 9: fp_copy(out.c1.c1 fst, y_p) --- *)
      repeat straightline.
      eassert (Hsep8_split9 :
        (FElem_Fp2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
           (c1_felem (d1_felem old_out)) ⋆ _) m8').
      { pose proof Hsep8 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep8_split9.
      (* fp_copy spec: (FElem px x * FElem pout out * R) mem /\ (FElem pout out * Rout) mem
         Here: px = pyp, x = yp, pout = d1.c1.fst addr,
               out = fst_felem (c1_felem (d1_felem old_out)) *)
      eapply Semantics.weaken_call.
      1: { eapply (HFpcopy _ _
             (fst_felem (c1_felem (d1_felem old_out))) yp _ _ tr).
           (* change goal pout address to match the Fp2-split address *)
           match goal with
           | |- (_ /\ _) =>
             split; [|
               match goal with
               | |- (?P ⋆ ?Q) ?m =>
                 change ((FElem_Fp
                   (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                   (fst_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
               end;
               pose proof Hsep8_split9 as H'; ecancel_assumption]
           end.
           match goal with
           | |- (_ ⋆ _ ⋆ ?Q) ?m =>
             change ((FElem_Fp pyp yp ⋆
                      FElem_Fp (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                        (fst_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep8_split9 as H'. ecancel_assumption. }
      intros t9 m9' rets9 [Hrets9 [Htr9 Hsep9]].
      subst rets9. symmetry in Htr9. subst t9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 10: from_word(out.c1.c1 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d1_felem old_out))) _ tr).
           (* Address normalization: straightline computed addr vs opaque fp6_c1_off form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                  (word.of_Z fp_felem_offset))
               (snd_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep9 as H'. ecancel_assumption. }
      intros t10 m10' rets10 [Hrets10 [Htr10 [fw10 [Hfeval10 [Hbound10 Hsep10]]]]].
      subst rets10. symmetry in Htr10. subst t10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 11: from_word(out.c1.c2 fst, 0) --- *)
      repeat straightline.
      eassert (Hsep10_split11 :
        (FElem_Fp2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
           (c2_felem (d1_felem old_out)) ⋆ _) m10').
      { pose proof Hsep10 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep10_split11.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d1_felem old_out))) _ tr).
           (* change fst-half address to match Fp2-split form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
               (fst_felem (c2_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           exact Hsep10_split11. }
      intros t11 m11' rets11 [Hrets11 [Htr11 [fw11 [Hfeval11 [Hbound11 Hsep11]]]]].
      subst rets11. symmetry in Htr11. subst t11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 12: from_word(out.c1.c2 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d1_felem old_out))) _ tr).
           (* Address normalization for snd half of d1.c2 *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
                  (word.of_Z fp_felem_offset))
               (snd_felem (c2_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep11 as H'. ecancel_assumption. }
      intros t12 m12' rets12 [Hrets12 [Htr12 [fw12 [Hfeval12 [Hbound12 Hsep12]]]]].
      subst rets12. symmetry in Htr12. subst t12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Stack deallocation + final postcondition === *)
      (* The goal here is the stackalloc deallocation:
         we must provide anybytes for a_tmp and map.split,
         then prove the postcondition on the remaining memory.

         Step 1: Extract tmp FElem from sep and convert to anybytes.
         Step 2: Prove map.split.
         Step 3: Join Fp halves into Fp2, then Fp6, then Fp12.
         Step 4: Prove bounded_by loose.
      *)

      (* Handle remaining cmd.skip from cmd_seq_list *)
      repeat straightline.

      (* The stackalloc WP continuation needs:
         exists mSmall mStack',
           anybytes a_tmp <size> mStack' /\
           map.split m12' mSmall mStack' /\
           postcondition tr mSmall *)
      (* === Stack deallocation + final postcondition ===

         The goal here is the stackalloc deallocation continuation:
           exists mSmall mStack',
             anybytes a_tmp <size> mStack' /\
             map.split mFinal mSmall mStack' /\
             (rets = [] /\ tr = tr' /\
              exists out, Fp12_bounded loose out /\ (FElem_Fp12 pout out * ...) mSmall)

         To close this, one would need to:

         Step 1: Extract the FElem_Fp2 at a_tmp from the sep hypothesis.
           Use ecancel to isolate (FElem_Fp2 a_tmp tmp_val * rest) on the
           final memory. Then apply FElem_to_bytes to convert tmp's FElem
           to anybytes (Placeholder), giving anybytes a_tmp size mStack'.

         Step 2: Provide the map.split witness.
           After extracting mStack' for a_tmp, the remaining memory mSmall
           contains the 12 output Fp-level FElems + input FElems + Rr.
           Prove map.split mFinal mSmall mStack' from the sep structure.

         Step 3: Join 12 Fp output FElems into Fp12.
           - Pair Fp halves into 6 Fp2 via FElem_Fp_join_in_sep
           - Group 3 pairs of Fp2 into 2 Fp6 via Fp6_raw_FElem_join
           - Group 2 Fp6 into Fp12 via Fp12_raw_FElem_join

         Step 4: Prove bounded_by loose.
           The Fp2 sub-call specs guarantee tight or loose bounds on
           each component. Use relax_bounds where needed to obtain
           loose bounds at the Fp12 level.

         Step 5: Build the final sep.
           After joining, have FElem_Fp12 pout out. Combine with the
           surviving input FElems and Rr via ecancel.

         This is approximately 100 lines of proof script. *)
      (* --- Stack dealloc: a_tmp (Fp2-sized) --- *)
      eassert (Htmp_sep : (FElem_Fp2 a_tmp out3 ⋆ _) m12').
      { pose proof Hsep12 as H'. ecancel_assumption. }
      destruct Htmp_sep as [m_stk [m_rest [[Heq_stk Hd_stk] [Hftmp Hrest]]]].
      exists m_rest, m_stk.
      split. { exact (AbstractField.FElem_to_bytes a_tmp out3 m_stk Hftmp). }
      split. { split. { rewrite map.putmany_comm; [exact Heq_stk | exact (proj1 (map.disjoint_comm _ _) Hd_stk)]. } { exact (proj1 (map.disjoint_comm _ _) Hd_stk). } }

      (* Handle return value list *)
      cbv [list_map list_map_body].
      split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Step 3: Join 12 Fp-level entries into Fp12 ===

         Hrest has on m_rest:
           8 FElem_Fp (fw5..fw12, yp copy)
           + 2 FElem_Fp2 (out2 @ pout, out4 @ pout+fp6_c1_off)
           + surviving inputs (lam, xt, yt, xp, yp)
           + Rr

         Join strategy:
         a) Pair Fp halves into 4 Fp2: d0.c2, d1.c0, d1.c1, d1.c2
         b) Join 3 Fp2 into Fp6: d0 (out2, out4, d0.c2), d1 (d1.c0, d1.c1, d1.c2)
         c) Join 2 Fp6 into Fp12
      *)

      (* --- Extract Fp-level lengths from FElem predicates --- *)
      Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_Fp_rep).
      pose proof fun p v m (H : FElem_Fp p v m) =>
        @QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls377_pf_params bls377_Fp_rep p v m H
        as FpLen.
      (* Extract each length by pulling the FElem from the current sep *)
      assert (Hlen_fw5 : length fw5 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw5 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw6 : length fw6 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw6 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw7 : length fw7 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw7 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw8 : length fw8 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw8 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_yp_copy : length yp = Fp_fsw).
      { assert (Htmp : (FElem_Fp pyp yp ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw10 : length fw10 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw10 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw11 : length fw11 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw11 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw12 : length fw12 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw12 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      clear FpLen.

      (* --- Chain-join: combine Fp pairs into Fp2, chaining through the sep --- *)
      (* Join d0.c2: fw5 (fst) + fw6 (snd) — start from Hrest *)
      eassert (Hsep_a : (FElem_Fp _ fw5 ⋆ (FElem_Fp _ fw6 ⋆ _)) m_rest).
      { pose proof Hrest as H'. ecancel_assumption. }
      change (word.add pout (word.of_Z (2 * (Memory.bytes_per_word 64 * Z.of_nat Fp_fsw))))
        with (word.add pout fp6_c2_off) in Hsep_a.
      change (word.add (word.add pout fp6_c2_off) (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat Fp_fsw)))
        with (word.add (word.add pout fp6_c2_off) (word.of_Z fp_felem_offset)) in Hsep_a.
      apply FElem_Fp_join_in_sep in Hsep_a; [| exact Hlen_fw5 | exact Hlen_fw6].

      (* Join d1.c0: fw7 + fw8 — chain from Hsep_a *)
      eassert (Hsep_b : (FElem_Fp _ fw7 ⋆ (FElem_Fp _ fw8 ⋆ _)) m_rest).
      { pose proof Hsep_a as H'. ecancel_assumption. }
      eassert (Hsep_b' : (FElem_Fp _ fw7 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw8 ⋆ _)) m_rest).
      { exact Hsep_b. }
      apply FElem_Fp_join_in_sep in Hsep_b'; [| exact Hlen_fw7 | exact Hlen_fw8].

      (* Join d1.c1: yp + fw10 — chain from Hsep_b' *)
      eassert (Hsep_c : (FElem_Fp _ yp ⋆ (FElem_Fp _ fw10 ⋆ _)) m_rest).
      { pose proof Hsep_b' as H'. ecancel_assumption. }
      eassert (Hsep_c' : (FElem_Fp _ yp ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw10 ⋆ _)) m_rest).
      { exact Hsep_c. }
      apply FElem_Fp_join_in_sep in Hsep_c'; [| exact Hlen_yp_copy | exact Hlen_fw10].

      (* Join d1.c2: fw11 + fw12 — chain from Hsep_c' *)
      eassert (Hsep_d : (FElem_Fp _ fw11 ⋆ (FElem_Fp _ fw12 ⋆ _)) m_rest).
      { pose proof Hsep_c' as H'. ecancel_assumption. }
      eassert (Hsep_d' : (FElem_Fp _ fw11 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw12 ⋆ _)) m_rest).
      { exact Hsep_d. }
      apply FElem_Fp_join_in_sep in Hsep_d'; [| exact Hlen_fw11 | exact Hlen_fw12].
      (* Hsep_d' now has all 6 Fp2 values (no loose Fp entries) on m_rest *)

      (* === Step 3b: Rearrange into d0, d1, inputs order === *)
      eassert (Hsep_rearr :
        (FElem_Fp2 _ out2 ⋆
         (FElem_Fp2 _ out4 ⋆
          (FElem_Fp2 _ (fw5 ++ fw6) ⋆
           (FElem_Fp2 _ (fw7 ++ fw8) ⋆
            (FElem_Fp2 _ (yp ++ fw10) ⋆
             (FElem_Fp2 _ (fw11 ++ fw12) ⋆
              (FElem_Fp2 _ lam ⋆
               (FElem_Fp2 _ xt ⋆
                (FElem_Fp2 _ yt ⋆
                 (FElem_Fp _ xp ⋆
                  (FElem_Fp _ yp ⋆ Rr))))))))))) m_rest).
      { pose proof Hsep_d' as H'. ecancel_assumption. }

      (* Destructure to get d0 and d1 sub-memories *)
      destruct Hsep_rearr as [m_oc0 [m_r1 [[Heq_r1 Hd_r1] [Hoc0 Hr1]]]].
      destruct Hr1 as [m_oc1 [m_r2 [[Heq_r2 Hd_r2] [Hoc1 Hr2]]]].
      destruct Hr2 as [m_oc2 [m_r3 [[Heq_r3 Hd_r3] [Hoc2 Hr3]]]].
      destruct Hr3 as [m_d1c0m [m_r4 [[Heq_r4 Hd_r4] [Hd1c0m Hr4]]]].
      destruct Hr4 as [m_d1c1m [m_r5 [[Heq_r5 Hd_r5] [Hd1c1m Hr5]]]].
      destruct Hr5 as [m_d1c2m [m_inputs [[Heq_r6 Hd_r6] [Hd1c2m Hinputs]]]].
      subst.

      (* Build disjointness facts *)
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r1) as [Hd_01 Hd_0r2].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r2) as [Hd_02 Hd_0r3].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r2) as [Hd_12 Hd_1r3].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r3) as [Hd_23 Hd_2r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r3) as [Hd_13 Hd_1r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r4) as [Hd_34 Hd_3r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r5) as [Hd_45 Hd_4inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_3r5) as [Hd_35 Hd_3inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_2r4) as [Hd_24 Hd_2r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_2r5) as [Hd_25 Hd_2inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r4) as [Hd_14 Hd_1r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r5) as [Hd_15 Hd_1inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r3) as [Hd_03 Hd_0r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r4) as [Hd_04 Hd_0r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r5) as [Hd_05 Hd_0inp].

      (* === Build Fp6 for d0 === *)
      assert (Hsep_d0_fp6 : (FElem_Fp2 pout out2 ⋆
        (FElem_Fp2 (word.add pout fp6_c1_off) out4 ⋆
         FElem_Fp2 (word.add pout fp6_c2_off) (fw5 ++ fw6)))
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))).
      { exists m_oc0, (map.putmany m_oc1 m_oc2).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; [exact Hd_01 | exact Hd_02]] |].
        split; [exact Hoc0 |].
        exists m_oc1, m_oc2.
        split; [split; [reflexivity | exact Hd_12] |].
        split; [exact Hoc1 | exact Hoc2]. }
      Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
      assert (Hlen_out2_fp2 : length out2 = Fp2_felem_size).
      { (* FElem = Bignum n, which stores length = n in its predicate *)
        unfold AbstractField.FElem, Bignum.Bignum in Hoc0.
        destruct Hoc0 as [me [ma [_ [[_ Hlen] _]]]]. exact Hlen. }
      assert (Hlen_out4_fp2 : length out4 = Fp2_felem_size).
      { unfold AbstractField.FElem, Bignum.Bignum in Hoc1.
        destruct Hoc1 as [me [ma [_ [[_ Hlen] _]]]]. exact Hlen. }
      assert (Hlen_d0c2_fp2 : length (fw5 ++ fw6) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw5, Hlen_fw6. reflexivity. }
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls377_pf_params bls377_beta bls377_xi_re bls377_xi_im bls377_Fp_rep fp6_prefix fp2_prefix
        pout out2 out4 (fw5 ++ fw6) _ Hlen_out2_fp2 Hlen_out4_fp2 Hlen_d0c2_fp2 Hsep_d0_fp6)
        as Hfe_d0.

      (* === Build Fp6 for d1 === *)
      assert (Hlen_d1c0_fp2 : length (fw7 ++ fw8) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
      assert (Hlen_d1c1_fp2 : length (yp ++ fw10) = Fp2_felem_size).
      { rewrite length_app, Hlen_yp_copy, Hlen_fw10. reflexivity. }
      assert (Hlen_d1c2_fp2 : length (fw11 ++ fw12) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw11, Hlen_fw12. reflexivity. }
      (* Need sep: (FElem_Fp2 base (fw7++fw8) * (FElem_Fp2 (base+c1) (yp++fw10) *
                     FElem_Fp2 (base+c2) (fw11++fw12))) m_d1 *)
      (* But the addresses for d1 Fp2s use (pout+fp6_off+X) while Fp6_raw_FElem_join
         expects base and (base+fp6_c1_offset) and (base+fp6_c2_offset).
         For d1, base = pout+fp6_felem_offset.
         The addresses for d1.c1 and d1.c2 from the rearranged sep use
         evar-unified addresses. We need to change them to
         (word.add base fp6_c1_off) and (word.add base fp6_c2_off). *)
      eassert (Hsep_d1_fp6 : (FElem_Fp2 _ (fw7 ++ fw8) ⋆
        (FElem_Fp2 (word.add _ fp6_c1_off) (yp ++ fw10) ⋆
         FElem_Fp2 (word.add _ fp6_c2_off) (fw11 ++ fw12)))
        (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))).
      { exists m_d1c0m, (map.putmany m_d1c1m m_d1c2m).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; [exact Hd_34 | exact Hd_35]] |].
        split; [exact Hd1c0m |].
        exists m_d1c1m, m_d1c2m.
        split; [split; [reflexivity | exact Hd_45] |].
        split; [exact Hd1c1m | exact Hd1c2m]. }
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls377_pf_params bls377_beta bls377_xi_re bls377_xi_im bls377_Fp_rep fp6_prefix fp2_prefix
        _ (fw7 ++ fw8) (yp ++ fw10) (fw11 ++ fw12) _ Hlen_d1c0_fp2 Hlen_d1c1_fp2 Hlen_d1c2_fp2 Hsep_d1_fp6)
        as Hfe_d1.

      (* === Build Fp12: join d0 and d1 === *)
      Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls377_Fp6_params' _ _ _ _ bls377_Fp6_rep').
      assert (Hlen_d0_fp6 : length (out2 ++ out4 ++ (fw5 ++ fw6)) = Fp6_fsw).
      { rewrite !length_app, Hlen_out2_fp2, Hlen_out4_fp2, Hlen_fw5, Hlen_fw6.
        reflexivity. }
      assert (Hlen_d1_fp6 : length ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_yp_copy, Hlen_fw10, Hlen_fw11, Hlen_fw12.
        reflexivity. }
      set (m_fp12 := map.putmany (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))
                                  (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))).
      assert (Hsep_fp12 : (FElem_Fp6 pout (out2 ++ out4 ++ (fw5 ++ fw6)) ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset))
          ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12))) m_fp12).
      { subst m_fp12. exists (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)),
          (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m)).
        split; [split; [reflexivity |] |].
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_03 | apply map.disjoint_putmany_r; split; [exact Hd_04 | exact Hd_05]]. }
          { apply map.disjoint_putmany_l. split.
            { apply map.disjoint_putmany_r. split; [exact Hd_13 | apply map.disjoint_putmany_r; split; [exact Hd_14 | exact Hd_15]]. }
            { apply map.disjoint_putmany_r. split; [exact Hd_23 | apply map.disjoint_putmany_r; split; [exact Hd_24 | exact Hd_25]]. } } }
        split; [exact Hfe_d0 | exact Hfe_d1]. }
      pose proof (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _
        wordok mapok bls377_pf_params bls377_Fp_rep bls377_beta bls377_xi_re bls377_xi_im fp12_prefix fp6_prefix fp2_prefix
        pout (out2 ++ out4 ++ (fw5 ++ fw6))
        ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12)) m_fp12
        Hlen_d0_fp6 Hlen_d1_fp6 Hsep_fp12)
        as Hfe_fp12.
      (* Hfe_fp12 : FElem_Fp12 pout <big_concat> m_fp12 *)

      (* === Step 4: Provide the existential witness and prove bounded === *)
      set (the_out := (out2 ++ out4 ++ (fw5 ++ fw6)) ++
                       ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12))).
      exists the_out.
      split.
      { (* bounded_by loose_bounds the_out *)
        subst the_out.
        (* Decompose Fp2 bounds into Fp bounds *)
        pose proof Hbound2 as Hb2.
        pose proof Hbound4 as Hb4.
        unfold Fp2_bounded, AbstractField.bounded_by,
               bls377_Fp2_rep', bls377_Fp2_params',
               QuadraticFieldExtensionsSpecs.Fp2_field_representation in Hb2, Hb4.
        cbv beta in Hb2, Hb4.
        destruct Hb2 as [Hb2a Hb2b]. destruct Hb4 as [Hb4a Hb4b].
        (* relax all tight to loose *)
        pose proof (@AbstractField.relax_bounds _ _ _ _ _ _
          bls377_Fp_rep bls377_Fp_rep_ok) as RB.
        (* Build Fp2-level loose bounds for joined pairs *)
        Local Ltac mk_fp2_loose Hfa Hfb Hlen :=
          unfold Fp2_bounded, AbstractField.bounded_by,
                 bls377_Fp2_rep', bls377_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation;
          cbv beta;
          unfold QuadraticFieldExtensionsSpecs.fst_felem,
                 QuadraticFieldExtensionsSpecs.snd_felem;
          rewrite firstn_app' by exact Hlen;
          rewrite QuadraticFieldExtensions.skipn_app by exact Hlen;
          exact (conj Hfa Hfb).
        assert (Hb_d0c2 : Fp2_bounded Fp2_loose (fw5 ++ fw6))
          by (mk_fp2_loose (RB _ Hbound5) (RB _ Hbound6) Hlen_fw5).
        assert (Hb_d1c0 : Fp2_bounded Fp2_loose (fw7 ++ fw8))
          by (mk_fp2_loose (RB _ Hbound7) (RB _ Hbound8) Hlen_fw7).
        assert (Hb_d1c1 : Fp2_bounded Fp2_loose (yp ++ fw10))
          by (mk_fp2_loose Hbyp (RB _ Hbound10) Hlen_yp_copy).
        assert (Hb_d1c2 : Fp2_bounded Fp2_loose (fw11 ++ fw12))
          by (mk_fp2_loose (RB _ Hbound11) (RB _ Hbound12) Hlen_fw11).
        assert (Hb_out2_l : Fp2_bounded Fp2_loose out2).
        { unfold Fp2_bounded, AbstractField.bounded_by,
                 bls377_Fp2_rep', bls377_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation.
          cbv beta. exact (conj (RB _ Hb2a) (RB _ Hb2b)). }
        assert (Hb_out4_l : Fp2_bounded Fp2_loose out4).
        { unfold Fp2_bounded, AbstractField.bounded_by,
                 bls377_Fp2_rep', bls377_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation.
          cbv beta. exact (conj (RB _ Hb4a) (RB _ Hb4b)). }
        (* Build Fp6 bounds *)
        (* Use Fp_rep_ok's relax_bounds to lift tight → loose at Fp level,
           then assemble via the representation structure.
           Since the opaque type classes make unfolding painful,
           we directly construct the proof using admit for now and
           will replace with a dedicated lemma if needed. *)
        Local Typeclasses Transparent bls377_Fp12_params'.
        Local Typeclasses Transparent bls377_Fp12_rep'.
        Local Typeclasses Transparent bls377_Fp6_params'.
        Local Typeclasses Transparent bls377_Fp6_rep'.
        Local Typeclasses Transparent bls377_Fp2_params'.
        Local Typeclasses Transparent bls377_Fp2_rep'.
        cbv [AbstractField.bounded_by AbstractField.loose_bounds
             bls377_Fp12_rep' bls377_Fp12_params'
             bls377_Fp6_rep' bls377_Fp6_params'
             bls377_Fp2_rep' bls377_Fp2_params'
             bls377_beta bls377_xi_re bls377_xi_im
             DodecicFieldExtensionsSpecs.Fp12_field_representation
             DodecicFieldExtensionsSpecs.Fp12_field_parameters
             DodecicFieldExtensionsSpecs.d0_felem
             DodecicFieldExtensionsSpecs.d1_felem
             CubicFieldExtensionsSpecs.Fp6_field_representation
             CubicFieldExtensionsSpecs.Fp6_field_parameters
             CubicFieldExtensionsSpecs.c0_felem
             CubicFieldExtensionsSpecs.c1_felem
             CubicFieldExtensionsSpecs.c2_felem
             QuadraticFieldExtensionsSpecs.Fp2_field_representation
             QuadraticFieldExtensionsSpecs.Fp2_field_parameters
             QuadraticFieldExtensionsSpecs.fst_felem
             QuadraticFieldExtensionsSpecs.snd_felem].
        cbv beta.
        (* firstn/skipn simplification.
           The key insight: after cbv, all sizes are in terms of Fp_fsw.
           Fp2_fsw = 2*Fp_fsw, Fp6_fsw = 3*(2*Fp_fsw) = 6*Fp_fsw, Fp12_fsw = 12*Fp_fsw.
           Build all needed length equalities with the correct numeric form. *)
        assert (Hlen_d0_num : length (out2 ++ out4 ++ fw5 ++ fw6) = (3 * (2 * Fp_fsw))%nat).
        { rewrite !length_app. rewrite Hlen_fw5, Hlen_fw6.
          unfold AbstractField.FElem, Bignum.Bignum in Hoc0, Hoc1.
          destruct Hoc0 as [? [? [_ [[_ Hl0] _]]]].
          destruct Hoc1 as [? [? [_ [[_ Hl1] _]]]].
          rewrite Hl0, Hl1. reflexivity. }
        (* firstn at Fp12 level: extract d0 *)
        rewrite (firstn_app' _ _ _ Hlen_d0_num).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d0_num).
        (* Build Fp2 length hypotheses compatible with the unfolded form *)
        assert (Hlen_out2_num : length out2 = (2 * Fp_fsw)%nat).
        { unfold AbstractField.FElem, Bignum.Bignum in Hoc0.
          destruct Hoc0 as [? [? [_ [[_ Hl] _]]]]. exact Hl. }
        assert (Hlen_out4_num : length out4 = (2 * Fp_fsw)%nat).
        { unfold AbstractField.FElem, Bignum.Bignum in Hoc1.
          destruct Hoc1 as [? [? [_ [[_ Hl] _]]]]. exact Hl. }
        (* The Fp6 bounded_by from DodecicFieldExtensions didn't fully unfold.
           Split the conjunction and handle each Fp6 half. *)
        split.
        (* d0 bound *)
        { change (DodecicFieldExtensionsSpecs.Fp6_repr_inst bls377_beta bls377_xi_re bls377_xi_im) with bls377_Fp6_rep'.
          unfold AbstractField.bounded_by, AbstractField.loose_bounds,
                 bls377_Fp6_rep', bls377_Fp6_params',
                 CubicFieldExtensionsSpecs.Fp6_field_representation,
                 CubicFieldExtensionsSpecs.Fp6_field_parameters,
                 CubicFieldExtensionsSpecs.c0_felem,
                 CubicFieldExtensionsSpecs.c1_felem,
                 CubicFieldExtensionsSpecs.c2_felem.
          cbv beta.
          (* Solve each Fp6 bounded goal by unfolding to Fp2 *)
          cbv [DodecicFieldExtensionsSpecs.Fp6_repr_inst bls377_beta bls377_xi_re bls377_xi_im
               CubicFieldExtensionsSpecs.Fp6_field_representation
               CubicFieldExtensionsSpecs.Fp6_field_parameters
               CubicFieldExtensionsSpecs.c0_felem
               CubicFieldExtensionsSpecs.c1_felem
               CubicFieldExtensionsSpecs.c2_felem
               AbstractField.bounded_by AbstractField.loose_bounds].
          cbv beta.
          rewrite (firstn_app' _ _ _ Hlen_out2_num).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out2_num).
          (* For c1: firstn uses Fp2_fsw from the Fp6 context which may differ from
             Hlen_out4_num's 2*Fp_fsw. Use eassert to match the exact form. *)
          match goal with |- context [firstn ?n (out4 ++ _)] =>
            assert (Hlen_out4_c1 : length out4 = n) by exact Hlen_out4_num
          end.
          rewrite (firstn_app' _ _ _ Hlen_out4_c1).
          (* c2: skipn (2*(2*Fp_fsw)) (out2 ++ out4 ++ fw5 ++ fw6) = fw5 ++ fw6 *)
          assert (Hlen_out2_out4 : length (out2 ++ out4) = (2 * (2 * Fp_fsw))%nat).
          { rewrite length_app, Hlen_out2_num, Hlen_out4_num. reflexivity. }
          rewrite (app_assoc out2 out4).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out2_out4).
          exact (conj Hb_out2_l (conj Hb_out4_l Hb_d0c2)). }
        (* d1 bound *)
        { cbv [DodecicFieldExtensionsSpecs.Fp6_repr_inst bls377_beta bls377_xi_re bls377_xi_im
               CubicFieldExtensionsSpecs.Fp6_field_representation
               CubicFieldExtensionsSpecs.Fp6_field_parameters
               CubicFieldExtensionsSpecs.c0_felem
               CubicFieldExtensionsSpecs.c1_felem
               CubicFieldExtensionsSpecs.c2_felem
               AbstractField.bounded_by AbstractField.loose_bounds].
          cbv beta.
          assert (Hlen_d1c0_inner : length (fw7 ++ fw8) = (2 * Fp_fsw)%nat).
          { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
          assert (Hlen_yp_fw10 : length (yp ++ fw10) = (2 * Fp_fsw)%nat).
          { rewrite length_app, Hlen_yp_copy, Hlen_fw10. reflexivity. }
          rewrite (firstn_app' _ _ _ Hlen_d1c0_inner).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d1c0_inner).
          match goal with |- context [firstn ?n ((yp ++ fw10) ++ _)] =>
            assert (Hlen_yp_fw10_c1 : length (yp ++ fw10) = n) by
              (rewrite length_app, Hlen_yp_copy, Hlen_fw10; reflexivity)
          end.
          rewrite (firstn_app' _ _ _ Hlen_yp_fw10_c1).
          (* c2: skipn (2*Fp2_fsw) ((fw7++fw8) ++ (yp++fw10) ++ fw11 ++ fw12) *)
          assert (Hlen_d1_c0c1 : length ((fw7 ++ fw8) ++ (yp ++ fw10)) = (2 * (2 * Fp_fsw))%nat).
          { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_yp_copy, Hlen_fw10. reflexivity. }
          rewrite (app_assoc (fw7 ++ fw8) (yp ++ fw10)).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d1_c0c1).
          exact (conj Hb_d1c0 (conj Hb_d1c1 Hb_d1c2)). } }
      { (* (FElem_Fp12 pout the_out ⋆ inputs) m_rest *)
        subst m_fp12. subst the_out.
        exists (map.putmany (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))
                            (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))),
               m_inputs.
        split; [split |].
        { rewrite ?map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_l. split.
            { exact Hd_0inp. }
            { apply map.disjoint_putmany_l. split; [exact Hd_1inp | exact Hd_2inp]. } }
          { apply map.disjoint_putmany_l. split.
            { exact Hd_3inp. }
            { apply map.disjoint_putmany_l. split; [exact Hd_4inp | exact Hd_r6]. } } }
        split; [exact Hfe_fp12 | exact Hinputs]. }
    Qed.

End BLS12_377_PairingHelpers.
