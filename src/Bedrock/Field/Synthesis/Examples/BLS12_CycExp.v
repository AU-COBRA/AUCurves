(** * BLS12-381 cyclotomic exponentiation: WP proofs

    Proves the two functions [bls12_Fp12_cyc_exp_x_neg] and
    [bls12_Fp12_cyc_exp_c_neg] of BLS12_Pairing.v, which compute
    out = conjugate(base^e) for e = |x| = 0xd201000000010000 and
    e = c = (|x|+1)/3 = 0x460055555555aaab, by left-to-right
    square-and-multiply over 64 bits with the cyclotomic squaring
    [cyc_sqr_body] (new_c0 = 1 + 2 v c1^2, new_c1 = 2 c0 c1).

    The specs are bounds-and-frame specs, as for bls12_Fp12_pow_x
    (BLS12_PowX.v): the output is bounded and the base and the frame are
    preserved.

    Lemmas:
      fp12_set_one_wp   the 12 from_word calls of fp12_set_one
      cyc_sqr_wp        one squaring by the earlier formula (cyc_sqr_body), in place
    The squaring of the loop is now a call to bls12_Fp12_cyclotomic_square
    (Granger-Scott); the proofs of the two functions are in BLS12_CycExpFunctional.v.
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.
Require Import bedrock2.SepAutoArray.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.


Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_CycExp.


    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul"; PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub"; PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square"; PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv"; PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes"; PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy"; PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

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

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp6_tight := (@AbstractField.tight_bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp6_loose := (@AbstractField.loose_bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp6_felem := (@AbstractField.felem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* === Callee specs === *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.bin_mul.

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix).

    Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
      AbstractField.binop_spec (F:=Fp6) (field_representation:=bls12_Fp6_rep') AbstractField.bin_mul.
    Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
      AbstractField.binop_spec (F:=Fp6) (field_representation:=bls12_Fp6_rep') AbstractField.bin_add.

    Let fp6_mul_by_v_name : string := (fp6_prefix ++ "mul_by_v")%string.
    Instance spec_of_Fp6_mul_by_v : spec_of fp6_mul_by_v_name :=
      AbstractField.unop_spec (F:=Fp6) (field_representation:=bls12_Fp6_rep')
        (@DodecicFieldExtensions.un_Fp6_mul_by_v _ _ _ _
          bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix).

    Instance spec_of_Fp_add : spec_of (AbstractField.add (F:=Fp)) :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls12_Fp_rep) AbstractField.bin_add.

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls12_Fp_rep).

    Local Instance bls12_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bls12_beta bls12_xi_re bls12_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    (* ================================================================ *)
    (* fp12_set_one: 12 from_word calls; result tight                  *)
    (* ================================================================ *)

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')).
    Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).

    (* Split an Fp12 FElem into its six Fp2 components *)
    Lemma FElem_Fp12_split6 a (x : Fp12_felem) R m :
      (FElem_Fp12 a x ⋆ R) m ->
      (FElem_Fp2 a (c0_felem (d0_felem x)) ⋆
       (FElem_Fp2 (word.add a fp6_c1_off) (c1_felem (d0_felem x)) ⋆
        (FElem_Fp2 (word.add a fp6_c2_off) (c2_felem (d0_felem x)) ⋆
         (FElem_Fp2 (word.add a (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem x)) ⋆
          (FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off)
             (c1_felem (d1_felem x)) ⋆
           (FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off)
              (c2_felem (d1_felem x)) ⋆ R)))))) m.
    Proof.
      intros [m_x [m_rest [[Heq Hd] [Hfe Hrest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix a x m_x Hfe) as [m_d0 [m_d1 [[Heq12 Hd12] [Hf0 Hf1]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix a _ m_d0 Hf0) as [m00 [m0r [[Heq0 Hd0] [Hf00 H0r]]]].
      destruct H0r as [m01 [m02 [[Heq01 Hd01] [Hf01 Hf02]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix (word.add a (word.of_Z fp6_felem_offset)) _ m_d1 Hf1)
        as [m10 [m1r [[Heq1 Hd1] [Hf10 H1r]]]].
      destruct H1r as [m11 [m12 [[Heq11 Hd11] [Hf11 Hf12]]]].
      subst.
      split_all_disjointness.
      rewrite <- ?map.putmany_assoc.
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
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hf12 | exact Hrest].
    Qed.

    (* Join six Fp2 components into an Fp12 FElem *)
    Lemma FElem_Fp12_join6 a (x0 x1 x2 y0 y1 y2 : list word) R m :
      length x0 = Fp2_fsw -> length x1 = Fp2_fsw -> length x2 = Fp2_fsw ->
      length y0 = Fp2_fsw -> length y1 = Fp2_fsw -> length y2 = Fp2_fsw ->
      (FElem_Fp2 a x0 ⋆
       (FElem_Fp2 (word.add a fp6_c1_off) x1 ⋆
        (FElem_Fp2 (word.add a fp6_c2_off) x2 ⋆
         (FElem_Fp2 (word.add a (word.of_Z fp6_felem_offset)) y0 ⋆
          (FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off) y1 ⋆
           (FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off) y2 ⋆ R)))))) m ->
      (FElem_Fp12 a ((x0 ++ x1 ++ x2) ++ (y0 ++ y1 ++ y2)) ⋆ R) m.
    Proof.
      intros L0 L1 L2 L3 L4 L5 H.
      destruct H as [m0 [r0 [[E0 D0] [H0 H]]]].
      destruct H as [m1 [r1 [[E1 D1] [H1 H]]]].
      destruct H as [m2 [r2 [[E2 D2] [H2 H]]]].
      destruct H as [m3 [r3 [[E3 D3] [H3 H]]]].
      destruct H as [m4 [r4 [[E4 D4] [H4 H]]]].
      destruct H as [m5 [mR [[E5 D5] [H5 HR]]]].
      subst.
      split_all_disjointness.
      assert (HA : FElem_Fp6 a (x0 ++ x1 ++ x2) (map.putmany m0 (map.putmany m1 m2))).
      { apply (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix);
          [exact L0 | exact L1 | exact L2 |].
        exists m0, (map.putmany m1 m2). split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact H0 |].
        exists m1, m2. split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact H1 | exact H2]. }
      assert (HB : FElem_Fp6 (word.add a (word.of_Z fp6_felem_offset)) (y0 ++ y1 ++ y2)
                     (map.putmany m3 (map.putmany m4 m5))).
      { apply (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix);
          [exact L3 | exact L4 | exact L5 |].
        exists m3, (map.putmany m4 m5). split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact H3 |].
        exists m4, m5. split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact H4 | exact H5]. }
      assert (HC : FElem_Fp12 a ((x0 ++ x1 ++ x2) ++ (y0 ++ y1 ++ y2))
                     (map.putmany (map.putmany m0 (map.putmany m1 m2)) (map.putmany m3 (map.putmany m4 m5)))).
      { apply (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix).
        { rewrite !length_app, L0, L1, L2. reflexivity. }
        { rewrite !length_app, L3, L4, L5. reflexivity. }
        exists (map.putmany m0 (map.putmany m1 m2)), (map.putmany m3 (map.putmany m4 m5)).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HA | exact HB]. }
      exists (map.putmany (map.putmany m0 (map.putmany m1 m2)) (map.putmany m3 (map.putmany m4 m5))), mR.
      split; [split; [rewrite <- ?map.putmany_assoc; reflexivity | map_disjoint_auto] |].
      split; [exact HC | exact HR].
    Qed.

    (* Bounds of an Fp12 built from six Fp2 components *)
    Lemma Fp12_bounded_join6 (x0 x1 x2 y0 y1 y2 : list word) :
      length x0 = Fp2_fsw -> length x1 = Fp2_fsw -> length x2 = Fp2_fsw ->
      length y0 = Fp2_fsw -> length y1 = Fp2_fsw -> length y2 = Fp2_fsw ->
      Fp2_bounded Fp2_tight x0 -> Fp2_bounded Fp2_tight x1 -> Fp2_bounded Fp2_tight x2 ->
      Fp2_bounded Fp2_tight y0 -> Fp2_bounded Fp2_tight y1 -> Fp2_bounded Fp2_tight y2 ->
      Fp12_bounded Fp12_tight ((x0 ++ x1 ++ x2) ++ (y0 ++ y1 ++ y2)).
    Proof.
      intros L0 L1 L2 L3 L4 L5 B0 B1 B2 B3 B4 B5.
      assert (LA : length (x0 ++ x1 ++ x2) = Fp6_fsw) by (rewrite !length_app, L0, L1, L2; reflexivity).
      change Fp12_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
             (felem : list word) =>
          Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)); cbv beta.
      rewrite (@DodecicFieldExtensions.d0_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
        bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ LA).
      rewrite (@DodecicFieldExtensions.d1_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
        bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ LA).
      change Fp6_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
             (felem : list word) =>
          Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
          Fp2_bounded b (c2_felem felem)); cbv beta.
      rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix x0 x1 x2 L0).
      rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix x0 x1 x2 L0 L1).
      rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix x0 x1 x2 L0 L1).
      rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix y0 y1 y2 L3).
      rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix y0 y1 y2 L3 L4).
      rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix y0 y1 y2 L3 L4).
      tauto.
    Qed.

    (* Bounds of an Fp2 built from two Fp components *)
    Lemma Fp2_bounded_join (u v : list word) :
      length u = Fp_fsw ->
      Fp_bounded Fp_tight u -> Fp_bounded Fp_tight v ->
      Fp2_bounded Fp2_tight (u ++ v).
    Proof.
      intros Lu Bu Bv.
      change Fp2_bounded with
        (fun (b : @AbstractField.bounds _ _ _ _ _ _ bls12_Fp_rep) (ws : list word) =>
          Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws)); cbv beta.
      unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Lu).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Lu).
      split; assumption.
    Qed.

    Lemma Fp_FElem_length p (x : Fp_felem) m : FElem_Fp p x m -> length x = Fp_fsw.
    Proof. exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _ bls12_pf_params bls12_Fp_rep p x m). Qed.

    Local Notation fpoff := (word.of_Z fp_felem_offset).

    (* Join twelve Fp components (in memory order) into an Fp12 FElem *)
    Lemma FElem_Fp12_join12 a (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : list word) R m :
      length f0 = Fp_fsw -> length f1 = Fp_fsw -> length f2 = Fp_fsw -> length f3 = Fp_fsw ->
      length f4 = Fp_fsw -> length f5 = Fp_fsw -> length f6 = Fp_fsw -> length f7 = Fp_fsw ->
      length f8 = Fp_fsw -> length f9 = Fp_fsw -> length f10 = Fp_fsw -> length f11 = Fp_fsw ->
      let a6 := word.add a (word.of_Z fp6_felem_offset) in
      (FElem_Fp a f0 ⋆ (FElem_Fp (word.add a fpoff) f1 ⋆
       (FElem_Fp (word.add a fp6_c1_off) f2 ⋆ (FElem_Fp (word.add (word.add a fp6_c1_off) fpoff) f3 ⋆
        (FElem_Fp (word.add a fp6_c2_off) f4 ⋆ (FElem_Fp (word.add (word.add a fp6_c2_off) fpoff) f5 ⋆
         (FElem_Fp a6 f6 ⋆ (FElem_Fp (word.add a6 fpoff) f7 ⋆
          (FElem_Fp (word.add a6 fp6_c1_off) f8 ⋆ (FElem_Fp (word.add (word.add a6 fp6_c1_off) fpoff) f9 ⋆
           (FElem_Fp (word.add a6 fp6_c2_off) f10 ⋆ (FElem_Fp (word.add (word.add a6 fp6_c2_off) fpoff) f11 ⋆
            R)))))))))))) m ->
      (FElem_Fp12 a (((f0 ++ f1) ++ (f2 ++ f3) ++ (f4 ++ f5)) ++
                     ((f6 ++ f7) ++ (f8 ++ f9) ++ (f10 ++ f11))) ⋆ R) m.
    Proof.
      intros L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 a6 H.
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L0 | exact L1].
      destruct H as [m0 [r0 [S0 [H0 H]]]].
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L2 | exact L3].
      destruct H as [m1 [r1 [S1 [H1 H]]]].
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L4 | exact L5].
      destruct H as [m2 [r2 [S2 [H2 H]]]].
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L6 | exact L7].
      destruct H as [m3 [r3 [S3 [H3 H]]]].
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L8 | exact L9].
      destruct H as [m4 [r4 [S4 [H4 H]]]].
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in H; [| exact L10 | exact L11].
      apply FElem_Fp12_join6;
        [ rewrite length_app, L0, L1; reflexivity
        | rewrite length_app, L2, L3; reflexivity
        | rewrite length_app, L4, L5; reflexivity
        | rewrite length_app, L6, L7; reflexivity
        | rewrite length_app, L8, L9; reflexivity
        | rewrite length_app, L10, L11; reflexivity | ].
      exists m0, r0. split; [exact S0 |]. split; [exact H0 |].
      exists m1, r1. split; [exact S1 |]. split; [exact H1 |].
      exists m2, r2. split; [exact S2 |]. split; [exact H2 |].
      exists m3, r3. split; [exact S3 |]. split; [exact H3 |].
      exists m4, r4. split; [exact S4 |]. split; [exact H4 | exact H].
    Qed.

    Local Ltac snd_from_word_ecancel H :=
      let H' := fresh "H" in
      pose proof H as H';
      ecancel_assumption_impl.

    Local Ltac fw_pair HFfromword a x :=
      repeat straightline;
      let Hs := fresh "Hs" in
      eassert (Hs : (FElem_Fp2 a x ⋆ _) _) by ecancel_assumption;
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hs;
      eexists; split; [eval_dexprs_fast |];
      eapply Semantics.weaken_call;
      [ eapply (HFfromword _ _ (fst_felem x)); exact Hs | ];
      let fwa := fresh "fw" in let Hba := fresh "Hb_fw" in let Hsa := fresh "Hsep_fw" in
      intros ? ? ? [? [? [fwa [? [Hba Hsa]]]]];
      subst; cbv [map.putmany_of_list_zip]; eexists; split; [ exact eq_refl | ];
      repeat straightline;
      eexists; split; [eval_dexprs_fast |];
      eapply Semantics.weaken_call;
      [ eapply (HFfromword _ _ (snd_felem x)); snd_from_word_ecancel Hsa | ];
      let fwb := fresh "fw" in let Hbb := fresh "Hb_fw" in let Hsb := fresh "Hsep_fw" in
      intros ? ? ? [? [? [fwb [? [Hbb Hsb]]]]];
      subst; cbv [map.putmany_of_list_zip]; eexists; split; [ exact eq_refl | ].

    Local Ltac fp_len x :=
        match goal with H : (_ ⋆ _) ?mf |- _ =>
          let Ht := fresh in
          eassert (Ht : (FElem_Fp _ x ⋆ _) mf) by ecancel_assumption;
          let Hfe := fresh in
          destruct Ht as [? [? [_ [Hfe _]]]];
          exact (Fp_FElem_length _ _ _ Hfe)
        end.

    Lemma fp12_set_one_wp :
      forall functions (HFfromword : spec_of_Fp_from_word functions)
        (a : word) (old : Fp12_felem) (R : mem -> Prop) tr (m : mem) (l : locals)
        (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "result" = Some a ->
        (FElem_Fp12 a old ⋆ R) m ->
        (forall m' (one : Fp12_felem),
           Fp12_bounded Fp12_tight one -> (FElem_Fp12 a one ⋆ R) m' -> post tr m' l) ->
        WeakestPrecondition.cmd functions (BLS12_Pairing.fp12_set_one "result") tr m l post.
    Proof.
      intros functions HFfromword a old R tr m l post Hget Hsep Hpost.
      apply FElem_Fp12_split6 in Hsep.
      unfold BLS12_Pairing.fp12_set_one, BLS12_Pairing.cmd_seq_list.
      unfold BLS12_Pairing.expr_fp12_c0, BLS12_Pairing.expr_fp12_c1,
             BLS12_Pairing.expr_fp6_c0, BLS12_Pairing.expr_fp6_c1,
             BLS12_Pairing.expr_fp6_c2, BLS12_Pairing.expr_fp_snd.
      fw_pair HFfromword a (c0_felem (d0_felem old)).
      fw_pair HFfromword (word.add a fp6_c1_off) (c1_felem (d0_felem old)).
      fw_pair HFfromword (word.add a fp6_c2_off) (c2_felem (d0_felem old)).
      fw_pair HFfromword (word.add a (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem old)).
      fw_pair HFfromword (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off) (c1_felem (d1_felem old)).
      fw_pair HFfromword (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off) (c2_felem (d1_felem old)).
      (* lengths of the twelve new Fp components *)
      match goal with H : (_ ⋆ _) ?mf |- _ => set (m_fw := mf) in * end.
      assert (L0 : length fw = Fp_fsw) by fp_len fw.
      assert (L1 : length fw0 = Fp_fsw) by fp_len fw0.
      assert (L2 : length fw1 = Fp_fsw) by fp_len fw1.
      assert (L3 : length fw2 = Fp_fsw) by fp_len fw2.
      assert (L4 : length fw3 = Fp_fsw) by fp_len fw3.
      assert (L5 : length fw4 = Fp_fsw) by fp_len fw4.
      assert (L6 : length fw5 = Fp_fsw) by fp_len fw5.
      assert (L7 : length fw6 = Fp_fsw) by fp_len fw6.
      assert (L8 : length fw7 = Fp_fsw) by fp_len fw7.
      assert (L9 : length fw8 = Fp_fsw) by fp_len fw8.
      assert (L10 : length fw9 = Fp_fsw) by fp_len fw9.
      assert (L11 : length fw10 = Fp_fsw) by fp_len fw10.
      eapply (Hpost _ (((fw ++ fw0) ++ (fw1 ++ fw2) ++ (fw3 ++ fw4)) ++
                       ((fw5 ++ fw6) ++ (fw7 ++ fw8) ++ (fw9 ++ fw10)))).
      { apply Fp12_bounded_join6;
          [ rewrite length_app, L0, L1; reflexivity
          | rewrite length_app, L2, L3; reflexivity
          | rewrite length_app, L4, L5; reflexivity
          | rewrite length_app, L6, L7; reflexivity
          | rewrite length_app, L8, L9; reflexivity
          | rewrite length_app, L10, L11; reflexivity
          | apply Fp2_bounded_join; assumption
          | apply Fp2_bounded_join; assumption
          | apply Fp2_bounded_join; assumption
          | apply Fp2_bounded_join; assumption
          | apply Fp2_bounded_join; assumption
          | apply Fp2_bounded_join; assumption ]. }
      eapply FElem_Fp12_join12; try eassumption.
      ecancel_assumption_impl.
    Qed.
    (* ================================================================ *)
    (* One cyclotomic squaring, in place on "result"                    *)
    (* ================================================================ *)

    Lemma sep3_frame (A B C R : mem -> Prop) m m1 m2 :
      map.split m m1 m2 -> (A ⋆ (B ⋆ C)) m1 -> R m2 -> (A ⋆ (B ⋆ (C ⋆ R))) m.
    Proof.
      intros Hs H1 H2.
      assert (H : ((A ⋆ (B ⋆ C)) ⋆ R) m) by (exists m1, m2; auto).
      ecancel_assumption.
    Qed.

    (* length of any FElem (a Bignum) *)
    Local Ltac felem_len P :=
      match goal with
      | |- Datatypes.length ?x = _ =>
        let Ht := fresh in
        eassert (Ht : (P _ x ⋆ _) _) by ecancel_assumption;
        let Hfe := fresh in
        destruct Ht as [? [? [_ [Hfe _]]]];
        let Hl := fresh in
        destruct Hfe as [? [? [_ [[_ Hl] _]]]];
        exact Hl
      end.

    Lemma cyc_sqr_wp :
      forall functions
        (HFp6mul : spec_of_Fp6_mul functions)
        (HFp6add : spec_of_Fp6_add functions)
        (HFp6mulv : spec_of_Fp6_mul_by_v functions)
        (HFpadd : spec_of_Fp_add functions)
        (a_r a_t0 a_t1 a_one : word) (r : Fp12_felem) (x0 x1 : Fp6_felem) (one : Fp_felem)
        (R : mem -> Prop) tr (m : mem) (l : locals)
        (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "result" = Some a_r ->
        map.get l "cyc_t0" = Some a_t0 ->
        map.get l "cyc_t1" = Some a_t1 ->
        map.get l "cyc_one" = Some a_one ->
        Fp12_bounded Fp12_tight r ->
        Fp_bounded Fp_tight one ->
        (FElem_Fp12 a_r r ⋆ (FElem_Fp6 a_t0 x0 ⋆ (FElem_Fp6 a_t1 x1 ⋆ (FElem_Fp a_one one ⋆ R)))) m ->
        (forall m' (r' : Fp12_felem) (x0' x1' : Fp6_felem),
           Fp12_bounded Fp12_tight r' ->
           (FElem_Fp12 a_r r' ⋆ (FElem_Fp6 a_t0 x0' ⋆ (FElem_Fp6 a_t1 x1' ⋆ (FElem_Fp a_one one ⋆ R)))) m' ->
           post tr m' l) ->
        WeakestPrecondition.cmd functions (BLS12_Pairing.cyc_sqr_body "result" "result") tr m l post.
    Proof.
      intros functions HFp6mul HFp6add HFp6mulv HFpadd a_r a_t0 a_t1 a_one r x0 x1 one R tr m l post
        Hgr Hgt0 Hgt1 Hgone Hbr Hbone Hsep Hpost.
      unfold BLS12_Pairing.cyc_sqr_body, BLS12_Pairing.cmd_seq_list.
      (* bounds of the halves *)
      change Fp12_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep') (felem : list word) =>
           Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)) in Hbr.
      cbv beta in Hbr. destruct Hbr as [Hbr0 Hbr1].
      (* split result into its halves *)
      destruct Hsep as [m_r [m_rest [[Heq Hd] [Hfe Hrest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_r r m_r Hfe) as [m_d0 [m_d1 [[Heq12 Hd12] [Hf0 Hf1]]]].
      subst m m_r.
      assert (Hsep6 :
        (FElem_Fp6 a_r (d0_felem r) ⋆
         (FElem_Fp6 (word.add a_r (word.of_Z fp6_felem_offset)) (d1_felem r) ⋆
          (FElem_Fp6 a_t0 x0 ⋆ (FElem_Fp6 a_t1 x1 ⋆ (FElem_Fp a_one one ⋆ R)))))
          (map.putmany (map.putmany m_d0 m_d1) m_rest)).
      { rewrite <- map.putmany_assoc.
        pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd) as [Hd0r Hd1r].
        exists m_d0, (map.putmany m_d1 m_rest).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; assumption] |].
        split; [exact Hf0 |].
        exists m_d1, m_rest. split; [split; [reflexivity | exact Hd1r] |].
        split; [exact Hf1 | exact Hrest]. }
      clear Hf0 Hf1 Hrest Hd Hd12.
      set (m0 := map.putmany (map.putmany m_d0 m_d1) m_rest) in *.

      (* Call 1: Fp6 mul(cyc_t0, c1, c1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mul.
           split; [exact Hbr1 |].
           split; [exact Hbr1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y1 [_ [Hb_y1 Hsep1]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 2: Fp6 mul(cyc_t1, c0, c1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mul.
           split; [exact Hbr0 |].
           split; [exact Hbr1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y2 [_ [Hb_y2 Hsep2]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 3: Fp6 mul_by_v(cyc_t0, cyc_t0) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mulv.
           split; [exact Hb_y1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y3 [_ [Hb_y3 Hsep3]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 4: Fp6 add(out_c0, cyc_t0, cyc_t0) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6add.
           split; [exact Hb_y3 |].
           split; [exact Hb_y3 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y4 [_ [Hb_y4 Hsep4]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 5: Fp add on the first Fp limb of out_c0 *)
      assert (Hb5 : Fp_bounded Fp_tight (fst_felem (c0_felem y4)) /\
                    Fp_bounded Fp_tight (snd_felem (c0_felem y4)) /\
                    Fp2_bounded Fp2_tight (c1_felem y4) /\ Fp2_bounded Fp2_tight (c2_felem y4)).
      { change Fp6_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep') (felem : list word) =>
             Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
             Fp2_bounded b (c2_felem felem)) in Hb_y4.
        cbv beta in Hb_y4. destruct Hb_y4 as [Hc0 [Hc1 Hc2]].
        change Fp2_bounded with
          (fun (b : @AbstractField.bounds _ _ _ _ _ _ bls12_Fp_rep) (ws : list word) =>
             Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws)) in Hc0.
        cbv beta in Hc0. destruct Hc0 as [Hc0a Hc0b].
        split; [exact Hc0a |]. split; [exact Hc0b |]. split; [exact Hc1 | exact Hc2]. }
      destruct Hb5 as [Hb5a [Hb5b [Hb5c Hb5d]]].
      destruct Hsep4 as [m_y4 [m_r4 [Sy4 [Hfe4 Hr4]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix a_r y4 m_y4 Hfe4) as Hy4s.
      pose proof (sep3_frame _ _ _ _ _ _ _ Sy4 Hy4s Hr4) as Hs5.
      clear Hy4s Hfe4 Hr4 Sy4.
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hs5.
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFpadd.
           split; [exact Hb5a |].
           split; [exact Hbone |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [z [_ [Hb_z Hsep5]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      assert (Lz : Datatypes.length z = Fp_fsw) by felem_len constr:(FElem_Fp).
      assert (Ls : Datatypes.length (snd_felem (c0_felem y4)) = Fp_fsw) by felem_len constr:(FElem_Fp).
      assert (L1 : Datatypes.length (c1_felem y4) = Fp2_fsw) by felem_len constr:(FElem_Fp2).
      assert (L2 : Datatypes.length (c2_felem y4) = Fp2_fsw) by felem_len constr:(FElem_Fp2).
      eassert (Hj : (FElem_Fp a_r z ⋆ (FElem_Fp (word.add a_r (word.of_Z fp_felem_offset))
                       (snd_felem (c0_felem y4)) ⋆ _)) _) by ecancel_assumption.
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hj; [| exact Lz | exact Ls].
      eassert (Hk : ((FElem_Fp2 a_r (z ++ snd_felem (c0_felem y4)) ⋆
                      (FElem_Fp2 (word.add a_r fp6_c1_off) (c1_felem y4) ⋆
                       FElem_Fp2 (word.add a_r fp6_c2_off) (c2_felem y4))) ⋆ _) _)
        by ecancel_assumption.
      clear Hj Hsep5.
      assert (L0 : Datatypes.length (z ++ snd_felem (c0_felem y4)) = Fp2_fsw)
        by (rewrite length_app, Lz, Ls; reflexivity).
      destruct Hk as [mk [mr [Sk [Hk1 Hk2]]]].
      apply (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix _ _ _ _ _
          L0 L1 L2) in Hk1.
      set (c0n := (z ++ snd_felem (c0_felem y4)) ++ c1_felem y4 ++ c2_felem y4) in *.
      assert (Hsep5' : (FElem_Fp6 a_r c0n ⋆ _) _) by (exists mk, mr; exact (conj Sk (conj Hk1 Hk2))).
      clear Hk1 Hk2 Sk.

      (* Call 6: Fp6 add(out_c1, cyc_t1, cyc_t1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6add.
           split; [exact Hb_y2 |].
           split; [exact Hb_y2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y6 [_ [Hb_y6 Hsep6']]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Rejoin result and conclude *)
      assert (Lc0n : Datatypes.length c0n = Fp6_fsw)
        by (subst c0n; rewrite !length_app, Lz, Ls, L1, L2; reflexivity).
      assert (Ly6 : Datatypes.length y6 = Fp6_fsw) by felem_len constr:(FElem_Fp6).
      eassert (H12 : ((FElem_Fp6 a_r c0n ⋆
                       FElem_Fp6 (word.add a_r (word.of_Z fp6_felem_offset)) y6) ⋆ _) _)
        by ecancel_assumption.
      destruct H12 as [m12 [mr12 [S12 [H12a H12b]]]].
      apply (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
          _ _ _ _ Lc0n Ly6) in H12a.
      eapply (Hpost _ (c0n ++ y6) y3 y2).
      { change Fp12_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
               (felem : list word) =>
            Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)); cbv beta.
        rewrite (@DodecicFieldExtensions.d0_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
          bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ Lc0n).
        rewrite (@DodecicFieldExtensions.d1_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
          bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ Lc0n).
        split; [| exact Hb_y6].
        subst c0n.
        change Fp6_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
               (felem : list word) =>
            Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
            Fp2_bounded b (c2_felem felem)); cbv beta.
        rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0).
        rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0 L1).
        rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0 L1).
        split; [apply Fp2_bounded_join; [exact Lz | exact Hb_z | exact Hb5b] |].
        split; [exact Hb5c | exact Hb5d]. }
      eassert (Hfin : ((FElem_Fp12 a_r (c0n ++ y6)) ⋆ _) _) by (exists m12, mr12; exact (conj S12 (conj H12a H12b))).
      ecancel_assumption.
    Qed.

    (* ================================================================ *)
    (* The function, for any 64-bit literal exponent e                 *)
    (* ================================================================ *)

    Definition spec_of_cyc_exp_neg (name : string) : spec_of name :=
      fnspec! name (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Local Instance bls12_Fp6_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' :=
      @CubicFieldExtensionsSpecs.Fp6_field_representation_ok _ _ _ _ bls12_pf_params bls12_Fp_rep
        bls12_Fp_rep_ok bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix.
    Local Instance bls12_Fp2_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      @QuadraticFieldExtensionsSpecs.Fp2_field_representation_ok _ _ _ _
        bls12_pf_params bls12_Fp_rep bls12_Fp_rep_ok bls12_beta fp2_prefix.

    Local Ltac solve_gets :=
      repeat (first [ rewrite map.get_put_same; reflexivity
                    | rewrite map.get_put_diff by congruence ]);
      try assumption.

    Local Ltac dealloc_with P :=
      match goal with
      | |- exists _ _, Memory.anybytes ?a _ _ /\ _ =>
        let H := fresh in
        eassert (H : (_ ⋆ P a _) _) by ecancel_assumption;
        destruct H as [? [? [[? ?] [? ?]]]];
        eexists _, _;
        split; [eapply AbstractField.FElem_to_bytes; eassumption|];
        split; [split; [eassumption | eassumption]|]
      end.

    (* The proofs of the two functions (bounds and frame, [spec_of_cyc_exp_neg]) are
       corollaries of the functional ones since the squaring became the call to
       bls12_Fp12_cyclotomic_square: BLS12_CycExpFunctional.bls12_Fp12_cyc_exp_x_neg_ok /
       bls12_Fp12_cyc_exp_c_neg_ok. *)

End BLS12_CycExp.
