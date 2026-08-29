(** * P-256 single-scalar wNAF scalar multiplication over the Rupicola
      general-a RCB addition.

    Instantiates the verified single-scalar wNAF chain
    ([BN254_wNAF_Instance.wnaf_single_full], Qed, Section-parametric)
    at the P-256 field representation [p256_frep] with the point
    addition [rcb_add_general_gallina] derived in CurveAddGeneralA.v and
    instantiated in CurveAddGeneralA_P256.v.

    Layout:
      §1  Gallina model: [p256_curve_add], [p256_scmul], constants.
      §2  bedrock2 function table: the derived add, its two constant
          loaders, the wrappers of NistWnafWrappers.v, felem_copy, and
          the wNAF driver [p256_wnaf_single_func] (257 digits, w = 4).
      §3  Arithmetic discharges at len = 257 (mirroring
          BLS12_wNAF_GLV_Instance.v at 129) and the digit-load lemma.
      §4  Callee-spec discharges from the function table.
      §5  [p256_wnaf_single_full]: the end-to-end statement.

    What remains hypothetical in §5 and why (docs/nist_scalar_mult_plan.md):
      - G5  [HOppInplace]: the chain hard-wires the FieldParameters name
            [opp] for the aliased negation; fiat-crypto's synthesized
            opp has no aliasing spec.  Discharged once the four generic
            files take an [opp_name] parameter (then
            [NistWnafWrappers.opp_inplace_ok] applies).
      - G6  Leibniz group laws on projective triples
            ([curve_add_assoc], [curve_add_comm], identities,
            [point_opp_inverse], and [Htable]).  These are FALSE for
            the raw RCB formula (BLS12_wNAF_PointOppInverse.v) and are
            kept as hypotheses, not Admitted.  Closing them needs the
            projective-equivalence refactor of the chain (phase 2).
      - G7  Digit array and table contents are caller-supplied.

    Honesty ledger: Admitted = the adapter lemmas of NistWnafWrappers.v
    (imported) plus [p256_Hhorner_step] and [p256_wnaf_single_full]
    (composition; positional-argument shapes need a compiler).
    Uncompiled draft. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Field.Synthesis.Examples.p256_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Instance.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoadAndProcess.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_Proof.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_HornerAlgebra.
Require Import Bedrock.Field.Synthesis.Examples.BN254_wNAF_Instance.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.WNAFTable.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256_Loaders.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section P256_wNAF.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (* ============================================================== *)
  (* §1. Gallina model                                               *)
  (* ============================================================== *)

  Definition p256_a_val : F := feval (proj1_sig p256_a_felem).
  Definition p256_three_b_val : F := feval (proj1_sig p256_three_b_felem).

  (** The chain's [curve_add] at P-256: the derived RCB formula on
      plain triples. *)
  Definition p256_curve_add : F * F * F -> F * F * F -> F * F * F :=
    curve_add_general_triple p256_a_val p256_three_b_val.

  Definition p256_point_opp : F * F * F -> F * F * F :=
    @point_opp_triple p256_field_parameters.

  (** [scmul] of BLS12_GLV_LoopInvariant.v, the chain's [scmul_s].
      Qualified: WNAFTable.v (imported later) also exports a [scmul]
      whose [Fzero]/[Fone] are implicit, so the short name resolves to
      the wrong one. *)
  Definition p256_scmul : nat -> F * F * F -> F * F * F :=
    BLS12_GLV_LoopInvariant.scmul Fzero Fone p256_curve_add.

  (** wNAF parameters: 256-bit scalars, window 4, hence 257 digits
      (cf. 129 digits for 128-bit GLV halves in the BLS12 chain). *)
  Definition p256_num_digits : nat := 257%nat.

  Lemma p256_felem_size_in_bytes_eq : felem_size_in_bytes = 32.
  Proof. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Function table                                              *)
  (* ============================================================== *)

  Definition p256_curve_add_inplace_func : function_t :=
    curve_add_inplace_general_func.
  Definition p256_curve_double_func : function_t :=
    curve_double_general_func.
  Definition p256_opp_inplace_func : function_t :=
    opp_inplace_func.
  Definition p256_store_zero_func : function_t :=
    store_zero_from_word_func.

  (** The wNAF driver.  Same shape as [bn254_wnaf_single_func]
      (wNAF_GLV_Func.v) with 257 iterations; [felem_size_in_bytes]
      is kept symbolic so the body matches [wnaf_single_full]'s
      statement syntactically ([p256_felem_size_in_bytes_eq] gives 32
      for extraction). *)
  Definition p256_wnaf_single_func : function_t :=
    ("p256_wnaf_single",
     (["outx"; "outy"; "outz";
       "table_P"; "digits_k";
       "auxx"; "auxy"; "auxz"],
      []%list,
      wnaf_single_func_body "curve_add" "curve_double" "store_zero"
        felem_copy opp (Z.of_nat p256_num_digits) felem_size_in_bytes
        "digits_k" "table_P")).

  (** Function-table membership bundle used by the discharges below.
      The five field leaves (mul/add/sub/opp/from_word) are the
      fiat-crypto syntheses of p256_prime.v and enter through their
      [spec_of_*] instances rather than by body. *)
  Definition p256_wnaf_table_ok (functions : Semantics.env) : Prop :=
    map.get functions "curve_add_general" = Some p256_curve_add_general_func
    /\ map.get functions "p256_three_b" = Some p256_three_b_func
    /\ map.get functions "p256_a_const" = Some p256_a_const_func
    /\ map.get functions "curve_add" = Some (snd p256_curve_add_inplace_func)
    /\ map.get functions "curve_double" = Some (snd p256_curve_double_func)
    /\ map.get functions "store_zero" = Some (snd p256_store_zero_func)
    /\ map.get functions felem_copy = Some p256_coord_felem_copy.

  Definition p256_wnaf_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_BinOp bin_mul functions
    /\ spec_of_BinOp bin_add functions
    /\ spec_of_BinOp bin_sub functions
    /\ spec_of_UnOp un_opp functions
    /\ spec_of_from_word functions.

  (* ============================================================== *)
  (* §3. Arithmetic discharges at len = 257                          *)
  (* ============================================================== *)

  Definition p256_digits (k : Z) : list Z := wnaf_digits 4 k p256_num_digits.

  Lemma p256_digits_length : forall k, length (p256_digits k) = p256_num_digits.
  Proof. intros. apply wnaf_digits_length. Qed.

  Lemma p256_digits_wsum : forall k,
    0 <= k < 2 ^ 256 -> wsum (p256_digits k) = k.
  Proof.
    intros k Hk. unfold p256_digits, p256_num_digits.
    apply wnaf_correct; [lia | lia |].
    replace (Z.of_nat (257 - 1)) with 256 by lia. exact Hk.
  Qed.

  Lemma p256_digits_Hws_nn : forall k,
    0 <= k < 2 ^ 256 ->
    forall n, (n <= p256_num_digits)%nat ->
    0 <= weighted_sum (skipn n (p256_digits k)) 0.
  Proof.
    intros k Hk n Hn. unfold p256_digits, p256_num_digits in *.
    apply (weighted_sum_skipn_wnaf_nonneg 4 k 257 n);
      [lia | split; [lia|]; replace (Z.of_nat (257 - 1)) with 256 by lia; lia
       | exact Hn].
  Qed.

  Lemma p256_digits_bounded : forall k,
    0 <= k ->
    forall i, (i < p256_num_digits)%nat -> -7 <= nth i (p256_digits k) 0 <= 7.
  Proof.
    intros k Hk i Hi. unfold p256_digits, p256_num_digits in *.
    assert (Hb : Z.abs (nth i (wnaf_digits 4 k 257) 0) < 2 ^ (Z.of_nat 4 - 1)).
    { apply (wnaf_digit_bound 4 k 257 i).
      - lia.
      - exact Hk.
      - apply nth_error_nth' with (d := 0). rewrite wnaf_digits_length. exact Hi. }
    change (Z.of_nat 4 - 1) with 3 in Hb. simpl (2^3) in Hb.
    apply Z.abs_lt in Hb. lia.
  Qed.

  (** Non-zero wNAF digits are odd (script of
      [BLS12_wNAF_GLV_Instance.wnaf_digits_odd] with 129 -> 257). *)
  Lemma p256_digits_odd : forall k,
    0 <= k ->
    forall i, (i < p256_num_digits)%nat ->
    Z.odd (nth i (p256_digits k) 0) = true \/ nth i (p256_digits k) 0 = 0.
  Proof.
    intros k Hk i Hi. unfold p256_digits, p256_num_digits in *.
    destruct (Z.eq_dec (nth i (wnaf_digits 4 k 257) 0) 0) as [Hz|Hnz].
    - right. exact Hz.
    - left.
      revert k Hk i Hi Hnz. induction (257)%nat as [|len IH]; intros k Hk i Hi Hnz.
      { exfalso. lia. }
      simpl wnaf_digits. destruct i as [|i'];
      [ simpl nth in Hnz |- *; unfold wnaf_digit in Hnz |- *;
        destruct (Z.odd k) eqn:Hok; [|exfalso; apply Hnz; reflexivity];
        set (m := k mod 2 ^ Z.of_nat 4) in *;
        assert (Hmodd : Z.odd m = true)
          by (subst m; pose proof (Z.div_mod k (2^Z.of_nat 4) ltac:(simpl;lia)) as Hkdm;
              assert (Z.odd (k mod 2^Z.of_nat 4) = Z.odd k)
                by (rewrite Hkdm at 2; rewrite Z.odd_add, Z.odd_mul; simpl; ring_simplify; reflexivity);
              congruence);
        destruct (m >=? 2 ^ (Z.of_nat 4 - 1));
        [ rewrite <- Z.negb_even, Z.even_sub; simpl (Z.even (2 ^ Z.of_nat 4));
          rewrite <- Z.negb_even in Hmodd; apply Bool.negb_true_iff in Hmodd;
          rewrite Hmodd; reflexivity
        | exact Hmodd ]
      | simpl nth in Hnz |- *;
        apply IH; [apply wnaf_shift_nonneg; lia | lia | exact Hnz] ].
  Qed.

  Lemma p256_Hnbound : Z.of_nat p256_num_digits < 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_Hfs_pos : 0 < felem_size_in_bytes.
  Proof. rewrite p256_felem_size_in_bytes_eq. lia. Qed.

  Lemma p256_Hfs_small : 12 * felem_size_in_bytes < 2 ^ 64.
  Proof. rewrite p256_felem_size_in_bytes_eq. vm_compute. reflexivity. Qed.

  (** Digit load: the generic lemma of BLS12_wNAF_GLV_Instance.v §2
      already has the required shape (its [DigitArray] is the one of
      BLS12_wNAF_ProcessDigits.v used by the chain). *)
  Lemma p256_Hdigit_load : forall (dk : list Z) (n : nat) (base : word)
      (m : BasicC64Semantics.mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word BasicC64Semantics.mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0)).
  Proof.
    intros. eapply digit_load_from_array; eassumption.
  Qed.

  (* ============================================================== *)
  (* §4. Callee-spec discharges from the table                       *)
  (* ============================================================== *)

  (** The derived add meets its FElem-level spec
      (CurveAddGeneralA_P256_Loaders.p256_curve_add_general_full). *)
  Lemma p256_rcb_add_general_spec :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions (Hadd & Htb & Ha & _ & _ & _ & _) (Hmul & Hfadd & Hsub & _ & _).
    eapply p256_curve_add_general_full; eassumption.
  Qed.

  Lemma p256_felem_copy_spec :
    forall functions,
      p256_wnaf_table_ok functions ->
      spec_of_felem_copy functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & _ & Hcopy).
    (* [p256_felem_copy_ok : program_logic_goal_for_function! p256_coord_felem_copy]
       unfolds to [map.get functions felem_copy = Some p256_coord_felem_copy ->
       spec_of_felem_copy functions] (bedrock2 program_logic_goal_for). *)
    exact (p256_felem_copy_ok functions Hcopy).
  Qed.

  (** [curve_add_g] of NistWnafWrappers.v at the P-256 constants is
      [p256_curve_add] (both are [curve_add_general_triple] at
      [feval (proj1_sig p256_a_felem)] / [feval (proj1_sig p256_three_b_felem)]). *)
  Lemma p256_curve_add_g_eq :
    curve_add_g p256_three_b_felem p256_a_felem = p256_curve_add.
  Proof. reflexivity. Qed.

  Lemma p256_HCurveAddInplace :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_curve_add_inplace_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & Hca & _ & _ & _).
    eapply curve_add_inplace_general_ok;
      eauto using p256_rcb_add_general_spec, p256_felem_copy_spec.
  Qed.

  Lemma p256_HCurveDouble :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      spec_of_curve_double_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & Hcd & _ & _).
    eapply curve_double_general_ok;
      eauto using p256_rcb_add_general_spec, p256_felem_copy_spec.
  Qed.

  Lemma p256_HStoreZero :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        p256_field_parameters p256_frep functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & Hsz & _) (_ & _ & _ & _ & Hfw).
    (* After Section discharge [store_zero_from_word_ok] takes, before
       [functions]: 6 implicits (width, BW, word, mem, locals,
       ext_spec), the four ok-hypotheses (word.ok, map.ok mem,
       map.ok locals, ext_spec.ok), field_parameters +
       FieldParameters_ok, field_representation +
       FieldRepresentation_ok, the bounds equation, and the two
       constant felems of the Section (three_b, a_const — unused by
       this lemma's conclusion, so any well-typed felems serve).
       Hence the fully applied form below; [_] for the ten class
       arguments, which unification and the ambient Existing Instances
       resolve.  [p256_store_zero_func] is [store_zero_from_word_func]
       at these instances, so [Hsz] matches the table premise by
       conversion. *)
    first
      [ exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 p256_bounds_eq p256_three_b_felem p256_a_felem
                 functions Hsz Hfw)
      | eapply store_zero_from_word_ok with (functions := functions);
        [ solve [ typeclasses eauto | exact _ ] ..
        | exact p256_bounds_eq
        | exact p256_three_b_felem
        | exact p256_a_felem
        | exact Hsz
        | exact Hfw ]
      | eapply store_zero_from_word_ok with (functions := functions);
        repeat first
          [ exact p256_bounds_eq
          | exact p256_three_b_felem
          | exact p256_a_felem
          | exact Hsz
          | exact Hfw
          | solve [ typeclasses eauto | exact _ ] ] ].
  Qed.

  (* ============================================================== *)
  (* §5. End-to-end statement                                        *)
  (* ============================================================== *)

  (** Leibniz group laws on projective triples (plan G6).  Bundled so
      that the final theorem names the residual trust in one place.
      These do NOT hold for the raw RCB formula; they are the
      hypotheses that the phase-2 projective-equivalence refactor
      replaces. *)
  Definition p256_leibniz_group_laws : Prop :=
    (forall x y z, p256_curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z))
    /\ (forall x y z, p256_curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z))
    /\ (forall P Q R, p256_curve_add P (p256_curve_add Q R)
                      = p256_curve_add (p256_curve_add P Q) R)
    /\ (forall P Q, p256_curve_add P Q = p256_curve_add Q P)
    /\ (forall P, p256_curve_add P (p256_point_opp P) = (Fzero,Fone,Fzero)).

  (** Table correctness in the chain's (Leibniz) form. *)
  Definition p256_table_ok (Px Py Pz : F) (table_entries : list (F * F * F)) : Prop :=
    length table_entries = 4%nat /\
    forall i, (i < 4)%nat ->
      nth i table_entries (Fzero,Fone,Fzero) = p256_scmul (2 * i + 1) (Px, Py, Pz).

  (** Horner step, from [wNAF_Single_HornerAlgebra.horner_step_single]
      (whose [sm] is definitionally [p256_scmul] and whose
      [digit_point_local] is definitionally ProcessDigits' [digit_point]
      at [point_opp := p256_point_opp]). *)
  Lemma p256_Hhorner_step :
    p256_leibniz_group_laws ->
    forall k, 0 <= k < 2 ^ 256 ->
    forall Px Py Pz table_entries,
      p256_table_ok Px Py Pz table_entries ->
      forall n (Ox Oy Oz : F),
        (n < p256_num_digits)%nat ->
        let ws_old := weighted_sum (skipn (S n) (p256_digits k)) 0 in
        (Ox,Oy,Oz) = p256_scmul (Z.to_nat (2 * ws_old)) (Px,Py,Pz) ->
        let d := nth n (p256_digits k) 0 in
        (if d =? 0 then (Ox,Oy,Oz)
         else p256_curve_add (Ox,Oy,Oz) (digit_point d table_entries))
        = p256_scmul (Z.to_nat (weighted_sum (skipn n (p256_digits k)) 0)) (Px,Py,Pz).
  Proof.
    intros (Hid_r & Hid_l & Hassoc & Hcomm & Hinv) k Hk Px Py Pz tab (Hlen & Hcorr).
    (* Intended script:
         intros n Ox Oy Oz Hn ws_old Hacc d.
         change (digit_point d tab) with
           (digit_point_local Fzero Fone p256_point_opp d tab).
         apply (horner_step_single Fzero Fone p256_curve_add p256_point_opp
                  Hid_r Hid_l Hassoc Hcomm Hinv (p256_digits k) Px Py Pz tab
                  Hlen Hcorr
                  (fun i Hi => p256_digits_odd k ltac:(lia) i ltac:(rewrite p256_digits_length in Hi; exact Hi))
                  (fun i Hi => p256_digits_bounded k ltac:(lia) i ltac:(rewrite p256_digits_length in Hi; exact Hi))
                  (fun n' Hn' => p256_digits_Hws_nn k Hk n' ltac:(rewrite p256_digits_length in Hn'; exact Hn'))
                  n Ox Oy Oz ltac:(rewrite p256_digits_length; exact Hn) Hacc).
       The explicit-argument order of [horner_step_single] (Section
       variables of wNAF_Single_HornerAlgebra.v) must be confirmed with
       a compiler. *)
  Admitted.

  (** The citable statement.  Under the function table and the field
      leaf specs, plus the three residual hypothesis groups (G5, G6,
      G7), the body of [p256_wnaf_single_func] computes [k * P] in the
      chain's sense ([p256_scmul (Z.to_nat k) P]). *)
  Theorem p256_wnaf_single_full :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
      (* G5: aliased negation on the FieldParameters name [opp]. *)
      (forall p (Y : F) R0 tr0 m0,
          (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
          Semantics.call functions opp tr0 m0 [p; p]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')) ->
      (* G6 *)
      p256_leibniz_group_laws ->
      forall k, 0 <= k < 2 ^ 256 ->
      forall Px Py Pz table_entries,
        (* G7: the caller's table holds [1P;3P;5P;7P] *)
        p256_table_ok Px Py Pz table_entries ->
      forall pOx pOy pOz pAx pAy pAz pT pDK
        (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
        (Rinner : BasicC64Semantics.mem -> Prop) tr m l,
      map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
      map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
      map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
      map.get l "table_P" = Some pT ->
      map.get l "digits_k" = Some pDK ->
      (* G7: the caller's digit array holds [wnaf_digits 4 k 257] *)
      (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
       ⋆ DigitArray pDK (p256_digits k) ⋆ Table4 pT table_entries
       ⋆ Rinner) m ->
      WeakestPrecondition.cmd functions
        (snd (snd p256_wnaf_single_func))
        tr m l
        (fun t m' l' =>
          exists Rx Ry Rz Ax' Ay' Az',
          (Rx,Ry,Rz) = p256_scmul (Z.to_nat k) (Px,Py,Pz)
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
              ⋆ DigitArray pDK (p256_digits k) ⋆ Table4 pT table_entries
              ⋆ Rinner) m').
  Proof.
    intros functions Htab Hleaf HOppInplace Hlaws k Hk Px Py Pz tab Htable.
    pose proof Hlaws as (Hid_r & Hid_l & Hassoc & Hcomm & Hinv).
    pose proof Hleaf as (_ & _ & _ & Hopp & _).
    (* Intended script:
         intros; cbv [p256_wnaf_single_func snd].
         eapply (wnaf_single_full
                   (curve_add := p256_curve_add)
                   (curve_add_name := "curve_add")
                   (curve_double_name := "curve_double")
                   (dk := p256_digits k) (num_iters := p256_num_digits)
                   (table_entries := tab) (Px := Px) (Py := Py) (Pz := Pz)
                   (k := k)); try eassumption.
         - exact p256_bounds_eq.
         - exact (p256_HCurveDouble functions Htab Hleaf).      (* HCurveDouble *)
         - exact (p256_HCurveAddInplace functions Htab Hleaf).  (* HCurveAddInplace *)
         - exact (felem_copy_HFelemCopy _ (p256_felem_copy_spec functions Htab)).
         - exact (opp_HOpp p256_bounds_eq _ Hopp).             (* HOpp *)
         - exact HOppInplace.
         - exact (p256_HStoreZero functions Htab Hleaf).
         - exact (p256_digits_length k).
         - exact p256_Hnbound.
         - exact (p256_digits_bounded k ltac:(lia)).
         - exact p256_Hfs_pos.  - exact p256_Hfs_small.
         - exact (proj1 Htable).
         - exact (p256_Hdigit_load (p256_digits k)).
         - exact (p256_digits_Hws_nn k Hk).
         - exact (p256_Hhorner_step Hlaws k Hk Px Py Pz tab Htable).
         - exact (p256_digits_wsum k Hk).  - lia.
       [wnaf_single_full]'s Section variables (BN254_wNAF_Instance.v)
       become explicit arguments in declaration order; the named-argument
       form above avoids committing to that order but still needs a
       compiler to confirm the names survive Section discharge. *)
  Admitted.

End P256_wNAF.

(** * Adapter-lemma inventory (statements drafted, proofs Admitted)

    NistWnafWrappers.v
      curve_add_inplace_general_ok   spec_of_rcb_add_general + spec_of_felem_copy
                                      -> HCurveAddInplace shape at "curve_add"
      curve_double_general_ok        same inputs -> HCurveDouble shape at "curve_double"
      felem_copy_HFelemCopy          spec_of_felem_copy (bytes dst) -> FElem-dst shape
      opp_HOpp                       spec_of_UnOp un_opp -> HOpp shape (loose->tight by Hbounds_eq)
      opp_inplace_ok                 spec_of_UnOp un_opp + spec_of_felem_copy
                                      -> both negation shapes at "opp_inplace" (needs G5 rename)
      store_zero_from_word_ok        spec_of_from_word -> StoreZero.spec_of_store_zero
    This file
      p256_Hhorner_step              horner_step_single at p256 (Leibniz laws as hypothesis)
      p256_wnaf_single_full          composition into wnaf_single_full *)
