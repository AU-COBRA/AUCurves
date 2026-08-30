(** * BN254 callee-spec discharges for the single-scalar wNAF chain.

    [BN254_wNAF_Instance.wnaf_single_full] and
    [BN254_wNAF_Laws.bn254_wnaf_single_full] take their point-operation
    callees as Section hypotheses:

      HCurveDouble, HCurveAddInplace, HFelemCopy, HOpp, HOppInplace,
      HStoreZero, Hdigit_load.

    This file discharges the ones that follow from a BN254 function
    table plus the fiat-crypto leaf specs, using the curve-generic
    wrapper lemmas of [NistWnafWrappers.v] — the same route
    [P256_wNAF_Instance.v] §4 takes for P-256.

    Discharged here (all seven):
      Hdigit_load       [digit_load_from_array]   (no table entry needed)
      HStoreZero        [store_zero_from_word_ok] + "store_zero" entry
      HOpp              [opp_inplace_ok] fst      + "opp_inplace" entry
      HOppInplace       [opp_inplace_ok] snd      + "opp_inplace" entry
      HFelemCopy        [felem_copy_HFelemCopy]   + spec_of_felem_copy
      HCurveDouble      [curve_double_general_ok] + "curve_double" entry
      HCurveAddInplace  [curve_add_inplace_general_ok] + "curve_add" entry

    The last two need the derived general-a RCB addition at the
    bedrock2 name "curve_add_general", i.e.
    [spec_of_rcb_add_general three_b a_const functions].  Section
    [BN254_GeneralA] below supplies the missing BN254 instantiation of
    [CurveAddGeneralA.v] -- the two constant felems (a = 0, 3b = 9),
    the two loader functions "bn254_three_b" and "bn254_a_const" with
    their loader-spec proofs, and [bn254_curve_add_general_func] --
    following [CurveAddGeneralA_P256.v] SS1-SS4 and
    [CurveAddGeneralA_P256_Loaders.v] verbatim, which transport
    because BN254 is a 4-limb 64-bit word-by-word Montgomery
    representation like P-256.

    Function-table note.  [bn254_curve_op_funcs] of
    [BN254_CurveOps.v] does NOT supply the entries these two lemmas
    need.  It binds "curve_add" to [ladderstep_body "bn254_three_b"]
    and "curve_double_a0" to [rcb_double_a0_body "bn254_three_b"];
    the wrappers need "curve_add" bound to
    [snd curve_add_inplace_general_func], "curve_double" bound to
    [snd curve_double_general_func], and three ADDITIONAL entries
    "curve_add_general", "bn254_three_b", "bn254_a_const".  See
    [bn254_general_table] below for the exact list. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Instance.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Bedrock.Field.Synthesis.Examples.bn254_three_b.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BN254_Callees.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).

  Lemma bn254_bounds_eq :
    loose_bounds (FieldRepresentation:=bn254_frep)
    = tight_bounds (FieldRepresentation:=bn254_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §1. The wrapper functions at BN254                              *)
  (* ============================================================== *)

  Definition bn254_opp_inplace_func : function_t := opp_inplace_func.
  Definition bn254_store_zero_func : function_t := store_zero_from_word_func.

  (** Table membership for the two wrapper bodies this file needs.
      The wNAF driver calls the negation at the parametric [opp_name],
      which for BN254 is "opp_inplace" (the aliasing-tolerant wrapper),
      and the identity store at "store_zero". *)
  Definition bn254_wnaf_wrapper_table (functions : Semantics.env) : Prop :=
    map.get functions "store_zero" = Some (snd bn254_store_zero_func)
    /\ map.get functions "opp_inplace" = Some (snd bn254_opp_inplace_func).

  (** The synthesized leaves the wrappers call.  [spec_of_UnOp un_opp]
      and [spec_of_from_word] come from the fiat-crypto synthesis at
      [bn254_frep]; [spec_of_felem_copy] from
      [Examples.bn254_felem_copy.felem_copy_ok]. *)
  Definition bn254_wnaf_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_UnOp un_opp functions
    /\ spec_of_from_word functions
    /\ spec_of_felem_copy functions.

  (* ============================================================== *)
  (* §2. Discharges                                                  *)
  (* ============================================================== *)

  (** [Hdigit_load] — no table entry, no leaf spec: the digit array is
      a plain word array and the load is [digit_load_from_array]. *)
  Lemma bn254_Hdigit_load : forall (dk : list Z) (n : nat) (base : word)
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

  (** [HStoreZero]. *)
  Lemma bn254_HStoreZero :
    forall functions,
      bn254_wnaf_wrapper_table functions ->
      bn254_wnaf_leaf_specs functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        bn254_field_parameters bn254_frep functions.
  Proof.
    intros functions (Hsz & _) (_ & Hfw & _).
    (* Fully applied: [store_zero_from_word_ok] takes, after Section
       discharge, six bedrock2 parameters, four ok-classes, the field
       parameters and representation, [FieldRepresentation_ok], then
       [functions] and the two premises.  Written as [exact] rather than
       [eapply] so the cost is one conversion, not a conclusion search. *)
    exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             functions Hsz Hfw).
  Qed.

  (** [HOpp] and [HOppInplace], both at the name "opp_inplace". *)
  Lemma bn254_HOppInplace_spec :
    forall functions,
      bn254_wnaf_wrapper_table functions ->
      bn254_wnaf_leaf_specs functions ->
      spec_of_opp_inplace functions.
  Proof.
    intros functions (_ & Hoi) (Hopp & _ & Hcopy).
    exact (@opp_inplace_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             bn254_bounds_eq functions Hoi Hopp Hcopy).
  Qed.

  (** [HFelemCopy]. *)
  Lemma bn254_HFelemCopy :
    forall functions,
      bn254_wnaf_leaf_specs functions ->
      forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
        Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) pSrc v
             ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m').
  Proof.
    intros functions (_ & _ & Hcopy).
    exact (felem_copy_HFelemCopy functions Hcopy).
  Qed.

End BN254_Callees.

(* ================================================================== *)
(** * BN254 instantiation of the general-a RCB addition.

    [NistWnafWrappers.curve_double_general_ok] and
    [curve_add_inplace_general_ok] both need
    [spec_of_rcb_add_general three_b a_const functions], i.e. a BN254
    instantiation of [CurveAddGeneralA.v].  This section supplies it,
    following [CurveAddGeneralA_P256.v] SS1-SS4 and
    [CurveAddGeneralA_P256_Loaders.v]: BN254 is a 4-limb 64-bit
    word-by-word Montgomery representation, exactly like P-256, so the
    loader bodies and their proofs transport verbatim with the two
    constants changed to a = 0 and 3b = 9. *)
(* ================================================================== *)

Section BN254_GeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* S1. Curve constants: a = 0, 3b = 9.                             *)
  (* ============================================================== *)

  (** Montgomery limbs of 3b = 9, from [bn254_three_b.three_b_mont]
      (the same witness [BN254_G1] and [BN254_CurveOps] use). *)
  Definition bn254_tb0 : Z := Eval vm_compute in nth 0 bn254_three_b.three_b_mont 0.
  Definition bn254_tb1 : Z := Eval vm_compute in nth 1 bn254_three_b.three_b_mont 0.
  Definition bn254_tb2 : Z := Eval vm_compute in nth 2 bn254_three_b.three_b_mont 0.
  Definition bn254_tb3 : Z := Eval vm_compute in nth 3 bn254_three_b.three_b_mont 0.

  Definition bn254_three_b_words : list word :=
    [word.of_Z bn254_tb0; word.of_Z bn254_tb1;
     word.of_Z bn254_tb2; word.of_Z bn254_tb3].

  (** a = 0 for BN254 (y^2 = x^3 + 3); the Montgomery encoding of 0 is
      the all-zero limb list. *)
  Definition bn254_a_words : list word :=
    [word.of_Z 0; word.of_Z 0; word.of_Z 0; word.of_Z 0].

  Lemma bn254_three_b_words_length :
    length bn254_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bn254_a_words_length :
    length bn254_a_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition bn254_three_b_felem : felem :=
    exist _ bn254_three_b_words bn254_three_b_words_length.
  Definition bn254_a_felem : felem :=
    exist _ bn254_a_words bn254_a_words_length.

  Lemma bn254_three_b_words_bounded :
    bounded_by loose_bounds bn254_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma bn254_a_words_bounded :
    bounded_by loose_bounds bn254_a_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma bn254_three_b_feval :
    feval (proj1_sig bn254_three_b_felem) = F.of_Z M_pos 9.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma bn254_a_feval :
    feval (proj1_sig bn254_a_felem) = F.of_Z M_pos 0.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* S2. The two constant-loader bedrock2 functions.                 *)
  (*     Pattern: CurveAddGeneralA_P256.v S3, 4 limbs of 64 bits.    *)
  (* ============================================================== *)

  Definition bn254_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal bn254_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal bn254_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal bn254_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal bn254_tb3)))).

  Definition bn254_a_const_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal 0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal 0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal 0))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal 0)))).

  Definition bn254_three_b_func : Syntax.func :=
    (["out"], [], bn254_three_b_loader_body).
  Definition bn254_a_const_func : Syntax.func :=
    (["out"], [], bn254_a_const_loader_body).

  (* ============================================================== *)
  (* S3. The derived general-a addition body at BN254.               *)
  (* ============================================================== *)

  Definition bn254_curve_add_general_func : Syntax.func :=
    rcb_add_general_body "bn254_three_b" "bn254_a_const".

  (* ============================================================== *)
  (* S4. Loader-spec proofs.                                         *)
  (*     Script of CurveAddGeneralA_P256_Loaders.v, unchanged: BN254 *)
  (*     is a 4-limb 64-bit WBW Montgomery representation too.       *)
  (* ============================================================== *)

  Lemma bn254_three_b_loader_ok :
    forall functions,
      map.get functions "bn254_three_b" = Some bn254_three_b_func ->
      spec_of_three_b_loader bn254_three_b_felem "bn254_three_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_three_b_loader].
    intros pout outold Rout tr mem0 Hpre.
    (* 1. Decompose the input FElem into four scalars. *)
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    (* 2. Enter the function body and execute the four stores. *)
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func bn254_three_b_func bn254_three_b_loader_body].
    repeat straightline.
    (* 3. Postcondition. *)
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := bn254_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact bn254_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [bn254_three_b_felem bn254_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  Lemma bn254_a_loader_ok :
    forall functions,
      map.get functions "bn254_a_const" = Some bn254_a_const_func ->
      spec_of_a_loader bn254_a_felem "bn254_a_const" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_a_loader].
    intros pout outold Rout tr mem0 Hpre.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func bn254_a_const_func bn254_a_const_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := bn254_a_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact bn254_a_words_bounded
      | |- _ => idtac
      end.
    cbv [bn254_a_felem bn254_a_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  (** [spec_of_rcb_add_general] for the instantiated body, from the
      generic derivation correctness [rcb_add_general_correct].  Fully
      applied (no [eapply]) so the cost is one conversion; measured
      9 ms. *)
  Lemma bn254_curve_add_general_ok :
    forall functions,
      map.get functions "curve_add_general"
      = Some bn254_curve_add_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_three_b_loader bn254_three_b_felem "bn254_three_b" functions ->
      spec_of_a_loader bn254_a_felem "bn254_a_const" functions ->
      spec_of_rcb_add_general bn254_three_b_felem bn254_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold bn254_curve_add_general_func in Henv.
    refine
      (rcb_add_general_correct bn254_bounds_eq
         bn254_three_b_felem "bn254_three_b" bn254_a_felem "bn254_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    exact Henv.
  Qed.

  (* ============================================================== *)
  (* S5. HCurveDouble and HCurveAddInplace at BN254.                 *)
  (* ============================================================== *)

  (** Table membership for the general-a chain.  Note the two wrapper
      entries: the wNAF ABI names "curve_add" and "curve_double" must
      carry the NistWnafWrappers BODIES (stack temporaries + copies),
      NOT the ladderstep of [BN254_G1] nor the RCB Algorithm 9 body of
      [BN254_CurveOps].  The derived complete addition sits underneath
      at "curve_add_general". *)
  Definition bn254_general_table (functions : Semantics.env) : Prop :=
    map.get functions "curve_add_general" = Some bn254_curve_add_general_func
    /\ map.get functions "bn254_three_b" = Some bn254_three_b_func
    /\ map.get functions "bn254_a_const" = Some bn254_a_const_func
    /\ map.get functions "curve_add" = Some (snd curve_add_inplace_general_func)
    /\ map.get functions "curve_double" = Some (snd curve_double_general_func).

  Definition bn254_general_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_BinOp bin_mul functions
    /\ spec_of_BinOp bin_add functions
    /\ spec_of_BinOp bin_sub functions
    /\ spec_of_felem_copy functions.

  (** The derived general-a addition meets its FElem-level spec. *)
  Lemma bn254_rcb_add_general_spec :
    forall functions,
      bn254_general_table functions ->
      bn254_general_leaf_specs functions ->
      spec_of_rcb_add_general bn254_three_b_felem bn254_a_felem functions.
  Proof.
    intros functions (Hag & Htb & Ha & _ & _) (Hmul & Hadd & Hsub & _).
    exact (bn254_curve_add_general_ok functions Hag Hmul Hadd Hsub
             (bn254_three_b_loader_ok functions Htb)
             (bn254_a_loader_ok functions Ha)).
  Qed.

  (** [HCurveDouble] of [BN254_wNAF_Instance.v], at
      [curve_double_name := "curve_double"] and
      [curve_add := curve_add_g bn254_three_b_felem bn254_a_felem].

      The body is the ADD-WITH-COPIES wrapper of [NistWnafWrappers.v]:
      in-place doubling calls the general COMPLETE addition with a copy
      of P as second operand, because the derived spec forbids
      P1 = P2 aliasing.  Copies remove the aliasing hazard and
      completeness removes any on-curve side condition -- which is why
      this route, and not [PointDoubleA0.rcb_double_a0_correct]
      (Algorithm 9 is not in-place safe: D8 writes Xout and D9 writes
      Yout while D16 still reads X1, Y1; and its bridge to the addition
      holds only on the curve). *)
  Lemma bn254_HCurveDouble :
    forall functions,
      bn254_general_table functions ->
      bn254_general_leaf_specs functions ->
      spec_of_curve_double_general bn254_three_b_felem bn254_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & Hcd).
    pose proof (proj2 (proj2 (proj2 Hleaf))) as Hcopy.
    (* Fully applied: 13 class arguments, then the two constants,
       [functions], and the three premises.  [eapply] against this
       conclusion is the slow pattern this file avoids. *)
    exact (@curve_double_general_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             bn254_three_b_felem bn254_a_felem functions Hcd
             (bn254_rcb_add_general_spec functions Htab Hleaf) Hcopy).
  Qed.

  (** [HCurveAddInplace] of [BN254_wNAF_Instance.v], at
      [curve_add_name := "curve_add"]. *)
  Lemma bn254_HCurveAddInplace :
    forall functions,
      bn254_general_table functions ->
      bn254_general_leaf_specs functions ->
      spec_of_curve_add_inplace_general bn254_three_b_felem bn254_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & Hca & _).
    pose proof (proj2 (proj2 (proj2 Hleaf))) as Hcopy.
    exact (@curve_add_inplace_general_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             bn254_three_b_felem bn254_a_felem functions Hca
             (bn254_rcb_add_general_spec functions Htab Hleaf) Hcopy).
  Qed.

  (** The [curve_add] the chain gets from this route, spelled out: the
      general-a RCB complete addition at a = 0 and 3b = 9, i.e. BN254's
      y^2 = x^3 + 3.  (Analogue of [P256_wNAF_Instance.p256_curve_add_g_eq].) *)
  Lemma bn254_curve_add_g_eq :
    curve_add_g bn254_three_b_felem bn254_a_felem
    = curve_add_general_triple (F.of_Z M_pos 0) (F.of_Z M_pos 9).
  Proof.
    unfold curve_add_g.
    rewrite bn254_a_feval, bn254_three_b_feval. reflexivity.
  Qed.

End BN254_GeneralA.
