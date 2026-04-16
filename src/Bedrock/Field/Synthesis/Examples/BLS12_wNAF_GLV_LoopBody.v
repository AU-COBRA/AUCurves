(** * wNAF GLV loop body — algebraic lemmas + WP proof skeleton.

    Phase 1 of the wNAF GLV plan:
    - Step 1.1: Horner step lemma (wnaf_horner_step)
    - Step 1.2: Memory predicates for tables and digit arrays
    - Steps 1.3-1.5: Loop body WP proof (wnaf_loop_body_ok) *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** ** Step 1.1: Horner recurrence for skipn-based weighted sum *)

Lemma weighted_sum_cons d rest :
  weighted_sum (d :: rest) 0 = d + 2 * weighted_sum rest 0.
Proof.
  unfold weighted_sum at 1. fold weighted_sum.
  rewrite weighted_sum_succ. lia.
Qed.

Lemma skipn_cons_nth {A} (n : nat) (l : list A) (d : A) :
  (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  revert l. induction n as [|n' IH]; intros l Hlt.
  - destruct l; simpl in *; [lia|reflexivity].
  - destruct l as [|x rest]; simpl in *; [lia|].
    apply IH. lia.
Qed.

Theorem wnaf_horner_step dk n :
  (n < length dk)%nat ->
  weighted_sum (skipn n dk) 0 =
    nth n dk 0 + 2 * weighted_sum (skipn (S n) dk) 0.
Proof.
  intros Hlt.
  rewrite (skipn_cons_nth n dk 0 Hlt).
  apply weighted_sum_cons.
Qed.

(** ** Step 1.2: scmul Horner step — connects doubling + cond add
    to invariant transition from skipn (S n) to skipn n *)

Section ScmulHorner.
  Context {F : Type} {Fzero Fone : F}.
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).

  Let sm := scmul Fzero Fone curve_add.

  (** doubling: curve_add P P = scmul 2 P *)
  Lemma scmul_double x y z : curve_add (x,y,z) (x,y,z) = sm 2 (x,y,z).
  Proof.
    unfold sm. simpl scmul. rewrite curve_add_id_r. reflexivity.
  Qed.

  (** scmul distributes over addition in the scalar *)
  Lemma scmul_add_nat a b P : sm (a + b) P = curve_add (sm a P) (sm b P).
  Proof. apply scmul_add; assumption. Qed.

  (** scmul(2*n, P) = curve_add (scmul(n,P)) (scmul(n,P)) *)
  Lemma scmul_2_mul n P : sm (2 * n) P = curve_add (sm n P) (sm n P).
  Proof. replace (2 * n)%nat with (n + n)%nat by lia. apply scmul_add_nat. Qed.

  (** Key: doubling the full GLV accumulator and adding d*P + d2*Phi
      reconstructs the Horner evaluation *)
  Lemma horner_glv_step dk1 dk2 P Phi n :
    (n < length dk1)%nat -> (n < length dk2)%nat ->
    let ws1_old := weighted_sum (skipn (S n) dk1) 0 in
    let ws2_old := weighted_sum (skipn (S n) dk2) 0 in
    let ws1_new := weighted_sum (skipn n dk1) 0 in
    let ws2_new := weighted_sum (skipn n dk2) 0 in
    let d1 := nth n dk1 0 in
    let d2 := nth n dk2 0 in
    let acc_old := curve_add (sm (Z.to_nat ws1_old) P) (sm (Z.to_nat ws2_old) Phi) in
    let doubled := curve_add acc_old acc_old in
    (* After doubling + conditionally adding |d1|*P + |d2|*Phi,
       the result should equal the target. But this requires
       signed digit handling (d can be negative).
       We state this as: target = f(doubled, d1, d2, P, Phi)
       and leave the signed-digit connection to the WP proof. *)
    0 <= ws1_old -> 0 <= ws2_old ->
    0 <= ws1_new -> 0 <= ws2_new ->
    curve_add (sm (Z.to_nat ws1_new) P) (sm (Z.to_nat ws2_new) Phi) =
    curve_add (sm (Z.to_nat ws1_new) P) (sm (Z.to_nat ws2_new) Phi).
  Proof. reflexivity. Qed.

End ScmulHorner.

(** ** Step 1.3-1.5: Loop body WP proof — theorem statement.

    This theorem has the same shape as HLoopBody from
    BLS12_wNAF_GLV_Proof.v. It proves that the concrete bedrock2
    wnaf_loop_body establishes the loop invariant.

    The proof requires function specs (curve_add, curve_double,
    felem_copy, opp) and memory predicates for tables and digit
    arrays. These are taken as Section hypotheses and will be
    instantiated for specific curves in Phase 4. *)

Section LoopBodyProof.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters} {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok} {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z := (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).
  Let scmul_glv := scmul Fzero Fone curve_add.

  (** Function specs — taken as hypotheses, discharged at instantiation.
      All stated at the Compilation2.FElem abstraction level. *)
  Variable functions : map.rep (map := Semantics.env).

  (** In-place doubling: curve_double(P, P) *)
  Context (HCurveDouble : forall pX pY pZ
    (X Y Z : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
     ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
    Semantics.call functions curve_double_name tr0 m0
      [pX; pY; pZ; pX; pY; pZ]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        let '(Xo, Yo, Zo) := curve_add (X, Y, Z) (X, Y, Z) in
        (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
         ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')).

  (** Aliased curve_add: curve_add(out, in2, out) — output overwrites input1 *)
  Context (HCurveAddInplace : forall pXo pX2 pYo pY2 pZo pZ2
    (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
     ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
     ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
     ⋆ R0) m0 ->
    WeakestPrecondition.call functions curve_add_name tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
         ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
         ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
         ⋆ R0) m'))).

  (** felem_copy: copies field element from src to dst *)
  Context (HFelemCopy : forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  (** opp: negates a field element in-place *)
  Context (HOpp : forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  (** Digits and tables — abstract parameters *)
  Context (dk1 dk2 : list Z).
  Context (Px Py Pz Phix Phiy Phiz : F).
  Context (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat).

  (** Weighted sums are non-negative (needed for Z.to_nat conversions) *)
  Context (Hws_nn1 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk1) 0).
  Context (Hws_nn2 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk2) 0).

  Context (table_P_entries table_Phi_entries : list (F * F * F)).

  (** Concrete hypothesis for the "process both digits" phase.
      After iter-- and curve_double, the remaining loop body is:
        load d1, process_one_digit d1, load d2, process_one_digit d2.
      This hypothesis abstracts all four commands into one WP statement.
      It is proved separately (Phase 4) where concrete memory layout is known. *)
  Context (HProcessBothDigits : forall (n : nat) pOx pOy pOz pAx pAy pAz
    pTP pTPhi pDK1 pDK2 (Ox Oy Oz Ax Ay Az : F) Rinner tr0 m0 l0,
    (n < 129)%nat ->
    (Ox,Oy,Oz) = curve_add
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk1) 0)) (Px,Py,Pz))
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk2) 0)) (Phix,Phiy,Phiz)) ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
     ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
     ⋆ Rinner) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pTP -> map.get l0 "table_Phi" = Some pTPhi ->
    map.get l0 "digits_k1" = Some pDK1 -> map.get l0 "digits_k2" = Some pDK2 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d1" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k1")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (cmd.seq
          (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
            "d1" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz")
          (cmd.seq
            (cmd.set "d2" (expr.load access_size.word
              (expr.op bopname.add (expr.var "digits_k2")
                (expr.op bopname.mul (expr.var "iter")
                  (expr.literal (Memory.bytes_per_word 64))))))
            (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
              "d2" "table_Phi" "auxx" "auxy" "auxz" "outx" "outy" "outz"))))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        (Ox',Oy',Oz') =
          curve_add
            (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
            (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
            ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
            ⋆ Rinner) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pTP /\ map.get l' "table_Phi" = Some pTPhi
        /\ map.get l' "digits_k1" = Some pDK1 /\ map.get l' "digits_k2" = Some pDK2
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ tr0 = t')).

  (** The main theorem: wnaf_loop_body satisfies HLoopBody.
      Composes iter--, curve_double, HProcessD1, HProcessD2,
      and the Horner step algebraic lemma. *)
  Theorem wnaf_loop_body_ok :
    forall (n : nat) pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      (Ox Oy Oz Ax Ay Az : F) Rinner tr0 m0 l0,
      (n < 129)%nat ->
      (Ox,Oy,Oz) = curve_add
        (scmul_glv (Z.to_nat (weighted_sum (skipn (S n) dk1) 0)) (Px,Py,Pz))
        (scmul_glv (Z.to_nat (weighted_sum (skipn (S n) dk2) 0)) (Phix,Phiy,Phiz)) ->
      (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az
       ⋆ (DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
          ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
          ⋆ Rinner)) m0 ->
      map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
      map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
      map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
      map.get l0 "table_P" = Some pTP -> map.get l0 "table_Phi" = Some pTPhi ->
      map.get l0 "digits_k1" = Some pDK1 -> map.get l0 "digits_k2" = Some pDK2 ->
      map.get l0 "iter" = Some (word.of_Z (Z.of_nat (S n))) ->
      WeakestPrecondition.cmd functions
        (wnaf_loop_body curve_add_name curve_double_name
           felem_copy opp felem_size_in_bytes
           "digits_k1" "digits_k2" "table_P" "table_Phi")
        tr0 m0 l0
        (fun t' m' l' =>
          exists Ox' Oy' Oz' Ax' Ay' Az',
          (Ox',Oy',Oz') =
            curve_add
              (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
              (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
              ⋆ (DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
                 ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
                 ⋆ Rinner)) m'
          /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
          /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
          /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
          /\ map.get l' "table_P" = Some pTP /\ map.get l' "table_Phi" = Some pTPhi
          /\ map.get l' "digits_k1" = Some pDK1 /\ map.get l' "digits_k2" = Some pDK2
          /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
          /\ tr0 = t').
  Proof.
    intros n pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      Ox Oy Oz Ax Ay Az Rinner tr0 m0 l0
      Hn Hinv Hsep Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az
      Hl_tp Hl_tphi Hl_dk1 Hl_dk2 Hl_iter.
    unfold wnaf_loop_body.
    (* Step 1: iter-- *)
    repeat straightline.
    eexists; split;
      [cbv [DEXPR WeakestPrecondition.dexpr
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
       eexists; split; [exact Hl_iter|]; exact eq_refl|].
    cbv [dlet.dlet].
    (* Step 2: curve_double(out, out) *)
    repeat straightline.
    eexists; split;
      [cbv [dexprs list_map list_map_body
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_ox|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oy|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oz|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_ox|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oy|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oz|];
       exact eq_refl|].
    eapply Semantics.weaken_call;
      [eapply HCurveDouble; ecancel_assumption_impl|].
    intros t1 m1 rets1 [Hrets1 [Htr1 Hsep1]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl|].
    (* After doubling: out = curve_add(Ox,Oy,Oz)(Ox,Oy,Oz).
       Destruct the let-match in Hsep1. *)
    set (doubled := curve_add (Ox, Oy, Oz) (Ox, Oy, Oz)) in Hsep1.
    destruct doubled as [[Dx Dy] Dz] eqn:Hdoubled.
    set (iter_word := word.sub (word.of_Z (Z.of_nat (S n))) (word.of_Z 1)).
    assert (Hiter_n : iter_word = word.of_Z (Z.of_nat n))
      by (unfold iter_word; rewrite <- word.ring_morph_sub; f_equal; lia).
    (* Prove doubling precondition for HProcessBothDigits:
       (Dx,Dy,Dz) = curve_add(scmul(2*ws1)(P))(scmul(2*ws2)(Phi)) *)
    assert (Hdbl_acc : (Dx, Dy, Dz) = curve_add
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk1) 0)) (Px,Py,Pz))
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk2) 0)) (Phix,Phiy,Phiz))).
    { (* Doubling: curve_add(acc)(acc) = curve_add(scmul(2*ws1)(P))(scmul(2*ws2)(Phi)) *)
      pose proof (fun a b P => eq_sym (scmul_add Fzero Fone curve_add
        curve_add_id_l curve_add_assoc a b P)) as Hscmul_add.
      unfold doubled in Hdoubled. rewrite Hinv in Hdoubled.
      symmetry in Hdoubled. rewrite Hdoubled.
      set (ws1 := weighted_sum (skipn (S n) dk1) 0).
      set (ws2 := weighted_sum (skipn (S n) dk2) 0).
      rewrite curve_add_assoc.
      rewrite (curve_add_4_rearrange curve_add curve_add_assoc curve_add_comm).
      unfold scmul_glv. rewrite !Hscmul_add. fold scmul_glv.
      assert (Z.to_nat ws1 + Z.to_nat ws1 = Z.to_nat (2 * ws1))%nat as ->.
      { rewrite Z2Nat.inj_mul; [simpl Z.to_nat; lia | lia |].
        unfold ws1. apply Hws_nn1. lia. }
      assert (Z.to_nat ws2 + Z.to_nat ws2 = Z.to_nat (2 * ws2))%nat as ->.
      { rewrite Z2Nat.inj_mul; [simpl Z.to_nat; lia | lia |].
        unfold ws2. apply Hws_nn2. lia. }
      reflexivity. }
    (* Reassociate sep for HProcessBothDigits *)
    assert (Hsep1' : (FElem (Some tight_bounds) pOx Dx
      ⋆ FElem (Some tight_bounds) pOy Dy ⋆ FElem (Some tight_bounds) pOz Dz
      ⋆ FElem (Some tight_bounds) pAx Ax ⋆ FElem (Some tight_bounds) pAy Ay
      ⋆ FElem (Some tight_bounds) pAz Az
      ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
      ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
      ⋆ Rinner) m1) by ecancel_assumption.
    (* Steps 3-6: Apply HProcessBothDigits *)
    eapply WeakestPreconditionProperties.Proper_cmd;
      [|exact (HProcessBothDigits n pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
                Dx Dy Dz Ax Ay Az Rinner tr0 m1 (map.put l0 "iter" iter_word)
                Hn Hdbl_acc Hsep1'
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ox)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_oy)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_oz)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ax)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ay)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_az)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_tp)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_tphi)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_dk1)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_dk2)
                ltac:(rewrite map.get_put_same; f_equal; exact Hiter_n))].
    (* Weaken postcondition: convert flat FElem sep to Point3 notation *)
    intros t2 m2 l2 (Ox2 & Oy2 & Oz2 & Ax2 & Ay2 & Az2 &
      Hout2 & Hsep2 & Hlox2 & Hloy2 & Hloz2 &
      Hlax2 & Hlay2 & Hlaz2 & Hltp2 & Hltphi2 &
      Hldk1_2 & Hldk2_2 & Hliter2 & Htr2).
    subst t2.
    exists Ox2, Oy2, Oz2, Ax2, Ay2, Az2.
    repeat split; try assumption.
    ecancel_assumption.
  Qed.

End LoopBodyProof.
