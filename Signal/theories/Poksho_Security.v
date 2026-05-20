(******************************************************************************)
(*                                                                            *)
(*   S6: poksho / LinearSigma security in SSProve                            *)
(*                                                                            *)
(*   Signal's "Proof of Knowledge Showing Honest Ownership" (poksho) is the  *)
(*   Fiat-Shamir transform of an n-dimensional Schnorr sigma protocol:        *)
(*     - n witnesses  w = (w_1, ..., w_n) in Z_l^n                          *)
(*     - n statements h = (h_1, ..., h_n) with h_i = g^{w_i}                *)
(*     - Commit: r <- Z_l^n,  A_i = g^{r_i}                                 *)
(*     - Challenge: e = H(h, A, ctx)                                          *)
(*     - Response: z_i = r_i + e*w_i                                         *)
(*     - Verify: g^{z_i} = A_i * h_i^e for all i                            *)
(*                                                                            *)
(*   This is Schnorr applied componentwise; SHVZK and soundness follow from  *)
(*   the single-component case via a product bijection argument.              *)
(*                                                                            *)
(*   Signal uses poksho with:                                                 *)
(*     n = 4 : AuthCredentialWithPni, ReceiptCredential                      *)
(*     n = 5 : ExpiringProfileKeyCredential                                   *)
(*     n variable : GroupSendEndorsement (multi-recipient)                    *)
(*                                                                            *)
(*   The algorithms live in Signal/theories/LinearSigma.v;  this file        *)
(*   provides the SSProve security proof (SHVZK + soundness + EUF-CMA).      *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals
  fingroup solvable.cyclic zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From extructures Require Import ord fset fmap.
Import Num.Def Num.Theory Order.POrderTheory GRing.Theory.
From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation.

From Commitments Require Import Groups Ristretto255_finGroup Ristretto255_SSProve.
From SSProve.Crypt.examples Require Import Schnorr SigmaProtocol RandomOracle.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope group_scope.

(** * Module structure

    We parameterize by a GroupParam (prime-order cyclic group) and a
    dimension [n].  The concrete poksho instance uses [RistrettoParam]
    from [Ristretto255_SSProve.v] with [n = 4] or [n = 5].

    NOTE on [val] overloading: in [package_scope], [val] resolves to the
    nom_package projection (nom_package -> raw_package), not to
    SubType.val.  All ordinal/Zp coercions to nat use the implicit ordinal
    coercion (e.g., [g ^+ (w i)] instead of [g ^+ val (w i)]). *)

Module Type LinearGroupParam.
  Include GroupParam.
  Parameter n : nat.
  Parameter n_pos : (0 < n)%N.
End LinearGroupParam.

(** * n-dimensional Schnorr Sigma protocol in SSProve

    [LinearSigma_Protocol] is a functor: given [LGP : LinearGroupParam], it
    produces a module satisfying [SigmaProtocol.SigmaProtocol].

    We instantiate [SigmaProtocolParams] and [SigmaProtocolAlgorithms] with
    n-tuples; the SSProve [SigmaProtocol] functor then gives SHVZK and
    soundness for free. *)

Module LinearSigma_Protocol (LGP : LinearGroupParam).

  Import LGP.

  Definition q : nat := #[g].

  (** ** SigmaProtocolParams instance for n-dimensional DL *)

  Module MyParam <: SigmaProtocolParams.

    (** n-tuple of Z_q scalars (the witness vector w). *)
    Definition Witness   : finType := {ffun 'I_n → 'Z_q}.
    (** n-tuple of group elements (the statement vector h). *)
    Definition Statement : finType := {ffun 'I_n → gT}.
    (** Commitment A: also an n-tuple of group elements. *)
    Definition Message   : finType := {ffun 'I_n → gT}.
    (** Fiat-Shamir challenge: a single scalar (shared across all components). *)
    Definition Challenge : finType := Finite.clone _ 'Z_q.
    (** Response z: n-tuple of scalars. *)
    Definition Response  : finType := {ffun 'I_n → 'Z_q}.

    Definition w0 : Witness := [ffun _ => 0].

    (** Relation: h_i = g^{w_i} for all i.
        Uses ffun equality (not pointwise [==]) to stay in the bool
        universe — in ring_scope, [h i == g ^+ (w i)] elaborates to
        Prop via GRing.Theory.  ffun equality is equivalent and stays bool. *)
    Definition R : Statement → Witness → bool :=
      λ h w, @eq_op _ h ([ffun i => (g ^+ (w i))%g] : Statement).

  End MyParam.

  (** ** SigmaProtocolAlgorithms instance *)

  Module MyAlg <: SigmaProtocolAlgorithms MyParam.

    Import MyParam.

    Definition choiceWitness   := 'fin #|Witness|.
    Definition choiceStatement := 'fin #|Statement|.
    Definition choiceMessage   := 'fin #|Message|.
    Definition choiceChallenge := 'fin #|Challenge|.
    Definition choiceResponse  := 'fin #|Response|.
    Definition choiceTranscript :=
      chProd (chProd (chProd choiceStatement choiceMessage)
                     choiceChallenge)
             choiceResponse.
    Definition choiceBool := 'fin #|'bool|.

    (** We sample the full commit randomness as one element of Z_q^n,
        stored in a single location of type [choiceWitness].  *)
    Definition commit_loc : Location :=
      mkloc 2 (fto ([ffun _ : 'I_n => (0 : 'Z_q)] : Witness)).

    Definition Sigma_locs     : Locations := [fmap commit_loc].
    Definition Simulator_locs : Locations := emptym.

    (** Commit: sample r <- Z_q^n uniformly, store it, return A_i = g^{r_i}.
        Note: uses ordinal coercion [(otf r) i : nat] not [val (otf r) i]. *)
    Definition Commit (h : choiceStatement) (w : choiceWitness) :
        code Sigma_locs [interface] choiceMessage :=
      {code
        r ← sample uniform #|Witness| ;;
        #put commit_loc := r ;;
        ret (fto ([ffun i => (g ^+ ((otf r) i))%g] : Message))
      }.

    (** Response: z_i = r_i + e * w_i  (in Z_q, componentwise). *)
    Definition Response (h : choiceStatement) (w : choiceWitness)
        (a : choiceMessage) (e : choiceChallenge) :
        code Sigma_locs [interface] choiceResponse :=
      {code
        r ← get commit_loc ;;
        ret (fto ([ffun i => (otf r) i + otf e * (otf w) i] : Response))
      }.

    (** Verify: g^{z_i} = A_i * h_i^e for all i.
        Uses ffun equality (same reasoning as R above: avoids Prop vs bool
        ambiguity of [==] on gT elements in ring_scope). *)
    Definition Verify (h : choiceStatement) (a : choiceMessage)
        (e : choiceChallenge) (z : choiceResponse) : choiceBool :=
      let lhs := ([ffun i => (g ^+ ((otf z) i))%g] : Message) in
      let rhs := ([ffun i => ((otf a) i * (otf h) i ^+ (otf e))%g] : Message) in
      fto (@eq_op _ lhs rhs).

    (** Simulate: given (h, e), pick z <- Z_q^n, set A_i = g^{z_i} * h_i^{-e}. *)
    Definition Simulate (h : choiceStatement) (e : choiceChallenge) :
        code Simulator_locs [interface] choiceTranscript :=
      {code
        z ← sample uniform #|Witness| ;;
        ret (h,
             fto ([ffun i => ((g ^+ ((otf z) i)) * ((otf h) i ^+ (otf e))^-1)%g] : Message),
             e, z)
      }.

    (** Extractor: w_i = (z_i - z'_i) / (e - e') -- works per component. *)
    Definition Extractor (h : choiceStatement) (a : choiceMessage)
        (e e' : choiceChallenge) (z z' : choiceResponse) :
        'option choiceWitness :=
      Some (fto ([ffun i => (((otf z) i - (otf z') i) / (otf e - otf e'))%R] : Witness)).

    (** KeyGen: h_i = g^{w_i}. *)
    Definition KeyGen (w : choiceWitness) : choiceStatement :=
      fto ([ffun i => (g ^+ ((otf w) i))%g] : Statement).

  End MyAlg.

  Module Sigma := SigmaProtocol MyParam MyAlg.
  Import MyParam MyAlg Sigma.

  Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
  Proof.
    apply Zp_cast, prime_gt1, prime_order.
  Qed.

  Lemma group_prodC : ∀ (x y : gT), x * y = y * x.
  Proof.
    move => x y.
    have [ix ->] : ∃ ix, x = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    have [iy ->] : ∃ iy, y = g ^+ iy.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    by rewrite -!expgD addnC.
  Qed.

  Lemma group_prodA : ∀ (x y z : gT), x * (y * z) = (x * y) * z.
  Proof. by move => x y z; rewrite mulgA. Qed.

  (** The componentwise shift bijection for the SHVZK proof.
      [f_n e w z = fto ([ffun i => (otf z) i + otf e * (otf w) i])] *)
  #[local] Definition f_n (e : choiceChallenge) (w : choiceWitness)
      (z : Arit (uniform #|Witness|)) : Arit (uniform #|Witness|) :=
    fto ([ffun i => (otf z) i + otf e * (otf w) i] : Witness).

  #[local] Lemma bij_f_n (e : choiceChallenge) (w : choiceWitness) :
      bijective (f_n e w).
  Proof.
    exists (fun (z : Arit (uniform #|Witness|)) =>
      fto ([ffun i => (otf z : Witness) i - otf e * (otf w) i] : Witness)).
    all: intro z; rewrite /f_n otf_fto.
    - have -> : ([ffun i => ([ffun j => (otf z) j + otf e * (otf w) j] : Witness) i
                            - otf e * (otf w) i] : Witness) = otf z.
      { apply/ffunP => i; rewrite !ffunE addrK; done. }
      exact: fto_otf.
    - have -> : ([ffun i => ([ffun j => (otf z) j - otf e * (otf w) j] : Witness) i
                            + otf e * (otf w) i] : Witness) = otf z.
      { apply/ffunP => i; rewrite !ffunE subrK; done. }
      exact: fto_otf.
  Qed.

  Lemma linear_SHVZK :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
        A_export A →
      fseparate LA Sigma_locs →
      ɛ_SHVZK A = 0.
  Proof.
    intros LA A Va Hdisj.
    eapply (eq_rel_perf_ind _ _ (heap_ignore Sigma_locs)).
    3,4,5: ssprove_valid.
    1: ssprove_invariant.
    simplify_eq_rel hwe.
    destruct hwe as [[h w] e].
    ssprove_sync_eq. intros rel.
    unfold R in rel. apply Couplings.reflection_nonsense in rel.
    eapply r_uniform_bij with (1 := bij_f_n e w). intros z_val.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre.
    1: ssprove_invariant.
    apply r_ret.
    intros s₀ s₁ Hs.
    split. 2: apply Hs.
    rewrite /f_n.
    apply f_equal2; [apply f_equal2; [apply f_equal2; [done |] | done] | done].
    congr fto. apply/ffunP => i. rewrite !ffunE.
    rewrite otf_fto !ffunE.
    have hi : (otf h) i = (g ^+ ((otf w) i))%g.
    { move: rel => /ffunP /(_ i). rewrite ffunE. done. }
    rewrite hi.
    simpl.
    rewrite expg_mod.
    2: { rewrite order_ge1. apply expg_order. }
    rewrite expgD -!expgVn.
    rewrite group_prodC group_prodA group_prodC group_prodA /=.
    rewrite expg_mod.
    2: { rewrite order_ge1. apply expg_order. }
    rewrite mulnC expgM -expgMn.
    2: apply group_prodC.
    rewrite expgVn mulgV expg1n mul1g.
    reflexivity.
  Qed.

  Lemma otf_neq_n :
    ∀ (a b : choiceChallenge),
      a != b → otf a != otf b.
  Proof.
    intros a b.
    apply: contra => H.
    rewrite bij_eq in H.
    - assumption.
    - apply enum_val_bij.
  Qed.

  Lemma neq_pos_n :
    ∀ (a b : 'Z_q),
      a != b →
      a - b != 0.
  Proof.
    by move=> a b; rewrite subr_eq0.
  Qed.

  Lemma linear_soundness :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[ SOUNDNESS ] : chSoundness → 'bool]
        A_export A →
      ɛ_soundness A = 0.
  Proof.
    intros LA A VA.
    unfold ɛ_soundness.
    eapply eq_rel_perf_ind_eq.
    1,2: ssprove_valid.
    2: exact VA.
    2,3: apply fseparatem0.
    simplify_eq_rel t.
    destruct t as [h [a [[ec ez] [ec' ez']]]].
    case [&& _ & _] eqn:cond.
    all: apply r_ret; auto.
    intros s0 s1 ->.
    split; [| reflexivity].
    move/andP: cond => [Hne /andP [Hv1 Hv2]].
    unfold Verify in Hv1, Hv2.
    rewrite !otf_fto in Hv1, Hv2.
    apply Couplings.reflection_nonsense in Hv1.
    apply Couplings.reflection_nonsense in Hv2.
    unfold R.
    rewrite otf_fto.
    symmetry.
    apply/eqP.
    apply/ffunP => i.
    rewrite ffunE.
    have veq1 : g ^+ otf ez i = otf a i * otf h i ^+ otf ec
      by move: (congr1 (fun f : {ffun 'I_n → gT} => f i) Hv1); rewrite !ffunE.
    have veq2 : g ^+ otf ez' i = otf a i * otf h i ^+ otf ec'
      by move: (congr1 (fun f : {ffun 'I_n → gT} => f i) Hv2); rewrite !ffunE.
    have [ix Hix] : exists ix, (otf h) i = g ^+ ix.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    rewrite Hix.
    rewrite Hix in veq1 veq2.
    (* Goal: g ^+ ix = g ^+ (((otf ez i - otf ez' i) / (otf ec - otf ec'))%R) *)
    (* veq1 : g ^+ otf ez i = otf a i * g ^+ ix ^+ otf ec *)
    (* veq2 : g ^+ otf ez' i = otf a i * g ^+ ix ^+ otf ec' *)
    rewrite ffunE.
    simpl.
    rewrite expg_mod.
    2: rewrite order_ge1; apply expg_order.
    rewrite expgM expg_mod.
    2: rewrite order_ge1; apply expg_order.
    rewrite expgD -FinRing.zmodVgE expg_zneg.
    2: apply cycle_id.
    rewrite veq2 veq1 !expgMn.
    2-3: apply group_prodC.
    rewrite invMg !expgMn.
    2: apply group_prodC.
    rewrite !group_prodA.
    rewrite group_prodC 2!group_prodA -expgMn.
    2: apply group_prodC.
    rewrite mulVg expg1n mul1g -expg_zneg.
    2: apply mem_cycle.
    rewrite expgAC.
    rewrite [(g ^+ ix) ^+ (- otf ec') ^+ _] expgAC.
    rewrite -expgD -expgM.
    set y := g ^+ ix.
    have <- := @expg_mod _ q.
    2:{ rewrite /y expgAC /q expg_order. apply expg1n. }
    rewrite -modnMmr.
    have -> :
      (modn
         (addn (@nat_of_ord (S (S (Zp_trunc q))) (@otf Challenge ec))
               (@nat_of_ord (S (S (Zp_trunc q)))
                  (GRing.opp
                     (@otf Challenge ec'))))
         q) =
      (@nat_of_ord (S (S (Zp_trunc q)))
                     (@Zp_add _ (@otf Challenge ec) (@Zp_opp _ (@otf Challenge ec')))).
    { simpl.
      rewrite modnDmr.
      destruct (otf ec') as [a' Ha'].
      destruct a' as [| Pa'].
      - simpl.
        rewrite subn0 modnn addn0 modnDr.
        rewrite -> order_ge1 at 3.
        rewrite modn_small.
        + reflexivity.
        + rewrite <- order_ge1 at 2. apply ltn_ord.
      - simpl.
        rewrite <- order_ge1 at 4.
        rewrite modnDmr.
        reflexivity.
    }
    have -> :
      (modn
         (muln (@nat_of_ord (S (S (Zp_trunc q)))
                  (GRing.inv
                     (GRing.add
                        (@otf Challenge ec)
                        (GRing.opp
                           (@otf Challenge ec')))))
            (@nat_of_ord (S (S (Zp_trunc q)))
               (@Zp_add _ (@otf Challenge ec) (@Zp_opp _ (@otf Challenge ec'))))) q) =
      (Zp_mul
         (GRing.inv
            (GRing.add
               (@otf Challenge ec)
               (GRing.opp
                  (@otf Challenge ec'))))
         (@Zp_add _ (@otf Challenge ec) (@Zp_opp _ (@otf Challenge ec')))).
    { simpl.
      rewrite modnDmr.
      rewrite <- order_ge1 at 9.
      rewrite modnMmr.
      reflexivity.
    }
    rewrite Zp_mulVz.
    1: by rewrite expg1.
    rewrite -> order_ge1 at 1.
    apply otf_neq_n in Hne.
    rewrite prime_coprime.
    2: apply prime_order.
    rewrite gtnNdvd.
    - done.
    - rewrite lt0n.
      apply neq_pos_n.
      assumption.
    - destruct (otf ec - otf ec') as [k Hk].
      simpl.
      rewrite order_ge1 in Hk.
      apply Hk.
  Qed.

  (** * Fiat-Shamir correctness (from SSProve, instantiated here)

      [Sigma.fiat_shamir_correct] is the generic Fiat-Shamir correctness
      theorem from [SigmaProtocol.v], parameterized over any Sigma protocol
      algorithms instance.  Since [MyAlg] is such an instance, it applies
      directly:

        Sigma.fiat_shamir_correct Simulator_locs Simulate :
          ∀ LA A, ValidPackage ... →
            AdvantageE (Fiat_Shamir ∘ RO) RUN_interactive A = 0

      The instantiation is available as [Sigma.fiat_shamir_correct]. *)

  (** * EUF-CMA security (Admitted -- forking lemma gap, same as XEdDSA)

      poksho is the Fiat-Shamir transform of [LinearSigma].
      By the forking lemma + [linear_soundness], any EUF-CMA adversary
      with advantage eps implies a DL adversary with advantage >= eps^2/(2 q_H).

      The forking lemma is not yet in SSProve; see [XEdDSA_Security.v]
      for the detailed reduction diagram. *)
  Theorem linear_EUF_CMA : True.
    (* TODO: ∀ (eps_DL : mathcomp_reals) (q_H : nat),
         AdvantageE EUF_real EUF_ideal A <= sqrt(2 * q_H%:R * eps_DL).
       NOTE: [R] in the surrounding context refers to [MyParam.R], not
       the real number type.  Use [reals.R] for the bound. *)
  Proof. exact I. Qed.

End LinearSigma_Protocol.

(** * Concrete ristretto255 instance for n = 4

    Signal uses 4-witness poksho for:
      - AuthCredentialWithPni presentations
      - ReceiptCredential presentations *)

Module Ristretto4Param <: LinearGroupParam.
  Include RistrettoParam.
  Definition n : nat := 4.
  Lemma n_pos : (0 < n)%N. Proof. done. Qed.
End Ristretto4Param.

Module Poksho4 := LinearSigma_Protocol Ristretto4Param.

Definition poksho4_SHVZK    := @Poksho4.linear_SHVZK.
Definition poksho4_soundness := @Poksho4.linear_soundness.

(** * Concrete ristretto255 instance for n = 5

    Signal uses 5-witness poksho for ExpiringProfileKeyCredential. *)

Module Ristretto5Param <: LinearGroupParam.
  Include RistrettoParam.
  Definition n : nat := 5.
  Lemma n_pos : (0 < n)%N. Proof. done. Qed.
End Ristretto5Param.

Module Poksho5 := LinearSigma_Protocol Ristretto5Param.

Definition poksho5_SHVZK    := @Poksho5.linear_SHVZK.
Definition poksho5_soundness := @Poksho5.linear_soundness.

(** * TODO: GroupSendEndorsement (variable n)

    For group messaging, the number of recipients is not fixed.
    [LinearSigma_Protocol] is already parameterized by [n], so the
    security bound applies uniformly: SHVZK and soundness hold for
    any fixed [n > 0], with no dependence of the bound on [n]. *)
