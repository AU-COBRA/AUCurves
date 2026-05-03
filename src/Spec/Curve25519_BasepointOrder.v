(** * Order of the Curve25519 Edwards basepoint
 *
 *  Discharges [B_order] in [Spec.XEdDSA_Curve25519] by transporting
 *  [Spec.Test.X25519.order_basepoint] (a Montgomery-ladder calculation
 *  closed by [vm_decide_no_check]) across the Edwards-Montgomery
 *  isomorphism [EdwardsMontgomery25519].
 *
 *  Roadmap:
 *  - Phase 1: bridge MxDH.ladderstep / M.xzladderstep (definitional eq).
 *  - Phase 2: bridge MxDH.montladder / M.montladder (loop-style equality).
 *  - Phase 3: from order_basepoint + bridge derive
 *             [X0 (M.scalarmult (Z.pos l) M.B) = 0].
 *  - Phase 4: rule out the (0,0) case to conclude
 *             [M.scalarmult (Z.pos l) M.B ~ M.zero] under M.eq.
 *  - Phase 5: transport through [M.of_Edwards] homomorphism →
 *             [E.scalarmult (Z.pos l) E.B ~ E.zero] under E.eq.
 *
 *  Build-time note (2026-05-03): a clean build of this file pegs a
 *  rocqworker at 99% CPU for 10+ minutes with steady ~340 MB RSS.
 *  The ondemand-native-cascade (Root Cause 9 in
 *  reference_slow_proofs_fiat.md) is *unlikely* to be the cause —
 *  per-sentence [-time] reports 0.0 secs for every visible sentence,
 *  and the certs in the dependency chain are all Qed-sealed
 *  (vm_decide / native_cast_no_check produce opaque proof terms,
 *  not redex-shaped bodies).  The hang is post-elaboration on the
 *  last sentence (likely a Qed kernel-conversion check on a large
 *  proof term).  Suspects: [cbv [MxDH.ladderstep M.xzladderstep]]
 *  expansions inside [mxdh_m_step_eq]/[downto_while_eq] producing
 *  large polynomial terms that the kernel re-checks at Qed; or
 *  [inversion Heq; subst] in [mxdh_eq_M_montladder] generating
 *  a deep [eq_rect] cascade.  Investigation pending.
 *)

From Stdlib Require Import ZArith BinNat BinPos.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Classes.Morphisms.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Curves.EdwardsMontgomery25519.
Require Import Crypto.Spec.Test.X25519.
Require Import Crypto.Util.Loops.

Local Open Scope Z_scope.

Local Notation p := Curve25519.p.
Local Notation l := Curve25519.l.
Local Notation F_p := (F p).

(* Don't elaborate Program obligations against Curve25519's concrete field. *)
Local Obligation Tactic := idtac.

(** ================================================================ *)
(** Phase 1: ladderstep equivalence                                    *)
(** ================================================================ *)

(** [MxDH.ladderstep] and [M.xzladderstep] are definitionally equal. *)
Lemma ladderstep_equiv :
  forall (F : Type) (Fadd Fsub Fmul : F -> F -> F) (a24 X1 : F) (P1 P2 : F * F),
    @MxDH.ladderstep F Fadd Fsub Fmul a24 X1 P1 P2
    = @M.xzladderstep F Fadd Fsub Fmul a24 X1 P1 P2.
Proof.
  intros F Fadd Fsub Fmul a24 X1 P1 P2.
  destruct P1 as [? ?]. destruct P2 as [? ?]. cbv. reflexivity.
Qed.

(** [Pos.testbit_nat] (used by [N.testbit_nat]) corresponds to [Z.testbit]
    on positives. *)
Lemma testbit_nat_pos_to_Z : forall (i : nat) (n : positive),
  Pos.testbit_nat n i = Z.testbit (Z.pos n) (Z.of_nat i).
Proof.
  induction i as [|i IH]; intros n.
  - destruct n; reflexivity.
  - destruct n.
    + simpl Pos.testbit_nat. rewrite IH.
      replace (Z.of_nat (S i)) with (Z.succ (Z.of_nat i)) by lia.
      change (Z.pos n~1) with (2 * Z.pos n + 1).
      rewrite Z.testbit_odd_succ; [reflexivity|lia].
    + simpl Pos.testbit_nat. rewrite IH.
      replace (Z.of_nat (S i)) with (Z.succ (Z.of_nat i)) by lia.
      change (Z.pos n~0) with (2 * Z.pos n).
      rewrite Z.testbit_even_succ; [reflexivity|lia].
    + simpl. reflexivity.
Qed.

Lemma testbit_nat_N_pos_to_Z : forall (i : nat) (n : positive),
  N.testbit_nat (N.pos n) i = Z.testbit (Z.pos n) (Z.of_nat i).
Proof.
  intros. simpl N.testbit_nat. apply testbit_nat_pos_to_Z.
Qed.

(** ================================================================ *)
(** Phase 2: MxDH.montladder ≡ M.montladder bridge                     *)
(** ================================================================ *)

Section MontladderBridge.
  Context {F : Type} (Fzero Fone : F)
          (Fadd Fsub Fmul : F -> F -> F)
          (Finv : F -> F)
          (a24 : F).

  (** The polymorphic cswap from [Spec.Test.X25519], specialized to F*F.
      Produces a pair-of-pairs (matching MxDH's [cswap] type). *)
  Definition cswap_FF (swap : bool) (a b : F * F) : (F * F) * (F * F) :=
    if swap then (b, a) else (a, b).

  (** State equivalence between MxDH's grouped state and M's flat state.
      MxDH carries [(P1, P2, swap)] where [P1, P2 : F*F].
      M carries     [(x2, z2, x3, z3, swap, i)]. *)

  Local Notation MxDHmontladder := (@MxDH.montladder F Fzero Fone Fadd Fsub Fmul Finv a24 cswap_FF).
  Local Notation Mmontladder    := (@M.montladder F Fzero Fone Fadd Fsub Fmul Finv a24).

  (** ---- inner loop bridge: one iteration of MxDH-step ≡ one of M-step ---- *)

  (** The MxDH step at iteration [i] over polymorphic cswap_FF. *)
  Definition mxdh_step (u : F) (testbit : nat -> bool)
             (state : F * F * (F * F) * bool) (i : nat)
    : F * F * (F * F) * bool :=
    let '(P1, P2, swap) := state in
    let s_i := testbit i in
    let swap' := xorb swap s_i in
    let '(P1', P2') := cswap_FF swap' P1 P2 in
    let '(P1'', P2'') := MxDH.ladderstep (a24:=a24) (Fadd:=Fadd) (Fsub:=Fsub) (Fmul:=Fmul) u P1' P2' in
    (P1'', P2'', s_i).

  Lemma mxdh_montladder_eq_unfolded :
    forall bound testbit u,
      MxDHmontladder bound testbit u =
      let '(P1, P2, swap) :=
        MxDH.downto ((Fone, Fzero), (u, Fone), false) bound (mxdh_step u testbit) in
      let '((x, z), _) := cswap_FF swap P1 P2 in
      Fmul x (Finv z).
  Proof.
    intros. cbv [MxDH.montladder mxdh_step]. reflexivity.
  Qed.

  (** ---- M-side: [while] = downto-style fold (proved by induction). ---- *)

  (** The body of [M.montladder]'s while loop. *)
  Definition m_body (u : F) (testbit : Z -> bool)
             (s : F * F * F * F * bool * Z) : F * F * F * F * bool * Z :=
    let '(x2, z2, x3, z3, swap, i) := s in
    let b := testbit i in
    let swap' := xorb swap b in
    let (x2', x3') := M.cswap swap' x2 x3 in
    let (z2', z3') := M.cswap swap' z2 z3 in
    let '((x4, z4), (x5, z5)) :=
      M.xzladderstep (Fadd:=Fadd) (Fsub:=Fsub) (Fmul:=Fmul) (a24:=a24) u (x2', z2') (x3', z3') in
    (x4, z4, x5, z5, b, Z.pred i).

  Definition m_test (s : F * F * F * F * bool * Z) : bool :=
    let '(_, _, _, _, _, i) := s in (i >=? 0)%Z.

  (** Phi maps an MxDH state plus a "current i" to the M-state. *)
  Definition phi (i : Z) (mx : F * F * (F * F) * bool) : F * F * F * F * bool * Z :=
    let '(P1, P2, swap) := mx in
    let '(x2, z2) := P1 in
    let '(x3, z3) := P2 in
    (x2, z2, x3, z3, swap, i).

  (** One iteration of MxDH-step at index [i] equals one iteration of m_body
      under the [phi] mapping (when [i >= 0]). *)
  Lemma mxdh_m_step_eq :
    forall (u : F) (testbit_n : nat -> bool) (testbit_z : Z -> bool)
           (i : nat) (mx : F * F * (F * F) * bool),
      testbit_z (Z.of_nat i) = testbit_n i ->
      phi (Z.pred (Z.of_nat i)) (mxdh_step u testbit_n mx i) =
      m_body u testbit_z (phi (Z.of_nat i) mx).
  Proof.
    intros u tbn tbz i mx Htb.
    destruct mx as [[[a b] [c d]] swap].
    cbv [mxdh_step m_body cswap_FF M.cswap MxDH.ladderstep M.xzladderstep phi].
    rewrite Htb.
    destruct (xorb swap (tbn i)); reflexivity.
  Qed.

  (** ---- Loop equivalence: MxDH.downto = while.while (fueled) ---- *)

  (** [while.while m_test (m_body u tbz) fuel s] does some iterations.
      We unfold its structure with this manual recursion lemma. *)

  (** [MxDH.downto] applied to [bound] iterations.  Each call to step
      receives index [bound-1, bound-2, ..., 0] in turn. *)
  Lemma downto_S : forall {St : Type} (init : St) (bound : nat) (step : St -> nat -> St),
    MxDH.downto init (S bound) step =
    MxDH.downto (step init bound) bound step.
  Proof.
    intros. cbv [MxDH.downto]. simpl MxDH.downto_iter. reflexivity.
  Qed.

  (** [while.while] applied to [(S fuel)] iterations from a state where
      [m_test s = true]. *)
  Lemma while_step :
    forall (test : F * F * F * F * bool * Z -> bool)
           (body : F * F * F * F * bool * Z -> F * F * F * F * bool * Z)
           (fuel : nat) (s : F * F * F * F * bool * Z),
      test s = true ->
      while.while test body (S fuel) s = while.while test body fuel (body s).
  Proof.
    intros. simpl. rewrite H. reflexivity.
  Qed.

  Lemma while_done :
    forall (test : F * F * F * F * bool * Z -> bool)
           (body : F * F * F * F * bool * Z -> F * F * F * F * bool * Z)
           (fuel : nat) (s : F * F * F * F * bool * Z),
      test s = false ->
      while.while test body fuel s = s.
  Proof.
    intros. destruct fuel; simpl; rewrite H; reflexivity.
  Qed.

  Lemma while_pointwise_eq :
    forall {St : Type} (test1 test2 : St -> bool) (body1 body2 : St -> St),
      (forall s, test1 s = test2 s) ->
      (forall s, body1 s = body2 s) ->
      forall fuel s,
        while.while test1 body1 fuel s = while.while test2 body2 fuel s.
  Proof.
    intros St t1 t2 b1 b2 Ht Hb fuel.
    induction fuel; intros s; simpl.
    - rewrite Ht. destruct (t2 s); [apply Hb | reflexivity].
    - rewrite Ht. destruct (t2 s) eqn:Ht2; [|reflexivity].
      rewrite Hb. apply IHfuel.
  Qed.

  (** Main loop equivalence.  We prove by induction on [bound]:
      starting with the same initial state in both representations,
      after [bound] iterations the states match under [phi].
      The MxDH side's first iteration is at index [bound-1]; the M side's
      first iteration body sees [i = bound-1].  After [bound] iterations,
      M's i variable is at [-1]. *)
  Lemma downto_while_eq :
    forall (u : F) (testbit_n : nat -> bool) (testbit_z : Z -> bool)
           (Htb : forall i : nat, testbit_z (Z.of_nat i) = testbit_n i)
           (bound : nat) (init : F * F * (F * F) * bool),
      phi (-1)%Z (MxDH.downto init bound (mxdh_step u testbit_n)) =
      while.while m_test (m_body u testbit_z) bound
                  (phi (Z.pred (Z.of_nat bound)) init).
  Proof.
    intros u tbn tbz Htb bound.
    induction bound as [|bound IH]; intros init.
    - cbv [MxDH.downto]. simpl MxDH.downto_iter. cbn [List.fold_left].
      cbv [m_test]. destruct init as [[[? ?] [? ?]] ?].
      cbv [phi]. simpl. reflexivity.
    - rewrite downto_S.
      cbn [while.while].
      assert (Htest : m_test (phi (Z.pred (Z.of_nat (S bound))) init) = true).
      { cbv [m_test phi]. destruct init as [[[? ?] [? ?]] ?].
        rewrite Z.geb_le. lia. }
      rewrite Htest.
      rewrite IH.
      f_equal.
      replace (Z.pred (Z.of_nat (S bound))) with (Z.of_nat bound) by lia.
      rewrite <- (mxdh_m_step_eq u tbn tbz bound init (Htb bound)).
      reflexivity.
  Qed.

  (** ---- Final montladder bridge ---- *)

  Lemma mxdh_eq_M_montladder :
    forall (bound : nat) (testbit_n : nat -> bool) (testbit_z : Z -> bool)
           (Htb : forall i : nat, testbit_z (Z.of_nat i) = testbit_n i)
           (u : F),
      MxDHmontladder bound testbit_n u =
      Mmontladder (Z.of_nat bound) testbit_z u.
  Proof.
    intros bound tbn tbz Htb u.
    cbv [MxDHmontladder Mmontladder MxDH.montladder M.montladder].
    cbv [Rewriter.Util.LetIn.Let_In].
    rewrite Znat.Nat2Z.id.
    (* Replace M's anonymous body and test with our m_body/m_test. *)
    erewrite while_pointwise_eq with (test2 := m_test) (body2 := m_body u tbz).
    2: { intros [[[[[? ?] ?] ?] ?] ?]. cbv [m_test]. reflexivity. }
    2: { intros [[[[[? ?] ?] ?] ?] ?]. cbv [m_body]. reflexivity. }
    (* Replace MxDH's anonymous body with our mxdh_step. *)
    pose proof (downto_while_eq u tbn tbz Htb bound
                 (Fone, Fzero, (u, Fone), false)) as Heq.
    cbv [mxdh_step phi] in Heq.
    set (S_MxDH := MxDH.downto _ bound _) in *.
    set (S_M := while.while m_test _ bound _) in *.
    destruct S_MxDH as [[[a b] [c d]] swap1] eqn:HMxDH.
    destruct S_M as [[[[[x2 z2] x3] z3] swap2] i2] eqn:HM.
    cbv [phi] in Heq. inversion Heq; subst.
    cbv [cswap_FF M.cswap].
    destruct swap2; reflexivity.
  Qed.
End MontladderBridge.

(** ================================================================ *)
(** Phase 3: Specialise to Curve25519, apply montladder_correct        *)
(** ================================================================ *)

(** Auxiliary 2-torsion point [(0,0)] on Curve25519's Montgomery model.
    This is the *unique* finite point whose X coordinate is 0. *)
Definition M_zero_two_torsion : Curve25519.M.point.
  refine (exist _ (inl (F.of_Z _ 0, F.of_Z _ 0)) _).
  Decidable.vm_decide.
Defined.

(** Restate Spec.Test.X25519.order_basepoint as an equality on F p,
    keeping the [monty] form rather than the unfolded
    [MxDH.montladder ... 255 ...] form.  This is critical for build
    speed: stating the goal in unfolded form makes [exact
    order_basepoint] trigger the kernel to unify the goal's
    [MxDH.montladder] with the type's [monty] by δ-unfolding [monty]
    and walking inside the body — which forces evaluation of the
    255-iteration [downto] symbolically (~10 min wall on this hardware).
    Keeping the goal in [monty] form avoids that walk. *)
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Lemma monty_l_eq_zero :
  Spec.Test.X25519.monty (N.pos l) (F.of_Z _ 9) = F.zero.
Proof.
  apply F.eq_to_Z_iff.
  rewrite (F.to_Z_0 (m := p)).
  exact Spec.Test.X25519.order_basepoint.
Qed.

(** Bridge from [monty] to the explicit [MxDH.montladder] form
    using [cswap_FF] (Phase 2's section variable after closing) as
    the cswap, so this can chain into [mxdh_eq_M_montladder].
    Both sides are definitionally equal — [Spec.Test.X25519.cswap]
    at type [F p * F p] and [cswap_FF (F:=F p)] are the same lambda. *)
Lemma monty_unfold :
  Spec.Test.X25519.monty (N.pos l) (F.of_Z _ 9) =
  @MxDH.montladder _ F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24
    (cswap_FF (F:=F p))
    255 (BinNat.N.testbit_nat (N.pos l)) (F.of_Z _ 9).
Proof. reflexivity. Qed.

(** Combined: MxDH.montladder (with [cswap_FF]) applied at the
    basepoint X-coord 9, 255 iterations, [N.pos l] testbits, equals
    zero in F p.  Phrased to feed into [mxdh_eq_M_montladder]. *)
Lemma mxdh_l_eq_zero :
  @MxDH.montladder _ F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24
    (cswap_FF (F:=F p))
    255 (BinNat.N.testbit_nat (N.pos l)) (F.of_Z _ 9)
  = F.zero.
Proof. rewrite <- monty_unfold. exact monty_l_eq_zero. Qed.

(** ================================================================ *)
(** Phase 4: route through [montladder_correct] to scalarmult         *)
(** ================================================================ *)

(** Bridge from MxDH-form to M-form using Phase 2's [mxdh_eq_M_montladder]. *)
Lemma m_montladder_l_eq_zero :
  @M.montladder _ F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24
    255 (Z.testbit (Z.pos l)) (F.of_Z p 9) = F.zero.
Proof.
  pose proof (mxdh_eq_M_montladder F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24
                255%nat (BinNat.N.testbit_nat (N.pos l)) (Z.testbit (Z.pos l))
                (fun i => eq_sym (testbit_nat_N_pos_to_Z i l)) (F.of_Z _ 9)) as Hbridge.
  rewrite mxdh_l_eq_zero in Hbridge.
  symmetry.
  replace 255 with (Z.of_nat 255) by reflexivity.
  exact Hbridge.
Qed.

(** ================================================================ *)
(** Phase 4b and Phase 5: TODO                                         *)
(** ================================================================ *)

(** Phase 4b: apply [M.montladder_correct] to [m_montladder_l_eq_zero]
    to obtain [M.X0 (M.scalarmult (Z.pos l) M.B) = F.zero].

    Side conditions verified individually:
      char_ge 28: [eapply Hierarchy.char_ge_weaken; [apply (@F.char_gt p) | vm_compute; discriminate].]
      char_ge 3:  same.
      4*a24=a-2:  [Decidable.vm_decide.] (~2.7 s)
      a2m4_nonsq: [intros r Hr. apply Curve25519.M.a2m4_nonsq. exists r. rewrite Hr; f_equal; ring.]
      F.inv 0=0:  [Decidable.vm_decide.]
      0<=255:     [lia.]
    All 6 side conditions are dischargeable.  The blocker is the final
    [rewrite Hml in Hcorr] / [change F.of_Z _ 9 with M.X0 M.B in Hml]:
    these trigger heavy kernel conversion (RSS oscillates 1.6-6 GB,
    eventual OOM).  Likely the same pattern as the [exact H] inside
    unfolded MxDH.montladder — kernel walks inside [M.montladder]'s
    body to align args.

    Mitigation paths to try next session:
    - Pose [M.X0 M.B = F.of_Z p 9] as a [reflexivity] lemma first,
      then chain via that lemma instead of [change ... with].
    - Make [M.montladder] Strategy-opaque locally during the rewrite.
    - State [m_X0_scalarmult_l_zero] in a form that doesn't need
      [change], e.g., factor out the [M.X0 M.B = 9] step as a separate
      small lemma. *)

(** Phase 5: transport via [homomorphism_scalarmult] across the
    [EdwardsMontgomery25519] isomorphism to derive
    [E.scalarmult (Z.pos l) E.B = E.zero] under E.eq, which is
    [B_order] in [XEdDSA_Curve25519.v]. *)

(** TODO Phase 3 (continued): combine [mxdh_l_eq_zero] with
    [mxdh_eq_M_montladder] (Phase 2) and [montladder_correct] from
    [Curves.Montgomery.XZProofs] to derive
    [X0 (M.scalarmult (Z.pos l) M.B) = 0] under M.eq.

    TODO Phase 4: rule out the (0,0) 2-torsion case via the parity
    argument [X0 (M.scalarmult (l+1) M.B) = 9 ≠ X0 ((0,0) + M.B)],
    concluding [M.scalarmult (Z.pos l) M.B ~ M.zero] under M.eq.

    TODO Phase 5: transport through the [EdwardsMontgomery25519]
    isomorphism via [homomorphism_scalarmult] to obtain
    [E.scalarmult (Z.pos l) E.B ~ E.zero] under E.eq, which is
    [B_order] in [XEdDSA_Curve25519.v]. *)
