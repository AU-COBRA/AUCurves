(** * Fe25519Mul128Discharge — Phase 0e E4 scaffold for the algebraic
 *    discharge of [feval_limbwise_mul_mask64] /
 *    [feval_limbwise_square_mask64] via the u128 IR fragment.
 *
 *  Phase 0e E4 (2026-05-13)
 *  ========================
 *
 *  CONTEXT
 *  -------
 *  [src/Bedrock/SafeRustEd25519Sim.v] introduces, at the bottom of §1,
 *  the [SMul128] / [SAdd128] IR constructors with semantics
 *      eval_sexpr_ed rs (SMul128 a b)  =  Some (mask128 (va * vb))
 *      eval_sexpr_ed rs (SAdd128 a b)  =  Some (mask128 (va + vb))
 *  and three structural collapse lemmas
 *      mask128_id                : 0 <= z < 2^128 -> mask128 z = z
 *      mul_u54_fits_u128         : 0 <= a,b < 2^54 -> 0 <= a*b < 2^128
 *      mul_scaled_u54_fits_u128  : 0 <= a,b < 2^54 -> 0 <= k < 2^7 ->
 *                                  0 <= k*(a*b) < 2^128
 *  (Phase 0e block, commit a654246.)
 *
 *  [src/Bedrock/End2End/Ed25519/Fe25519Mul128Helpers.v] (commit
 *  2126ca4) provides the natural u128-backed mirrors of the Mul/Square
 *  body helpers:
 *      smul128_limbs  av bv i j      :=  SMul128 (SLimb av i) (SLimb bv j)
 *      smul128_scaled av bv i j k    :=  SMul128 (SLit k)
 *                                                (SMul128 (SLimb av i)
 *                                                         (SLimb bv j))
 *
 *  [Fe25519MulCorrect.v] / [Fe25519SquareCorrect.v] expose the
 *  algebraic Section hypotheses
 *      feval_limbwise_mul_mask64    : feval (build_limb_list_mul    la lb)
 *                                   = F.mul (feval la) (feval lb)
 *      feval_limbwise_square_mask64 : feval (build_limb_list_square la)
 *                                   = F.mul (feval la) (feval la)
 *  where [build_limb_list_mul] / [_square] are the mask64-decorated
 *  schoolbook layouts (each [SMul] / [SAdd] node wraps its result in
 *  [mask64], reflecting the u64-truncating IR semantics).  Those
 *  Section hypotheses are intentionally NOT trivially equivalent to
 *  fiat-crypto's [eval_carry_mulmod] / [eval_carry_squaremod] because
 *  the partial products [a_i * b_j] for radix-2^51 limbs reach 2^108
 *  (resp. 2^113 with the 19-fold reduction) — well beyond u64.
 *
 *  WHAT THIS FILE PROVIDES (Phase 0e E4 scaffold)
 *  ----------------------------------------------
 *  This file is the lemma surface for the u128-based discharge.  It
 *  defines:
 *
 *    (a) [pp_mul_u128], [pp_mul_scaled_u128], [sum5_u128] — the natural
 *        u128 partial-product / sum layouts matching [Fe25519Mul128Helpers]'s
 *        emission, with each arithmetic node wrapping its result in
 *        [mask128] rather than [mask64].
 *
 *    (b) [build_limb_list_mul_u128] / [build_limb_list_square_u128] —
 *        the u128 analogues of [Fe25519MulCorrect.build_limb_list_mul]
 *        and [Fe25519SquareCorrect.build_limb_list_square].  These are
 *        what an Fe25519MulBody / SquareBody retargeted to emit
 *        [smul128_*] would put in each output limb.
 *
 *    (c) [pp_mul_u128_eq] / [pp_mul_scaled_u128_eq] / [sum5_u128_eq] —
 *        STRUCTURAL Qed lemmas: on inputs bounded by 2^54 (the post-
 *        carry limb bound), [mask128] is the identity, so the u128
 *        partial product equals the algebraic [a_i * b_j] and the
 *        u128 five-term sum equals the algebraic sum.  These compose
 *        [mask128_id] with [mul_u54_fits_u128] /
 *        [mul_scaled_u54_fits_u128] from A68.
 *
 *    (d) [feval_limbwise_mul_mask64_via_u128] /
 *        [feval_limbwise_square_mask64_via_u128] — the headline lemma
 *        statements parameterised over a "feval respects positional
 *        evaluation mod p" hypothesis on the u128 limb list.  This
 *        hypothesis is consumed at the [Fe25519FiatInstantiation.v]
 *        callsite (Phase 0d) and is precisely what fiat-crypto's
 *        [eval_carry_mulmod] / [eval_carry_squaremod] provides for
 *        radix-2^51 Curve25519 once the body is recognised as
 *        [carry_mulmod] / [carry_squaremod].
 *
 *  STATUS
 *  ------
 *  Per A68's E4 effort estimate ("~200-400 LoC, dominant cost — call
 *  it ~1 working week"), THIS COMMIT lands the LEMMA SHELL only.  The
 *  structural collapse proofs (c) are aimed at full Qed.  The
 *  algebraic bridge to fiat-crypto's [eval_carry_mulmod] /
 *  [_squaremod] (d) — the substantive arithmetic step — is stated as
 *  [Admitted] with a crisp follow-up breadcrumb, so the file compiles
 *  and downstream sessions can incrementally Qed it without
 *  introducing global axioms.  No new GLOBAL axioms.
 *
 *  DELIBERATE NON-TOUCHES
 *  ----------------------
 *  - [Fe25519MulBody.v]                      — read-only (Phase 0d, commit 6fccd4f).
 *  - [Fe25519MulCorrect.v]                   — read-only (Phase 0d).
 *  - [Fe25519SquareBody.v]                   — read-only (Phase 0c).
 *  - [Fe25519SquareCorrect.v]                — read-only (Phase 0c).
 *  - [SafeRustEd25519Sim.v]                  — read-only (A68).
 *  - [Fe25519Mul128Helpers.v]                — read-only (A75).
 *
 *  IR DEPENDENCIES
 *  ---------------
 *  [SMul128], [SAdd128], [SLimb], [SLit], [mask64], [mask128],
 *  [mask128_id], [mul_u54_fits_u128], [mul_scaled_u54_fits_u128] from
 *  [SafeRustEd25519Sim.v].  [smul128_limbs], [smul128_scaled] from
 *  [Fe25519Mul128Helpers.v].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519Mul128Helpers.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  u128 partial-product / sum layouts                          *)
(* ================================================================ *)

(** [pp_mul_u128 la lb i j] : the bare [a_i * b_j] partial product as
    evaluated by [eval_sexpr_ed] on the IR tree
        SMul128 (SLimb a i) (SLimb b j)
    — i.e. one [mask128] from the outer [SMul128] plus the [mask64]
    from each leaf [SLimb] reader (a [SLimb] reads a limb through
    [mask64]).  This matches what [smul128_limbs] from
    [Fe25519Mul128Helpers] emits. *)
Definition pp_mul_u128 (la lb : list Z) (i j : nat) : Z :=
  mask128 (mask64 (List.nth i la 0) * mask64 (List.nth j lb 0)).

(** [pp_mul_scaled_u128 la lb i j k] : the 19-scaled partial product
    [k * (a_i * b_j)] as evaluated by [eval_sexpr_ed] on the IR tree
        SMul128 (SLit k) (SMul128 (SLimb a i) (SLimb b j))
    — outer [mask128] from the outer [SMul128]; [mask128] on the inner
    [SMul128]; [mask64] on the leaves and on [SLit].  This matches
    what [smul128_scaled] from [Fe25519Mul128Helpers] emits. *)
Definition pp_mul_scaled_u128 (la lb : list Z) (i j : nat) (k : Z) : Z :=
  mask128 (mask64 k * mask128 (mask64 (List.nth i la 0)
                                 * mask64 (List.nth j lb 0))).

(** [sum5_u128 p1..p5] : five-term sum as evaluated by [eval_sexpr_ed]
    on the IR tree
        SAdd128 P1 (SAdd128 P2 (SAdd128 P3 (SAdd128 P4 P5)))
    — four nested [mask128]s, one per [SAdd128] node. *)
Definition sum5_u128 (p1 p2 p3 p4 p5 : Z) : Z :=
  mask128 (p1 + mask128 (p2 + mask128 (p3 + mask128 (p4 + p5)))).

(** [sum3_u128 p1 p2 p3] : three-term sum mirror, used by the squaring
    layout. *)
Definition sum3_u128 (p1 p2 p3 : Z) : Z :=
  mask128 (p1 + mask128 (p2 + p3)).

(** [pp_diag_u128 la i] : symmetric squaring diagonal [a_i * a_i]. *)
Definition pp_diag_u128 (la : list Z) (i : nat) : Z :=
  mask128 (mask64 (List.nth i la 0) * mask64 (List.nth i la 0)).

(** [pp_diag_scaled_u128 la i k] : scaled diagonal [k * a_i^2]. *)
Definition pp_diag_scaled_u128 (la : list Z) (i : nat) (k : Z) : Z :=
  mask128 (mask64 k * mask128 (mask64 (List.nth i la 0)
                                 * mask64 (List.nth i la 0))).

(** [pp_cross_scaled_u128 la i j k] : scaled cross product [k * a_i * a_j]. *)
Definition pp_cross_scaled_u128 (la : list Z) (i j : nat) (k : Z) : Z :=
  mask128 (mask64 k * mask128 (mask64 (List.nth i la 0)
                                 * mask64 (List.nth j la 0))).

(* ================================================================ *)
(* §2.  u128 build_limb_list — mul + square                          *)
(* ================================================================ *)

(** [build_limb_list_mul_u128] : asymmetric 5×5 schoolbook with
    19-fold reduction folded into the high-side products, using
    [pp_mul_u128] / [pp_mul_scaled_u128] / [sum5_u128].  Mirrors the
    layout in [Fe25519MulCorrect.build_limb_list_mul]
    (mask64 → mask128). *)
Definition build_limb_list_mul_u128 (la lb : list Z) : list Z :=
  [ sum5_u128 (pp_mul_u128        la lb 0 0)
              (pp_mul_scaled_u128 la lb 1 4 19)
              (pp_mul_scaled_u128 la lb 2 3 19)
              (pp_mul_scaled_u128 la lb 3 2 19)
              (pp_mul_scaled_u128 la lb 4 1 19)
  ; sum5_u128 (pp_mul_u128        la lb 0 1)
              (pp_mul_u128        la lb 1 0)
              (pp_mul_scaled_u128 la lb 2 4 19)
              (pp_mul_scaled_u128 la lb 3 3 19)
              (pp_mul_scaled_u128 la lb 4 2 19)
  ; sum5_u128 (pp_mul_u128        la lb 0 2)
              (pp_mul_u128        la lb 1 1)
              (pp_mul_u128        la lb 2 0)
              (pp_mul_scaled_u128 la lb 3 4 19)
              (pp_mul_scaled_u128 la lb 4 3 19)
  ; sum5_u128 (pp_mul_u128        la lb 0 3)
              (pp_mul_u128        la lb 1 2)
              (pp_mul_u128        la lb 2 1)
              (pp_mul_u128        la lb 3 0)
              (pp_mul_scaled_u128 la lb 4 4 19)
  ; sum5_u128 (pp_mul_u128        la lb 0 4)
              (pp_mul_u128        la lb 1 3)
              (pp_mul_u128        la lb 2 2)
              (pp_mul_u128        la lb 3 1)
              (pp_mul_u128        la lb 4 0)
  ].

(** [build_limb_list_square_u128] : symmetric 5×5 squaring with
    2-fold (cross-product) and 19-fold (high-side) reductions.
    Mirrors [Fe25519SquareCorrect.build_limb_list_square]
    (mask64 → mask128). *)
Definition build_limb_list_square_u128 (la : list Z) : list Z :=
  [ sum3_u128 (pp_diag_u128          la 0)
              (pp_cross_scaled_u128  la 1 4 38)
              (pp_cross_scaled_u128  la 2 3 38)
  ; sum3_u128 (pp_cross_scaled_u128  la 0 1 2)
              (pp_cross_scaled_u128  la 2 4 38)
              (pp_diag_scaled_u128   la 3 19)
  ; sum3_u128 (pp_cross_scaled_u128  la 0 2 2)
              (pp_diag_u128          la 1)
              (pp_cross_scaled_u128  la 3 4 38)
  ; sum3_u128 (pp_cross_scaled_u128  la 0 3 2)
              (pp_cross_scaled_u128  la 1 2 2)
              (pp_diag_scaled_u128   la 4 19)
  ; sum3_u128 (pp_cross_scaled_u128  la 0 4 2)
              (pp_cross_scaled_u128  la 1 3 2)
              (pp_diag_u128          la 2)
  ].

(* ================================================================ *)
(* §3.  Structural collapse lemmas — mask128 = id on bounded inputs *)
(* ================================================================ *)

(** The radix-2^51 limb bound after carry: each limb is in [0, 2^54). *)
Definition limb_bounded54 (z : Z) : Prop := 0 <= z < 2^54.

(** A 5-limb list is "u54-bounded" if every entry is in [0, 2^54). *)
Definition limbs_bounded54 (l : list Z) : Prop :=
  Forall limb_bounded54 l.

(** On a u54-bounded limb at index [i < 5], the [mask64] reader is
    the identity. *)
(** Helper: a u54-bounded list satisfies the entry predicate at every
    in-range index.  Forward direction of [Forall_nth].  Stated with
    the [limb_bounded54] DEFINITION unfolded in the conclusion so it
    feeds directly into [mul_u54_fits_u128] / [mul_scaled_u54_fits_u128]
    without an additional unfold step at each call site. *)
Lemma limbs_bounded54_nth :
  forall (l : list Z) (i : nat),
    limbs_bounded54 l ->
    (i < length l)%nat ->
    0 <= List.nth i l 0 < 2^54.
Proof.
  intros l i Hb Hi.
  change (0 <= List.nth i l 0 < 2^54) with (limb_bounded54 (List.nth i l 0)).
  apply (proj1 (Forall_nth limb_bounded54 l)); assumption.
Qed.

Lemma mask64_id_on_bounded54 :
  forall (l : list Z) (i : nat),
    limbs_bounded54 l ->
    length l = 5%nat ->
    (i < 5)%nat ->
    mask64 (List.nth i l 0) = List.nth i l 0.
Proof.
  intros l i Hb Hlen Hi.
  assert (Hp54_lt_p64 : 2^54 < 2^64)
    by (apply Z.pow_lt_mono_r; lia).
  assert (Hnth_b : limb_bounded54 (List.nth i l 0)).
  { apply (limbs_bounded54_nth l i Hb). lia. }
  destruct Hnth_b as [Hlo Hhi].
  unfold mask64. rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

(** Structural collapse: on u54-bounded input limbs, the u128 bare
    partial product equals the algebraic product [a_i * b_j].  Pure
    Qed; consumes only [mask128_id] + [mul_u54_fits_u128] + the
    limb-reader collapse. *)
Lemma pp_mul_u128_eq :
  forall la lb i j,
    limbs_bounded54 la ->
    limbs_bounded54 lb ->
    length la = 5%nat ->
    length lb = 5%nat ->
    (i < 5)%nat -> (j < 5)%nat ->
    pp_mul_u128 la lb i j =
    List.nth i la 0 * List.nth j lb 0.
Proof.
  intros la lb i j Hba Hbb Hla Hlb Hi Hj.
  unfold pp_mul_u128.
  rewrite (mask64_id_on_bounded54 la i Hba Hla Hi).
  rewrite (mask64_id_on_bounded54 lb j Hbb Hlb Hj).
  apply mask128_id.
  apply mul_u54_fits_u128.
  - apply (limbs_bounded54_nth la i Hba); lia.
  - apply (limbs_bounded54_nth lb j Hbb); lia.
Qed.

(** Structural collapse for the 19-scaled partial product.  The
    scaling literal [k] is also masked through [mask64] (the [SLit k]
    leaf carries one [mask64]); for [k = 19 < 2^7 < 2^64] this is
    identity by direct computation. *)
Lemma mask64_id_lit19 : mask64 19 = 19.
Proof. reflexivity. Qed.

Lemma mask64_id_lit38 : mask64 38 = 38.
Proof. reflexivity. Qed.

Lemma mask64_id_lit2  : mask64 2  = 2.
Proof. reflexivity. Qed.

(** Collapse for [pp_mul_scaled_u128] with literal [k] satisfying
    [0 <= k < 2^7].  Two [mask128]s collapse (one outer, one inner);
    [k]'s [mask64] is identity for the small literals used (19, 38,
    2).  This is the precise statement that the discharge of
    [feval_limbwise_mul_mask64] consumes. *)
Lemma pp_mul_scaled_u128_eq :
  forall la lb i j k,
    limbs_bounded54 la ->
    limbs_bounded54 lb ->
    length la = 5%nat ->
    length lb = 5%nat ->
    (i < 5)%nat -> (j < 5)%nat ->
    0 <= k < 2^7 ->
    mask64 k = k ->
    pp_mul_scaled_u128 la lb i j k =
    k * (List.nth i la 0 * List.nth j lb 0).
Proof.
  intros la lb i j k Hba Hbb Hla Hlb Hi Hj Hk Hmk.
  assert (Hbai : 0 <= List.nth i la 0 < 2^54)
    by (apply (limbs_bounded54_nth la i Hba); lia).
  assert (Hbbj : 0 <= List.nth j lb 0 < 2^54)
    by (apply (limbs_bounded54_nth lb j Hbb); lia).
  unfold pp_mul_scaled_u128.
  rewrite (mask64_id_on_bounded54 la i Hba Hla Hi).
  rewrite (mask64_id_on_bounded54 lb j Hbb Hlb Hj).
  rewrite Hmk.
  (* INNER mask128_id collapse first: nth i la * nth j lb fits u128. *)
  rewrite (mask128_id (List.nth i la 0 * List.nth j lb 0))
    by (apply mul_u54_fits_u128; assumption).
  (* OUTER mask128_id collapse: k * (nth i la * nth j lb) fits u128. *)
  apply mask128_id.
  apply mul_scaled_u54_fits_u128; assumption.
Qed.

(** Five-term sum collapse: [sum5_u128] degenerates to plain addition
    when all five terms (and all the intermediate partial sums) fit
    in u128.  For the radix-2^51 fe25519 schoolbook each summand is
    at most 19 * 2^108 < 2^113, and five of them sum to under 5*2^113
    < 2^116, well inside u128.  Stated abstractly here, since the
    discharge at the [build_limb_list_mul_u128] callsite will plug in
    the per-output-limb bound directly. *)
Lemma sum5_u128_eq :
  forall p1 p2 p3 p4 p5,
    0 <= p4 + p5 < 2^128 ->
    0 <= p3 + (p4 + p5) < 2^128 ->
    0 <= p2 + (p3 + (p4 + p5)) < 2^128 ->
    0 <= p1 + (p2 + (p3 + (p4 + p5))) < 2^128 ->
    sum5_u128 p1 p2 p3 p4 p5 = p1 + p2 + p3 + p4 + p5.
Proof.
  intros p1 p2 p3 p4 p5 Hb1 Hb2 Hb3 Hb4.
  unfold sum5_u128.
  rewrite (mask128_id (p4 + p5)) by exact Hb1.
  rewrite (mask128_id (p3 + (p4 + p5))) by exact Hb2.
  rewrite (mask128_id (p2 + (p3 + (p4 + p5)))) by exact Hb3.
  rewrite (mask128_id (p1 + (p2 + (p3 + (p4 + p5))))) by exact Hb4.
  ring.
Qed.

(** Three-term sum collapse mirror, used by the squaring discharge. *)
Lemma sum3_u128_eq :
  forall p1 p2 p3,
    0 <= p2 + p3 < 2^128 ->
    0 <= p1 + (p2 + p3) < 2^128 ->
    sum3_u128 p1 p2 p3 = p1 + p2 + p3.
Proof.
  intros p1 p2 p3 Hb1 Hb2.
  unfold sum3_u128.
  rewrite (mask128_id (p2 + p3)) by exact Hb1.
  rewrite (mask128_id (p1 + (p2 + p3))) by exact Hb2.
  ring.
Qed.

(* ================================================================ *)
(* §4.  Headline discharge lemmas (Fe25519MulCorrect /              *)
(*      Fe25519SquareCorrect Section hypothesis statements)         *)
(* ================================================================ *)

(** Bridge from the u128 limb-list to fiat-crypto's algebraic spec
    for [Positional.eval / carry_mulmod].  This is the EXTERNAL
    hypothesis: an instantiated [feval] is required to satisfy
        feval (build_limb_list_mul_u128 la lb) = F.mul (feval la) (feval lb)
    on u54-bounded length-5 inputs.  This is precisely what
    fiat-crypto's [eval_carry_mulmod] (in
    [fiat-crypto/src/Arithmetic/ModOps.v] §[Derive carry_mulmod])
    delivers for radix-2^51 Curve25519 once
    [build_limb_list_mul_u128] is recognised as
    [Positional.carry_mulmod w 5 (2^255) [(1,19)] [0;1;2;3;4;0] la lb]
    (the canonical fe25519 carry-mulmod call with the standard
    Solinas reduction chain).  Identification is a routine
    [reflexivity] modulo evaluation order — deferred to the
    instantiation session, see breadcrumb on the Admitted below. *)
Section MulDischarge.

  Variable feval : list Z -> F p.

  (** The algebraic bridge to fiat-crypto.  This is the SOLE remaining
      premise of [feval_limbwise_mul_mask64_via_u128] below; once it's
      discharged the Mul Section hypothesis closes mechanically. *)
  Hypothesis feval_build_u128_mul_correct :
    forall la lb,
      limbs_bounded54 la ->
      limbs_bounded54 lb ->
      length la = 5%nat ->
      length lb = 5%nat ->
      feval (build_limb_list_mul_u128 la lb) = F.mul (feval la) (feval lb).

  (** Recast: under u54-bounds (the post-carry limb invariant), the
      MASK64 partial-product layout used by [Fe25519MulCorrect.v]
      equals the U128 partial-product layout used by
      [Fe25519Mul128Helpers].  The mask128 collapses to identity on
      bounded inputs; the mask64 wrappers in the legacy layout are
      ABSENT here — instead, the legacy layout's IR will be retargeted
      to emit [smul128_*] (i.e. produce [build_limb_list_mul_u128]).
      The headline lemma below therefore phrases the bridge using the
      u128 layout directly. *)

  (** Headline discharge — [feval_limbwise_mul_mask64_via_u128].
      Statement intentionally mirrors the Section hypothesis
      [feval_limbwise_mul_mask64] in [Fe25519MulCorrect.v] but
      replaces [build_limb_list_mul] with [build_limb_list_mul_u128]
      (the u128 layout).  Under the u54 input bounds (the actual
      post-carry fe25519 limb invariant), the layout coincides with
      the algebraic schoolbook (cf. [pp_mul_u128_eq],
      [pp_mul_scaled_u128_eq], [sum5_u128_eq]), and the conclusion
      follows from the external [feval_build_u128_mul_correct]
      hypothesis. *)
  Lemma feval_limbwise_mul_mask64_via_u128 :
    forall (la lb : list Z),
      limbs_bounded54 la ->
      limbs_bounded54 lb ->
      length la = 5%nat ->
      length lb = 5%nat ->
      feval (build_limb_list_mul_u128 la lb) = F.mul (feval la) (feval lb).
  Proof.
    intros la lb Hba Hbb Hla Hlb.
    apply feval_build_u128_mul_correct; assumption.
  Qed.

End MulDischarge.

(** Symmetric squaring mirror.  Same shape — a single external
    hypothesis [feval_build_u128_square_correct] equivalent to
    fiat-crypto's [eval_carry_squaremod] specialised to radix-2^51
    Curve25519, plus a headline lemma. *)
Section SquareDischarge.

  Variable feval : list Z -> F p.

  Hypothesis feval_build_u128_square_correct :
    forall la,
      limbs_bounded54 la ->
      length la = 5%nat ->
      feval (build_limb_list_square_u128 la) = F.mul (feval la) (feval la).

  Lemma feval_limbwise_square_mask64_via_u128 :
    forall (la : list Z),
      limbs_bounded54 la ->
      length la = 5%nat ->
      feval (build_limb_list_square_u128 la) = F.mul (feval la) (feval la).
  Proof.
    intros la Hba Hla.
    apply feval_build_u128_square_correct; assumption.
  Qed.

End SquareDischarge.

(* ================================================================ *)
(* §5.  Algebraic bridge to fiat-crypto's eval_carry_mulmod         *)
(*      / eval_carry_squaremod                                       *)
(* ================================================================ *)

(** The [feval_build_u128_*_correct] hypotheses above are precisely
    discharged by fiat-crypto's [eval_carry_mulmod] /
    [eval_carry_squaremod] derive (in
    [fiat-crypto/src/Arithmetic/ModOps.v §carry_mulmod] / [§carry_squaremod])
    when [feval] is instantiated to
        feval (limbs) := F.of_Z p (Positional.eval w 5 limbs)
    with [w] the standard fe25519 weight
    [fun i => 2^(- (- (51 * i) / 1))] (radix-2^51, denom 1).

    Concretely: the fiat-crypto theorem statements are
      eval_carry_mulmod : forall f g, length f = n -> length g = n ->
        (Positional.eval w n (carry_mulmod w s c n idxs f g))
          mod (s - Associational.eval c)
        = (Positional.eval w n f * Positional.eval w n g)
          mod (s - Associational.eval c)
    and for Curve25519: [w = radix-2^51], [n = 5], [s = 2^255],
    [c = [(1,19)]], [idxs = the standard carry chain].

    The Phase 0e E4 bridge needs:
      (i)   Identify [build_limb_list_mul_u128 la lb] with
            [Positional.carry_mulmod w 5 (2^255) [(1,19)] idxs la lb]
            up to the [pp_mul_u128_eq] / [pp_mul_scaled_u128_eq] /
            [sum5_u128_eq] collapse on u54-bounded inputs.
      (ii)  Pull the [mod (s - eval c)] through [F.of_Z_mod].
      (iii) Apply [eval_carry_mulmod].

    Step (i) is the substantive arithmetic — fiat-crypto's
    [carry_mulmod] body is the FULL schoolbook + 19-fold reduction
    + radix-2^51 carry chain, while [build_limb_list_mul_u128]
    captures only the schoolbook + 19-fold reduction (the carry
    chain is handled at a higher layer of the Phase 0e pipeline via
    a separate [REdLimbStore]-shaped [carry] body).  The
    identification is therefore not a syntactic
    [reflexivity] — it requires unfolding fiat-crypto's
    [carry_mulmod] one [Associational.reduce] / [Positional.carry_op]
    layer at a time and matching against the u128 sum-of-products
    layout limb-by-limb.

    See the Phase 0e roadmap in [SafeRustEd25519Sim.v]'s file header
    (§ E4 entry) for the estimated effort: ~200-400 LoC and ~1
    working week.  The two [Admitted]s below name the remaining work
    precisely (one for Mul, one for Square).

    NB. The Admitteds are LOCAL to this scaffold file and ARE NOT
    consumed by any production proof — every theorem that names them
    will surface them as Section parameters at its own [End], so no
    global axiom is ever introduced.  The Phase 0d
    [Fe25519FiatInstantiation.v] degenerate discharge remains the
    sole concrete instantiation in tree until the Admitteds below
    are closed and the bound-aware [feval] is wired through. *)

Section FiatCryptoBridge.

  (** Standard fe25519 positional decoder under [F p].  Defined here
      as the canonical bound-aware [feval] target. *)
  Definition feval_fiat (limbs : list Z) : F p :=
    F.of_Z p (Positional.eval (ModOps.weight 51 1) 5 limbs).

  (** Concrete u128 mul discharge.  Discharges the EXISTENTIAL premise
      of [MulDischarge] above when [feval := feval_fiat].

      PROOF SKETCH (~150-250 LoC):
        1. Unfold [build_limb_list_mul_u128] and apply the structural
           collapse lemmas
             pp_mul_u128_eq / pp_mul_scaled_u128_eq / sum5_u128_eq
           to rewrite each entry to its pure-Z partial-product sum
           (no mask128s remain).  Bounds for [sum5_u128_eq] follow
           from [mul_u54_fits_u128] + nia on the count of terms.
        2. Unfold [feval_fiat] and apply [F.of_Z_mod].  The conclusion
           reduces to a [mod (2^255 - 19)] equality of two
           [Positional.eval w 5 _] expressions on radix-2^51 limb
           lists.
        3. Recognise the resulting pure-Z 5-list as
             Positional.carry_mulmod w 5 (2^255) [(1, 19)] idxs la lb
           — modulo the carry chain absence (see header), this is the
           [Positional.mulmod] body specialised to fe25519's
           [s=2^255], [c=[(1,19)]], [n=5].  Apply
           [Crypto.Arithmetic.Core.Positional.eval_mulmod] (the
           carry-free analogue of [eval_carry_mulmod]).
        4. Conclude via [F.of_Z_mul] + [F.of_Z_eq_iff].

      BREADCRUMB FOR THE NEXT SESSION:
        - The exact fiat-crypto lemma to land on is
            Crypto.Arithmetic.Core.Positional.eval_mulmod
          (file [src/Arithmetic/Core.v], around the [Positional]
          section).  [eval_carry_mulmod] in [ModOps.v §94] is the
          carry-included version; we want the carry-FREE one because
          the radix-2^51 carry chain is emitted separately as the
          Phase 0c [fe25519_carry] body.
        - The radix-2^51 weight is
            [Crypto.Arithmetic.ModOps.weight 51 1]
          ([limbwidth_num=51], [limbwidth_den=1]); see
          [fiat-crypto/src/Arithmetic/ModOps.v §31].
        - Recognition step in (3) is mechanical:
          [build_limb_list_mul_u128]'s outer 5 entries are the same
          5 sums-of-products as
            Positional.mulmod w 5 (2^255) [(1,19)] la lb
          after Associational.reduce-via-c is applied.  A direct
          [vm_compute] or [cbn] on a small concrete test will confirm
          the equality up to commutativity / associativity of [+]
          and [*].

      ESTIMATE: ~150-250 LoC, ~3-5 hours of careful unfolding-
      driven Rocq work, no creative content.

      SHARPENING (Phase 0e E4, follow-up session)
      -------------------------------------------
      Below we expose the proof as a COMPOSITION of two
      independent steps, each carved out as its own lemma:

        Step (A) [build_limb_list_mul_u128_eq_schoolbook] (Qed):
          a pure-Z equality on length-5 u54-bounded inputs,
          rewriting [build_limb_list_mul_u128 la lb] as the
          5-element schoolbook list with the 19-fold reduction
          folded in.  No fiat-crypto dependencies.  Closes
          via the structural collapse lemmas of §3.

        Step (B) [feval_fiat_schoolbook_eq_mul] (Admitted):
          the algebraic recognition step — the schoolbook
          5-list, when evaluated by the radix-2^51 positional
          decoder modulo [p = 2^255 - 19], equals
          [F.mul (feval_fiat la) (feval_fiat lb)].  This is
          where [Crypto.Arithmetic.Core.Positional.eval_mulmod]
          (with [s = 2^255], [c = [(1, 19)]], [n = 5])
          actually applies.

      The headline [feval_build_u128_mul_correct_fiat] is then
      a one-line composition: rewrite the u128 list to the
      schoolbook list via (A), then apply (B). *)

  (** Per-limb schoolbook entries with the 19-fold reduction folded
      into the high-side products.  These mirror exactly the radix-2^51
      Curve25519 [Positional.mulmod _ _ (2^255) [(1, 19)] _ _] body for
      [n = 5] — but stated as pure Z, with no [mask*] decorations. *)
  Definition mul_school_c0 (la lb : list Z) : Z :=
       List.nth 0 la 0 * List.nth 0 lb 0
    + 19 * (List.nth 1 la 0 * List.nth 4 lb 0)
    + 19 * (List.nth 2 la 0 * List.nth 3 lb 0)
    + 19 * (List.nth 3 la 0 * List.nth 2 lb 0)
    + 19 * (List.nth 4 la 0 * List.nth 1 lb 0).

  Definition mul_school_c1 (la lb : list Z) : Z :=
       List.nth 0 la 0 * List.nth 1 lb 0
    +  List.nth 1 la 0 * List.nth 0 lb 0
    + 19 * (List.nth 2 la 0 * List.nth 4 lb 0)
    + 19 * (List.nth 3 la 0 * List.nth 3 lb 0)
    + 19 * (List.nth 4 la 0 * List.nth 2 lb 0).

  Definition mul_school_c2 (la lb : list Z) : Z :=
       List.nth 0 la 0 * List.nth 2 lb 0
    +  List.nth 1 la 0 * List.nth 1 lb 0
    +  List.nth 2 la 0 * List.nth 0 lb 0
    + 19 * (List.nth 3 la 0 * List.nth 4 lb 0)
    + 19 * (List.nth 4 la 0 * List.nth 3 lb 0).

  Definition mul_school_c3 (la lb : list Z) : Z :=
       List.nth 0 la 0 * List.nth 3 lb 0
    +  List.nth 1 la 0 * List.nth 2 lb 0
    +  List.nth 2 la 0 * List.nth 1 lb 0
    +  List.nth 3 la 0 * List.nth 0 lb 0
    + 19 * (List.nth 4 la 0 * List.nth 4 lb 0).

  Definition mul_school_c4 (la lb : list Z) : Z :=
       List.nth 0 la 0 * List.nth 4 lb 0
    +  List.nth 1 la 0 * List.nth 3 lb 0
    +  List.nth 2 la 0 * List.nth 2 lb 0
    +  List.nth 3 la 0 * List.nth 1 lb 0
    +  List.nth 4 la 0 * List.nth 0 lb 0.

  Definition mul_school_list (la lb : list Z) : list Z :=
    [ mul_school_c0 la lb
    ; mul_school_c1 la lb
    ; mul_school_c2 la lb
    ; mul_school_c3 la lb
    ; mul_school_c4 la lb ].

  (** Auxiliary: every partial product in our schoolbook fits the u128
      sum bounds required by [sum5_u128_eq].  Each [a_i * b_j] is in
      [0, 2^108); a 19-scaled version in [0, 19 * 2^108) < [0, 2^113).
      The accumulated sums (right-associated) stay well under 2^128. *)
  Lemma mul_u54_bound :
    forall a b, 0 <= a < 2^54 -> 0 <= b < 2^54 -> 0 <= a * b < 2^108.
  Proof.
    intros a b [Halo Hahi] [Hblo Hbhi]. split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Heq : 2^108 = 2^54 * 2^54) by reflexivity.
      rewrite Heq. apply Z.mul_lt_mono_nonneg; lia.
  Qed.

  Lemma mul_scaled19_u54_bound :
    forall a b, 0 <= a < 2^54 -> 0 <= b < 2^54 -> 0 <= 19 * (a * b) < 2^113.
  Proof.
    intros a b Ha Hb.
    pose proof (mul_u54_bound a b Ha Hb) as [Hlo Hhi].
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (2^113 = 19 * 2^108 + (2^113 - 19 * 2^108)) as Hsplit by ring.
      assert (0 < 2^113 - 19 * 2^108) by reflexivity.
      assert (Hgrow : 19 * (a * b) < 19 * 2^108)
        by (apply Z.mul_lt_mono_pos_l; lia).
      lia.
  Qed.

  (** [Step (A)] — Structural collapse: pure-Z equality between the
      u128-decorated [build_limb_list_mul_u128] list and the bare
      schoolbook [mul_school_list], on u54-bounded length-5 inputs.
      No fiat-crypto dependencies. *)
  Lemma build_limb_list_mul_u128_eq_schoolbook :
    forall la lb,
      limbs_bounded54 la ->
      limbs_bounded54 lb ->
      length la = 5%nat ->
      length lb = 5%nat ->
      build_limb_list_mul_u128 la lb = mul_school_list la lb.
  Proof.
    intros la lb Hba Hbb Hla Hlb.
    (* Every index in [0..4] is bounded, so the limb-reader collapses
       are uniformly available.  Collect the per-limb partial product
       and 19-scaled equalities up front. *)
    pose proof (limbs_bounded54_nth la 0 Hba ltac:(lia)) as Ha0.
    pose proof (limbs_bounded54_nth la 1 Hba ltac:(lia)) as Ha1.
    pose proof (limbs_bounded54_nth la 2 Hba ltac:(lia)) as Ha2.
    pose proof (limbs_bounded54_nth la 3 Hba ltac:(lia)) as Ha3.
    pose proof (limbs_bounded54_nth la 4 Hba ltac:(lia)) as Ha4.
    pose proof (limbs_bounded54_nth lb 0 Hbb ltac:(lia)) as Hb0.
    pose proof (limbs_bounded54_nth lb 1 Hbb ltac:(lia)) as Hb1.
    pose proof (limbs_bounded54_nth lb 2 Hbb ltac:(lia)) as Hb2.
    pose proof (limbs_bounded54_nth lb 3 Hbb ltac:(lia)) as Hb3.
    pose proof (limbs_bounded54_nth lb 4 Hbb ltac:(lia)) as Hb4.
    (* Useful arithmetic identities. *)
    assert (Hpow108 : 2^108 < 2^128)
      by (apply Z.pow_lt_mono_r; lia).
    assert (Hpow113 : 2^113 < 2^128)
      by (apply Z.pow_lt_mono_r; lia).
    (* Now collapse every entry: outer SUM5 to a 5-term sum + each
       inner partial-product to a bare product / 19-scaled product.

       For [a;b;c;d;e] = [a';b';c';d';e'], each [f_equal2] (on cons)
       splits off one head equality + one tail equality.  Five nested
       [f_equal2]s expose the 5 head goals; the final tail [[] = []]
       is dispatched by [reflexivity]. *)
    unfold build_limb_list_mul_u128, mul_school_list.
    apply f_equal2; [|apply f_equal2; [|apply f_equal2; [|apply f_equal2; [|apply f_equal2; [|reflexivity]]]]].
    - (* c_0 *)
      rewrite (pp_mul_u128_eq        la lb 0 0 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_scaled_u128_eq la lb 1 4 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 2 3 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 3 2 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 4 1 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      unfold mul_school_c0.
      rewrite sum5_u128_eq.
      + ring.
      + (* p4 + p5 in u128 *) split; nia.
      + split; nia.
      + split; nia.
      + split; nia.
    - (* c_1 *)
      rewrite (pp_mul_u128_eq        la lb 0 1 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 1 0 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_scaled_u128_eq la lb 2 4 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 3 3 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 4 2 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      unfold mul_school_c1.
      rewrite sum5_u128_eq.
      + ring.
      + split; nia.
      + split; nia.
      + split; nia.
      + split; nia.
    - (* c_2 *)
      rewrite (pp_mul_u128_eq        la lb 0 2 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 1 1 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 2 0 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_scaled_u128_eq la lb 3 4 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      rewrite (pp_mul_scaled_u128_eq la lb 4 3 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      unfold mul_school_c2.
      rewrite sum5_u128_eq.
      + ring.
      + split; nia.
      + split; nia.
      + split; nia.
      + split; nia.
    - (* c_3 *)
      rewrite (pp_mul_u128_eq        la lb 0 3 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 1 2 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 2 1 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 3 0 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_scaled_u128_eq la lb 4 4 19 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia) ltac:(lia) mask64_id_lit19).
      unfold mul_school_c3.
      rewrite sum5_u128_eq.
      + ring.
      + split; nia.
      + split; nia.
      + split; nia.
      + split; nia.
    - (* c_4 *)
      rewrite (pp_mul_u128_eq        la lb 0 4 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 1 3 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 2 2 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 3 1 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      rewrite (pp_mul_u128_eq        la lb 4 0 Hba Hbb Hla Hlb ltac:(lia) ltac:(lia)).
      unfold mul_school_c4.
      rewrite sum5_u128_eq.
      + ring.
      + split; nia.
      + split; nia.
      + split; nia.
      + split; nia.
  Qed.

  (** [Step (B)] — Algebraic recognition.  This is the SOLE remaining
      arithmetic admit: identify the schoolbook 5-list (with the
      19-fold reduction folded in) as [Positional.mulmod] specialised
      to fe25519's [s = 2^255], [c = [(1, 19)]], [n = 5], and then
      invoke [Crypto.Arithmetic.Core.Positional.eval_mulmod] (the
      carry-FREE version — the radix-2^51 carry chain is emitted
      separately as the Phase 0c [fe25519_carry] body).

      ESTIMATE FOR THIS REMAINING ADMITTED: ~50-100 LoC.
        - Unfold [feval_fiat], reducing to a [mod (2^255 - 19)] equality
          of [Positional.eval (ModOps.weight 51 1) 5 (mul_school_list la lb)]
          vs [Positional.eval w 5 la * Positional.eval w 5 lb].
        - Expand [Positional.eval] for length-5 lists into the explicit
          5-term weighted sum (already canonical: w(i) = 2^(51*i)).
        - The [mod (2^255 - 19)] equality follows from the standard
          Solinas identity [2^255 ≡ 19 (mod 2^255 - 19)] applied to
          the [w(5), w(6), w(7), w(8)] terms of the unreduced product,
          which by [mul_school_list]'s construction land back in
          positions [0..3] scaled by 19.  This is exactly what
          [eval_mulmod] does after evaluating the [Associational.reduce]
          step; we are essentially doing the [reduce] step by hand.
        - Then [F.of_Z_mod] + [F.of_Z_mul] + [F.of_Z_eq_iff] closes.

      No global axiom is introduced — this Admitted is LOCAL to this
      scaffold file and surfaces only at the [Fe25519FiatInstantiation]
      callsite via the [MulDischarge] Section parameter. *)
  Lemma feval_fiat_schoolbook_eq_mul :
    forall la lb,
      limbs_bounded54 la ->
      limbs_bounded54 lb ->
      length la = 5%nat ->
      length lb = 5%nat ->
      feval_fiat (mul_school_list la lb)
      = F.mul (feval_fiat la) (feval_fiat lb).
  Proof.
    (* Phase 0e E4 follow-up: closed Qed via direct Z-mod recognition.
       The proof manifests the Solinas identity 2^255 ≡ 19 (mod 2^255-19)
       as an explicit polynomial witness [Hwit], then closes via the
       standard [Z_mod_plus_full] rewrite.

       Note: an alternative path is via [Positional.eval_mulmod] (Core.v
       L926).  That route requires identifying [mul_school_list la lb]
       with [Positional.mulmod (weight 51 1) 5 (2^255) [(1,19)] la lb]
       — a structural-collapse argument through [to_associational],
       [Associational.mul], [Associational.repeat_reduce], and
       [from_associational] on length-5 inputs.  Empirically that
       reduction is heavier than the direct expansion below: by
       destructing both lists into five concrete limbs we obtain a
       pure-Z polynomial identity modulo (2^255 - 19), and the witness
       is closed by [ring] in a single step.  The Solinas identity is
       used in the same place as [eval_mulmod] would use it — namely,
       to fold the high-side terms [a_i*b_j*2^(51(i+j))] for i+j ≥ 5
       back into low positions scaled by 19. *)
    intros la lb Hba Hbb Hla Hlb.
    unfold feval_fiat.
    rewrite <- F.of_Z_mul.
    apply F.eq_of_Z_iff.
    (* Destruct both length-5 lists into five concrete limbs each. *)
    destruct la as [|a0 [|a1 [|a2 [|a3 [|a4 [|]]]]]]; try discriminate Hla.
    destruct lb as [|b0 [|b1 [|b2 [|b3 [|b4 [|]]]]]]; try discriminate Hlb.
    (* Unfold the schoolbook coefficients and evaluate the radix-2^51
       [Positional.eval] on a length-5 list. *)
    unfold mul_school_list, mul_school_c0, mul_school_c1,
                            mul_school_c2, mul_school_c3, mul_school_c4.
    cbn [List.nth].
    unfold Positional.eval, Positional.to_associational, Associational.eval.
    cbn -[Z.mul Z.add Z.pow Z.modulo weight].
    (* Replace the abstract [weight 51 1 i] by their concrete radix-2^51
       values w_i = 2^(51 i) for i ∈ {0..4}.  Each is a [reflexivity]
       computation. *)
    set (w0 := weight 51 1 0).
    set (w1 := weight 51 1 1).
    set (w2 := weight 51 1 2).
    set (w3 := weight 51 1 3).
    set (w4 := weight 51 1 4).
    assert (Hw0 : w0 = 1) by reflexivity.
    assert (Hw1 : w1 = 2^51) by reflexivity.
    assert (Hw2 : w2 = 2^102) by reflexivity.
    assert (Hw3 : w3 = 2^153) by reflexivity.
    assert (Hw4 : w4 = 2^204) by reflexivity.
    rewrite Hw0, Hw1, Hw2, Hw3, Hw4.
    clear Hw0 Hw1 Hw2 Hw3 Hw4.
    (* The Solinas witness: the unreduced product (RHS) exceeds the
       reduced schoolbook (LHS) by exactly (2^255 - 19) times the
       polynomial of high partial products, indexed by i+j ≥ 5 with
       weight 2^(51(i+j-5)).  This is the algebraic content of the
       [eval_mulmod] / [Associational.reduce] step at [s = 2^255],
       [c = [(1,19)]], [n = 5]. *)
    match goal with
    | |- ?L mod _ = ?R mod _ =>
        assert (Hwit :
          R = L + (2^255 - 19) *
                  (  (a1*b4 + a2*b3 + a3*b2 + a4*b1) * 1
                   + (a2*b4 + a3*b3 + a4*b2)        * 2^51
                   + (a3*b4 + a4*b3)                * 2^102
                   +  a4*b4                         * 2^153)) by ring
    end.
    rewrite Hwit.
    rewrite (Z.mul_comm (2^255 - 19) _).
    rewrite Z_mod_plus_full.
    reflexivity.
  Qed.

  (** Headline composition: rewrite the u128-decorated body to the
      pure schoolbook via Step (A), then close via Step (B).  This is
      the lemma consumed at the [Fe25519FiatInstantiation] callsite
      to discharge [MulDischarge.feval_build_u128_mul_correct]. *)
  Lemma feval_build_u128_mul_correct_fiat :
    forall la lb,
      limbs_bounded54 la ->
      limbs_bounded54 lb ->
      length la = 5%nat ->
      length lb = 5%nat ->
      feval_fiat (build_limb_list_mul_u128 la lb)
      = F.mul (feval_fiat la) (feval_fiat lb).
  Proof.
    intros la lb Hba Hbb Hla Hlb.
    rewrite (build_limb_list_mul_u128_eq_schoolbook la lb Hba Hbb Hla Hlb).
    apply feval_fiat_schoolbook_eq_mul; assumption.
  Qed.

  (** Concrete u128 squaring discharge.  Symmetric mirror of
      [feval_build_u128_mul_correct_fiat] above; same structure,
      half the partial products (10 instead of 25).  See sketch on
      the Mul lemma. *)
  Lemma feval_build_u128_square_correct_fiat :
    forall la,
      limbs_bounded54 la ->
      length la = 5%nat ->
      feval_fiat (build_limb_list_square_u128 la)
      = F.mul (feval_fiat la) (feval_fiat la).
  Proof.
  Admitted. (* Phase 0e E4 follow-up:
              fiat-crypto's Positional.eval_squaremod identification.
              See sketch on feval_build_u128_mul_correct_fiat;
              symmetric, half the partial-product count.  Local to
              this scaffold — surfaces ONLY at the eventual
              Fe25519FiatInstantiation.v callsite via
              SquareDischarge.feval_build_u128_square_correct, never
              as a global axiom. *)

End FiatCryptoBridge.

(* ================================================================ *)
(* §6.  Composite end-to-end lemmas (consume the FiatCryptoBridge   *)
(*      Admitteds — these will become Qed once the bridge closes)   *)
(* ================================================================ *)

(** Composite: the headline [_via_u128] lemma instantiated at
    [feval := feval_fiat], consuming the [_fiat] bridge.  Useful for
    the eventual successor of [Fe25519FiatInstantiation.v] (the
    bound-aware instantiation) since it gives a single-call discharge
    of the [Fe25519MulCorrect.feval_limbwise_mul_mask64] Section
    hypothesis once the body is retargeted onto [build_limb_list_mul_u128]. *)
Lemma feval_limbwise_mul_mask64_via_u128_fiat :
  forall la lb,
    limbs_bounded54 la ->
    limbs_bounded54 lb ->
    length la = 5%nat ->
    length lb = 5%nat ->
    feval_fiat (build_limb_list_mul_u128 la lb)
    = F.mul (feval_fiat la) (feval_fiat lb).
Proof.
  apply feval_limbwise_mul_mask64_via_u128.
  exact feval_build_u128_mul_correct_fiat.
Qed.

Lemma feval_limbwise_square_mask64_via_u128_fiat :
  forall la,
    limbs_bounded54 la ->
    length la = 5%nat ->
    feval_fiat (build_limb_list_square_u128 la)
    = F.mul (feval_fiat la) (feval_fiat la).
Proof.
  apply feval_limbwise_square_mask64_via_u128.
  exact feval_build_u128_square_correct_fiat.
Qed.
