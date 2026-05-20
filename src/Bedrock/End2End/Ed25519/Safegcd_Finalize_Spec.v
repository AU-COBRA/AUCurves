(** * Safegcd_Finalize_Spec — Gallina spec + Z-bridge for the
 *    [safegcd_finalize] leaf of the divstep-based fe25519 inverter.
 *
 *  Scope
 *  =====
 *  This file states the *algebraic* contract that any concrete
 *  implementation of the [safegcd_finalize] leaf (bedrock2 body,
 *  hand-written safe Rust, asm wrapper) must satisfy in order for
 *  the composite [fe25519_invert_v2_body] (in
 *  [Fe25519InvertBodyV2.v]) to compute [a^{-1} mod p25519].
 *
 *  Algebraically [safegcd_finalize] does two things in one shot:
 *
 *    1. *Sign-correct* the accumulator [V] by the sign of [F].
 *       After 590 divsteps, [|F| = 1] (paper Theorem 1), so the
 *       value [V * 2^{-590} mod p] is the inverse up to sign;
 *       multiplying by [sign(F)] (encoded as a top-bit test on
 *       [F[3]]) repairs the sign:
 *
 *          v_corrected = if F < 0 then (m - V) mod m
 *                        else V mod m
 *
 *    2. *Cancel the 2^N factor* introduced by the [V, R] update
 *       rule across the loop.  This is a single multiplication by
 *       the precomputed constant [precomp_val = 2^{-590} mod p]
 *       from [Fe25519_FpInv.precomp_val]:
 *
 *          out = (v_corrected * precomp_val) mod m
 *
 *  Two layers of spec are exposed (mirroring [Safegcd_Step59_Spec.v]):
 *
 *  • [safegcd_finalize_spec]    — list-of-limb form, mirroring the
 *    Rust [REdCall "safegcd_finalize" out [V; F]] leaf from
 *    [Fe25519InvertBodyV2.v].  Stub for now.
 *
 *  • [safegcd_finalize_spec_Z]  — abstract integer form: takes the
 *    modulus [m] and the post-loop [d], [F], [V] Z-values, returns
 *    the inverse-modulo-m as a Z.  Matches the closing two lines
 *    of [Fe25519_FpInv.fp_inv_spec].
 *
 *  The composition lemma [safegcd_finalize_correct_Z] is stated and
 *  [Admitted] with a sketch.
 *
 *  Compile cost
 *  ============
 *  Definitions only — < 5 s on rocq-9.
 *
 *  Cross-references
 *  ================
 *  • Rust source:   curve25519-jasmin-rs/src/safegcd.rs §finalize
 *  • Skeleton AST:  src/Bedrock/End2End/Ed25519/Fe25519InvertBodyV2.v §2
 *  • Z-level spec:  src/Bedrock/Field/Synthesis/Examples/Fe25519_FpInv.v
 *                   [fp_inv_spec] §closing two lines.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Arithmetic.BYInv.
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.
Require Import Bedrock.End2End.Ed25519.Safegcd_Step59_Spec.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================== *)
(* §1.  Abstract-Z spec layer                                          *)
(* ================================================================== *)

(** Z-level functional spec for [safegcd_finalize].

    Inputs:
      - [m]    : modulus
      - [d]    : post-loop δ-encoding (unused at this stage — the
                 caller has already exhausted the divsteps)
      - [F]    : post-loop value of [F]; expected to be [±1]
      - [V]    : post-loop accumulator
    Output:
      - Z value of the modular inverse — i.e. the same expression
        appearing in the last two lines of [fp_inv_spec]. *)
Definition safegcd_finalize_spec_Z (m d F V : Z) : Z :=
  let v_corrected := if F <? 0 then (m - V) mod m else V mod m in
  (v_corrected * precomp_val) mod m.

(** Sanity: at the [m := p25519] instantiation and *any* post-loop
    triple [(d, F, V)] satisfying [F = ±1] and [0 ≤ V < p], the
    output matches the corresponding tail of [fp_inv_spec].

    The point is that running [iter_divstep_spec_half p25519 590
    (-1) p25519 x 0 1], then feeding the final triple
    [(d, F, V)] into [safegcd_finalize_spec_Z p25519], produces
    [fp_inv_spec x] exactly.  This is what
    [Safegcd_Outer_Loop_Chain.v] formalises. *)
Lemma safegcd_finalize_spec_Z_matches_fp_inv_tail :
  forall x d F G V R,
    iter_divstep_spec_half p25519 (Z.to_nat p25519_divstep_iters)
                           (-1) p25519 x 0 1 = (d, F, G, V, R) ->
    safegcd_finalize_spec_Z p25519 d F V = fp_inv_spec x.
Proof.
  intros x d F G V R Hiter.
  unfold safegcd_finalize_spec_Z, fp_inv_spec.
  rewrite Hiter.
  reflexivity.
Qed.

(* ================================================================== *)
(* §2.  Concrete list-of-limbs spec layer                              *)
(* ================================================================== *)

(** List-of-limbs functional spec for [safegcd_finalize].

    Inputs:
      - [m]  : modulus (Z; static)
      - [F]  : 5×62 signed-limb encoding of the post-loop F (= ±1)
      - [V]  : 5×62 signed-limb encoding of the post-loop V
    Output:
      - 5×62 signed-limb encoding of the modular inverse.

    Concrete form: we evaluate [F] and [V] to their Z values, apply
    the sign-correct + mul-by-[precomp_val] computation, then re-encode
    in unsigned 5×62 limbs.  This is the algebraic shape any concrete
    implementation (bedrock2, safe Rust, asm) must match. *)

(** Decompose a non-negative Z value into 5 unsigned 62-bit limbs via
    [Safegcd_Step59_Spec.encode62] (which delegates to
    [Partition.partition (uweight 62) 5]).  The output of
    [safegcd_finalize_spec] uses this encoding for its return value. *)
Definition encode_5x62 (z : Z) : list Z := encode62 z.

Definition safegcd_finalize_spec
           (m : Z) (F V : list Z) : list Z :=
  let Fz := eval62 F in
  let Vz := eval62 V in
  let v_corrected := if Fz <? 0 then (m - Vz) mod m else Vz mod m in
  encode_5x62 ((v_corrected * precomp_val) mod m).

(** Helper: encoding a Z value in [0, p25519) yields a well-formed limb
    list whose [eval62] is the same Z value.  We rely on [p25519 < 2^309]
    so the value is in the signed-310-bit envelope. *)
Lemma encode_5x62_eval :
  forall z, 0 <= z < p25519 ->
    wf_signed62 (encode_5x62 z) /\ eval62 (encode_5x62 z) = z.
Proof.
  intros z Hz. unfold encode_5x62. split.
  - apply encode62_wf.
  - apply eval62_encode62.
    rewrite sg_bw_val.
    unfold p25519 in Hz. lia.
Qed.

(* ================================================================== *)
(* §3.  Composition lemma — the bridge.                                *)
(* ================================================================== *)

(** [safegcd_finalize_correct_Z] — the *contract* every concrete
    implementation of [safegcd_finalize_spec] must satisfy.

    Reads: given well-formed (5×62 signed-limb) post-loop inputs
    [F, V] whose Z-evaluations are [Fz, Vz], the list-of-limbs output
    of [safegcd_finalize_spec] re-evaluates to the abstract Z output
    of [safegcd_finalize_spec_Z m d Fz Vz].

    The discharge proceeds in three steps:

    1. Sign-correct branch — [if F[3]_top_bit then m - V else V].
       This is a conditional copy / subtract; both branches reduce
       to limb-level subtraction modulo p (no carry propagation
       across the modulus because [0 ≤ V < p] post-loop).
    2. Reduce the working representation to canonical [0, p).  At
       this stage the saturated 5×62 layer is converted to the
       4×64-bit Montgomery layer if the caller wants the canonical
       Fp25519_64 output type; for the present Gallina-only spec
       we keep 5×62 throughout.
    3. Multiplication by [precomp_val] (a Z constant; the body
       loads it from a static table) — one [fe25519_64_mul] call
       at the leaf level.

    LoC estimate (when implemented): ~150 lines using the existing
    [Fe25519_FpInv.precomp_val] constant and standard
    [eval_twos_complement] reasoning for the conditional copy. *)
Lemma safegcd_finalize_correct_Z :
  forall (m : Z) (d : Z) (F V : list Z) (Fz Vz : Z),
    wf_signed62 F -> wf_signed62 V ->
    eval62 F = Fz ->
    eval62 V = Vz ->
    m = p25519 ->
    (Fz = 1 \/ Fz = -1) ->
    0 <= Vz < m ->
    let out := safegcd_finalize_spec   m F V in
    let outz := safegcd_finalize_spec_Z m d Fz Vz in
    wf_signed62 out /\ eval62 out = outz.
Proof.
  intros m d F V Fz Vz HwfF HwfV HevF HevV Hm HFcases HVbound. subst m.
  unfold safegcd_finalize_spec, safegcd_finalize_spec_Z.
  rewrite HevF, HevV.
  apply encode_5x62_eval.
  apply Z.mod_pos_bound. unfold p25519. lia.
Qed.

(* ================================================================== *)
(* §4.  Future work — wiring to the outer-loop chain                  *)
(* ================================================================== *)
(*
 *  This lemma is consumed exactly once per [fe25519_invert_v2_body]
 *  evaluation (the finalize call is the last leaf in the body).
 *  See [Safegcd_Outer_Loop_Chain.v] for the composition with
 *  [safegcd_init_correct_Z] and [safegcd_step59_correct_Z] (× 10)
 *  that gives the headline statement
 *      [fe25519_invert_v2_body x = Fe25519_FpInv.fp_inv_spec x]
 *  modulo the localised Admits in each leaf spec.
 *)
