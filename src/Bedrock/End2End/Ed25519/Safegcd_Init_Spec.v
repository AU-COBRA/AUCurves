(** * Safegcd_Init_Spec — Gallina spec + Z-bridge for the
 *    [safegcd_init] leaf of the divstep-based fe25519 inverter.
 *
 *  Scope
 *  =====
 *  This file states the *algebraic* contract that any concrete
 *  implementation of the [safegcd_init] leaf (bedrock2 body,
 *  hand-written safe Rust, asm wrapper) must satisfy in order for the
 *  composite [fe25519_invert_v2_body] (in [Fe25519InvertBodyV2.v])
 *  to compute [a^{-1} mod p25519].
 *
 *  Algebraically [safegcd_init] is trivial: it loads the constants
 *  required to start the δ₀ = 1/2 Bernstein–Yang loop from
 *  [Fe25519_FpInv.fp_inv_spec], namely
 *
 *      (d, F, G, V, R)  =  (-1, p, x, 0, 1)
 *
 *  Two layers of spec are exposed (mirroring [Safegcd_Step59_Spec.v]):
 *
 *  • [safegcd_init_spec]   — list-of-limb form, mirroring the Rust
 *    [REdCallN "safegcd_init" [F; G; V; R; m] [a]] leaf from
 *    [Fe25519InvertBodyV2.v].  Inputs/outputs are 5×62-bit signed
 *    limbs (encoded as [list Z]).  Stub for now.
 *
 *  • [safegcd_init_spec_Z] — abstract integer form: takes the modulus
 *    [m], the initial δ-encoding [d0 = -1], and the input value [x],
 *    returns the 5-tuple [(d, F, G, V, R) = (-1, m, x, 0, 1)] that
 *    [Fe25519_FpInv.fp_inv_spec] feeds into its [iter_divstep_spec_half]
 *    call.
 *
 *  The composition lemma [safegcd_init_correct_Z] is stated and
 *  [Admitted] with a short sketch.  It is *nearly* trivial since the
 *  Z-level definition is just a 5-tuple of constants; the only thing
 *  to discharge is the limb-evaluation side of the stub
 *  [safegcd_init_spec], i.e. that the 5×62 representation of each
 *  output really evaluates back to the corresponding Z value.
 *
 *  Compile cost
 *  ============
 *  Definitions only — < 5 s on rocq-9.
 *
 *  Cross-references
 *  ================
 *  • Rust source:   curve25519-jasmin-rs/src/safegcd.rs §init
 *  • Skeleton AST:  src/Bedrock/End2End/Ed25519/Fe25519InvertBodyV2.v §2
 *  • Z-level spec:  src/Bedrock/Field/Synthesis/Examples/Fe25519_FpInv.v
 *                   [fp_inv_spec] — the initial state passed to
 *                   [iter_divstep_spec_half] is exactly
 *                   [(-1, p25519, x, 0, 1)].
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

(** Z-level functional spec for [safegcd_init].
    Takes the modulus [m] and input value [x] (and the static δ-encoding
    constant [d0 = -1]), returns the initial state tuple that
    [Fe25519_FpInv.fp_inv_spec] feeds into [iter_divstep_spec_half].

    Output tuple shape matches [iter_divstep_spec_half] inputs:
    [(d, F, G, V, R) = (d0, m, x, 0, 1)]. *)
Definition safegcd_init_spec_Z (m d0 : Z) (x : Z) : Z * Z * Z * Z * Z :=
  (d0, m, x, 0, 1).

(** Sanity: at [m := p25519] and [d0 := -1], the output is precisely
    the seed of the [iter_divstep_spec_half] call in [fp_inv_spec]. *)
Lemma safegcd_init_spec_Z_at_p25519 : forall x,
  safegcd_init_spec_Z p25519 (-1) x = (-1, p25519, x, 0, 1).
Proof. intros; reflexivity. Qed.

(* ================================================================== *)
(* §2.  Concrete list-of-limbs spec layer                              *)
(* ================================================================== *)

(** List-of-limbs functional spec for [safegcd_init].

    Inputs:
      - [m]  : modulus (Z; supplied as a static constant by the body)
      - [x]  : 5×62 signed-limb encoding of the input value
    Outputs:
      - [d]  : initial δ-encoding (Z; the leaf actually writes a u64
               machine word, but the *value* of that word as a
               twos-complement Z is the spec output)
      - [F]  : 5×62 signed-limb encoding of [m]
      - [G]  : 5×62 signed-limb encoding of [x] (i.e. identical to
               input [x])
      - [V]  : 5×62 signed-limb encoding of [0]
      - [R]  : 5×62 signed-limb encoding of [1]

    Concrete form: the 5×62-limb encoding of [m = p25519] is precomputed,
    [G] is the input limbs verbatim, [V] is the zero limbs, [R] is the
    one limbs, and [d] is the u64 [2^62 - 1] which decodes (via
    [Z.twos_complement 62]) to [-1].  The contract is the *correctness*
    lemma [safegcd_init_correct_Z] below. *)

(** 5×62 unsigned-limb encoding of [p25519 = 2^255 - 19]. *)
Definition p25519_limbs : list Z :=
  [4611686018427387885; 4611686018427387903;
   4611686018427387903; 4611686018427387903; 127].

(** 5×62 unsigned-limb encoding of [0]. *)
Definition zero62_limbs : list Z := [0; 0; 0; 0; 0].

(** 5×62 unsigned-limb encoding of [1]. *)
Definition one62_limbs : list Z := [1; 0; 0; 0; 0].

(** u64 word for [-1] in [Z.twos_complement 62] encoding: [2^62 - 1]. *)
Definition d0_init : Z := 4611686018427387903.

Definition safegcd_init_spec
           (m : Z) (x : list Z)
  : Z * (list Z) * (list Z) * (list Z) * (list Z) :=
  (d0_init, p25519_limbs, x, zero62_limbs, one62_limbs).

(* ================================================================== *)
(* §3.  Composition lemma — the bridge.                                *)
(* ================================================================== *)

(** [safegcd_init_correct_Z] — the *contract* every concrete
    implementation of [safegcd_init_spec] must satisfy.

    Reads: given a well-formed (5×62 signed-limb) input [x] whose
    Z-evaluation is [xz], the list-of-limbs output of
    [safegcd_init_spec] re-evaluates limb-by-limb to the abstract Z
    output of [safegcd_init_spec_Z p25519 (-1) xz].

    Almost-trivial discharge: this is just constant-limb checking,
    since at the Z level the spec is a 5-tuple of integers.  The
    only real obligation is to exhibit *some* 5×62-limb encoding of
    [m = p25519], of [0], and of [1] (the [G ← x] move is a verbatim
    copy of the input limbs).

    LoC estimate (when implemented): ~60 lines, mostly listing the
    static encodings and showing they re-evaluate correctly. *)
Lemma safegcd_init_correct_Z :
  forall (m : Z) (x : list Z) (xz : Z),
  m = p25519 ->
  wf_signed62 x ->
  eval62 x = xz ->
  0 < xz < m ->
  let '(d', F', G', V', R')    := safegcd_init_spec   m x in
  let '(dz', Fz', Gz', Vz', Rz') := safegcd_init_spec_Z m (-1) xz in
  wf_signed62 F' /\ wf_signed62 G' /\ wf_signed62 V' /\ wf_signed62 R' /\
  Z.twos_complement sg_mw d' = dz' /\
  eval62 F' = Fz' /\
  eval62 G' = Gz' /\
  eval62 V' = Vz' /\
  eval62 R' = Rz'.
Proof.
  intros m x xz Hm Hwf Hev Hbound. subst m.
  unfold safegcd_init_spec, safegcd_init_spec_Z.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  all:
    try (unfold wf_signed62, sg_n, sg_mw, p25519_limbs, zero62_limbs,
           one62_limbs;
         split; [reflexivity|];
         intros z H; cbn in H;
         repeat (destruct H as [<-|H]; [lia|]); contradiction);
    try assumption;
    try (unfold Z.twos_complement, d0_init, sg_mw; vm_compute; reflexivity);
    try (unfold eval62, eval_twos_complement, sg_mw, sg_n, p25519_limbs,
           zero62_limbs, one62_limbs, p25519; vm_compute; reflexivity).
Qed.

(* ================================================================== *)
(* §4.  Future work — wiring to the outer-loop chain                  *)
(* ================================================================== *)
(*
 *  This lemma is consumed exactly once per [fe25519_invert_v2_body]
 *  evaluation (the init call is the first leaf in the body).  See
 *  [Safegcd_Outer_Loop_Chain.v] for the composition with
 *  [safegcd_step59_correct_Z] (× 10) and [safegcd_finalize_correct_Z]
 *  that gives the headline statement
 *      [fe25519_invert_v2_body x = Fe25519_FpInv.fp_inv_spec x]
 *  modulo the localised Admits in each leaf spec.
 *)
