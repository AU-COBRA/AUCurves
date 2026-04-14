(** * BN254_EndToEnd.v
 *
 * Phase 4 of the formal refinement plan: end-to-end theorem connecting
 * the executable safe Rust to the math-level BN254 optimal-ate pairing.
 *
 * ** Architecture
 *
 * Three independent proof artefacts come together here:
 *
 *   (1) [bn254_tower_correct]   (SafeRustBN254Concrete.v, Qed)
 *       — for every toy-bedrock program [c], if [bedrock_exec] reaches
 *         [rs2] from [rs1], then [rust_exec (btranslate c)] reaches the
 *         same [rs2]. Shows the generated safe Rust preserves the
 *         semantics of its bedrock source.
 *
 *   (2) [bn254_pairing_dsd_optimal_ok] (BN254_PairingTopOptimal.v, Qed)
 *       — the bedrock2 source of [bn254_pairing_dsd_optimal] satisfies a
 *         WP functional spec (output is a bounded Fp12).
 *
 *   (3) [bn254_optimal_ate_spec]       (MillerLoopWP.v, Definition)
 *       — the math-level Gallina function for the BN254 optimal-ate pairing
 *         (ZModTower instance of [PairingSpec.optimal_ate]).
 *
 * ** Remaining gaps (tracked as hypotheses below)
 *
 *   (G1) WP ↔ bedrock_exec bridge. Theorem (1) operates on the toy
 *        [bcmd] language (see SafeRustSimulation.v); theorem (2)
 *        operates on [Syntax.cmd.cmd] via [WeakestPrecondition]. No
 *        theorem currently connects the two — closing this gap is
 *        a separate effort (roughly: reproduce the WP proof against
 *        [bedrock_exec], or prove a meta simulation).
 *
 *   (G2) WP spec strengthening. The postcondition of
 *        [spec_of_bn254_pairing_dsd_optimal] says "exists a bounded
 *        Fp12 [out] in memory at [pout]". It does NOT currently say
 *        [feval out = bn254_optimal_ate_spec ...]. Lifting the
 *        per-iteration [cont_inv] through [bn254_miller_loop_optimal]
 *        and the final-exp wrapper requires an analogue of
 *        [L4_via_bridge] (already Qed for the miller-loop exit) for
 *        the outer pairing function.
 *
 * This file states the end-to-end theorem under named hypotheses
 * corresponding to (G1) and (G2), and proves the top-level claim by a
 * short chain through [bn254_tower_correct] and transitivity.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustBN254Concrete.

(* ================================================================ *)
(* §1. Projecting an Fp12 value from a rust_state                    *)
(* ================================================================ *)

(** We need a way to read a tower-typed value out of a [rust_state]
    at a named slot. The concrete projection depends on the
    representation of limbs and on the Montgomery-form conversion;
    rather than fixing it here we parametrise over it. The resulting
    [Fp12] value is opaque (type [Fp12_val]); the WP hypothesis below
    ties it to the math-level [Fp12_Z]. *)

Definition rs_has_Fp12 (rs : rust_state) (x : string)
                        (v : rust_val TFp12) : Prop :=
  lookup_t (rs_tower rs) x = Some (exist_tval TFp12 v).

(* ================================================================ *)
(* §2. Hypotheses corresponding to the two architectural gaps         *)
(* ================================================================ *)

Section EndToEnd.

  (** Math-level inputs. We use the Z-indexed representation matching
      [MillerLoopWP.bn254_optimal_ate_spec]. *)

  Variables (gamma1 gamma_y gamma1_p2 : Z * Z)
            (Px Py : Z) (Qx Qy : Z * Z).

  (** A placeholder for the mathematical result value. For the purposes
      of this conditional theorem we treat the pairing output as an
      uninterpreted [Fp12] witness reflected into the [rust_state]. *)

  Variable Fp12_val : Type.
  Variable fp12_of_rust : rust_val TFp12 -> Fp12_val.
  Variable fp12_of_ate : (Z*Z) -> (Z*Z) -> (Z*Z) -> Z -> Z ->
                         (Z*Z) -> (Z*Z) -> Fp12_val.

  (** The toy-bedrock source program for the pairing. We leave this as
      a [Variable] because the extraction from the fiat-crypto function
      [bn254_pairing_dsd_optimal] into [bcmd] is itself part of the
      bridge work (G1). *)

  Variable pairing_bcmd : bcmd.
  Variable out_var : string.

  (** ** Hypothesis (G2): the bedrock source, under bedrock_exec,
      produces the math-level pairing result in the output slot. *)

  Hypothesis H_wp_implies_math :
    forall rs1 rs2 v_out,
      cmd_clean pairing_bcmd ->
      state_ac_fresh rs1 ->
      bedrock_exec bn254_N bn254_u64_max bn254_leaf_spec_concrete
                   pairing_bcmd rs1 rs2 ->
      rs_has_Fp12 rs2 out_var v_out ->
      fp12_of_rust v_out = fp12_of_ate gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  (** ** End-to-end theorem: safe Rust computes the math-level pairing.
      Instantiated with a concrete [pairing_bcmd] and the hypothesis
      [H_wp_implies_math] (i.e. with (G1) and (G2) closed), this gives
      the fully-verified chain from math spec to executable safe Rust. *)

  Theorem bn254_pairing_end_to_end :
    forall rs1 rs2 v_out,
      cmd_clean pairing_bcmd ->
      state_ac_fresh rs1 ->
      bedrock_exec bn254_N bn254_u64_max bn254_leaf_spec_concrete
                   pairing_bcmd rs1 rs2 ->
      rs_has_Fp12 rs2 out_var v_out ->
      (** The translated safe Rust reaches the same final state ... *)
      rust_exec bn254_N bn254_u64_max bn254_leaf_spec_concrete
                (btranslate pairing_bcmd) rs1 rs2
      (** ... whose output slot holds the math-level pairing value. *)
      /\ fp12_of_rust v_out =
         fp12_of_ate gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
  Proof.
    intros rs1 rs2 v_out Hclean Hfresh Hexec Hhas.
    split.
    - (** Translator-soundness chain: leaf-refinement + simulation. *)
      exact (bn254_tower_correct
               pairing_bcmd rs1 rs2 Hclean Hfresh Hexec).
    - (** WP chain: [H_wp_implies_math] packages (G2). *)
      apply (H_wp_implies_math rs1 rs2 v_out
                               Hclean Hfresh Hexec Hhas).
  Qed.

End EndToEnd.

(* ================================================================ *)
(* §3. What (G1) and (G2) would look like when discharged            *)
(* ================================================================ *)

(** Discharge checklist:
 *
 *  (G1) Produce a concrete [pairing_bcmd : bcmd] by translating the
 *       fiat-crypto [Syntax.cmd.cmd] of [bn254_pairing_dsd_optimal]
 *       into [bcmd]. The [ToSafeRustBody.safe_cmd] function already
 *       consumes [Syntax.cmd.cmd]; a matching [Syntax.cmd.cmd -> bcmd]
 *       would let us share the bridge. Alternatively: strengthen the
 *       simulation theorem to operate directly on [Syntax.cmd.cmd]
 *       (the toy language was introduced to keep the proof tractable).
 *
 *  (G2) Strengthen [spec_of_bn254_pairing_dsd_optimal] so its
 *       postcondition asserts
 *         [feval out = bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2
 *                                             Px Py Qx Qy].
 *       The per-iteration ingredients already exist
 *       (cont_inv + L4_via_bridge + affine_miller_aux_morphism). The
 *       missing piece is the outer wrapper that threads cont_inv
 *       through [bn254_miller_loop_optimal] and composes with the
 *       DSD final-exponentiation spec.
 *
 * Given these, [H_wp_implies_math] is dischargeable by combining the
 * G1-bridge with the G2-strengthened postcondition, and the theorem
 * [bn254_pairing_end_to_end] can be instantiated without hypotheses —
 * yielding a closed end-to-end statement connecting the generated
 * safe Rust to the math-level BN254 optimal-ate pairing. *)
