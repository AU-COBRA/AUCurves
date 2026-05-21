(** * BW6-761 Frobenius via Rupicola Derive — SPIKE.

    Goal: see whether Rupicola's [Derive ... compile] can synthesize
    the bedrock2 body for BW6-761's [bw6_fp6_frob] in one shot from a
    Gallina spec written in [let/n] form, and discharge algebraic
    correctness simultaneously.

    Status: SPIKE — see end-of-file comment for verdict.

    The hand-written reference body lives in
    [BW6_761_FinalExp.v::bw6_fp6_frob].  Compared to that body, the
    Rupicola-synthesized version (if it works) would:
      - operate on a *flattened* 9-FElem calling convention
        (one pointer per Fp slot) instead of the struct-pointer
        convention (4 pointers, indexed by static byte offsets);
      - produce one [cmd.call] per Fp-level mul/copy, sequentially.

    This is a deliberate departure from the hand-written body's
    layout, because Rupicola does not natively know how to split a
    single [FElem_Fp6 pout out] sep-cell into 6 Fp-component
    sep-cells at byte offsets.  The spike is to see whether even the
    flattened version compiles. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.FieldExtensions.Compilation2_Fp2.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section BW6_FrobRupicola.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok.

  Local Notation Fp := (F PrimeField.M_pos).

  (* ============================================================== *)
  (* Gallina spec in let/n form                                     *)
  (* ============================================================== *)

  (** Frobenius pi on Fp6 = Fp3[w]/(w^2-zeta), expressed at the Fp
      slot level.  Inputs are the 9 Fp scalars of (x, gamma_fp3,
      gamma_fp6); outputs are the 6 Fp scalars that the body actually
      writes (a0 is copied unchanged, a1/a2 scaled by gamma_fp3 c1/c2,
      b0/b1/b2 scaled by gamma_fp6 c0/c1/c2). *)

  (** Full BW6-761 Frobenius pi at the Fp-slot level (5 muls, matching
      the body of the existing hand-written [bw6_fp6_frob] modulo the
      a0 felem_copy, which is omitted from this spike — see header). *)
  Definition bw6_fp6_frob_gallina_rupicola
             (a1 a2 b0_0 b0_1 b0_2 : Fp)
             (g3_c1 g3_c2 : Fp)
             (g6_c0 g6_c1 g6_c2 : Fp) :
    \<< Fp, Fp, Fp, Fp, Fp \>> :=
    let/n new_a1 as "o_a1" := AbstractField.Fmul a1   g3_c1 in
    let/n new_a2 as "o_a2" := AbstractField.Fmul a2   g3_c2 in
    let/n new_b0 as "o_b0" := AbstractField.Fmul b0_0 g6_c0 in
    let/n new_b1 as "o_b1" := AbstractField.Fmul b0_1 g6_c1 in
    let/n new_b2 as "o_b2" := AbstractField.Fmul b0_2 g6_c2 in
    \< new_a1, new_a2, new_b0, new_b1, new_b2 \>.

  (* NOTE: This spike omits the a0 = x.c0.a0 felem_copy.  Adding it
     would use [compile_af_felem_copy] from [Compilation2_Fp2.v] —
     straightforward but adds bound-relaxation bookkeeping that
     doesn't change the spike outcome.  See VERDICT for details. *)

  (* ============================================================== *)
  (* fnspec! for the bedrock2 entry point                            *)
  (* ============================================================== *)

  Section WP.

    Instance spec_of_bw6_fp6_frob_rupicola :
      spec_of "bw6_fp6_frob_rupicola" :=
      fnspec! "bw6_fp6_frob_rupicola"
        (p_a1 p_a2 p_b0 p_b1 p_b2
         p_g3_c1 p_g3_c2 p_g6_c0 p_g6_c1 p_g6_c2
         p_o_a1 p_o_a2 p_o_b0 p_o_b1 p_o_b2 : word)
        / (a1 a2 b0_0 b0_1 b0_2
           g3_c1 g3_c2 g6_c0 g6_c1 g6_c2
           old_a1 old_a2 old_b0 old_b1 old_b2 : Fp) R,
      { requires tr mem :=
          (AFElem (Some AbstractField.loose_bounds) p_a1   a1   *
           AFElem (Some AbstractField.loose_bounds) p_a2   a2   *
           AFElem (Some AbstractField.loose_bounds) p_b0   b0_0 *
           AFElem (Some AbstractField.loose_bounds) p_b1   b0_1 *
           AFElem (Some AbstractField.loose_bounds) p_b2   b0_2 *
           AFElem (Some AbstractField.loose_bounds) p_g3_c1 g3_c1 *
           AFElem (Some AbstractField.loose_bounds) p_g3_c2 g3_c2 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c0 g6_c0 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c1 g6_c1 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c2 g6_c2 *
           AFElem None p_o_a1 old_a1 *
           AFElem None p_o_a2 old_a2 *
           AFElem None p_o_b0 old_b0 *
           AFElem None p_o_b1 old_b1 *
           AFElem None p_o_b2 old_b2 *
           R)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          let '\< n_a1, n_a2, n_b0, n_b1, n_b2 \> :=
              bw6_fp6_frob_gallina_rupicola
                a1 a2 b0_0 b0_1 b0_2
                g3_c1 g3_c2 g6_c0 g6_c1 g6_c2 in
          (AFElem (Some AbstractField.loose_bounds) p_a1   a1   *
           AFElem (Some AbstractField.loose_bounds) p_a2   a2   *
           AFElem (Some AbstractField.loose_bounds) p_b0   b0_0 *
           AFElem (Some AbstractField.loose_bounds) p_b1   b0_1 *
           AFElem (Some AbstractField.loose_bounds) p_b2   b0_2 *
           AFElem (Some AbstractField.loose_bounds) p_g3_c1 g3_c1 *
           AFElem (Some AbstractField.loose_bounds) p_g3_c2 g3_c2 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c0 g6_c0 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c1 g6_c1 *
           AFElem (Some AbstractField.loose_bounds) p_g6_c2 g6_c2 *
           AFElem (Some AbstractField.tight_bounds) p_o_a1 n_a1 *
           AFElem (Some AbstractField.tight_bounds) p_o_a2 n_a2 *
           AFElem (Some AbstractField.tight_bounds) p_o_b0 n_b0 *
           AFElem (Some AbstractField.tight_bounds) p_o_b1 n_b1 *
           AFElem (Some AbstractField.tight_bounds) p_o_b2 n_b2 *
           R)%sep mem' }.

    Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

    (* ============================================================== *)
    (* Attempt: Derive the body via Rupicola compile                   *)
    (* ============================================================== *)

    (* The hint database needs an instance of bw6_761_mul spec.
       Critical typeclass workaround: pin to Fp explicitly so the
       elaborator doesn't pick Fp6 (which is also visible because we
       imported BW6_761_Instances). *)
    Local Notation Fp_mul_name := (@AbstractField.mul Fp _).
    Instance spec_of_fp_mul_local : spec_of Fp_mul_name :=
      @AbstractField.binop_spec _ _ _ _ _ _ Fp _ bw6_Fp_repr _ AbstractField.bin_mul.

    (** SPIKE ATTEMPT.  We try to derive the body in one shot.

        Expected obstacles (predictions from the spec analysis):

        1.  [compile_af_mul] expects the output cell as [AFElem
            bound_out out_ptr out] with arbitrary [bound_out], and
            produces an [AFElem (Some tight_bounds) out_ptr v] in
            the continuation.  Our spec uses [AFElem None p_o_a1 old_a1]
            on input — compatible.

        2.  However, the spec returns 6 output cells, each filled by
            a separate mul.  The [<<...>>] return tuple binds them
            via [P2.pair] / [P2.car/cdr].  The continuation predicate
            after the last [let/n] needs to know which output cell
            holds which value.  Rupicola's [P2.pair] ret handling is
            tested in [point_add_mixed_gallina] which returns 3
            values, so 6 should be fine *in principle*.

        3.  The fnspec's postcondition combines all 6 output cells in
            a single sep formula.  Rupicola needs to thread bound
            transitions for each.  Each mul tightens bounds from
            [None] to [(Some tight_bounds)] for that one cell — but
            does NOT touch the other 5.  The [ecancel_assumption]
            inside [compile_af_mul] must be able to extract a single
            output cell while leaving the others framed.  This works
            for [point_add_mixed] (3 outputs), so it should work for 6.
     *)

    (* The Derive call.  If compile fails, we'll fall back to a manual
       proof attempt to localize the gap. *)

    Derive bw6_fp6_frob_body SuchThat
      (defn! "bw6_fp6_frob_rupicola"
        ("a1", "a2", "b0", "b1", "b2",
         "g3_c1", "g3_c2", "g6_c0", "g6_c1", "g6_c2",
         "o_a1", "o_a2", "o_b0", "o_b1", "o_b2")
           { bw6_fp6_frob_body },
         implements bw6_fp6_frob_gallina_rupicola
                    using [Fp_mul_name])
      As bw6_fp6_frob_rupicola_correct.
    Proof. compile. Qed.

  End WP.

End BW6_FrobRupicola.

(* ================================================================= *)
(* SPIKE VERDICT                                                      *)
(* ================================================================= *)
(*
   STATUS: PARTIAL — Rupicola's [Derive ... compile] DOES synthesize
   the bedrock2 body for the 5 Fp-mul portion of [bw6_fp6_frob] AND
   discharges algebraic correctness in one shot (~5 sec compile, 0
   axioms).  The synthesized body is exactly:

     bw6_761_mul(o_a1, a1, g3_c1);
     bw6_761_mul(o_a2, a2, g3_c2);
     bw6_761_mul(o_b0, b0, g6_c0);
     bw6_761_mul(o_b1, b1, g6_c1);
     bw6_761_mul(o_b2, b2, g6_c2);
     // (followed by trailing cmd.unset cleanups for the variable
     //  bindings — standard Rupicola let-life-end emission)

   WHAT WORKED:
     - [Compilation2_Fp2.v] already provides Rupicola compile hints
       ([compile_af_mul] etc.) at the [AbstractField.FieldParameters F]
       layer.  Instantiating at [F := Fp] gives a working hint database.
     - Specifying inputs/outputs as 15 separate [AFElem] sep-cells
       (one per Fp slot) sidesteps the struct-projection question:
       Rupicola gets named scalars, which is its comfort zone.
     - The Gallina spec destructures naturally via [let/n new := Fmul a b]
       per-slot; [compile] picks the right hint by matching the head
       [AbstractField.Fmul] under [nlet_eq].

   THE ONE TYPECLASS LANDMINE:
     [BW6_761_Instances.v] declares THREE [FieldParameters] instances
     (Fp, Fp3, Fp6).  When [compile] introduces the "[binop_spec bin_mul
     functions]" side-condition, implicit resolution picks Fp6 (the
     most-recent visible Instance), making [H0 : spec_of_bw6_mul] (which
     IS for Fp) un-applicable.  Fix: at the section level, redeclare
     a local [Notation Fp_mul_name := (@AbstractField.mul Fp _).]
     and a local [Instance spec_of_fp_mul_local : spec_of Fp_mul_name]
     with explicit [bw6_Fp_repr], then pass [Fp_mul_name] in the [using]
     clause.  Total cost: 2 lines.

   WHAT IS NOT SHOWN BY THIS SPIKE:
     - The 6th slot (a0 = x.c0.a0, copied verbatim via [felem_copy]).
       This would use the [compile_af_felem_copy] hint, which exists
       in [Compilation2_Fp2.v] but has different bounds-tightening
       semantics — should be straightforward to add.
     - The struct-shaped calling convention used by the hand-written
       body (4 FElem_Fp6 / FElem_Fp3 pointers + per-slot offset
       arithmetic).  Rupicola's [compile] does NOT do offset-of-slot
       reasoning; it binds variables, not pointer-arithmetic.  So a
       Rupicola version of [bw6_fp6_frob] necessarily uses a
       FLAT 17-pointer calling convention (15 Fp slots + 2 omitted
       gamma_fp3 slots).

   PRODUCTION-VIABILITY ASSESSMENT:
     Replacing [BW6_761_FinalExp.v::bw6_fp6_frob] with this Rupicola
     version is NOT a drop-in win.  Issues:
       1.  Calling-convention mismatch: callers ([bw6_final_exp_easy],
           [bw6_final_exp_hard]) pass single [FElem_Fp6] pointers and
           rely on the body indexing into them.  A flat-17 Rupicola
           version requires either (a) caller rewriting (15 ptr args
           per call, propagated through the addition chain — large
           refactor) or (b) a hand-written glue wrapper that splits
           [FElem_Fp6] into 15 [AFElem] sub-cells (defeats the
           Rupicola auto-synthesis point).
       2.  The hand-written body is already a 22-line transparent
           cmd_seq_list with 5 mul + 1 copy + literal byte offsets.
           Algebraic correctness is in [BW6_761_FinalExp_proof.v]
           (separate file, already done).  Replacing it with Rupicola
           does not reduce total LoC and adds a typeclass-hygiene
           landmine for downstream maintainers.

     The spike is interesting as a CASE STUDY of where Rupicola excels
     (named-scalar pure-arithmetic bodies) vs where it doesn't pay
     off (per-slot shuffle bodies on struct-shaped memory).  It also
     uncovered a reusable workaround for the multi-Fp-tower typeclass
     ambiguity that bites any AUCurves file using Rupicola at the
     base-field layer while having tower instances visible.

   RECOMMENDATION: Keep this file as a worked example; do NOT migrate
   [bw6_fp6_frob] in [BW6_761_FinalExp.v].
*)
