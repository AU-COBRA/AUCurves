(** * Ristretto_RustCmd — Phase B.5b Rupicola Derive of ristretto255
      encode + decode as [rust_cmd_ed].
 *
 *  GOAL: produce [ristretto_decode_rs : rust_cmd_ed] and its
 *  correctness theorem from the existing Gallina spec at
 *  [End2End/Lizard/RistrettoDecode.ristretto_decode_gallina],
 *  WITHOUT manually transcribing the AST.
 *
 *  Strategy (per [BLS/writeup/RISTRETTO255_B5_ZMIRROR_PLAN.md] §B.5b):
 *
 *  1. Wrap the existing Gallina with Rupicola [nlet_red] markup.
 *     This is documentation only — semantically [_nlet] = [_gallina]
 *     by [eq_refl] after unfolding [nlet_red].
 *
 *  2. Use Rupicola's [Derive ... SuchThat ... As ...] flow to
 *     auto-generate the [rust_cmd_ed] body and a simulation proof
 *     in one Qed.  Driver: [compile] from
 *     [RustCmdRupicolaTactics.v], which applies the 10 core compile
 *     lemmas (+ Tier-2 + Tier-4 sugar from
 *     [RustCmdRupicolaRistretto.v]).
 *
 *  3. Compose with the markup-equivalence lemma to obtain the
 *     simulation theorem against the original (un-marked-up) Gallina.
 *
 *  This file is the FIRST end-to-end use of the [Derive]+[compile]
 *  flow for [rust_cmd_ed] (the Ed25519 [Sign_Verify_RustCmd.v] uses
 *  hand-written AST + Tier-4 lemma application instead, predating
 *  the Tier-2 framework completion on 2026-05-10).  Ristretto is the
 *  natural first demo because:
 *
 *  - Algorithm is purely sequential (no scalar-mult-style
 *    well-founded recursion — does not exercise [compile_red_downto]).
 *  - All leaves are existing verified felem ops + RFC-specified
 *    sqrt-ratio + LE encoder.
 *  - Demand is concrete: closes 16 RAM-heavy admits in
 *    [Ristretto255_DecodeReject.v] when wired into the extracted
 *    Rust crate (Phase B.5c).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.RustCmdRupicolaRistretto.
Require Import Bedrock.RustCmdRupicolaDefn.
Require Import Bedrock.RustCmdRupicolaGallina.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.  (* slot_holds *)
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.RistrettoDecode.
Require Import Bedrock.End2End.Lizard.RistrettoEncode.
Require Import Bedrock.End2End.Ristretto.RistrettoBridges.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ========================================================================
   Section 1: nlet-annotated Gallina decoder.

   Pure markup over [ristretto_decode_gallina] — every [let] becomes a
   [nlet_red [var_name] (stack value) (fun var => ...)].  Used as the
   input to the [Derive] block in §2.
   ======================================================================== *)

(** ** [ristretto_decode_gallina_nlet] — Rupicola-markup variant.

    Each algorithmic step is wrapped in [nlet_red ["name"] (stack v)
    (fun name => ...)].  The [stack] wrapper is purely a hint for the
    Rupicola compile tactic that this binding wants a stack slot
    (vs. a scalar register).  Semantically [nlet_red] is just
    function application, and [stack v = v] by definition (see
    [RustCmdRupicola.v] §0 for [nlet_red] / [Rupicola/Lib/Core.stack]).

    The body below corresponds line-for-line to the body of
    [ristretto_decode_gallina] in [End2End/Lizard/RistrettoDecode.v].
    To stay in sync if the source moves, the per-step comments
    reference RFC 9496 §4.3.1 line numbers.

    NOTE: [stack] is now imported from [RustCmdRupicolaGallina.v]
    (where it's used as a Gallina-driven dispatch marker).  Both
    definitions were [fun A x => x]; the import keeps the marker
    constant identical between the Gallina program and the
    dispatcher's lazymatches. *)

Definition ristretto_decode_gallina_nlet (bs : list Byte.byte) : list Byte.byte :=
  match ristretto_parse_canonical_felem bs with
  | None => ristretto_bad_point
  | Some s =>
      nlet_red ["ss"]     (stack ((s * s) mod ed25519_p))                  (fun ss =>
      nlet_red ["u1"]     (stack ((1 - ss) mod ed25519_p))                 (fun u1 =>
      nlet_red ["u2"]     (stack ((1 + ss) mod ed25519_p))                 (fun u2 =>
      nlet_red ["u2_sqr"] (stack ((u2 * u2) mod ed25519_p))                (fun u2_sqr =>
      nlet_red ["u1_sq"]  (stack ((u1 * u1) mod ed25519_p))                (fun u1_sq =>
      nlet_red ["v"]      (stack (((ed25519_p - (ed25519_d * u1_sq) mod ed25519_p)
                                    mod ed25519_p - u2_sqr) mod ed25519_p)) (fun v =>
      nlet_red ["den"]    (stack ((v * u2_sqr) mod ed25519_p))             (fun den =>
      let '(was_square, I_val) := ristretto_sqrt_ratio_m1 1 den in
      nlet_red ["Dx"]     (stack ((I_val * u2) mod ed25519_p))             (fun Dx =>
      nlet_red ["Dy"]     (stack ((I_val * Dx * v) mod ed25519_p))         (fun Dy =>
      nlet_red ["x_raw"]  (stack ((2 * s * Dx) mod ed25519_p))             (fun x_raw =>
      nlet_red ["x"]      (stack (if ristretto_is_negative x_raw
                                   then ristretto_canonical_negate x_raw
                                   else x_raw))                            (fun x =>
      nlet_red ["y"]      (stack ((Dy * u1) mod ed25519_p))                (fun y =>
      nlet_red ["t"]      (stack ((x * y) mod ed25519_p))                  (fun t =>
        if orb (negb was_square)
               (orb (ristretto_is_negative t) (Z.eqb y 0))
        then ristretto_bad_point
        else pack_xyzt5 x y 1 x y
      )))))))))))))
  end.

(** ** [ristretto_decode_gallina_nlet] is [eq_refl]-equal to
       [ristretto_decode_gallina].

    Proof: unfold [nlet_red] (function application) and [stack]
    (identity); the per-line body matches verbatim. *)
Lemma ristretto_decode_gallina_nlet_eq :
  forall bs, ristretto_decode_gallina_nlet bs
           = ristretto_decode_gallina bs.
Proof.
  intros bs.
  unfold ristretto_decode_gallina_nlet, ristretto_decode_gallina,
         nlet_red, stack.
  reflexivity.
Qed.

(* ========================================================================
   Section 2: Derive block (Rupicola compile flow).

   This is the SCAFFOLDED [Derive] call.  As of 2026-05-22 the
   [compile] tactic in [RustCmdRupicolaTactics.v] is fully wired for
   the 10 core constructors + the 4 Tier-2 sugar lemmas; the
   ristretto-specific Tier-4 lemmas in [RustCmdRupicolaRistretto.v]
   are scaffolded (proofs trivial [exact I.] for now), and will Qed
   once the [strong_callee_post] schema for ristretto leaves
   (`fe25519_op`, `sqrt_ratio_m1`, `parse_canonical_felem`,
   `pack_canonical_felem`) is formalised.

   The shape below is what the final [Derive] block looks like; the
   automation status is documented in §3.
   ======================================================================== *)

(** ** Helper: build the function-spec record for ristretto_decode.

    The actual [defn_ed!] notation in the Ed25519 [Sign_Verify_RustCmd.v]
    is verbose; we hide the boilerplate behind this definition so the
    [Derive] line is readable. *)

(** ** [spec_of_ed_ristretto_decode] — Hoare-style spec via [fnspec_ed!].

    Slot precondition: caller-supplied "bs_var" holds the input bytes.
    Slot postcondition: caller-supplied "out_var" holds the 200-byte
    xyzt encoding of the decoded point (or [ristretto_bad_point] on
    rejection — embedded in the Gallina spec's behavior).

    The slot names "bs_var" and "out_var" are the entry-point's
    Rust-level identifiers; the actual Rust signature in the
    extracted [decode.rs] is
      [fn ristretto_decode(bs: *const u8, out: *mut u8)]
    with the slot mapping fixed by the AST's [located_ed]
    annotations. *)
Instance spec_of_ed_ristretto_decode : spec_of_ed "ristretto_decode" :=
  fnspec_ed! "ristretto_decode" (bs : list Byte.byte) ~> out,
  { requires rs := slot_holds rs "bs_var" bs;
    ensures  rs' := slot_holds rs' "out_var" out /\
                    out = ristretto_decode_gallina_nlet bs }.

(** ** Probe: instantiate the [defn_ed!] notation against the spec.

    We declare the goal as a [Definition : Prop] (rather than a Derive)
    to verify the notation expands without invoking [compile].  If this
    type-checks, the surface is wired correctly. *)
Definition ristretto_decode_derive_goal : Prop :=
  defn_ed! "ristretto_decode"("bs_var") ~> "out_var"
           { REdSkip },
           implements ristretto_decode_gallina_nlet
           using ["fe25519_mul"; "fe25519_add"; "fe25519_sub"; "fe25519_sq";
                  "ristretto_sqrt_ratio_m1";
                  "ristretto_parse_canonical_felem";
                  "ristretto_pack_canonical_felem";
                  "ristretto_canonical_negate"].

(** Status placeholder for the AST.  In the gallina-driven [compile]
    world this would be the [Derive] output; here we hand-anchor it
    to [REdSkip] so the file builds.  The actual AST authoring is the
    next deliverable (path A.1 of the §3 trade-off below).  *)
Definition ristretto_decode_rs : rust_cmd_ed := REdSkip.

(** Status placeholder for the simulation theorem. *)
Theorem ristretto_decode_rs_correct_stub :
  True.
Proof. exact I. Qed.

(* ========================================================================
   Section 2b: gallina-driven dispatcher demonstration.

   Demonstrates that the new [compile_step_ristretto] dispatcher
   (see [RustCmdRupicolaGallina.v]) actually fires on the [nlet_red /
   stack (s * s) mod ed25519_p] pattern that appears as the FIRST step
   inside the [Some s] branch of [ristretto_decode_gallina_nlet].

   The proof emits [REdCall "fe25519_mul"] into the body evar via the
   gallina pattern lemma [compile_gallina_modp_mul_emit].  This proves
   that, given a single [nlet_red ["ss"] (stack ((s*s) mod ed25519_p))]
   step with [s = le_combine s_bs] for some input bytes [s_bs], the
   dispatcher synthesises the correct AST head.

   This is a microcosm of how the full ristretto Derive will look once
   the abstract-Z bridge (mapping Gallina [Z] values to [le_combine
   bs_var] for some slot [bs_var]) is wired up.
   ======================================================================== *)

Section GallinaDispatchDemo.
  Context (function_table : function_table_ed).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).

  (** Single-step gallina-driven emit: given [s_var] holding [s_bs],
      the body [REdCall "fe25519_mul" ss_var s_var s_var] computes
      [(s * s) mod ed25519_p] into [ss_var] where [s = le_combine s_bs].

      The post matches the FIRST [nlet_red] step in
      [ristretto_decode_gallina_nlet]'s [Some s] branch verbatim
      (modulo the rest-of-program continuation, which is left as a
      generic continuation [k_gallina] here). *)
  Lemma ristretto_first_ss_step_demo
        (rs : rust_state_ed)
        (s_bs : list Byte.byte)
        (k_gallina : Z -> rust_state_ed -> Prop) :
    slot_holds rs "s_var" s_bs ->
    ("s_var" <> "ss_var")%string ->
    (forall rs1,
        slot_holds rs1 "ss_var"
          (le_split 32 ((le_combine s_bs * le_combine s_bs) mod ed25519_p)) ->
        slot_holds rs1 "s_var" s_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1
               REdSkip
               (k_gallina ((le_combine s_bs * le_combine s_bs) mod ed25519_p))) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_mul"
                 {| loc_var := "ss_var"; loc_type := TBytes 32 |}
                 [{| loc_var := "s_var"; loc_type := TBytes 32 |};
                  {| loc_var := "s_var"; loc_type := TBytes 32 |}])
              REdSkip)
      (fun rs' =>
         nlet_red ["ss"%string]
                  (stack ((le_combine s_bs * le_combine s_bs) mod ed25519_p))
                  k_gallina rs').
  Proof.
    intros Hs Hne Hk.
    (* The dispatcher fires compile_gallina_modp_mul_emit. *)
    compile_step_ristretto.
    - exact Hs.
    - exact Hs.
    - exact Hne.
    - exact Hne.
    - intros rs1 Hss Hka Hkb.
      apply Hk; assumption.
  Qed.

  (** ** Note on the abstract-Z bridge

      The full one-shot [Derive ristretto_decode_rs ... Proof. compile. Qed.]
      needs to handle the Gallina value [s : Z] that emerges from
      [match ristretto_parse_canonical_felem bs with Some s => ...].
      In the byte-level world, [s = le_combine s_bs] for some slot
      [s_bs] holding the parser's output.

      The bridging lemma [compile_red_parse_canonical] in
      [RustCmdRupicolaRistretto.v] already produces a [slot_holds rs1
      "s_var" (parse_canonical_felem_s_spec bs_input)] hypothesis,
      where the s_spec is [le_split 32 z] (with [Some z = parse...]).
      Composing this with the demo above closes the FIRST nlet_red.

      The remaining 13 [nlet_red] steps follow the same pattern with
      the appropriate operator (add, sub, mul, sq); the sqrt_ratio_m1
      destructuring let needs a dedicated 2-output dispatcher
      (planned, ~80 LoC).

      *AST so far*: [REdSeq (REdCallN "ristretto_parse_canonical_felem"
        [s_loc; status_loc] [bs_loc]) (REdIfNz status_expr
          (REdSkip with-bad-out)
          (REdSeq (REdCall "fe25519_mul" ss_loc [s_loc; s_loc])
                  ?k_rs))]
      with [?k_rs] still to fill.  About 12 more [REdSeq + REdCall]
      sites + 1 REdCallN for sqrt_ratio + the final if-then-else
      (~250-line emit total). *)

  (** ** Diagnostic: 2-step composition needs the abstract-Z bridge.

      Attempted a 2-step demo (mul `ss := s*s` then mul `ss_sq := ss*ss`)
      to validate that [compile_step_ristretto] composes through
      continuations.  Result: dispatcher fires both times correctly,
      AST is emitted, but the final [apply Hk; assumption] fails on:

      Hss_sq : slot_holds rs2 "ss_sq_var"
                 (le_split 32
                   ((le_combine (le_split 32 ((le_combine s_bs *
                                               le_combine s_bs)
                                               mod ed25519_p))
                     * le_combine (le_split 32 ((le_combine s_bs *
                                                 le_combine s_bs)
                                                 mod ed25519_p)))
                    mod ed25519_p))

      vs goal:    slot_holds rs2 "ss_sq_var"
                 (le_split 32 (((le_combine s_bs * le_combine s_bs)
                                  mod ed25519_p)
                                 * ((le_combine s_bs * le_combine s_bs)
                                    mod ed25519_p)
                                 mod ed25519_p))

      The two are propositionally equal via
      [le_combine_split : le_combine (le_split n z) = z mod 2^(n*8)]
      (n=32 ⇒ mod 2^256; since z < ed25519_p < 2^256, mod is identity).
      But they are NOT syntactically equal, so [assumption] / [eapply]
      fail to unify.

      This empirically confirms **gap #1 (abstract-Z bridge)** is the
      foundational blocker for multi-step composition.  Fix: introduce
      a [slot_holds_z rs x z := slot_holds rs x (le_split 32 z) /\
      0 <= z < 2^255-19] predicate, reformulate the bridging lemmas
      with [slot_holds_z] in both pre- and post-condition, and the
      round-trip canonicalization happens implicitly at the slot
      boundary.  Estimated ~50 LoC.

      Once gap #1 is closed, the 2-step demo (and the full Derive)
      should follow automatically — the dispatcher already handles
      the gallina-side recursion correctly; only the byte/Z
      bookkeeping was the blocker. *)

End GallinaDispatchDemo.

(* ========================================================================
   Section 3: Status, remaining work, and the live [Derive] block
   ======================================================================== *)

(** ** Live [Derive] block.

    As of Phase B.5b (2026-05-22) the supporting Tier-4 lemmas in
    [RustCmdRupicolaRistretto.v] are Qed-clean (4 single-output
    fe25519 arithmetic compile lemmas + 2 multi-output compile
    lemmas for sqrt_ratio_m1 and parse_canonical), and the per-leaf
    [strong_callee_post] schema is formalised in
    [RistrettoBridges.v] (Definitions, no axioms).

    What remains before [Derive ... compile.] runs end-to-end:

    1. A [defn_ed!] notation analogous to the Ed25519
       [Sign_Verify_RustCmd.v]'s entry point (which is
       hand-transcribed AST + [refine]).  No such notation exists
       in the current tree — Rupicola's [Derive] flow infers the
       function signature from the [defn_ed!] header.  Adding it is
       ~50 LoC of Notation + a goal-shape lemma.

    2. The [implements] / [using] dispatch in
       [RustCmdRupicolaTactics.v] (the [compile] tactic) currently
       targets Ed25519's hint database.  Adding the ristretto leaves
       to the hint set requires either a [Hint Resolve
       compile_red_modp_arith_mul ...] block here or a
       per-protocol tactic variant.

    3. Each remaining [compile_red_call] obligation for fe25519_mul,
       fe25519_add, fe25519_sub, fe25519_sq is one [eapply
       compile_red_modp_arith_<op>; assumption] line per call site;
       sqrt_ratio_m1 is one [eapply compile_red_sqrt_ratio_m1] line;
       parse_canonical is one [eapply compile_red_parse_canonical].

    Therefore the block below is the INTENDED shape of the final
    extraction.  Until items (1) and (2) above are addressed, the
    block fails immediately at the [defn_ed!] notation lookup, so we
    keep it commented out and document the path.

    Status (2026-05-22): the [defn_ed!] notation referenced above
    DOES NOT EXIST anywhere in the tree — neither in
    [End2End/Ed25519/Sign_Verify_RustCmd.v] nor in any Rupicola
    library import.  The Ed25519 [Sign_Verify_RustCmd.v] uses
    hand-written [REdLetZero/REdCall/REdIfNz] AST construction
    directly (see e.g. its [ed25519_sign_rs] Definition).
    Activating the [Derive] block below therefore requires either
    (a) authoring a fresh [defn_ed!] Notation (~50 LoC of Coq
    Notation + a [implements] helper Definition), or (b) following
    the Ed25519 pattern and hand-writing the AST (~150 LoC of
    REdSeq/REdLetZero/REdCall plumbing).

    Path (b) is more proven (it's how Ed25519 is wired today); the
    Tier-4 lemmas above (compile_red_modp_arith_{mul,add,sub,sq} +
    compile_red_sqrt_ratio_m1 + compile_red_parse_canonical) collapse
    the per-leaf proof obligations once the AST is written.  Estimated
    250 LoC total (150 AST + 100 Tier-4 chain proof) using the
    Ed25519 [ed25519_sign_rs_correct] pattern.

[[
Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

Derive ristretto_decode_rs_v2 SuchThat
  (forall bs_var out_var,
     defn_ed! "ristretto_decode" (bs_var, out_var)
              { ristretto_decode_rs_v2 }
     implements (ristretto_decode_gallina_nlet bs_var)
     using [ristretto_sqrt_ratio_m1;
            ristretto_parse_canonical_felem;
            ristretto_pack_canonical_felem;
            ristretto_canonical_negate])
  As ristretto_decode_rs_v2_correct.
Proof.
  compile.
  (* [compile] iterates [compile_step] from
     [RustCmdRupicolaTactics.v], which tries each [compile_red_*]
     hint in order.  For ristretto-specific patterns (modp_arith,
     sqrt_ratio_m1, parse_canonical) the Tier-4 sugar in
     [RustCmdRupicolaRistretto.v] takes over.

     Open obligations after [compile]:
     - per-call [strong_callee_post] discharge (~10 sub-goals for the
       felem ops + 1 for sqrt-ratio + 1 for parse).  Each is one
       [eapply <leaf_correct>; assumption.] line.
   *)
Qed.
]]

   After this block lands, [ristretto_decode_rs] (the placeholder
   above) is replaced by [ristretto_decode_rs_v2] and the
   simulation theorem follows from
   [ristretto_decode_gallina_nlet_eq] composed with
   [ristretto_decode_rs_v2_correct]:

[[
Theorem ristretto_decode_rs_simulates_gallina :
  forall bs_var out_var rs1 rs2,
    rust_exec_ed callee_post callee_post_n function_table
                 ristretto_decode_rs_v2 rs1 rs2 ->
    (* (rs2 reads out_var) = ristretto_decode_gallina (rs1 reads bs_var) *)
    ... .
Proof.
  intros. rewrite <- ristretto_decode_gallina_nlet_eq.
  exact (ristretto_decode_rs_v2_correct ...).
Qed.
]]
*)

(* ========================================================================
   Phase B.5b deliverables summary (updated 2026-05-22):

   QED in this file:
     - ristretto_decode_gallina_nlet           (markup wrapper, def)
     - ristretto_decode_gallina_nlet_eq        (Qed, one [reflexivity])

   STUB (placeholder pending Derive):
     - ristretto_decode_rs                     (= REdSkip placeholder)
     - ristretto_decode_rs_correct_stub        (= I)

   LANDED (in companion files):
     - [RistrettoBridges.v]: 7 [strong_callee_post] branches for
       ristretto leaves (fe25519_mul/add/sub/sq + sqrt_ratio_m1 +
       parse_canonical + pack_canonical_felem + canonical_negate),
       plus length lemmas and composite single/multi-output
       dispatchers ([strong_callee_post_ristretto] and
       [strong_callee_post_n_ristretto]).
     - [RustCmdRupicolaRistretto.v]: 6 Qed Tier-4 compile lemmas
       (4 single-output for fe25519 arithmetic + 2 multi-output for
       sqrt_ratio_m1 and parse_canonical).

   PENDING:
     - [defn_ed!] notation for ristretto entry points (~50 LoC).
     - [compile]-tactic hint-set wiring to include the new Tier-4
       lemmas (Hint Resolve block).
     - The [Derive ristretto_decode_rs_v2 ...] block (§3 above).
     - Encoder companion ([ristretto_encode_gallina_nlet] +
       Derive); analogous shape, ~200 LoC.

   TOTAL TO CLOSE: ~250 LoC (much less than the original ~500 LoC
   estimate, since the strong_callee_post schema and Tier-4 lemmas
   have landed).  Phase B.5c (Rust extraction + KAT tests) remains
   mechanical: [RustCmdToRust.rs_func_emit] on the Derived AST
   dumps the .rs files into
   [curve25519-jasmin-rs/src/ristretto_rustcmd/].
   ======================================================================== *)
