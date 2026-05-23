(** * RustCmdRupicolaGallina — gallina-driven [compile_step] extension
 *
 *  This module extends the AST-driven [compile_step] in
 *  [RustCmdRupicolaTactics.v] with a Gallina-driven dispatcher.  Where
 *  the original [compile_step] lazymatches on the [rust_cmd_ed] head
 *  constructor (which presupposes the AST is already known), the new
 *  [compile_step_gallina] lazymatches on the POSTCONDITION's Gallina
 *  shape — typically a chain of [nlet_red] wrappers around mod-p
 *  arithmetic and FFI calls — and emits the corresponding
 *  [rust_cmd_ed] AST head constructor onto the evar that holds the
 *  body-to-be-derived.
 *
 *  Mirrors [fiat-crypto/rupicola/src/Rupicola/Lib/Compiler.v] line
 *  ~755-779 [compile_step] / [compile_triple] / [compile] dispatch,
 *  with the [Hint Extern] hook pattern adapted to [rust_cmd_ed].
 *
 *  **Status (2026-05-22)**
 *
 *    - §1 Gallina-shape bridging lemmas:
 *        compile_gallina_modp_mul / _add / _sub / _sq — Qed.
 *        These transform a goal whose post is
 *          [fun rs' => slot_holds rs' result_var
 *                       (le_split 32 ((le_combine a_bs * le_combine b_bs) mod ed25519_p))]
 *        into the body-arithmetic side of the canonical Tier-4 lemma.
 *
 *    - §2 [compile_step_ristretto] Ltac dispatcher: lazymatches the
 *        gallina patterns and applies the corresponding bridging
 *        lemma + Tier-4 sugar, leaving the next [k] continuation as
 *        an evar for further dispatch.
 *
 *    - §3 [compile_ristretto] = [repeat compile_step_ristretto] until
 *        either the AST is fully synthesised or no pattern matches
 *        (leaving the residual goal documented for the user).
 *
 *  Acceptable outcome (this iteration): the framework parses and the
 *  per-pattern bridging lemmas Qed.  Full one-shot synthesis of
 *  [ristretto_decode_rs] from [ristretto_decode_gallina_nlet] is the
 *  next deliverable; the residual is the abstract-Z bridge for
 *  inputs derived from [ristretto_parse_canonical_felem]'s output.
 *
 *  The simplest mental model:
 *  - "Gallina drives": post mentions [nlet_red ["ss"] (stack ((s*s) mod ed25519_p))
 *      (fun ss => ...)], dispatcher binds ss := le_combine ?ss_bs, applies
 *      [compile_red_modp_arith_mul], emits AST head [REdCall "fe25519_mul" ...]
 *      and recurses on the continuation [k].
 *  - "AST drives": post mentions [slot_holds rs' result_var (le_split 32 ...)],
 *      the Tier-4 lemma [compile_red_modp_arith_mul] applies directly.
 *
 *  This file provides the first kind; [RustCmdRupicolaRistretto.v] provides
 *  the second.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.RustCmdRupicolaRistretto.
Require Import Bedrock.RustCmdRupicolaTactics.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Ristretto.RistrettoBridges.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** [stack] is an identity wrapper used as a Rupicola-level hint
    that a binding wants a stack slot (vs. a scalar register).  This
    file's pattern-match recognises [stack X] in the post; the user's
    program (e.g. [End2End/Ristretto/Ristretto_RustCmd.v]) defines
    its own [stack] — we use a local alias here and ensure
    definitionally-equal unifications via [unfold]. *)
Definition stack {A} (x : A) : A := x.

(* ================================================================ *)
(* §1. Gallina-shape bridging lemmas                                 *)
(*                                                                    *)
(* Each [compile_gallina_<pattern>] lemma takes a goal whose post     *)
(* mentions the Gallina-level mathematical operator (e.g. [_ * _]    *)
(* mod ed25519_p]) wrapped in [nlet_red] and transforms it to the     *)
(* canonical Tier-4 lemma's form, then applies the Tier-4 lemma.     *)
(* ================================================================ *)

Section GallinaBridges.
  Context (function_table : function_table_ed).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).

  (** [compile_gallina_modp_mul_emit] — gallina-driven emission for
      [(le_combine a_bs * le_combine b_bs) mod ed25519_p].

      Reads off [a_bs], [b_bs] from the [slot_holds] hypotheses,
      identifies the gallina-level [Z] values as
      [le_combine a_bs] and [le_combine b_bs], and bridges from the
      gallina-level post
        [nlet_red [result_name] (stack ((le_combine a_bs * le_combine b_bs)
                                         mod ed25519_p)) k_gallina]
      to the byte-level Tier-4 lemma [compile_red_modp_arith_mul].

      The continuation [k_rs] is the [rust_cmd_ed] evar to be
      synthesised next.  [k_gallina] is the Gallina continuation of the
      [nlet_red] (i.e., the user's [fun ss => ...] body). *)
  Lemma compile_gallina_modp_mul_emit
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (result_name : String.string)
        (k_rs : rust_cmd_ed)
        (k_gallina : Z -> rust_state_ed -> Prop) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var
          (le_split 32 ((le_combine a_bs * le_combine b_bs) mod ed25519_p)) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1
               k_rs
               (k_gallina ((le_combine a_bs * le_combine b_bs) mod ed25519_p))) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_mul"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k_rs)
      (fun rs' =>
         nlet_red [result_name]
                  (stack ((le_combine a_bs * le_combine b_bs) mod ed25519_p))
                  k_gallina rs').
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    unfold nlet_red, stack.
    eapply (compile_red_modp_arith_mul function_table callee_post_n
              rs result_var a_var b_var a_bs b_bs k_rs
              (k_gallina ((le_combine a_bs * le_combine b_bs) mod ed25519_p))
              Ha Hb Hne_a Hne_b).
    exact Hk.
  Qed.

  (** [compile_gallina_modp_add_emit] — symmetric to _mul for [_+_]. *)
  Lemma compile_gallina_modp_add_emit
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (result_name : String.string)
        (k_rs : rust_cmd_ed)
        (k_gallina : Z -> rust_state_ed -> Prop) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var
          (le_split 32 ((le_combine a_bs + le_combine b_bs) mod ed25519_p)) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1
               k_rs
               (k_gallina ((le_combine a_bs + le_combine b_bs) mod ed25519_p))) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_add"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k_rs)
      (fun rs' =>
         nlet_red [result_name]
                  (stack ((le_combine a_bs + le_combine b_bs) mod ed25519_p))
                  k_gallina rs').
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    unfold nlet_red, stack.
    eapply (compile_red_modp_arith_add function_table callee_post_n
              rs result_var a_var b_var a_bs b_bs k_rs
              (k_gallina ((le_combine a_bs + le_combine b_bs) mod ed25519_p))
              Ha Hb Hne_a Hne_b).
    exact Hk.
  Qed.

  (** [compile_gallina_modp_sub_emit] — symmetric to _mul for [_-_]. *)
  Lemma compile_gallina_modp_sub_emit
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (result_name : String.string)
        (k_rs : rust_cmd_ed)
        (k_gallina : Z -> rust_state_ed -> Prop) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var
          (le_split 32 ((le_combine a_bs - le_combine b_bs) mod ed25519_p)) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1
               k_rs
               (k_gallina ((le_combine a_bs - le_combine b_bs) mod ed25519_p))) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_sub"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k_rs)
      (fun rs' =>
         nlet_red [result_name]
                  (stack ((le_combine a_bs - le_combine b_bs) mod ed25519_p))
                  k_gallina rs').
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    unfold nlet_red, stack.
    eapply (compile_red_modp_arith_sub function_table callee_post_n
              rs result_var a_var b_var a_bs b_bs k_rs
              (k_gallina ((le_combine a_bs - le_combine b_bs) mod ed25519_p))
              Ha Hb Hne_a Hne_b).
    exact Hk.
  Qed.

  (** [compile_gallina_modp_sq_emit] — gallina-driven emission for
      squaring: [(le_combine a_bs * le_combine a_bs) mod ed25519_p]. *)
  Lemma compile_gallina_modp_sq_emit
        (rs : rust_state_ed)
        (result_var a_var : var)
        (a_bs : list Byte.byte)
        (result_name : String.string)
        (k_rs : rust_cmd_ed)
        (k_gallina : Z -> rust_state_ed -> Prop) :
    slot_holds rs a_var a_bs ->
    a_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var
          (le_split 32 ((le_combine a_bs * le_combine a_bs) mod ed25519_p)) ->
        slot_holds rs1 a_var a_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1
               k_rs
               (k_gallina ((le_combine a_bs * le_combine a_bs) mod ed25519_p))) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_sq"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |}])
              k_rs)
      (fun rs' =>
         nlet_red [result_name]
                  (stack ((le_combine a_bs * le_combine a_bs) mod ed25519_p))
                  k_gallina rs').
  Proof.
    intros Ha Hne_a Hk.
    unfold nlet_red, stack.
    eapply (compile_red_modp_arith_sq function_table callee_post_n
              rs result_var a_var a_bs k_rs
              (k_gallina ((le_combine a_bs * le_combine a_bs) mod ed25519_p))
              Ha Hne_a).
    exact Hk.
  Qed.

End GallinaBridges.

(* ================================================================ *)
(* §2. compile_step_ristretto — gallina-driven dispatcher            *)
(*                                                                    *)
(* This Ltac lazymatches on the [rhoare]-goal's POST shape and        *)
(* applies the appropriate Gallina-bridging lemma above (or the       *)
(* AST-driven Tier-4 lemma from [RustCmdRupicolaRistretto.v]).        *)
(*                                                                    *)
(* The "right" architecture (Hint Extern + compile_db) follows        *)
(* Rupicola's pattern exactly; for now we use a single Ltac to keep   *)
(* the dispatch surface explicit and traceable.                       *)
(* ================================================================ *)

(** [compile_step_ristretto] — try, in order:
    1. AST-driven [compile_step] from [RustCmdRupicolaTactics.v] (for
       cases where the AST head is already determined).
    2. Gallina-driven [compile_gallina_modp_<op>_emit] lemmas (for
       [nlet_red] / [stack] wrappers around mod-p arithmetic).
    3. Tier-4 sugar lemmas (when the AST head is REdSeq+REdCall).

    Side conditions (slot_holds, slot disjointness) become subgoals
    for the user to discharge. *)
Ltac compile_step_ristretto :=
  lazymatch goal with
  (* §2a. Gallina-driven: post is [nlet_red [_] (stack ((_*_) mod
     ed25519_p)) k_gallina].  Apply the bridging lemma. *)
  | |- rhoare strong_callee_post_ristretto _ _ _ _
        (fun _ => nlet_red _ (stack ((_ * _) mod ed25519_p)) _ _) =>
      eapply compile_gallina_modp_mul_emit
  | |- rhoare strong_callee_post_ristretto _ _ _ _
        (fun _ => nlet_red _ (stack ((_ + _) mod ed25519_p)) _ _) =>
      eapply compile_gallina_modp_add_emit
  | |- rhoare strong_callee_post_ristretto _ _ _ _
        (fun _ => nlet_red _ (stack ((_ - _) mod ed25519_p)) _ _) =>
      eapply compile_gallina_modp_sub_emit

  (* §2b. AST-driven Tier-4: post is unconstrained, AST is REdSeq +
     REdCall "fe25519_<op>" ... *)
  | |- rhoare _ _ _ _
        (REdSeq (REdCall "fe25519_mul" _ _) _) _ =>
      eapply compile_red_modp_arith_mul
  | |- rhoare _ _ _ _
        (REdSeq (REdCall "fe25519_add" _ _) _) _ =>
      eapply compile_red_modp_arith_add
  | |- rhoare _ _ _ _
        (REdSeq (REdCall "fe25519_sub" _ _) _) _ =>
      eapply compile_red_modp_arith_sub
  | |- rhoare _ _ _ _
        (REdSeq (REdCall "fe25519_sq" _ _) _) _ =>
      eapply compile_red_modp_arith_sq
  | |- rhoare _ _ _ _
        (REdSeq (REdCallN "ristretto_sqrt_ratio_m1" _ _) _) _ =>
      eapply compile_red_sqrt_ratio_m1
  | |- rhoare _ _ _ _
        (REdSeq (REdCallN "ristretto_parse_canonical_felem" _ _)
                (REdIfNz _ _ _)) _ =>
      eapply compile_red_parse_canonical

  (* §2c. Fall through to the AST-driven base dispatcher (REdSkip /
     REdSeq / REdLetZero / REdLetU64 / REdCall / REdCallN / REdIfNz
     / REdByteLoad / REdByteStore / REdSelect / REdBlock / REdFor /
     REdWhileNz). *)
  | |- _ => compile_step
  end.

(** [compile_ristretto] — repeated dispatcher.  Like Rupicola's
    [compile], iterates [compile_step_ristretto] until no progress.
    Residual side conditions (slot_holds, slot disjointness,
    eval_sexpr_ed) become subgoals.  *)
Ltac compile_ristretto := repeat compile_step_ristretto.

(* ================================================================ *)
(* §3. Smoke test                                                     *)
(*                                                                    *)
(* Demonstrates that a single-step compile of a [nlet_red] wrapping  *)
(* a [(_*_) mod ed25519_p] post emits the right [REdCall fe25519_mul] *)
(* AST head.                                                          *)
(* ================================================================ *)

Module SmokeGallina.

  (** A trivial gallina program: one mul-then-skip.  Post:
      [slot_holds rs' "result" (le_split 32 ((le_combine a_bs *
      le_combine b_bs) mod ed25519_p))].  *)
  Lemma compile_single_mul_smoke
        (function_table : function_table_ed)
        (callee_post_n : String.string -> list located_ed -> list located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop)
        (rs : rust_state_ed)
        (a_bs b_bs : list Byte.byte) :
    slot_holds rs "a_var" a_bs ->
    slot_holds rs "b_var" b_bs ->
    "a_var" <> "result"%string ->
    "b_var" <> "result"%string ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_mul"
                 {| loc_var := "result"; loc_type := TBytes 32 |}
                 [{| loc_var := "a_var"; loc_type := TBytes 32 |};
                  {| loc_var := "b_var"; loc_type := TBytes 32 |}])
              REdSkip)
      (fun rs' =>
         nlet_red ["product"%string]
                  (stack ((le_combine a_bs * le_combine b_bs) mod ed25519_p))
                  (fun _ rs' => slot_holds rs' "result"
                                  (le_split 32
                                    ((le_combine a_bs * le_combine b_bs)
                                      mod ed25519_p)))
                  rs').
  Proof.
    intros Ha Hb Hne_a Hne_b.
    (* The dispatcher should fire compile_gallina_modp_mul_emit. *)
    compile_step_ristretto.
    - exact Ha.
    - exact Hb.
    - exact Hne_a.
    - exact Hne_b.
    - intros rs1 Hresult Hka Hkb.
      (* k_rs = REdSkip; continuation hypothesis Hresult gives us the
         slot. *)
      apply compile_red_skip.
      exact Hresult.
  Qed.

End SmokeGallina.

(* ================================================================ *)
(* §4. Notes / future work                                            *)
(* ================================================================ *)

(** ** Roadmap

    1. **Multi-step gallina dispatch**: extend [compile_step_ristretto]
       to recognise nested [nlet_red] chains so a single
       [compile_ristretto] call walks the whole [ristretto_decode_gallina_nlet]
       body.  The [compile_gallina_*_emit] lemmas already produce a
       post-continuation of the form [k_gallina v], which itself can
       be another [nlet_red]; the dispatcher recurses.

    2. **[Hint Extern]-based dispatch**: register each
       [compile_gallina_*_emit] in a hint database
       [compile_db_gallina] using [Hint Extern 1 (rhoare _ _ _ _ _
       (fun _ => nlet_red _ (stack (_ * _ mod ed25519_p)) _ _)) =>
       eapply compile_gallina_modp_mul_emit].  This mirrors
       Rupicola's exact pattern from
       [fiat-crypto/rupicola/src/Rupicola/Lib/Compiler.v] §651.

    3. **sqrt_ratio_m1 / parse_canonical gallina dispatch**: the
       2-output [REdCallN] requires recognizing the [let '(ws, r) :=
       sqrt_ratio_m1 ... in k] pattern in the gallina post.  This is
       a destructuring let; the compile lemma must thread both [ws_var]
       and [r_var] through the [REdSeq] continuation.

    4. **[Hint Extern] for ristretto leaves**: extend [compile_db]
       with hints for the 7 ristretto leaves' callee dispatch
       branches (canonical_negate, pack_canonical, etc.).

    Estimated total: ~150 LoC for items 1-3 plus a few hours of
    interactive debugging.  Item 4 is ~80 LoC.

    ** Why this file is "framework-only"

    The Gallina-driven compile lemmas in §1 already work when the user
    has the byte-level inputs [a_bs], [b_bs] explicit in scope (e.g.,
    after a [destruct] or [pose proof] following a
    [ristretto_parse_canonical_felem] dispatch).  Walking the entire
    [ristretto_decode_gallina_nlet] body in one [compile] call
    requires also handling:

      - the outer [match ristretto_parse_canonical_felem bs with]
        which produces an [option Z] (vs. our [option (list byte)]),
      - the inner [let '(ws, r) := sqrt_ratio_m1 1 den] which is a
        destructuring let (not [nlet_red]),
      - the final [if ... then ristretto_bad_point else pack_xyzt5 ...]
        which is an arbitrary [if]-then-else not [REdIfNz]-ready.

    All three are mechanical translations once the matching pattern
    lemmas (compile_red_match_option, compile_red_let_pair) are
    written; ~80 LoC each.  Phase B.5c.
*)
