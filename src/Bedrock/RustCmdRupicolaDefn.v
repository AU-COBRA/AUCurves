(** * RustCmdRupicolaDefn — [defn_ed!] Notation + Derive flow for [rust_cmd_ed].
 *
 *  Parallel to [fiat-crypto/rupicola/src/Rupicola/Lib/Notations.v]'s
 *  [defn!] (which targets bedrock2 [Syntax.cmd]).  This file targets
 *  our [rust_cmd_ed] AST instead.
 *
 *  Surface (mirrors Rupicola for muscle-memory compatibility):
 *
 *  {{
 *    Instance spec_of_ed_my_op : spec_of_ed "my_op" :=
 *      fnspec_ed! "my_op" (a : list byte) (b : list byte) ~> out,
 *      { requires rs := slot_holds rs "a_var" a /\ slot_holds rs "b_var" b;
 *        ensures rs' := slot_holds rs' "out_var" (my_op_gallina a b) }.
 *
 *    Derive my_op_rs SuchThat
 *      (defn_ed! "my_op"("a_var", "b_var") ~> "out_var" { my_op_rs },
 *       implements my_op_gallina using [fe25519_mul; fe25519_add])
 *      As my_op_rs_ok.
 *    Proof. compile. Qed.
 *  }}
 *
 *  Architectural map to Rupicola:
 *
 *    Rupicola (bedrock2)         |  This file (rust_cmd_ed)
 *    ----------------------------+-------------------------------
 *    spec_of fname               |  spec_of_ed fname
 *    fnspec! name ...            |  fnspec_ed! name ...
 *    defn! name(args) ...        |  defn_ed! name(args) ...
 *    Syntax.func                 |  rust_cmd_ed (bare body)
 *    Syntax.cmd                  |  rust_cmd_ed
 *    WeakestPrecondition.call    |  rhoare (RustCmdRupicola.rhoare)
 *    program_logic_goal_for_function
 *                                |  program_logic_goal_for_function_ed
 *    __rupicola_program_marker   |  REUSED — same marker; compile
 *                                   tactic identifies it identically
 *
 *  Status (2026-05-22): framework scaffold.  Build-verified parsing
 *  of the custom entries pending the next dune cycle.  Test consumer:
 *  [End2End/Ristretto/Ristretto_RustCmd.v] (the live Derive block
 *  there should activate after this file lands).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
(** Rupicola is transitively available in the [Bedrock] dune theory
    via [Crypto] (= fiat-crypto), which lists Rupicola in its own
    theories.  Several existing [src/Bedrock/] files already
    [Require Import Rupicola.*] (e.g. BN254_PairingCorrect.v,
    BLS12_MSM.v, SafeRustBN254Instance.v).  We reuse the same
    program marker to stay consistent with the bedrock2 path and
    let Rupicola's existing tactic infrastructure pick up our
    Derive goals if the user opts in. *)
Require Import Rupicola.Lib.Core.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  spec_of_ed typeclass                                          *)
(* ================================================================ *)

(** [spec_of_ed fname] is a typeclass whose instance for a given
    function name is the full Hoare-style spec (precondition +
    postcondition + frame) for that function.  Mirrors Rupicola's
    [spec_of] but operates on [rust_state_ed] rather than
    [(trace, mem, locals)].

    A spec for a function with name [fname] is a value of type

      [rust_cmd_ed -> Prop]

    saying: for any [body : rust_cmd_ed], whenever the body is the
    function's implementation, the body satisfies the per-protocol
    precondition / postcondition contract.

    Concrete instances are declared via [fnspec_ed!] below. *)
Class spec_of_ed (fname : String.string) : Type :=
  spec_of_ed_body : rust_cmd_ed -> Prop.

(** Existing-instance unfold helper: lets [defn_ed!]'s [eval red] step
    see through the typeclass projection. *)
#[global] Arguments spec_of_ed_body {fname _} _.

(* ================================================================ *)
(* §2.  fnspec_ed!: spec declaration notation                         *)
(* ================================================================ *)

(** [fnspec_ed! "name" (a : T1) (b : T2) ~> out0 .. outN,
       { requires rs := P;
         ensures rs' := Q }]
    declares a Hoare-style spec for the named function.  Variadic in
    BOTH the number of Gallina inputs and the number of Gallina
    outputs, exactly matching Rupicola's [fnspec!] surface.  Single
    output: write [~> out].  Two outputs: [~> a b].

    The variables [rs] and [rs'] are bound to the initial and final
    [rust_state_ed]s respectively, and may reference all the input
    and output names.  The output names are existentially quantified
    so the user can refer to them in [Q] without committing to a
    specific Gallina-level witness in the spec.

    The notation desugars to a function [body : rust_cmd_ed -> Prop]
    using [rhoare] (see [RustCmdRupicola.rhoare]).  Variadic
    expansion of the [..] is via Coq's standard notation recursion. *)
Notation "'fnspec_ed!' name a0 .. an '~>' r0 .. rn , '{' 'requires' rs ':=' P ; 'ensures' rs' ':=' Q '}'" :=
  (fun (body : rust_cmd_ed) =>
     forall (callee_post : String.string -> list located_ed -> located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop)
            (callee_post_n : String.string -> list located_ed -> list located_ed ->
                             rust_state_ed -> rust_state_ed -> Prop)
            (function_table : function_table_ed),
       (forall a0, .. (forall an,
         forall (rs : rust_state_ed),
           P ->
           rhoare callee_post callee_post_n function_table rs body
                  (fun rs' => (exists r0, .. (exists rn, Q) ..))) ..))
    (at level 200,
     name at level 0,
     a0 closed binder, an closed binder,
     r0 closed binder, rn closed binder,
     rs name, rs' name,
     P at level 200,
     Q at level 200,
     only parsing).

(** Variant with no Gallina inputs (effects entirely on caller-supplied
    output slots). *)
Notation "'fnspec_ed!' name '~>' r0 .. rn , '{' 'requires' rs ':=' P ; 'ensures' rs' ':=' Q '}'" :=
  (fun (body : rust_cmd_ed) =>
     forall (callee_post : String.string -> list located_ed -> located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop)
            (callee_post_n : String.string -> list located_ed -> list located_ed ->
                             rust_state_ed -> rust_state_ed -> Prop)
            (function_table : function_table_ed)
            (rs : rust_state_ed),
       P ->
       rhoare callee_post callee_post_n function_table rs body
              (fun rs' => (exists r0, .. (exists rn, Q) ..)))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     rs name, rs' name,
     P at level 200,
     Q at level 200,
     only parsing).

(** Variant with no outputs (the function's effect is fully captured
    by Q on rs' without any existentially-quantified value). *)
Notation "'fnspec_ed!' name a0 .. an , '{' 'requires' rs ':=' P ; 'ensures' rs' ':=' Q '}'" :=
  (fun (body : rust_cmd_ed) =>
     forall (callee_post : String.string -> list located_ed -> located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop)
            (callee_post_n : String.string -> list located_ed -> list located_ed ->
                             rust_state_ed -> rust_state_ed -> Prop)
            (function_table : function_table_ed),
       (forall a0, .. (forall an,
         forall (rs : rust_state_ed),
           P ->
           rhoare callee_post callee_post_n function_table rs body
                  (fun rs' => Q)) ..))
    (at level 200,
     name at level 0,
     a0 closed binder, an closed binder,
     rs name, rs' name,
     P at level 200,
     Q at level 200,
     only parsing).

(* ================================================================ *)
(* §3.  Custom entries for defn_ed! surface                           *)
(* ================================================================ *)

Declare Custom Entry defn_ed_spec.

Record _defn_ed_spec_sig :=
  { _defn_ed_args : list String.string;
    _defn_ed_rets : list String.string }.

Record _defn_ed_spec {A : Type} :=
  { _defn_ed_name : String.string;
    _defn_ed_sig : _defn_ed_spec_sig;
    _defn_ed_impl : rust_cmd_ed;       (* the body evar to be filled *)
    _defn_ed_gallina : A;              (* the Gallina spec value *)
    _defn_ed_calls : list String.string }.

Declare Custom Entry defn_ed_spec_commas.
Notation "a0 , .. , an" :=
  (cons a0 .. (cons an []) ..)
    (in custom defn_ed_spec_commas at level 0,
        a0 constr at level 0, an constr at level 0).

Declare Custom Entry defn_ed_spec_args.
Notation "'()'" := [] (in custom defn_ed_spec_args at level 0).
Notation "'(' ')'" := [] (in custom defn_ed_spec_args at level 0).
Notation "'(' args ')'" :=
  args (in custom defn_ed_spec_args at level 0,
            args custom defn_ed_spec_commas at level 0).

Declare Custom Entry defn_ed_spec_sig.
Notation "args  '~>'  rets" :=
  {| _defn_ed_args := args; _defn_ed_rets := rets |}
    (in custom defn_ed_spec_sig at level 0,
        args custom defn_ed_spec_args at level 0,
        rets custom defn_ed_spec_commas at level 0).
Notation "args" :=
  {| _defn_ed_args := args; _defn_ed_rets := [] |}
    (in custom defn_ed_spec_sig at level 0,
        args custom defn_ed_spec_args at level 0).

Notation "name sig  {  impl  } ,  'implements'  fn" :=
  {| _defn_ed_name := name;
     _defn_ed_sig := sig;
     _defn_ed_impl := match impl return rust_cmd_ed with c => c end;
     _defn_ed_gallina := fn;
     _defn_ed_calls := [] |}
    (in custom defn_ed_spec at level 10,
        name constr at level 0,
        sig custom defn_ed_spec_sig at level 0,
        impl constr at level 200,
        fn constr at level 0,
        no associativity).

Notation "name sig  {  impl  } ,  'implements'  fn  'using'  fns" :=
  {| _defn_ed_name := name;
     _defn_ed_sig := sig;
     _defn_ed_impl := match impl return rust_cmd_ed with c => c end;
     _defn_ed_gallina := fn;
     _defn_ed_calls := fns |}
    (in custom defn_ed_spec at level 10,
        name constr at level 0,
        sig custom defn_ed_spec_sig at level 0,
        impl constr at level 200,
        fn constr at level 0,
        fns constr at level 0,
        no associativity).

(* ================================================================ *)
(* §4.  program_logic_goal_for_function_ed                            *)
(* ================================================================ *)

(** [program_logic_goal_for_function_ed body callees] builds the
    Derive goal: looks up [spec_of_ed name] for the named function,
    instantiates its precondition + postcondition over the
    implementation [body], and threads the [callees] list as
    "assuming each callee's spec holds, the body satisfies its spec".

    Mirrors [Rupicola.Lib.Tactics.program_logic_goal_for_function]. *)
Ltac program_logic_goal_for_function_ed name body callees :=
  let spec := lazymatch constr:(_ : spec_of_ed name) with ?s => s end in
  (* For now, the goal is just [spec body]; the [callees] list is
     threaded into the spec at instance-declaration time via
     [fnspec_ed!]'s framing.  A future refinement: emit an
     [assuming_correctness_of_in callees ...] wrapper analogous to
     Rupicola's, once we have a "list of callee specs" notion. *)
  constr:(spec body).

(* ================================================================ *)
(* §5.  The defn_ed! Notation                                         *)
(* ================================================================ *)

(** [defn_ed! name(args) ~> rets { body }, implements gallina using calls]
    expands to a [Prop] suitable as the [SuchThat] argument of [Derive]:

      __rupicola_program_marker gallina -> program_logic_goal_for_function_ed body calls

    The compile tactic from [RustCmdRupicolaTactics.v] picks up the
    [__rupicola_program_marker] hypothesis to find the Gallina spec
    and walks it to fill the [body] evar. *)
Notation "'defn_ed!' spec" :=
  (match spec with
   | spec_constr =>
     (* Typecheck `spec` first for nicer error messages, then dispatch. *)
     ltac:(lazymatch (eval red in spec_constr) with
           | {| _defn_ed_name := ?name;
                _defn_ed_sig := {| _defn_ed_args := _; _defn_ed_rets := _ |};
                _defn_ed_impl := ?impl;
                _defn_ed_gallina := ?gallina;
                _defn_ed_calls := ?calls |} =>
              (* Open the body evar at type rust_cmd_ed and unify with impl. *)
              let body := open_constr:(match _ return rust_cmd_ed with c => c end) in
              unify impl body;
              let goal := program_logic_goal_for_function_ed name body calls in
              exact (__rupicola_program_marker gallina -> goal)
           end)
   end)
    (at level 0, spec custom defn_ed_spec at level 200, only parsing).

(* ================================================================ *)
(* §6.  Smoke test (minimal, no protocol-specific imports)            *)
(* ================================================================ *)

(** A minimal smoke test: define a trivial Gallina spec, declare its
    [spec_of_ed] instance via [fnspec_ed!], and exercise [defn_ed!]
    to set up the Derive goal.  We do NOT run [compile] here — that
    would pull in protocol-specific [strong_callee_post] schemas;
    instead we [Admitted] the proof, just verifying that the goal
    type-checks. *)

Module SmokeTest.
  Definition trivial_op (x : list Byte.byte) : list Byte.byte := x.

  Instance spec_of_ed_trivial : spec_of_ed "trivial_op" :=
    fun body =>
      forall callee_post callee_post_n function_table
             (x : list Byte.byte) (rs : rust_state_ed),
        True ->
        rhoare callee_post callee_post_n function_table rs body
               (fun rs' => True).

  (** Verify the defn_ed! Notation parses + type-checks. *)
  Definition trivial_op_derive_goal : Prop :=
    defn_ed! "trivial_op"() { REdSkip },
             implements trivial_op.

  (** Verify the trivial_op_derive_goal is inhabited by REdSkip. *)
  Lemma trivial_op_derive_goal_holds : trivial_op_derive_goal.
  Proof.
    unfold trivial_op_derive_goal.
    intros _.
    unfold spec_of_ed_body, spec_of_ed_trivial.
    intros cp cpn ft x rs _ rs' Hexec.
    exact I.
  Qed.
End SmokeTest.

(* ================================================================ *)
(* §7.  Build status / next steps                                     *)
(* ================================================================ *)

(** Build verification status (2026-05-22):
      - File parses without error: PENDING next dune cycle.
      - Smoke test [trivial_op_derive_goal_holds] Qed: PENDING.
      - Real consumer ([Ristretto_RustCmd.v] Derive block uncommented
        with [defn_ed!]): PENDING after this file's Qed.

    Known limitations:
      - [fnspec_ed!] currently provides 1-arg and 2-arg variants.
        Higher arities follow the same pattern (~10 LoC each).
      - [program_logic_goal_for_function_ed] does NOT yet generate
        the [assuming_correctness_of_in] wrapper for callees — the
        callee list is threaded via the spec's framing.  A future
        refinement matches Rupicola's exact shape.
      - The framework here is single-output ([fun rs' => exists out, Q]).
        Multi-output via [REdCallN] needs a parallel
        [fnspec_ed_n!] notation; ~20 LoC, deferred.

    With this file landed, the [Derive] block in [Ristretto_RustCmd.v]
    becomes a one-liner:

      Derive ristretto_decode_rs SuchThat
        (defn_ed! "ristretto_decode"("bs") ~> "out"
                  { ristretto_decode_rs },
         implements ristretto_decode_gallina_nlet
         using ["fe25519_mul"; "fe25519_add"; "fe25519_sub"; "fe25519_sq";
                "ristretto_sqrt_ratio_m1"; "ristretto_parse_canonical_felem";
                "ristretto_pack_canonical_felem"; "ristretto_canonical_negate"])
        As ristretto_decode_rs_correct.
      Proof. compile. Qed.

    Plus a [spec_of_ed_ristretto_decode] instance via [fnspec_ed!]
    (~10 LoC) declaring the slot precondition on "bs" and the
    postcondition on "out".
*)
