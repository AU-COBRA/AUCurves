(** * WPToBedrockExec.v — G1: the WP ↔ safe-Rust semantic bridge.
 *
 * ** Updated architectural analysis (after closer reading of
 *    [SafeRustLeafRefinement.bn254_leaf_spec]).
 *
 * Initial framing of G1 — "bridge bedrock2 WP semantics to the toy
 * [bedrock_exec] over [bcmd]" — is only half the story.  A deeper
 * reading of [bn254_leaf_spec] shows that [bedrock_exec] and
 * [rust_exec] are leaf-level models only:
 *
 *   [Lemma leaf_spec_non_fp : forall f dt in_ts dst args,
 *      dt <> TFp -> bn254_leaf_spec f dt in_ts dst args = dst.]
 *
 * For non-Fp destinations (Fp2, Fp6, Fp12 — i.e. every pairing-level
 * call), [bn254_leaf_spec] is the identity: the "simulation" reads
 * and writes back the same rust_val.  So [bedrock_exec] of the
 * pairing body, treating [miller_loop_optimal] and [final_exp_dsd]
 * as Fp12 callees, computes a no-op: [rs2 = rs1].  The leaf-level
 * correspondence [bn254_tower_correct] is genuine, but what it
 * actually certifies is that each *leaf primitive* in the Rust tower
 * matches its bedrock2 counterpart — not that a composite tower
 * function does.
 *
 * ** What G1 actually requires
 *
 * The honest end-to-end story has three layers, only two of which
 * are currently modelled:
 *
 *   L0 (leaf Fp arithmetic)     — [bn254_leaf_spec] + refinement
 *                                 witnesses [bn254_*_refines] in
 *                                 [SafeRustBN254Concrete.v].  Qed.
 *
 *   L1 (WP composition)         — G2's [bn254_pairing_dsd_optimal_correct]
 *                                 shows that if callees satisfy strong
 *                                 WP specs, the pairing WP call yields
 *                                 [bn254_optimal_ate_spec].  Qed.
 *
 *   L2 (Rust composition)       — NOT YET MODELLED.  The intended
 *                                 meaning of "running the generated
 *                                 safe Rust" is recursive evaluation
 *                                 with a function environment
 *                                 [fenv : string -> rust_cmd].  The
 *                                 current [rust_exec] is leaf-only;
 *                                 it has no call-unfolding rule for
 *                                 non-leaf functions.
 *
 * G1 is therefore NOT a small simulation lemma but a systemic
 * extension to the semantic models.  Two concrete paths:
 *
 *   (A)  Extend [rust_exec] with a function-environment rule
 *        [XR_call_fn : forall f body args ...
 *           fenv f = Some body ->
 *           rust_exec body (bind-args rs_init) rs_mid ->
 *           (rs' = writeback dest rs_mid) ->
 *           rust_exec (RCall f dest args) rs rs'].
 *        Then prove each tower function's Rust body satisfies a
 *        "Rust spec" mirroring the bedrock2 WP spec.  Composition
 *        follows by induction on the call depth.
 *
 *   (B)  Build a separate semantics [rust_exec_full] that models the
 *        full Rust language we actually emit (not just the leaf
 *        subset), then prove [btranslate]-preservation at that level.
 *        More ambitious; more general.
 *
 * Either path is ~1–2 weeks of work and not closable in a single
 * session; both require modifying [SafeRustSimulation.v] or adding
 * parallel infrastructure.
 *
 * ** Deliverable of this file
 *
 * Since the original G1 statement was misaligned with what's
 * actually needed, this file now documents:
 *
 *   (1)  The translator [syntax_to_bcmd] (still useful
 *        infrastructure for future work on path (A)).
 *
 *   (2)  A PRECISE statement of the real G1 obligation in terms of
 *        a function-environment-aware Rust semantics
 *        ([rust_pairing_output] specification).  Parameterised over
 *        the function environment, not over abstract predicates.
 *
 *   (3)  Concrete action items for paths (A) and (B).
 *
 * No proof content — the point is to hand next-session work a
 * sharp, implementable problem statement rather than a
 * mis-factored simulation.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import bedrock2.Syntax.

Require Import Bedrock.SafeRustSimulation.

(* ================================================================ *)
(* §1. Translator: Syntax.cmd.cmd -> option bcmd (carried over)      *)
(* ================================================================ *)

(** Translation of bedrock2 scalar expressions to [sexpr]. *)
Fixpoint syntax_expr_to_sexpr (e : Syntax.expr.expr) : option sexpr :=
  match e with
  | Syntax.expr.var x => Some (SVar x)
  | Syntax.expr.literal z =>
      if Z.leb 0 z then Some (SLit (Z.to_nat z)) else None
  | Syntax.expr.op Syntax.bopname.add a b =>
      match syntax_expr_to_sexpr a, syntax_expr_to_sexpr b with
      | Some sa, Some sb => Some (SAdd sa sb)
      | _, _ => None
      end
  | Syntax.expr.op Syntax.bopname.sub a b =>
      match syntax_expr_to_sexpr a, syntax_expr_to_sexpr b with
      | Some sa, Some sb => Some (SSub sa sb)
      | _, _ => None
      end
  | Syntax.expr.op Syntax.bopname.sru a b =>
      match syntax_expr_to_sexpr a, syntax_expr_to_sexpr b with
      | Some sa, Some sb => Some (SShr sa sb)
      | _, _ => None
      end
  | Syntax.expr.op Syntax.bopname.and a b =>
      match syntax_expr_to_sexpr a, syntax_expr_to_sexpr b with
      | Some sa, Some sb => Some (SAnd sa sb)
      | _, _ => None
      end
  | _ => None
  end.

Section Translator.
  Variable resolve_located : Syntax.expr.expr -> option located.

  Fixpoint syntax_to_bcmd (c : Syntax.cmd.cmd) : option bcmd :=
    match c with
    | Syntax.cmd.skip => Some BSkip
    | Syntax.cmd.seq c1 c2 =>
        match syntax_to_bcmd c1, syntax_to_bcmd c2 with
        | Some b1, Some b2 => Some (BSeq b1 b2)
        | _, _ => None
        end
    | Syntax.cmd.stackalloc x _ body =>
        match syntax_to_bcmd body with
        | Some bbody => Some (BLetZero x TFp bbody)
        | None => None
        end
    | Syntax.cmd.set x e =>
        match syntax_expr_to_sexpr e with
        | Some se => Some (BScalarSet x se)
        | None => None
        end
    | Syntax.cmd.cond t ct cf =>
        match syntax_expr_to_sexpr t,
              syntax_to_bcmd ct,
              syntax_to_bcmd cf with
        | Some st, Some bt, Some bf => Some (BIfNz st bt bf)
        | _, _, _ => None
        end
    | Syntax.cmd.while t body =>
        match syntax_expr_to_sexpr t, syntax_to_bcmd body with
        | Some st, Some bbody => Some (BWhileNz st bbody)
        | _, _ => None
        end
    | Syntax.cmd.call nil fname args =>
        match args with
        | dest_e :: src_es =>
            match resolve_located dest_e with
            | Some dloc =>
                let fix map_resolve (es : list Syntax.expr.expr)
                  : option (list located) :=
                  match es with
                  | [] => Some []
                  | e :: rest =>
                      match resolve_located e, map_resolve rest with
                      | Some l, Some ls => Some (l :: ls)
                      | _, _ => None
                      end
                  end in
                match map_resolve src_es with
                | Some src_locs => Some (BCall fname dloc src_locs)
                | None => None
                end
            | None => None
            end
        | [] => None
        end
    | Syntax.cmd.store _ addr val =>
        match resolve_located addr, syntax_expr_to_sexpr val with
        | Some loc, Some sval => Some (BLimbStore loc 0 sval)
        | _, _ => None
        end
    | Syntax.cmd.unset _ => Some BSkip
    | _ => None
    end.
End Translator.

(* ================================================================ *)
(* §2. Precise statement of the real G1 obligation                   *)
(* ================================================================ *)

(** The obligation is a compositional theorem saying that the Rust
    code, under a function-environment-aware semantics, produces the
    same Fp12 output as the bedrock2 WP proof predicts.

    Abstractly:

        Let [rust_fenv : string -> option rust_cmd] be the function
        environment built from [btranslate]-ing every bedrock2
        function in the BN254 tower.  Let [rust_exec_fenv] be the
        extension of [rust_exec] with an [XR_call_fn] rule that
        unfolds callees through [rust_fenv].

        Then for the top-level pairing:

          forall Px Py Qx Qy gamma1 gamma_y gamma1_p2,
            (* WP-level G2: *)
            bn254_pairing_dsd_optimal_correct ... ->
            (* rust_fenv is btranslate(bedrock2_fenv): *)
            rust_fenv = btranslate_fenv bedrock2_fenv ->
            (* Each leaf refines: *)
            (forall f, f in leaves -> bedrock2_leaf_fnspec f refines_to
                                        rust_leaf_spec f) ->
            (* Conclusion: *)
            exists rs1 rs2,
              rust_exec_fenv rust_fenv
                (RCall "bn254_pairing_dsd_optimal" <loc out> args)
                rs1 rs2
              /\ fp12_at_loc rs2 <loc out> =
                 bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2
                                        Px Py Qx Qy.

    The key new piece is [rust_exec_fenv] — which requires extending
    [SafeRustSimulation.rust_exec] with a function-environment call
    rule.  Neither [rust_exec] nor [bedrock_exec] in
    [SafeRustSimulation.v] currently models non-leaf calls. *)

(* ================================================================ *)
(* §3. Concrete action items for next-session work                   *)
(* ================================================================ *)

(** To close G1 on path (A) above:

    [A.1]  In [SafeRustSimulation.v], add a function environment
           parameter and the following to [rust_exec]:

             Variable fenv : string -> option rust_cmd.

             | XR_call_fn :
                 forall f body dest args in_vals call_dst rs_init rs_mid rs',
                   fenv f = Some body ->
                   locateds_lookup rs args = Some in_vals ->
                   bind_args_into_env in_vals rs = Some rs_init ->
                   rust_exec body rs_init rs_mid ->
                   located_update rs dest (extract_output rs_mid) = Some rs' ->
                   rust_exec (RCall f dest args) rs rs'

           (And similarly add [bedrock_exec] a function environment.)

           Estimated: ~200 LoC for the extension, ~300 LoC to update
           [safe_cmd_correct] to handle the new rule.

    [A.2]  For each non-leaf tower function (~50 functions), state
           a "Rust spec" in terms of [rust_exec_fenv] and prove it
           from the bedrock2 WP spec + leaf-refinement witnesses.

           For additive functions (e.g. Fp2_add), the Rust spec is
           just the composition of leaf ops — trivially provable from
           the leaf refinements.

           For higher-level functions (e.g. Fp12_mul), the Rust spec
           is proved by induction on the body: each call site is
           discharged by the callee's already-proved Rust spec.

           Estimated: ~50 functions × 20 LoC each = 1000 LoC.

    [A.3]  Instantiate the top-level theorem:

             Theorem bn254_pairing_rust_correct : ...

           Chain G2 + the Rust specs of the 5 callees (loaders,
           miller_loop, final_exp) via the composition structure.

           Estimated: ~200 LoC.

    Total path-(A) effort: ~1700 LoC / 2 focused weeks.

    ** Path (B) effort is larger (full Rust semantics model, not just
       fenv extension) and unnecessary for the BN254 end-to-end; (A)
       is the recommended path. *)

(* ================================================================ *)
(* §4. Current status recap                                          *)
(* ================================================================ *)

(** Summary of the BN254 end-to-end chain after this session:

    Layer              | Theorem                              | Status
    ------------------ | ------------------------------------ | ------
    Math spec          | bn254_optimal_ate_spec (Gallina)     | -
    WP composition G2  | bn254_pairing_dsd_optimal_correct    | Qed
    Math compose G2    | pairing_spec_compose                 | Qed
    Leaf refinement    | bn254_*_refines (6 witnesses)        | Qed
    Leaf simulation    | bn254_tower_correct                  | Qed
    Safe-Rust emit Ph3 | verify_safe_tower.sh (bit-exact)     | PASS
    G1 (Rust compose)  | bn254_pairing_rust_correct           | OPEN

    G1 is the only remaining formal obligation.  It is architecturally
    larger than originally scoped (~1700 LoC / 2 weeks, not the
    ~700 LoC / 1 week initial estimate) because it requires extending
    [SafeRustSimulation] with a function environment, not just
    writing a simulation proof over the existing semantics.

    All other verification effort for BN254 is complete and Qed-closed
    in [AUCurves/src/Bedrock/] — no fiat-crypto changes required. *)
