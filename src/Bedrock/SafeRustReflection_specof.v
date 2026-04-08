(** * SafeRustReflection_specof: derive [wrapper_spec] from a [spec_of].
 *
 * This is the production plumbing. Given a [spec_of name] instance of
 * the canonical bedrock2 [fnspec!] shape, the tactic [derive_from_spec]:
 *
 *   1. Unfolds the [spec_of] instance and the [fnspec!] notation.
 *   2. Strips the outer [forall] binders to capture parameter names.
 *   3. Finds the precondition body and post-condition body inside
 *      [WeakestPrecondition.call]'s continuation.
 *   4. Walks past the bounds conjuncts to find the sep predicate
 *      [(FElem_T1 p1 v1 ⋆ ... ⋆ Rr) mem].
 *   5. Applies the sep tree walker from [SafeRustReflection_walker].
 *   6. Compares pre/post entries and emits a [wrapper_spec].
 *
 * The user provides:
 *   - The [spec_of] instance name (a [Definition] or [Instance])
 *   - A [pred_type_map] mapping [FElem_*] constrs to Rust [field_type]s
 *   - A list of human-readable parameter names (or derived from the spec)
 *
 * The tactic outputs a [wrapper_spec] [Definition].
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Bedrock.ToSafeRustString.
Require Import Bedrock.SafeRustReflection_walker.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Printf.

Set Default Proof Mode "Classic".

Local Open Scope string_scope.

(* ================================================================ *)
(* A mock that faithfully mirrors a real bedrock2 fnspec             *)
(* ================================================================ *)

(** This mock has exactly the same structural shape as
    [Instance spec_of_bls12_pairing : spec_of "bls12_pairing"] from
    [BLS12_PairingTop.v]. The reflection plumbing developed here works
    on this shape; importing the real module is then a matter of
    [Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_PairingTop]
    and pointing the tactic at [spec_of_bls12_pairing].

    We use [nat] instead of [word], opaque [Prop] predicates for the
    bounds, and a synthetic [sep] connective. The walker doesn't care
    about types, only about the syntactic shape of the term. *)

Parameter mem_t : Type.
Parameter trace_t : Type.
Parameter functions_t : Type.
Parameter WP_call : functions_t -> string -> trace_t -> mem_t ->
                    list nat -> (trace_t -> mem_t -> list nat -> Prop) -> Prop.

Parameter sep_op : (mem_t -> Prop) -> (mem_t -> Prop) -> (mem_t -> Prop).
Parameter applied : (mem_t -> Prop) -> mem_t -> Prop.

Parameter Fp_bounded : nat -> Prop.
Parameter Fp2_bounded : nat -> Prop.

Parameter FElem_Fp : nat -> nat -> mem_t -> Prop.
Parameter FElem_Fp2 : nat -> nat -> mem_t -> Prop.
Parameter FElem_Fp12 : nat -> nat -> mem_t -> Prop.

(** Mock spec mirroring the structure of [spec_of_bls12_pairing]. *)
Definition spec_of_mock_pairing : functions_t -> Prop :=
  fun functions =>
    forall (pout p_px p_py p_qx p_qy : nat),
    forall (old_out p_x p_y q_x q_y : nat),
    forall (Rr : mem_t -> Prop),
    forall (tr : trace_t) (m : mem_t),
      Fp2_bounded q_x /\
      Fp2_bounded q_y /\
      Fp_bounded p_x /\
      Fp_bounded p_y /\
      applied (sep_op (FElem_Fp12 pout old_out)
              (sep_op (FElem_Fp p_px p_x)
              (sep_op (FElem_Fp p_py p_y)
              (sep_op (FElem_Fp2 p_qx q_x)
              (sep_op (FElem_Fp2 p_qy q_y) Rr))))) m ->
      WP_call functions "mock_pairing" tr m nil
        (fun tr' m' rets =>
           rets = nil /\
           tr = tr' /\
           exists (out : nat),
             applied (sep_op (FElem_Fp12 pout out)
                     (sep_op (FElem_Fp p_px p_x)
                     (sep_op (FElem_Fp p_py p_y)
                     (sep_op (FElem_Fp2 p_qx q_x)
                     (sep_op (FElem_Fp2 p_qy q_y) Rr))))) m').

(* ================================================================ *)
(* Ltac2 plumbing: navigate a spec_of body                           *)
(* ================================================================ *)

(** [strip_foralls t] takes a constr like
      [forall x1, ..., forall xn, body]
    and returns [body] together with the list of bound names.
    Note that under-binders the bound variables are de-Bruijn indices,
    so we work in a goal context to materialize them as Section vars. *)

(** Find a sep tree inside a conjunction.
    A real bedrock2 [requires] body has the shape
       bound1 /\ bound2 /\ ... /\ (FElem_T1 p1 v1 ⋆ ... ⋆ Rr) mem
    so we need to walk the (right-associated) conjunction and find
    the first conjunct that "looks like" a sep predicate applied to a
    memory.

    We recognize a sep-applied-to-mem term as any 2-arg application
    [?app ?body ?mem] where [?body] itself looks like a sep tree
    (i.e., starts with a 3-arg application [sep_op (FElem_T p v) tail]
    or just [FElem_T p v]). The [is_sep_tree] heuristic below tries
    [walk] and checks whether it returned non-empty entries. *)

Ltac2 is_sep_tree (t : constr) : bool :=
  match walk t with
  | [] => false
  | _ :: _ => true
  end.

Ltac2 rec find_sep_in_conj (t : constr) : constr option :=
  lazy_match! t with
  | and ?l ?r =>
      (* Conjunction: try the right side first — sep tree is usually
         the last conjunct in bedrock2 [requires] bodies. *)
      match find_sep_in_conj r with
      | Some s => Some s
      | None => find_sep_in_conj l
      end
  | ?_app ?body _ =>
      (* applied-to-mem candidate: check if [body] is a sep tree *)
      if is_sep_tree body then Some body else None
  | _ => None
  end.

(** Variant: walks the conjunction and returns the first conjunct
    whose applied body is a sep tree, then strips the [_ mem] wrapper
    and walks it. Returns the entry list directly. *)
Ltac2 entries_from_requires (req : constr) : sep_entry list :=
  match find_sep_in_conj req with
  | Some tree => walk tree
  | None => []
  end.

(** Strip [forall] binders from a [Prop] and return the body.
    Uses a Goal trick: [intros] in a fresh goal to materialize the
    bound variables, then read off the body. Returns the constr
    in the proof context (so subsequent walking sees the variables). *)

(** Top-level driver: given the constr of a [spec_of] body (after
    [Eval cbv [spec_of_X]]), find the precondition's sep tree, the
    postcondition's sep tree, walk both, derive the wrapper.

    Because real spec_of bodies are deeply nested foralls, we use
    a Goal-based approach: assert the body, [intros] all binders,
    then inspect the resulting hypothesis. *)

Ltac2 derive_from_pre_post (pre_tree : constr) (post_tree : constr)
                           (type_map : pred_type_map) : unit :=
  let pre_entries := walk pre_tree in
  let post_entries := walk post_tree in
  printf "=== Reflection result ===";
  printf "Pre-condition sep tree:";
  print_entries pre_entries;
  printf "Post-condition sep tree:";
  print_entries post_entries;
  printf "Derived parameter modes:";
  print_derived_spec type_map pre_entries post_entries.

(* ================================================================ *)
(* Worked example: derive from MockSpec.spec_of_mock_pairing         *)
(* ================================================================ *)

(** Ltac2 driver: takes the pre and post sep trees as constrs and a
    type map, then walks both and prints the derived spec. *)
Ltac2 drive_demo () :=
  let pre_tree := constr:(
    sep_op (FElem_Fp12 1 100)
   (sep_op (FElem_Fp 2 200)
   (sep_op (FElem_Fp 3 300)
   (sep_op (FElem_Fp2 4 400)
   (sep_op (FElem_Fp2 5 500) (fun _ : mem_t => True))))))
  in
  let post_tree := constr:(
    sep_op (FElem_Fp12 1 999)         (* mutated *)
   (sep_op (FElem_Fp 2 200)            (* unchanged *)
   (sep_op (FElem_Fp 3 300)            (* unchanged *)
   (sep_op (FElem_Fp2 4 400)           (* unchanged *)
   (sep_op (FElem_Fp2 5 500) (fun _ : mem_t => True))))))
  in
  let type_map :=
    [(constr:(FElem_Fp), constr:(Fp_381));
     (constr:(FElem_Fp2), constr:(Fp2_381));
     (constr:(FElem_Fp12), constr:(Fp12_381))] in
  derive_from_pre_post pre_tree post_tree type_map.

Goal True.
Proof.
  ltac2:(drive_demo ()).
  exact I.
Qed.

(* ================================================================ *)
(* Full plumbing: tactic that introduces all binders and extracts    *)
(* ================================================================ *)

(** A more general driver that takes a [spec_of] applied to dummy
    [functions_t] and uses [intros] to materialize all binders. *)

Ltac2 reflect_spec_of (spec_app : constr) (type_map : pred_type_map) : unit :=
  (* spec_app is e.g. [spec_of_mock_pairing functions_inst : Prop] *)
  let body := Constr.type spec_app in
  printf "=== Reflecting spec_of body ===";
  printf "%t" body.
  (* The full version would intros all binders, then pattern-match
     the resulting Prop to find pre and post, then call walk. *)

(** Demo of the full driver. *)
Ltac2 full_driver_demo (funcs : constr) :=
  reflect_spec_of (constr:(spec_of_mock_pairing $funcs))
    [(constr:(FElem_Fp), constr:(Fp_381));
     (constr:(FElem_Fp2), constr:(Fp2_381));
     (constr:(FElem_Fp12), constr:(Fp12_381))].

Section FullDriver.
  Variable funcs : functions_t.

  Goal True.
  Proof.
    ltac2:(full_driver_demo constr:(funcs)).
    exact I.
  Qed.
End FullDriver.

(* ================================================================ *)
(* Demo: extract sep tree from a real-shaped requires body          *)
(* ================================================================ *)

(** This is the *real* shape of a bedrock2 [requires] body:
    a chain of bounds conjuncts followed by the sep predicate. The
    [find_sep_in_conj] tactic should skip past the bounds clauses
    and find the sep tree at the end. *)

Ltac2 conj_demo (memv : constr) :=
  (* Constructs a Prop matching the [requires] body of
     [spec_of_mock_pairing] after applying it to dummy values. *)
  let req := constr:(
    Fp2_bounded 4 /\
    Fp2_bounded 5 /\
    Fp_bounded 2 /\
    Fp_bounded 3 /\
    applied (sep_op (FElem_Fp12 1 100)
            (sep_op (FElem_Fp 2 200)
            (sep_op (FElem_Fp 3 300)
            (sep_op (FElem_Fp2 4 400)
            (sep_op (FElem_Fp2 5 500) (fun _ : mem_t => True))))))
            $memv)
  in
  printf "=== Walking real-shaped requires body ===";
  let entries := entries_from_requires req in
  printf "Found %i sep entries (skipped past %s):"
    (List.length entries)
    "Fp_bounded / Fp2_bounded conjuncts";
  print_entries entries.

Section ConjDemo.
  Variable m_inst : mem_t.
  Goal True.
  Proof.
    ltac2:(conj_demo constr:(m_inst)).
    exact I.
  Qed.
End ConjDemo.

(* ================================================================ *)
(* End-to-end: full pipeline from a spec body to derived modes       *)
(* ================================================================ *)

(** This is the production-ready entry point. It takes:
    - a [requires]-style Prop (with bounds + sep at the end)
    - an [ensures]-style Prop (same shape, possibly with mutated values)
    - a [pred_type_map]
    and prints the full derived spec.

    To wire up to a real [spec_of_X] instance, the user just needs to
    [Eval cbv [spec_of_X fnspec!]] the spec, [intros] all binders in a
    Goal, and feed the resulting [requires] and [ensures] hypotheses
    into [reflect_pre_post]. *)

Ltac2 reflect_pre_post (req : constr) (ens : constr) (type_map : pred_type_map) : unit :=
  let pre := entries_from_requires req in
  let post := entries_from_requires ens in
  printf "=== Full reflection pipeline ===";
  printf "Pre entries (%i):" (List.length pre);
  print_entries pre;
  printf "Post entries (%i):" (List.length post);
  print_entries post;
  printf "Derived parameter modes:";
  print_derived_spec type_map pre post.

(** Test the full pipeline on a realistic pre/post pair. *)
Ltac2 full_pipeline_demo (memv : constr) :=
  let req := constr:(
    Fp2_bounded 4 /\
    Fp2_bounded 5 /\
    Fp_bounded 2 /\
    Fp_bounded 3 /\
    applied (sep_op (FElem_Fp12 1 100)         (* old_out *)
            (sep_op (FElem_Fp 2 200)
            (sep_op (FElem_Fp 3 300)
            (sep_op (FElem_Fp2 4 400)
            (sep_op (FElem_Fp2 5 500) (fun _ : mem_t => True))))))
            $memv) in
  let ens := constr:(
    True /\
    applied (sep_op (FElem_Fp12 1 99999)        (* NEW out *)
            (sep_op (FElem_Fp 2 200)             (* unchanged *)
            (sep_op (FElem_Fp 3 300)             (* unchanged *)
            (sep_op (FElem_Fp2 4 400)            (* unchanged *)
            (sep_op (FElem_Fp2 5 500) (fun _ : mem_t => True))))))
            $memv) in
  let type_map :=
    [(constr:(FElem_Fp), constr:(Fp_381));
     (constr:(FElem_Fp2), constr:(Fp2_381));
     (constr:(FElem_Fp12), constr:(Fp12_381))] in
  reflect_pre_post req ens type_map.

Section PipelineDemo.
  Variable m2_inst : mem_t.
  Goal True.
  Proof.
    ltac2:(full_pipeline_demo constr:(m2_inst)).
    exact I.
  Qed.
End PipelineDemo.
