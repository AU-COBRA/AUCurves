(** * SafeRustReflection_walker: Ltac2 sep-tree walker.
 *
 * Walks a sep tree of the canonical shape
 *
 *   sep (Pred1 p1 v1) (sep (Pred2 p2 v2) (... (sep PredN pN vN) Rr))
 *
 * and returns a list of [(predicate_constr, ptr_constr, val_constr)]
 * triples. The predicate constructor is captured as a constr (not a
 * string), so the caller can match on it.
 *
 * Combined with the [WrapperSpecFor] typeclass approach in
 * [SafeRustReflection.v], this gives us mechanical extraction of
 * wrapper specs from a [spec_of] instance.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Bedrock.ToSafeRustString.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Printf.

(* ================================================================ *)
(* Synthetic memory model for testing                                *)
(* ================================================================ *)

Section Mock.
  Variable mem : Type.
  Variable sep : (mem -> Prop) -> (mem -> Prop) -> (mem -> Prop).
  Variable FElem_Fp   : nat -> nat -> mem -> Prop.
  Variable FElem_Fp2  : nat -> nat -> mem -> Prop.
  Variable FElem_Fp12 : nat -> nat -> mem -> Prop.
  Variable Rr : mem -> Prop.

  Definition mock_pre (pout p_px p_py : nat) (out p_x p_y : nat) : mem -> Prop :=
    sep (FElem_Fp12 pout out)
   (sep (FElem_Fp p_px p_x)
   (sep (FElem_Fp p_py p_y) Rr)).
End Mock.

(* ================================================================ *)
(* Ltac2 walker                                                      *)
(* ================================================================ *)

(** A [sep_entry] in Ltac2: triple of constrs. *)
Ltac2 Type sep_entry := constr * constr * constr.

(** Try to recognize [t] as [Pred ?p ?v] (an FElem-shaped predicate).
    Returns [Some (Pred, p, v)] or [None]. *)
Ltac2 try_split_pred (t : constr) : (constr * constr * constr) option :=
  lazy_match! t with
  | ?pred ?p ?v => Some (pred, p, v)
  | _ => None
  end.

(** Walk a sep tree and collect entries.
    Recognizes any 4-arity application as the [sep] connective:
    [?sep_op ?head ?tail]. The first argument is treated as head and
    second as tail. *)
Ltac2 rec walk (t : constr) : (constr * constr * constr) list :=
  lazy_match! t with
  | ?_sep ?head ?tail =>
      (* Either: [sep head tail] (head is a pred application, tail is sep tree)
         or: [pred ptr val] (we've reached a final predicate, no more sep) *)
      match try_split_pred head with
      | Some entry =>
          (* head was a predicate application, so this is [sep head tail] *)
          entry :: walk tail
      | None =>
          (* head was not a predicate application, so [t] itself is [pred ptr val]
             — we should have matched it as [pred a1 a2 ... an]. *)
          match try_split_pred t with
          | Some entry => [entry]
          | None => []
          end
      end
  | _ => []
  end.

(** Pretty-print entries for debugging. *)
Ltac2 print_entry (e : constr * constr * constr) : unit :=
  let (pred, p, v) := e in
  printf "  pred=%t  ptr=%t  val=%t" pred p v.

Ltac2 print_entries (es : (constr * constr * constr) list) : unit :=
  List.iter print_entry es.

(* ================================================================ *)
(* Demonstration                                                      *)
(* ================================================================ *)

(** Top-level tactic for running the walker on a constr.
    First reduces lets/betas, then walks. *)

Ltac2 walk_and_print (t : constr) : unit :=
  let es := walk t in
  printf "Walker found %i entries:" (List.length es);
  print_entries es.

(** Compare pre and post entry lists by pointer name.
    A parameter at pointer [p] is read-only iff its value name is the
    same in both pre and post. Returns a list of [(ptr, mode_string)]
    where mode_string is "in" or "out". *)

Ltac2 entries_to_modes (pre : sep_entry list) (post : sep_entry list)
  : (constr * string) list :=
  List.map (fun e =>
    let (_, p, v_pre) := e in
    let v_post :=
      List.find_opt (fun e' =>
        let (_, p', _) := e' in Constr.equal p p') post
    in
    let mode :=
      match v_post with
      | None => "out"
      | Some e' =>
          let (_, _, v') := e' in
          if Constr.equal v_pre v' then "in" else "out"
      end
    in
    (p, mode)
  ) pre.

(** Demo: full pre/post comparison. *)
Section WalkerDemo.
  Variable mem_t : Type.
  Variable sep_v : (mem_t -> Prop) -> (mem_t -> Prop) -> (mem_t -> Prop).
  Variable F : nat -> nat -> mem_t -> Prop.
  Variable Rframe : mem_t -> Prop.

  (** Pre and post for a function with one mutated and two read-only args.
      [pout] holds [old_out] in pre, [out_new] in post → mutated.
      [p_x], [p_y] hold the same values [x], [y] in both → read-only. *)
  Goal True.
  Proof.
    let pre := walk constr:(
      sep_v (F 1 1000)         (* pout, old_out *)
       (sep_v (F 2 2000)        (* p_x, x *)
        (sep_v (F 3 3000) Rframe))) in    (* p_y, y *)
    let post := walk constr:(
      sep_v (F 1 9999)         (* pout, NEW out *)
       (sep_v (F 2 2000)        (* p_x, x — unchanged *)
        (sep_v (F 3 3000) Rframe))) in    (* p_y, y — unchanged *)
    let modes := entries_to_modes pre post in
    printf "Pre/post comparison:";
    List.iter (fun pm =>
      let (p, m) := pm in
      printf "  ptr=%t mode=%s" p m
    ) modes;
    exact I.
  Qed.
End WalkerDemo.

(* ================================================================ *)
(* Building a wrapper_spec from walker output                        *)
(* ================================================================ *)

(** Map a predicate-name string and a Rust type. The type lookup is
    user-provided because the walker captures the predicate as a constr,
    which doesn't directly give a string name. *)

Ltac2 Type pred_type_map := (constr * constr) list.   (* (pred constr, field_type constr) *)

(** Look up a predicate constr in the type map. *)
Ltac2 rec lookup_pred (m : pred_type_map) (p : constr) : constr option :=
  match m with
  | [] => None
  | (p', ft) :: rest =>
      if Constr.equal p p' then Some ft else lookup_pred rest p
  end.

(** Print a derived param spec summary. The result of the walker is
    a sequence of [(predicate, ptr, mode)] triples; mapping these to
    Rust [field_type] constants and string names is straightforward
    once the user provides a [pred_type_map]. *)

Ltac2 print_derived_spec
  (type_map : pred_type_map)
  (pre : sep_entry list)
  (post : sep_entry list)
  : unit :=
  let modes := entries_to_modes pre post in
  printf "Derived parameter specs:";
  List.iter (fun e =>
    let (pred, p, _) := e in
    let ft :=
      match lookup_pred type_map pred with
      | Some ft => ft
      | None => constr:(Fp_381)  (* default *)
      end
    in
    let mode :=
      match List.find_opt (fun pm =>
        let (p', _) := pm in Constr.equal p p') modes with
      | Some pm => let (_, m) := pm in m
      | None => "?"
      end
    in
    printf "  %t : %t (%s)" p ft mode
  ) pre.

(** Demo: derive a wrapper spec from a synthetic pre/post pair using
    a type map that says [F → Fp_381]. *)
Section DeriveDemo.
  Variable mem_t : Type.
  Variable sep_v : (mem_t -> Prop) -> (mem_t -> Prop) -> (mem_t -> Prop).
  Variable Pf : nat -> nat -> mem_t -> Prop.
  Variable Pfp2 : nat -> nat -> mem_t -> Prop.
  Variable Pfp12 : nat -> nat -> mem_t -> Prop.
  Variable Rframe : mem_t -> Prop.

  Goal True.
  Proof.
    (* Pre: pout/Fp12 with old_out, p_x/Fp with x, q_x/Fp2 with q *)
    let pre := walk constr:(
      sep_v (Pfp12 100 1)
       (sep_v (Pf 200 2)
        (sep_v (Pfp2 300 3) Rframe))) in
    (* Post: same shape, but pout has new value *)
    let post := walk constr:(
      sep_v (Pfp12 100 999)
       (sep_v (Pf 200 2)
        (sep_v (Pfp2 300 3) Rframe))) in
    let type_map :=
      [(constr:(Pf), constr:(Fp_381));
       (constr:(Pfp2), constr:(Fp2_381));
       (constr:(Pfp12), constr:(Fp12_381))] in
    print_derived_spec type_map pre post;
    exact I.
  Qed.
End DeriveDemo.

