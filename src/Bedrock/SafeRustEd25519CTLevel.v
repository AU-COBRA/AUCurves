(** * Ed25519 SafeRust — constant-time information-flow analysis
 *
 * A syntactic CT typing discipline over [rust_cmd_ed] (defined in
 * [SafeRustEd25519Sim.v]).  Each storage slot is classified as either
 * [Public] or [Secret].  The pass:
 *
 *   §1  Level lattice (Public ⊑ Secret)
 *   §2  Level environment (finite-list-based)
 *   §3  Expression typing — [sexpr_level]
 *   §4  Command typing    — [cmd_ct_ok]
 *   §5  Soundness statement (paper claim)
 *   §6  Demo programs + Compute checks
 *
 * Key design point: [REdSelect] is allowed to branch on a [Secret]
 * condition because it compiles to a mask-based, branch-free
 * conditional move (subtle::ConditionallySelectable).  [REdIfNz] and
 * [REdWhileNz] must branch on Public values only.
 *
 * Read-only over the existing AST: this file is purely additive and
 * does not modify [SafeRustEd25519Sim.v] or [SafeRustEd25519BorrowCheck.v].
 *
 * Reference: RustCmdRupicola roadmap, Tier 6 (1).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Levels                                                        *)
(* ================================================================ *)

(** Two-point security lattice: [Public ⊑ Secret]. *)
Inductive level : Set := Public | Secret.

Definition level_eqb (a b : level) : bool :=
  match a, b with
  | Public, Public => true
  | Secret, Secret => true
  | _, _ => false
  end.

(** Join: least upper bound. *)
Definition level_join (a b : level) : level :=
  match a, b with
  | Public, Public => Public
  | _, _ => Secret
  end.

(** Order: [a ⊑ b].  Secret is the top. *)
Definition level_le (a b : level) : bool :=
  match a, b with
  | Public, _ => true
  | Secret, Secret => true
  | _, _ => false
  end.

Lemma level_join_idem : forall l, level_join l l = l.
Proof. destruct l; reflexivity. Qed.

Lemma level_join_Public_l : forall l, level_join Public l = l.
Proof. destruct l; reflexivity. Qed.

Lemma level_join_Public_r : forall l, level_join l Public = l.
Proof. destruct l; reflexivity. Qed.

(* ================================================================ *)
(* §2. Level environment                                             *)
(* ================================================================ *)

(** A level environment maps slot names to security levels.  Names
    absent from the environment default to [Public] — this matches the
    intuition that callers supply explicit secrecy labels for input
    slots and everything else (intermediate scratch, etc.) starts as
    Public until labelled by an assignment. *)
Definition level_env := list (String.string * level).

Definition env_lookup (e : level_env) (x : String.string) : level :=
  match List.find (fun p => String.eqb (fst p) x) e with
  | Some (_, l) => l
  | None => Public
  end.

(** Extend (or override) the level of [x] in [e]. *)
Definition env_set (e : level_env) (x : String.string) (l : level) : level_env :=
  (x, l) :: e.

(* ================================================================ *)
(* §3. Expression typing                                             *)
(* ================================================================ *)

(** A [sexpr_ed]'s level is the join of all variables it reads;
    literals contribute [Public]. *)
Fixpoint sexpr_level (env : level_env) (e : sexpr_ed) : level :=
  match e with
  | SVar x   => env_lookup env x
  | SLit _   => Public
  | SAdd a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SSub a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SMul a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SShr a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SAnd a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SLt  a b => level_join (sexpr_level env a) (sexpr_level env b)
  | SLimb v _ => env_lookup env v
                   (* Phase 0b: limb read inherits the level of the
                      enclosing tower slot. *)
  | SMul128 a b => level_join (sexpr_level env a) (sexpr_level env b)
                   (* Phase 0e (2026-05-13): u128 ops are leveled
                      identically to their u64 counterparts — the
                      operation itself is constant-time on x86_64
                      (single MUL + MULH or compiled to a single
                      mulx).  Level is the join of operand levels. *)
  | SAdd128 a b => level_join (sexpr_level env a) (sexpr_level env b)
  end.

(* ================================================================ *)
(* §4. Command typing                                                *)
(* ================================================================ *)

(** Join over a list of [located_ed]'s levels (looked up in env). *)
Fixpoint args_level (env : level_env) (args : list located_ed) : level :=
  match args with
  | [] => Public
  | a :: rest => level_join (env_lookup env a.(loc_var)) (args_level env rest)
  end.

(** [cmd_ct_ok c env pc] returns [Some env'] when [c] is CT-safe in
    program-counter context [pc] starting from environment [env];
    [None] signals a CT violation.

    The pc-level is raised on entry to [REdIfNz] / [REdWhileNz] branches
    so that any write inside is at least as secret as the condition. *)
Fixpoint cmd_ct_ok (c : rust_cmd_ed) (env : level_env) (pc : level)
    : option level_env :=
  match c with

  | REdSkip => Some env

  | REdSeq c1 c2 =>
      match cmd_ct_ok c1 env pc with
      | Some env' => cmd_ct_ok c2 env' pc
      | None => None
      end

  | REdLetZero x _ body =>
      (* Fresh tower slot bound to the zero value; gets level [pc]. *)
      cmd_ct_ok body (env_set env x pc) pc

  | REdLetU64 x e body =>
      cmd_ct_ok body
        (env_set env x (level_join (sexpr_level env e) pc)) pc

  | REdScalarSet x e =>
      let le := level_join (sexpr_level env e) pc in
      let lx := env_lookup env x in
      (* Must not assign secret data into a public-labelled slot. *)
      if level_le le lx then Some env else None

  | REdCall _ dest args =>
      let dl := env_lookup env dest.(loc_var) in
      let al := level_join (args_level env args) pc in
      if level_le al dl then Some env else None

  | REdIfNz e ct cf =>
      (* Branching on a secret is forbidden here (use REdSelect). *)
      if level_le (sexpr_level env e) Public then
        let pc' := level_join pc (sexpr_level env e) in
        match cmd_ct_ok ct env pc' with
        | Some env' => cmd_ct_ok cf env' pc'
        | None => None
        end
      else None

  | REdWhileNz e body =>
      (* Loop count must be Public — no termination side-channel. *)
      if level_le (sexpr_level env e) Public then
        cmd_ct_ok body env pc
      else None

  | REdByteStore loc idx val =>
      let ll := env_lookup env loc.(loc_var) in
      let li := sexpr_level env idx in
      let lv := sexpr_level env val in
      let rhs := level_join (level_join li lv) pc in
      if level_le rhs ll then Some env else None

  | REdByteLoad x loc idx =>
      let ll := env_lookup env loc.(loc_var) in
      let li := sexpr_level env idx in
      let l := level_join (level_join ll li) pc in
      Some (env_set env x l)

  | REdFor x _ body =>
      (* Counted up 0..n-1; the index is Public-by-construction.
         Bound [n] is a Coq [nat], hence statically known. *)
      cmd_ct_ok body (env_set env x Public) pc

  | REdSelect cond src_t src_f dest =>
      (* CT conditional move: compiles to a branch-free mask merge.
         Both sources are ALWAYS read.  Hence a Secret cond is fine
         AS LONG AS the dest is labelled to hold the join of cond,
         src_t, src_f, and pc — i.e. at least Secret if any input is. *)
      let lc := sexpr_level env cond in
      let lt := env_lookup env src_t.(loc_var) in
      let lf := env_lookup env src_f.(loc_var) in
      let ld := env_lookup env dest.(loc_var) in
      let rhs := level_join (level_join lc (level_join lt lf)) pc in
      if level_le rhs ld then Some env else None

  | REdCallN _ dests args =>
      let al := level_join (args_level env args) pc in
      (* Every dest must be at least as secret as the joined args. *)
      let fix all_ok (ds : list located_ed) : bool :=
        match ds with
        | [] => true
        | d :: rest =>
            andb (level_le al (env_lookup env d.(loc_var))) (all_ok rest)
        end in
      if all_ok dests then Some env else None

  | REdCallFn _ dest args =>
      (* Verified-helper call: same level check as REdCall. *)
      let dl := env_lookup env dest.(loc_var) in
      let al := level_join (args_level env args) pc in
      if level_le al dl then Some env else None

  | REdBlock body =>
      (* Scoped block: transparent — body checks under same env / pc. *)
      cmd_ct_ok body env pc

  | REdSetBytes loc _ =>
      (* Whole-array literal write: the source list is closed Z data
         (compile-time constants), so its level is Public.  Allow the
         write iff the destination is at least Public ∨ pc.  We model
         this conservatively by requiring [pc ⊑ env(loc)] — same as
         the [REdByteStore] case with an empty value/index level. *)
      let ll := env_lookup env loc.(loc_var) in
      if level_le pc ll then Some env else None

  | REdArrLoad dst src idx =>
      (* Phase Ext: array-of-slots read.  Treat as REdByteLoad but
         over the array slot: the dst's level becomes the join of the
         src slot, index, and pc. *)
      let ls := env_lookup env src.(loc_var) in
      let li := sexpr_level env idx in
      let l := level_join (level_join ls li) pc in
      Some (env_set env dst.(loc_var) l)

  | REdArrStore arr idx src =>
      (* Phase Ext: array-of-slots write.  Treat as REdByteStore:
         the join of src's level, idx's level, and pc must be at most
         the array slot's level. *)
      let ll := env_lookup env arr.(loc_var) in
      let ls := env_lookup env src.(loc_var) in
      let li := sexpr_level env idx in
      let rhs := level_join (level_join li ls) pc in
      if level_le rhs ll then Some env else None

  | REdLimbStore loc _ e =>
      (* Phase 0b: limb-level write.  The level of the source sexpr
         (including any [SLimb] reads it contains) joined with [pc]
         must be at most the destination slot's level.  Mirrors the
         [REdByteStore] case. *)
      let ll := env_lookup env loc.(loc_var) in
      let le := sexpr_level env e in
      let rhs := level_join le pc in
      if level_le rhs ll then Some env else None
  end.

(* ================================================================ *)
(* §5. Soundness statement (paper claim)                             *)
(* ================================================================ *)

(** Top-level CT predicate: a command is CT-safe under [env] iff it
    type-checks starting from [pc = Public]. *)
Definition cmd_ct_safe (c : rust_cmd_ed) (env : level_env) : Prop :=
  exists env', cmd_ct_ok c env Public = Some env'.

(** Non-interference is the intended semantic content of [cmd_ct_safe],
    stated as a paper claim.  A full operational-equivalence proof is
    out of scope for this pass; the typing rules above are a
    well-formed syntactic discipline that downstream consumers (the
    RustCmdRupicola emitter, paper claims) can rely on. *)

(* ================================================================ *)
(* §6. Anchor lemmas                                                 *)
(* ================================================================ *)

Lemma cmd_ct_ok_skip_id : forall env pc, cmd_ct_ok REdSkip env pc = Some env.
Proof. reflexivity. Qed.

(** Builders for the select-on-secret demo. *)
Definition loc_secret_in  : located_ed := {| loc_var := "s_in";  loc_type := TU64 |}.
Definition loc_pub_in     : located_ed := {| loc_var := "p_in";  loc_type := TU64 |}.
Definition loc_secret_out : located_ed := {| loc_var := "s_out"; loc_type := TU64 |}.
Definition loc_pub_out    : located_ed := {| loc_var := "p_out"; loc_type := TU64 |}.

(** REdSelect on a Secret condition is accepted when dest is Secret. *)
Lemma cmd_ct_ok_select_secret :
  let env := [("c", Secret); ("s_in", Secret); ("p_in", Public);
              ("s_out", Secret); ("p_out", Public)] in
  cmd_ct_ok (REdSelect (SVar "c") loc_secret_in loc_pub_in loc_secret_out)
    env Public
  = Some env.
Proof. reflexivity. Qed.

(** Symmetrically: REdSelect on a Secret condition is REJECTED when
    dest is Public.  This pins the constraint down. *)
Lemma cmd_ct_ok_select_secret_into_public_fails :
  let env := [("c", Secret); ("s_in", Secret); ("p_in", Public);
              ("s_out", Secret); ("p_out", Public)] in
  cmd_ct_ok (REdSelect (SVar "c") loc_secret_in loc_pub_in loc_pub_out)
    env Public
  = None.
Proof. reflexivity. Qed.

(** Branching on a Secret with REdIfNz is rejected. *)
Lemma cmd_ct_ok_if_secret_fails :
  let env := [("c", Secret)] in
  cmd_ct_ok (REdIfNz (SVar "c") REdSkip REdSkip) env Public = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §7. Demo programs                                                 *)
(* ================================================================ *)

(** Demo 1: select on a Secret bit -- the canonical CT idiom.
      let c : Secret = ...;       // user-supplied
      let s_in : Secret = ...;
      let p_in : Public = ...;
      let s_out : Secret = ...;
      s_out := if c then s_in else p_in   // mask merge, NOT a branch
*)
Definition demo_select_secret : rust_cmd_ed :=
  REdSelect (SVar "c") loc_secret_in loc_pub_in loc_secret_out.

Definition demo_env_secret : level_env :=
  [("c", Secret); ("s_in", Secret); ("p_in", Public);
   ("s_out", Secret); ("p_out", Public)].

(** Should reduce to [Some demo_env_secret]. *)
Definition demo_select_check : option level_env :=
  cmd_ct_ok demo_select_secret demo_env_secret Public.

Compute demo_select_check.

(** Demo 2: REdIfNz on a Secret -- the canonical CT VIOLATION.
      if c { /* secret-dependent control flow */ }
    Should reduce to [None]. *)
Definition demo_if_secret : rust_cmd_ed :=
  REdIfNz (SVar "c") REdSkip REdSkip.

Definition demo_if_check : option level_env :=
  cmd_ct_ok demo_if_secret demo_env_secret Public.

Compute demo_if_check.

(** Demo 3: REdIfNz on a Public guard is fine. *)
Definition demo_if_public : rust_cmd_ed :=
  REdIfNz (SVar "p_in") REdSkip REdSkip.

Definition demo_if_public_check : option level_env :=
  cmd_ct_ok demo_if_public demo_env_secret Public.

Compute demo_if_public_check.
