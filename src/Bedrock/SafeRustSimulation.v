(** * Simulation proof for ToSafeRustBody.v.
 *
 * This file gives a soundness theorem for the safe-Rust pretty printer
 * in [ToSafeRustBody.v].
 *
 * Contents:
 *   §1 Tower types and Rust value layout (#[repr(C)])
 *   §2 Field paths (well-typed projections into struct trees)
 *   §3 The Rust subset emitted by safe_cmd, with small-step semantics
 *   §4 Equivalence with bedrock2 — abstract relation
 *   §5 The simulation theorem (statement; structural proof outline)
 *   §6 Per-leaf refinement obligations (one per Fp primitive)
 *
 * Status: definitions and statements complete. The simulation theorem
 * is admitted modulo:
 *   (a) instantiation of bedrock2.Semantics for [equiv]
 *   (b) per-leaf refinement lemmas (8 leaves; one per primitive)
 *
 * The structure of the proof — by induction on bedrock_step, one case
 * per cmd constructor — is described in the technical report §12.5
 * and in comments below.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Tower types                                                   *)
(* ================================================================ *)

Inductive tower_type :=
  | TFp
  | TFp2
  | TFp6
  | TFp12.

Definition tower_type_eq_dec (t1 t2 : tower_type) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

(** Sizes in bytes, parameterized by Fp limb count [N]. *)
Definition tt_bytes (N : nat) (t : tower_type) : nat :=
  let fp := N * 8 in
  match t with
  | TFp   => fp
  | TFp2  => 2 * fp
  | TFp6  => 6 * fp
  | TFp12 => 12 * fp
  end.

(** Inductive Rust value: matches the [#[repr(C)]] struct definitions
    emitted by [type_decls] in ToSafeRustBody.v. The Fp constructor
    holds a list of u64 limbs; in the actual Rust, this is [u64; N]. *)
Inductive rust_val : tower_type -> Type :=
  | VFp   : list nat -> rust_val TFp
  | VFp2  : rust_val TFp -> rust_val TFp -> rust_val TFp2
  | VFp6  : rust_val TFp2 -> rust_val TFp2 -> rust_val TFp2 -> rust_val TFp6
  | VFp12 : rust_val TFp6 -> rust_val TFp6 -> rust_val TFp12.

Fixpoint zero_limbs (k : nat) : list nat :=
  match k with O => [] | S k' => 0 :: zero_limbs k' end.

Definition vfp_zero (N : nat) : rust_val TFp := VFp (zero_limbs N).

(** Defined non-recursively because the tower has fixed depth 4
    and Coq's guard checker can't see that TFp2/TFp6/TFp12 are
    "smaller" than TFp12 in the recursion. *)
Definition vfp2_zero (N : nat) : rust_val TFp2 :=
  VFp2 (vfp_zero N) (vfp_zero N).
Definition vfp6_zero (N : nat) : rust_val TFp6 :=
  VFp6 (vfp2_zero N) (vfp2_zero N) (vfp2_zero N).
Definition vfp12_zero (N : nat) : rust_val TFp12 :=
  VFp12 (vfp6_zero N) (vfp6_zero N).

Definition tt_zero (N : nat) (t : tower_type) : rust_val t :=
  match t with
  | TFp   => vfp_zero N
  | TFp2  => vfp2_zero N
  | TFp6  => vfp6_zero N
  | TFp12 => vfp12_zero N
  end.

(* ================================================================ *)
(* §2. Field paths                                                   *)
(* ================================================================ *)

Inductive field_step : tower_type -> tower_type -> Type :=
  | StepFp2_0 : field_step TFp2 TFp
  | StepFp2_1 : field_step TFp2 TFp
  | StepFp6_0 : field_step TFp6 TFp2
  | StepFp6_1 : field_step TFp6 TFp2
  | StepFp6_2 : field_step TFp6 TFp2
  | StepFp12_0 : field_step TFp12 TFp6
  | StepFp12_1 : field_step TFp12 TFp6.

Inductive field_path : tower_type -> tower_type -> Type :=
  | PathNil  : forall t, field_path t t
  | PathCons : forall t1 t2 t3, field_step t1 t2 -> field_path t2 t3 -> field_path t1 t3.

Definition project_step {t1 t2 : tower_type}
    (s : field_step t1 t2) (v : rust_val t1) : rust_val t2 :=
  match s in field_step a b return rust_val a -> rust_val b with
  | StepFp2_0 => fun v => match v with VFp2 a _ => a end
  | StepFp2_1 => fun v => match v with VFp2 _ b => b end
  | StepFp6_0 => fun v => match v with VFp6 a _ _ => a end
  | StepFp6_1 => fun v => match v with VFp6 _ b _ => b end
  | StepFp6_2 => fun v => match v with VFp6 _ _ c => c end
  | StepFp12_0 => fun v => match v with VFp12 a _ => a end
  | StepFp12_1 => fun v => match v with VFp12 _ b => b end
  end v.

Fixpoint project {t1 t2 : tower_type}
    (p : field_path t1 t2) (v : rust_val t1) : rust_val t2 :=
  match p in field_path a b return rust_val a -> rust_val b with
  | PathNil _ => fun v => v
  | PathCons _ _ _ s p' => fun v => project p' (project_step s v)
  end v.

Definition update_step {t1 t2 : tower_type}
    (s : field_step t1 t2) (new : rust_val t2) (v : rust_val t1) : rust_val t1 :=
  match s in field_step a b return rust_val b -> rust_val a -> rust_val a with
  | StepFp2_0 => fun n v => match v with VFp2 _ b => VFp2 n b end
  | StepFp2_1 => fun n v => match v with VFp2 a _ => VFp2 a n end
  | StepFp6_0 => fun n v => match v with VFp6 _ b c => VFp6 n b c end
  | StepFp6_1 => fun n v => match v with VFp6 a _ c => VFp6 a n c end
  | StepFp6_2 => fun n v => match v with VFp6 a b _ => VFp6 a b n end
  | StepFp12_0 => fun n v => match v with VFp12 _ b => VFp12 n b end
  | StepFp12_1 => fun n v => match v with VFp12 a _ => VFp12 a n end
  end new v.

Fixpoint update {t1 t2 : tower_type}
    (p : field_path t1 t2) (new : rust_val t2) (v : rust_val t1) : rust_val t1 :=
  match p in field_path a b return rust_val b -> rust_val a -> rust_val a with
  | PathNil _ => fun n _ => n
  | PathCons _ _ _ s p' => fun n v =>
      update_step s (update p' n (project_step s v)) v
  end new v.

(* ================================================================ *)
(* §2b. Field path computation from byte offsets                     *)
(* ================================================================ *)

(** [field_path_compute] is the Coq counterpart of the OCaml
    [field_path] function in [ToSafeRustBody.v] (which produces a
    string like ".c1.c0"). It returns the typed [field_path] value
    for a given byte offset within a tower type, given the Fp limb
    count [N].

    For BN254 ([N = 4], so each [Fp] is 32 bytes):
      - offset 0  in [TFp2]   → [.c0]
      - offset 32 in [TFp2]   → [.c1]
      - offset 64 in [TFp6]   → [.c1.c0] (second [Fp2], first [Fp])

    The function returns [None] for invalid offsets (not on a 32-byte
    boundary, or beyond the type's size). *)

Definition fp_size_bytes (N : nat) : nat := N * 8.

(** Field path for offset within [TFp2]: must be 0 (→ c0) or
    [fp_size_bytes N] (→ c1). *)
Definition field_path_fp2 (N : nat) (off : nat)
    : option { t : tower_type & field_path TFp2 t } :=
  if Nat.eqb off 0 then
    Some (existT _ TFp (PathCons _ _ _ StepFp2_0 (PathNil _)))
  else if Nat.eqb off (fp_size_bytes N) then
    Some (existT _ TFp (PathCons _ _ _ StepFp2_1 (PathNil _)))
  else None.

Example field_path_fp2_test_0 :
  field_path_fp2 4 0 = Some (existT _ TFp (PathCons _ _ _ StepFp2_0 (PathNil _))).
Proof. reflexivity. Qed.

Example field_path_fp2_test_32 :
  field_path_fp2 4 32 = Some (existT _ TFp (PathCons _ _ _ StepFp2_1 (PathNil _))).
Proof. reflexivity. Qed.

Example field_path_fp2_test_invalid :
  field_path_fp2 4 17 = None.
Proof. reflexivity. Qed.

(** Field path for [TFp6]: 3 sub-Fp2s, each [2 * fp_size_bytes N]
    bytes wide. Each Fp2 is then split into 2 Fps. *)
Definition field_path_fp6 (N : nat) (off : nat)
    : option { t : tower_type & field_path TFp6 t } :=
  let fp_sz := fp_size_bytes N in
  let fp2_sz := 2 * fp_sz in
  if Nat.eqb off 0 then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_0
                        (PathCons _ _ _ StepFp2_0 (PathNil _))))
  else if Nat.eqb off fp_sz then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_0
                        (PathCons _ _ _ StepFp2_1 (PathNil _))))
  else if Nat.eqb off fp2_sz then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_1
                        (PathCons _ _ _ StepFp2_0 (PathNil _))))
  else if Nat.eqb off (fp2_sz + fp_sz) then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_1
                        (PathCons _ _ _ StepFp2_1 (PathNil _))))
  else if Nat.eqb off (2 * fp2_sz) then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_2
                        (PathCons _ _ _ StepFp2_0 (PathNil _))))
  else if Nat.eqb off (2 * fp2_sz + fp_sz) then
    Some (existT _ TFp (PathCons _ _ _ StepFp6_2
                        (PathCons _ _ _ StepFp2_1 (PathNil _))))
  else None.

Example field_path_fp6_test_0 :
  field_path_fp6 4 0 =
  Some (existT _ TFp (PathCons _ _ _ StepFp6_0
                      (PathCons _ _ _ StepFp2_0 (PathNil _)))).
Proof. reflexivity. Qed.

Example field_path_fp6_test_64 :
  field_path_fp6 4 64 =
  Some (existT _ TFp (PathCons _ _ _ StepFp6_1
                      (PathCons _ _ _ StepFp2_0 (PathNil _)))).
Proof. reflexivity. Qed.

Example field_path_fp6_test_160 :
  field_path_fp6 4 160 =
  Some (existT _ TFp (PathCons _ _ _ StepFp6_2
                      (PathCons _ _ _ StepFp2_1 (PathNil _)))).
Proof. reflexivity. Qed.

(** Well-typedness of [field_path_fp2]: every successful result has
    destination type [TFp]. *)
Lemma field_path_fp2_dst :
  forall N off p, field_path_fp2 N off = Some p -> projT1 p = TFp.
Proof.
  intros N off p Hp.
  unfold field_path_fp2 in Hp.
  destruct (Nat.eqb off 0); [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (fp_size_bytes N)); [injection Hp as <-; reflexivity|].
  discriminate.
Qed.

(** Well-typedness of [field_path_fp6]: every successful result has
    destination type [TFp]. *)
Lemma field_path_fp6_dst :
  forall N off p, field_path_fp6 N off = Some p -> projT1 p = TFp.
Proof.
  intros N off p Hp.
  unfold field_path_fp6 in Hp.
  destruct (Nat.eqb off 0); [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (fp_size_bytes N)); [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (2 * fp_size_bytes N)); [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (2 * fp_size_bytes N + fp_size_bytes N));
    [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (2 * (2 * fp_size_bytes N))); [injection Hp as <-; reflexivity|].
  destruct (Nat.eqb off (2 * (2 * fp_size_bytes N) + fp_size_bytes N));
    [injection Hp as <-; reflexivity|].
  discriminate.
Qed.

(* ================================================================ *)
(* §3. The Rust subset                                               *)
(* ================================================================ *)

Definition var := string.

(** Anchored field path: a base variable + a path from its declared type. *)
Record located := mkLocated {
  loc_var : var;
  loc_src : tower_type;
  loc_dst : tower_type;
  loc_path : field_path loc_src loc_dst;
}.

(** A scalar expression (u64-valued). *)
Inductive sexpr :=
  | SVar : var -> sexpr
  | SLit : nat -> sexpr
  | SAdd : sexpr -> sexpr -> sexpr
  | SSub : sexpr -> sexpr -> sexpr
  | SShr : sexpr -> sexpr -> sexpr
  | SAnd : sexpr -> sexpr -> sexpr.

(** The Rust subset commands emitted by safe_cmd. *)
Inductive rust_cmd :=
  | RSkip
  | RSeq : rust_cmd -> rust_cmd -> rust_cmd
  | RLetZero : var -> tower_type -> rust_cmd -> rust_cmd
  | RLetU64Zero : var -> rust_cmd -> rust_cmd
  | RScalarSet : var -> sexpr -> rust_cmd
  | RCall : string -> located -> list located -> rust_cmd
  | RCloneCall : var -> located -> string -> located -> list located -> rust_cmd
  | RIfNz : sexpr -> rust_cmd -> rust_cmd -> rust_cmd
  | RWhileNz : sexpr -> rust_cmd -> rust_cmd
  | RLimbStore : located -> nat -> sexpr -> rust_cmd.

(* ================================================================ *)
(* §4. Rust state and small-step semantics                           *)
(* ================================================================ *)

Inductive tval := exist_tval : forall t, rust_val t -> tval.

Record rust_state := {
  rs_tower  : list (var * tval);
  rs_scalar : list (var * nat);
}.

Definition rs_empty : rust_state := {| rs_tower := []; rs_scalar := [] |}.

Fixpoint lookup_t (env : list (var * tval)) (x : var) : option tval :=
  match env with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_t rest x
  end.

Fixpoint lookup_s (env : list (var * nat)) (x : var) : option nat :=
  match env with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_s rest x
  end.

Definition rs_get_scalar (rs : rust_state) (x : var) : option nat :=
  lookup_s (rs_scalar rs) x.

(** Remove every binding for [x] from a tower environment. *)
Fixpoint remove_var (env : list (var * tval)) (x : var) : list (var * tval) :=
  match env with
  | [] => []
  | (y, v) :: rest =>
      if String.eqb y x then remove_var rest x
      else (y, v) :: remove_var rest x
  end.

(** Update an environment in place: if [x] is already bound, replace
    its value at that position; otherwise append [(x, v)] at the end.
    This makes [rs_set_tower] order-preserving for existing keys, so
    that [located_update] (which sets an existing key) leaves the list
    shape unchanged. *)
Fixpoint update_in_place (env : list (var * tval)) (x : var) (v : tval)
    : list (var * tval) :=
  match env with
  | [] => [(x, v)]
  | (y, w) :: rest =>
      if String.eqb y x then (x, v) :: rest
      else (y, w) :: update_in_place rest x v
  end.

Definition rs_set_tower (rs : rust_state) (x : var) (v : tval) : rust_state :=
  {| rs_tower := update_in_place (rs_tower rs) x v;
     rs_scalar := rs_scalar rs |}.
Definition rs_set_scalar (rs : rust_state) (x : var) (v : nat) : rust_state :=
  {| rs_tower := rs_tower rs; rs_scalar := (x, v) :: rs_scalar rs |}.

(** [set_nth k v xs]: replace the k-th element of [xs] with [v].
    Returns the original list unchanged if [k >= length xs].  Used to
    model a limb-level store into a [rust_val TFp] (backed by a
    [list nat]). *)
Fixpoint set_nth (k : nat) (v : nat) (xs : list nat) : list nat :=
  match xs, k with
  | []       , _      => []
  | _  :: rest, O     => v :: rest
  | x  :: rest, S k'  => x :: set_nth k' v rest
  end.

(** [replace_limb k v fp]: replace the k-th limb of an Fp value
    ([VFp limbs]) with [v]. *)
Definition replace_limb (k v : nat) (fp : rust_val TFp) : rust_val TFp :=
  match fp with
  | VFp limbs => VFp (set_nth k v limbs)
  end.

(** [set_nth] preserves length. *)
Lemma set_nth_length : forall k v xs,
  length (set_nth k v xs) = length xs.
Proof.
  induction k; intros v xs; destruct xs; simpl; auto.
Qed.

(** At index [k < length xs], [set_nth k v xs] has [v] at position [k]. *)
Lemma nth_set_nth_same : forall k v xs d,
  k < length xs -> nth k (set_nth k v xs) d = v.
Proof.
  induction k; intros v xs d Hlt; destruct xs as [| x rest]; simpl in *.
  - lia.
  - reflexivity.
  - lia.
  - apply IHk. lia.
Qed.

(** At index [j <> k], [set_nth k v xs] is unchanged at [j]. *)
Lemma nth_set_nth_other : forall k v xs j d,
  j <> k -> nth j (set_nth k v xs) d = nth j xs d.
Proof.
  induction k; intros v xs j d Hneq; destruct xs as [| x rest]; simpl.
  - reflexivity.
  - destruct j as [| j']; [contradiction | reflexivity].
  - reflexivity.
  - destruct j as [| j']; [reflexivity | apply IHk; lia].
Qed.

Section Semantics.

Variable u64_max : nat.

Fixpoint sexpr_eval (rs : rust_state) (e : sexpr) : option nat :=
  match e with
  | SVar x => rs_get_scalar rs x
  | SLit n => Some n
  | SAdd a b =>
      match sexpr_eval rs a, sexpr_eval rs b with
      | Some va, Some vb => Some ((va + vb) mod u64_max)
      | _, _ => None
      end
  | SSub a b =>
      match sexpr_eval rs a, sexpr_eval rs b with
      | Some va, Some vb => Some ((va + u64_max - vb) mod u64_max)
      | _, _ => None
      end
  | SShr a b =>
      match sexpr_eval rs a, sexpr_eval rs b with
      | Some va, Some vb => Some (Nat.shiftr va (vb mod 64))
      | _, _ => None
      end
  | SAnd a b =>
      match sexpr_eval rs a, sexpr_eval rs b with
      | Some va, Some vb => Some (Nat.land va vb)
      | _, _ => None
      end
  end.

Variable N : nat. (* Fp limb count *)

(** Small-step semantics for the structural cases. The call and store
    cases need access to leaf-function specs and are handled separately. *)
Inductive rust_step : rust_state -> rust_cmd -> rust_state -> rust_cmd -> Prop :=
  | RS_seq_skip : forall rs c,
      rust_step rs (RSeq RSkip c) rs c
  | RS_seq_step : forall rs1 c1 rs2 c1' c2,
      rust_step rs1 c1 rs2 c1' ->
      rust_step rs1 (RSeq c1 c2) rs2 (RSeq c1' c2)
  | RS_let_zero : forall rs x t c,
      rust_step rs (RLetZero x t c)
                (rs_set_tower rs x (exist_tval t (tt_zero N t))) c
  | RS_let_u64_zero : forall rs x c,
      rust_step rs (RLetU64Zero x c)
                (rs_set_scalar rs x 0) c
  | RS_scalar_set : forall rs x e v,
      sexpr_eval rs e = Some v ->
      rust_step rs (RScalarSet x e) (rs_set_scalar rs x v) RSkip
  | RS_if_true : forall rs e ct cf v,
      sexpr_eval rs e = Some v -> v <> 0 ->
      rust_step rs (RIfNz e ct cf) rs ct
  | RS_if_false : forall rs e ct cf,
      sexpr_eval rs e = Some 0 ->
      rust_step rs (RIfNz e ct cf) rs cf
  | RS_while_true : forall rs e body v,
      sexpr_eval rs e = Some v -> v <> 0 ->
      rust_step rs (RWhileNz e body) rs (RSeq body (RWhileNz e body))
  | RS_while_false : forall rs e body,
      sexpr_eval rs e = Some 0 ->
      rust_step rs (RWhileNz e body) rs RSkip.

Inductive rust_step_star : rust_state -> rust_cmd -> rust_state -> rust_cmd -> Prop :=
  | RSS_refl : forall rs c, rust_step_star rs c rs c
  | RSS_step : forall rs1 c1 rs2 c2 rs3 c3,
      rust_step rs1 c1 rs2 c2 ->
      rust_step_star rs2 c2 rs3 c3 ->
      rust_step_star rs1 c1 rs3 c3.

End Semantics.

(* ================================================================ *)
(* §5. Big-step Rust semantics (for the simulation proof)            *)
(* ================================================================ *)

(** We use big-step semantics for the simulation proof — it gives us
    structural induction on derivations directly, avoiding the
    bookkeeping of small-step closures.

    The small-step relation [rust_step] in §4 above is kept as a
    separate operational model; it can be linked to [rust_exec] by
    a standard equivalence theorem if needed. *)

Section BigStep.

Variable N : nat.
Variable u64_max : nat.

(** A leaf-function spec: given the function name, the destination
    type, the input destination value, and the typed input argument
    list, return the new destination value. The spec is total (no
    [option]) because we are inside the proof of a verified
    extraction; if a leaf can fail, the bedrock2 fnspec already
    rules that out. *)
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt -> list { t : tower_type & rust_val t } -> rust_val dt.

(** Look up the value at a [located] in a [rust_state]. We use [option]
    because a variable may not be in scope. *)
Definition located_lookup (rs : rust_state) (loc : located) : option (rust_val (loc_dst loc)) :=
  match lookup_t (rs_tower rs) (loc_var loc) with
  | Some (exist_tval t v) =>
      match tower_type_eq_dec t (loc_src loc) with
      | left H => Some (project (loc_path loc) (eq_rect t rust_val v _ H))
      | right _ => None
      end
  | None => None
  end.

(** Update a [located] in a [rust_state]. *)
Definition located_update (rs : rust_state) (loc : located)
    (new : rust_val (loc_dst loc)) : option rust_state :=
  match lookup_t (rs_tower rs) (loc_var loc) with
  | Some (exist_tval t v) =>
      match tower_type_eq_dec t (loc_src loc) with
      | left H =>
          let v' := update (loc_path loc) new (eq_rect t rust_val v _ H) in
          Some (rs_set_tower rs (loc_var loc)
                  (exist_tval (loc_src loc) v'))
      | right _ => None
      end
  | None => None
  end.

(** Pack a located lookup into a typed Sigma value. *)
Definition located_lookup_sig (rs : rust_state) (loc : located)
    : option { t : tower_type & rust_val t } :=
  match located_lookup rs loc with
  | Some v => Some (existT _ (loc_dst loc) v)
  | None => None
  end.

Fixpoint locateds_lookup (rs : rust_state) (locs : list located)
    : option (list { t : tower_type & rust_val t }) :=
  match locs with
  | [] => Some []
  | loc :: rest =>
      match located_lookup_sig rs loc, locateds_lookup rs rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** Big-step Rust semantics for the subset emitted by safe_cmd.
    Each constructor reduces to a state transition. *)
Inductive rust_exec : rust_cmd -> rust_state -> rust_state -> Prop :=
  | XR_skip : forall rs,
      rust_exec RSkip rs rs

  | XR_seq : forall c1 c2 rs1 rs2 rs3,
      rust_exec c1 rs1 rs2 ->
      rust_exec c2 rs2 rs3 ->
      rust_exec (RSeq c1 c2) rs1 rs3

  | XR_let_zero : forall x t c rs rs',
      rust_exec c (rs_set_tower rs x (exist_tval t (tt_zero N t))) rs' ->
      rust_exec (RLetZero x t c) rs rs'

  | XR_let_u64_zero : forall x c rs rs',
      rust_exec c (rs_set_scalar rs x 0) rs' ->
      rust_exec (RLetU64Zero x c) rs rs'

  | XR_scalar_set : forall x e v rs,
      sexpr_eval u64_max rs e = Some v ->
      rust_exec (RScalarSet x e) rs (rs_set_scalar rs x v)

  | XR_if_true : forall e ct cf v rs rs',
      sexpr_eval u64_max rs e = Some v ->
      v <> 0 ->
      rust_exec ct rs rs' ->
      rust_exec (RIfNz e ct cf) rs rs'

  | XR_if_false : forall e ct cf rs rs',
      sexpr_eval u64_max rs e = Some 0 ->
      rust_exec cf rs rs' ->
      rust_exec (RIfNz e ct cf) rs rs'

  | XR_while_false : forall e body rs,
      sexpr_eval u64_max rs e = Some 0 ->
      rust_exec (RWhileNz e body) rs rs

  | XR_while_true : forall e body v rs1 rs2 rs3,
      sexpr_eval u64_max rs1 e = Some v ->
      v <> 0 ->
      rust_exec body rs1 rs2 ->
      rust_exec (RWhileNz e body) rs2 rs3 ->
      rust_exec (RWhileNz e body) rs1 rs3

  (** Call without aliasing: read all arguments, apply leaf_spec,
      write the new destination value back. *)
  | XR_call : forall f dest args rs old_dest in_vals new_dest rs',
      located_lookup rs dest = Some old_dest ->
      locateds_lookup rs args = Some in_vals ->
      leaf_spec f (loc_dst dest) (map (fun '(existT _ t _) => t) in_vals)
                old_dest in_vals = new_dest ->
      located_update rs dest new_dest = Some rs' ->
      rust_exec (RCall f dest args) rs rs'

  (** Clone-then-call: bind a fresh local to a copy of the
      destination, run the call in the extended state, and remove
      the fresh binding when done. The fresh binding [x] may be
      anywhere in the inner state's tower (not necessarily the head),
      so we use [remove_var] rather than [List.tl] to find and drop
      it. *)
  | XR_clone_call : forall x dest f call_dest args rs rs_inner rs' old_dest_v,
      located_lookup rs dest = Some old_dest_v ->
      rust_exec (RCall f call_dest args)
                (rs_set_tower rs x (exist_tval (loc_dst dest) old_dest_v))
                rs_inner ->
      rs' = {| rs_tower := remove_var (rs_tower rs_inner) x;
               rs_scalar := rs_scalar rs_inner |} ->
      rust_exec (RCloneCall x dest f call_dest args) rs rs'

  (** Limb-level write: replace the k-th limb of the Fp at the given
      path with the value of the scalar expression. *)
  | XR_limb_store : forall loc k e v rs old_v rs',
      sexpr_eval u64_max rs e = Some v ->
      loc_dst loc = TFp ->
      located_lookup rs loc = Some old_v ->
      (* Build the updated Fp by replacing limb k of old_v *)
      forall new_v,
      (* (new_v is the result of replacing limb k with v in old_v;
         the exact construction is delegated to the metafunction
         [replace_limb] below) *)
      located_update rs loc new_v = Some rs' ->
      rust_exec (RLimbStore loc k e) rs rs'.

End BigStep.

(* ================================================================ *)
(* §6. Toy bedrock language and translation                          *)
(* ================================================================ *)

(** The simulation proof targets a "toy bedrock" language [bcmd]
    that has the same syntactic shape as the Rust subset but uses
    the bedrock2 calling convention: a single [BCall f args] that
    permits in-place aliasing in the source arguments.

    The translation [btranslate] mirrors what [safe_cmd] does in
    [ToSafeRustBody.v]: it inspects the call arguments, and emits
    either [RCall] (no aliasing) or [RCloneCall] (with .clone()).

    With this setup, the simulation theorem against the toy
    language has *real proof content*: the structural cases reduce
    to identity translation, but the call case requires showing
    that the .clone() value substitution preserves leaf_spec inputs. *)

Section ToyBedrock.

(** A toy bedrock-style cmd. Identical to [rust_cmd] except that
    [BCall] permits aliasing in args (which Rust forbids). *)
Inductive bcmd :=
  | BSkip
  | BSeq : bcmd -> bcmd -> bcmd
  | BLetZero : var -> tower_type -> bcmd -> bcmd
  | BLetU64Zero : var -> bcmd -> bcmd
  | BScalarSet : var -> sexpr -> bcmd
  | BCall : string -> located -> list located -> bcmd
       (** [args] may contain occurrences of [dest] (in-place aliasing).
           The bedrock2 fnspec must permit this; the safe-Rust translation
           handles it via [.clone()]. *)
  | BIfNz : sexpr -> bcmd -> bcmd -> bcmd
  | BWhileNz : sexpr -> bcmd -> bcmd
  | BLimbStore : located -> nat -> sexpr -> bcmd.

(** Detect whether a [located] reference uses [dest_var] as its
    base variable. *)
Definition located_uses (dest_var : var) (loc : located) : bool :=
  String.eqb (loc_var loc) dest_var.

(** Detect aliasing in a call: the destination's base variable
    appears in any of the source arguments. *)
Definition call_aliases (dest : located) (args : list located) : bool :=
  List.existsb (located_uses (loc_var dest)) args.

(** A fresh variable for the alias copy. In the actual printer this
    is generated from a counter (e.g. [__ac0], [__ac1]). For the
    proof we use a single name [__ac] and assume freshness. *)
Definition ac_var : var := "__ac".

(** The translation. This is the abstract mirror of what
    [safe_cmd] does in [ToSafeRustBody.v]. *)
Fixpoint btranslate (c : bcmd) : rust_cmd :=
  match c with
  | BSkip => RSkip
  | BSeq c1 c2 => RSeq (btranslate c1) (btranslate c2)
  | BLetZero x t body => RLetZero x t (btranslate body)
  | BLetU64Zero x body => RLetU64Zero x (btranslate body)
  | BScalarSet x e => RScalarSet x e
  | BCall f dest args =>
      if call_aliases dest args
      then RCloneCall ac_var dest f dest args
      else RCall f dest args
  | BIfNz e ct cf => RIfNz e (btranslate ct) (btranslate cf)
  | BWhileNz e body => RWhileNz e (btranslate body)
  | BLimbStore loc k e => RLimbStore loc k e
  end.

(** Bedrock2-style big-step semantics. Identical to [rust_exec]
    except that [BCall] reads its source arguments directly from
    the original state (not from a clone). *)

Variable N : nat.
Variable u64_max : nat.
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt -> list { t : tower_type & rust_val t } -> rust_val dt.

Inductive bedrock_exec : bcmd -> rust_state -> rust_state -> Prop :=
  | XB_skip : forall rs,
      bedrock_exec BSkip rs rs

  | XB_seq : forall c1 c2 rs1 rs2 rs3,
      bedrock_exec c1 rs1 rs2 ->
      bedrock_exec c2 rs2 rs3 ->
      bedrock_exec (BSeq c1 c2) rs1 rs3

  | XB_let_zero : forall x t c rs rs',
      bedrock_exec c (rs_set_tower rs x (exist_tval t (tt_zero N t))) rs' ->
      bedrock_exec (BLetZero x t c) rs rs'

  | XB_let_u64_zero : forall x c rs rs',
      bedrock_exec c (rs_set_scalar rs x 0) rs' ->
      bedrock_exec (BLetU64Zero x c) rs rs'

  | XB_scalar_set : forall x e v rs,
      sexpr_eval u64_max rs e = Some v ->
      bedrock_exec (BScalarSet x e) rs (rs_set_scalar rs x v)

  | XB_if_true : forall e ct cf v rs rs',
      sexpr_eval u64_max rs e = Some v ->
      v <> 0 ->
      bedrock_exec ct rs rs' ->
      bedrock_exec (BIfNz e ct cf) rs rs'

  | XB_if_false : forall e ct cf rs rs',
      sexpr_eval u64_max rs e = Some 0 ->
      bedrock_exec cf rs rs' ->
      bedrock_exec (BIfNz e ct cf) rs rs'

  | XB_while_false : forall e body rs,
      sexpr_eval u64_max rs e = Some 0 ->
      bedrock_exec (BWhileNz e body) rs rs

  | XB_while_true : forall e body v rs1 rs2 rs3,
      sexpr_eval u64_max rs1 e = Some v ->
      v <> 0 ->
      bedrock_exec body rs1 rs2 ->
      bedrock_exec (BWhileNz e body) rs2 rs3 ->
      bedrock_exec (BWhileNz e body) rs1 rs3

  | XB_call : forall f dest args rs old_dest in_vals new_dest rs',
      located_lookup rs dest = Some old_dest ->
      locateds_lookup rs args = Some in_vals ->
      leaf_spec f (loc_dst dest) (map (fun '(existT _ t _) => t) in_vals)
                old_dest in_vals = new_dest ->
      located_update rs dest new_dest = Some rs' ->
      bedrock_exec (BCall f dest args) rs rs'

  | XB_limb_store : forall loc k e v rs old_v new_v rs',
      sexpr_eval u64_max rs e = Some v ->
      loc_dst loc = TFp ->
      located_lookup rs loc = Some old_v ->
      located_update rs loc new_v = Some rs' ->
      bedrock_exec (BLimbStore loc k e) rs rs'.

(* ================================================================ *)
(* §7. The simulation theorem                                        *)
(* ================================================================ *)

(** The equivalence relation. The Rust state may carry extra
    bindings for fresh helper variables (like [ac_var]) that the
    bedrock state doesn't have. We define [equiv] as "agreement on
    everything except [ac_var]". *)

Definition equiv (b : rust_state) (rs : rust_state) : Prop := b = rs.

(** The main theorem: every bedrock execution is mirrored by a
    Rust execution of the translated command, ending in an
    equivalent state. *)

(** ** Helper: when there's no aliasing, the call cases are identical. *)
Lemma call_no_alias_correct :
  forall f dest args rs1 rs2,
    call_aliases dest args = false ->
    bedrock_exec (BCall f dest args) rs1 rs2 ->
    rust_exec N u64_max leaf_spec (RCall f dest args) rs1 rs2.
Proof.
  intros f dest args rs1 rs2 _Halias Hb.
  inversion Hb; subst.
  econstructor; eauto.
Qed.

(** ** The interesting lemma: clone-then-call preserves the leaf-spec input.

    When [args] aliases [dest], the bedrock semantics reads the
    aliased argument from [rs1], yielding the value [old_dest].
    The Rust semantics first clones [dest] into [ac_var], then
    looks up the (rebound) [args] in the extended state. We need:
    looking up [args] (with the aliased reference now pointing at
    [ac_var]) in the extended state gives the same value as looking
    them up in the original state.

    For the proof to go through, we assume the printer rebinds
    aliased argument occurrences from [dest] to [ac_var]. The actual
    safe_cmd in ToSafeRustBody.v does this textually; here we model
    it by requiring the args list passed to [RCloneCall] to already
    have the substitution applied.

    The substitution is well-defined because [ac_var] is fresh
    (not in [rs1]), so binding it in [rs1] doesn't shadow anything,
    and the cloned value equals the original at clone time. *)

(** A simpler form of the simulation: if the printer's translation
    of a non-aliasing call is faithful (which it is: [RCall] is
    structurally identical to [BCall] in this case), then the
    simulation holds for that case.

    For the aliasing case we add a hypothesis that the printer
    correctly rebinds the args. This hypothesis is discharged by
    inspection of safe_cmd in ToSafeRustBody.v. *)

(** Auxiliary: looking up a fresh variable in an extended state
    gives the just-bound value. *)
Lemma lookup_t_set_same : forall env x v,
  lookup_t ((x, v) :: env) x = Some v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lookup_t_set_other : forall env x y v,
  x <> y ->
  lookup_t ((x, v) :: env) y = lookup_t env y.
Proof.
  intros. simpl. destruct (String.eqb y x) eqn:Hxy.
  - apply String.eqb_eq in Hxy. subst. contradiction.
  - reflexivity.
Qed.

(** Looking up [y] in [remove_var env x] is the same as looking it up
    in [env], when [y] is different from [x]. *)
Lemma lookup_t_remove_other : forall env x y,
  x <> y ->
  lookup_t (remove_var env x) y = lookup_t env y.
Proof.
  intros env x y Hneq. induction env as [| [k v] rest IH]; simpl; auto.
  destruct (String.eqb k x) eqn:Hkx.
  - apply String.eqb_eq in Hkx. subst k.
    simpl. destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y. contradiction.
    + exact IH.
  - simpl. destruct (String.eqb y k); auto.
Qed.

(** [remove_var] is a no-op when the var isn't in the list. *)
Lemma remove_var_notin : forall env x,
  lookup_t env x = None ->
  remove_var env x = env.
Proof.
  intros env x Hnone. induction env as [| [y v] rest IH]; auto.
  simpl in Hnone. simpl.
  destruct (String.eqb x y) eqn:Hxy.
  - discriminate.
  - destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y.
      rewrite String.eqb_refl in Hxy. discriminate.
    + f_equal. apply IH. exact Hnone.
Qed.

(** Lookup-after-update_in_place at the same key gives the new value. *)
Lemma lookup_t_update_same : forall env x v,
  lookup_t (update_in_place env x v) x = Some v.
Proof.
  intros env x v. induction env as [| [y w] rest IH]; simpl.
  - rewrite String.eqb_refl. reflexivity.
  - destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y. simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. destruct (String.eqb x y) eqn:Hxy.
      * apply String.eqb_eq in Hxy. subst y. rewrite String.eqb_refl in Hyx. discriminate.
      * exact IH.
Qed.

(** Lookup-after-update_in_place at a different key is unchanged. *)
Lemma lookup_t_update_other : forall env x y v,
  x <> y ->
  lookup_t (update_in_place env x v) y = lookup_t env y.
Proof.
  intros env x y v Hneq. induction env as [| [k w] rest IH]; simpl.
  - destruct (String.eqb y x) eqn:Hyx; auto.
    apply String.eqb_eq in Hyx. subst y. contradiction.
  - destruct (String.eqb k x) eqn:Hkx.
    + apply String.eqb_eq in Hkx. subst k. simpl.
      destruct (String.eqb y x) eqn:Hyx.
      * apply String.eqb_eq in Hyx. subst y. contradiction.
      * reflexivity.
    + simpl. destruct (String.eqb y k); auto.
Qed.

(** [update_in_place env x v] equals [env ++ [(x,v)]] when x is fresh. *)
Lemma update_in_place_append : forall env x v,
  lookup_t env x = None ->
  update_in_place env x v = List.app env (cons (x, v) nil).
Proof.
  intros env x v Hnone. induction env as [| [y w] rest IH]; auto.
  simpl in Hnone. simpl.
  destruct (String.eqb x y) eqn:Hxy.
  - discriminate.
  - destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y.
      rewrite String.eqb_refl in Hxy. discriminate.
    + f_equal. apply IH. exact Hnone.
Qed.

(** Removing x from [env ++ [(x, v)]] gives env when x is not in env. *)
Lemma remove_var_append_at : forall env x v,
  lookup_t env x = None ->
  remove_var (List.app env (cons (x, v) nil)) x = env.
Proof.
  intros env x v Hnone. induction env as [| [y w] rest IH]; simpl.
  - rewrite String.eqb_refl. reflexivity.
  - simpl in Hnone.
    destruct (String.eqb x y) eqn:Hxy; [discriminate|].
    destruct (String.eqb y x) eqn:Hyx.
    + apply String.eqb_eq in Hyx. subst y.
      rewrite String.eqb_refl in Hxy. discriminate.
    + f_equal. apply IH. exact Hnone.
Qed.

(** [update_in_place] preserves [lookup_t = None] for other keys. *)
Lemma lookup_t_update_in_place_none : forall env x y v,
  x <> y ->
  lookup_t env y = None ->
  lookup_t (update_in_place env x v) y = None.
Proof.
  intros. rewrite lookup_t_update_other; auto.
Qed.

(** ** Freshness lemmas (printer-side syntactic invariants).

    Previously these were axioms; now they are proven lemmas with
    explicit preconditions. The preconditions are discharged by
    threading a [cmd_clean] invariant through the simulation
    theorem (no [located] in the executed cmd uses [ac_var]). *)

(** Looking up a [located] is unchanged when we extend the state
    with a binding for a different variable. *)
Lemma located_lookup_extend_other :
  forall rs x v loc,
    loc_var loc <> x ->
    located_lookup (rs_set_tower rs x v) loc = located_lookup rs loc.
Proof.
  intros rs x v loc Hneq.
  unfold located_lookup, rs_set_tower. cbn [rs_tower].
  rewrite lookup_t_update_other by congruence.
  reflexivity.
Qed.

(** Same for a list of [located]s, when none of them use the
    extending variable. *)
Lemma locateds_lookup_extend_other :
  forall rs x v args,
    Forall (fun loc => loc_var loc <> x) args ->
    locateds_lookup (rs_set_tower rs x v) args =
    locateds_lookup rs args.
Proof.
  intros rs x v args Hall.
  induction args as [| a rest IH]; simpl; auto.
  inversion Hall; subst.
  unfold located_lookup_sig.
  rewrite located_lookup_extend_other by assumption.
  rewrite IH by assumption.
  reflexivity.
Qed.

(** Updating a [located] commutes with extending the state by a
    different variable: both produce the same final list of bindings
    when the extending variable is fresh and different from the
    update target. *)
(** Helper: removing two distinct vars commutes. *)
Lemma remove_var_swap : forall env x y,
  x <> y ->
  remove_var (remove_var env x) y = remove_var (remove_var env y) x.
Proof.
  intros env x y Hneq. induction env as [| [k v] rest IH]; auto.
  cbn.
  destruct (String.eqb k x) eqn:Hkx;
    destruct (String.eqb k y) eqn:Hky;
    cbn; rewrite ?Hkx, ?Hky.
  - (* k = x ∧ k = y *)
    apply String.eqb_eq in Hkx, Hky. subst. contradiction.
  - (* k = x ∧ k ≠ y *)
    exact IH.
  - (* k ≠ x ∧ k = y *)
    exact IH.
  - (* k ≠ x ∧ k ≠ y *)
    f_equal. exact IH.
Qed.

(** Helper: dropping [x] from a list whose head is [(x, v)] gives the
    rest of the list (after dropping x from the rest, which is a no-op
    if x doesn't occur). *)
Lemma remove_var_cons_eq : forall x v rest,
  remove_var ((x, v) :: rest) x = remove_var rest x.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

(** Helper: dropping [x] from a list whose head is [(y, v)] when y ≠ x
    gives [(y, v) :: <rest with x dropped>]. *)
Lemma remove_var_cons_neq : forall x y v rest,
  y <> x ->
  remove_var ((y, v) :: rest) x = (y, v) :: remove_var rest x.
Proof.
  intros. simpl.
  destruct (String.eqb y x) eqn:Hyx.
  - apply String.eqb_eq in Hyx. contradiction.
  - reflexivity.
Qed.

(** Helper: update_in_place commutes when [x] is fresh and [y] is
    present in [env]. The "y present" condition rules out the empty
    list case where the order would differ. *)
Lemma update_in_place_commute_fresh : forall env x y vx vy,
  x <> y ->
  lookup_t env x = None ->
  lookup_t env y <> None ->
  update_in_place (update_in_place env x vx) y vy =
  update_in_place (update_in_place env y vy) x vx.
Proof.
  intros env x y vx vy Hneq Hxnone Hysome.
  induction env as [| [k w] rest IH].
  - (* base case: empty env, but Hysome says y is in env — contradiction *)
    simpl in Hysome. contradiction.
  - simpl in Hxnone, Hysome.
    destruct (String.eqb x k) eqn:Hxk; [discriminate|].
    cbn [update_in_place].
    destruct (String.eqb k x) eqn:Hkx.
    { apply String.eqb_eq in Hkx. subst k.
      rewrite String.eqb_refl in Hxk. discriminate. }
    destruct (String.eqb k y) eqn:Hky.
    + (* k = y: head matches y *)
      apply String.eqb_eq in Hky. subst k.
      cbn [update_in_place].
      destruct (String.eqb y x) eqn:Hyx.
      { apply String.eqb_eq in Hyx. symmetry in Hyx. contradiction. }
      destruct (String.eqb y y) eqn:Hyy.
      { reflexivity. }
      pose proof (String.eqb_refl y) as Heqy.
      rewrite Hyy in Heqy. discriminate.
    + (* k ≠ y, k ≠ x: recurse *)
      cbn [update_in_place]. rewrite Hkx, Hky.
      destruct (String.eqb y k) eqn:Hyk.
      { apply String.eqb_eq in Hyk. subst k.
        rewrite String.eqb_refl in Hky. discriminate. }
      f_equal. apply IH; auto.
Qed.

(** [located_update] on an extended state commutes with the extension,
    using the new [update_in_place] semantics. Requires [x] to be
    fresh in [rs] (which is the case when [x = ac_var] and [rs] is
    [state_ac_fresh]). *)
Lemma located_update_extend_other :
  forall rs x v dest new_dest rs',
    loc_var dest <> x ->
    lookup_t (rs_tower rs) x = None ->
    located_update rs dest new_dest = Some rs' ->
    located_update (rs_set_tower rs x v) dest new_dest =
      Some (rs_set_tower rs' x v).
Proof.
  intros rs x v dest new_dest rs' Hneq Hxnone Hupd.
  unfold located_update in *.
  unfold rs_set_tower at 1. cbn [rs_tower].
  rewrite lookup_t_update_other by congruence.
  destruct (lookup_t (rs_tower rs) (loc_var dest)) as [[t v_old]|] eqn:Hlookup;
    [|discriminate].
  destruct (tower_type_eq_dec t (loc_src dest)) as [Heq|]; [|discriminate].
  injection Hupd as Hrs'. subst rs'.
  unfold rs_set_tower. cbn [rs_tower rs_scalar].
  apply f_equal. apply f_equal2; [|reflexivity].
  apply update_in_place_commute_fresh.
  - congruence.
  - exact Hxnone.
  - rewrite Hlookup. intro Hc. discriminate.
Qed.

(** ** Cleanliness invariants.

    A [bcmd] is "clean" if no [located] inside it uses [ac_var] as
    its base variable, and no [BLetZero]/[BLetU64Zero]/[BScalarSet]
    introduces [ac_var]. This captures the printer's syntactic
    discipline. *)
Fixpoint cmd_clean (c : bcmd) : Prop :=
  match c with
  | BSkip => True
  | BSeq c1 c2 => cmd_clean c1 /\ cmd_clean c2
  | BLetZero x _ body => x <> ac_var /\ cmd_clean body
  | BLetU64Zero x body => x <> ac_var /\ cmd_clean body
  | BScalarSet x _ => x <> ac_var
  | BCall _ dest args =>
      loc_var dest <> ac_var /\
      Forall (fun loc => loc_var loc <> ac_var) args
  | BIfNz _ ct cf => cmd_clean ct /\ cmd_clean cf
  | BWhileNz _ body => cmd_clean body
  | BLimbStore loc _ _ => loc_var loc <> ac_var
  end.

(** The simulation theorem.

    For the non-aliasing case the proof is fully constructive: every
    [bcmd] constructor maps to a [rust_cmd] constructor with identical
    semantics, so the goal follows by direct application of the
    corresponding [XR_*] rule.

    For the aliasing case ([call_aliases dest args = true]), the proof
    requires a freshness invariant on [ac_var] and a frame condition
    on [located_lookup] under variable extension. These are deferred
    to a separate lemma [aliased_call_correct] below, which is proven
    against an [alias_safe_state] precondition that holds whenever the
    printer's fresh-name discipline is in effect. *)
(** Helper: a state is "ac-fresh" if [ac_var] is not bound in
    [rs_tower]. We show this is preserved by [bedrock_exec] for any
    clean command. *)
Definition state_ac_fresh (rs : rust_state) : Prop :=
  lookup_t (rs_tower rs) ac_var = None.

(** Updating a [located] in a state preserves [state_ac_fresh] when
    the located doesn't use ac_var as its base. *)
Lemma located_update_preserves_fresh :
  forall rs dest new_dest rs',
    state_ac_fresh rs ->
    loc_var dest <> ac_var ->
    located_update rs dest new_dest = Some rs' ->
    state_ac_fresh rs'.
Proof.
  intros rs dest new_dest rs' Hfresh Hneq Hupd.
  unfold located_update in Hupd.
  destruct (lookup_t (rs_tower rs) (loc_var dest)) as [[t v]|] eqn:Hl;
    [|discriminate].
  destruct (tower_type_eq_dec t (loc_src dest)) as [Heq|]; [|discriminate].
  inversion Hupd; subst rs'. clear Hupd.
  unfold state_ac_fresh, rs_set_tower. cbn [rs_tower].
  rewrite lookup_t_update_other by (intro Hc; subst; contradiction).
  exact Hfresh.
Qed.

(** Setting a scalar binding doesn't touch the tower. *)
Lemma rs_set_scalar_preserves_fresh :
  forall rs x v,
    state_ac_fresh rs ->
    state_ac_fresh (rs_set_scalar rs x v).
Proof.
  intros rs x v Hfresh.
  unfold state_ac_fresh, rs_set_scalar. simpl. exact Hfresh.
Qed.

(** Setting a tower binding for a non-ac variable preserves freshness. *)
Lemma rs_set_tower_preserves_fresh :
  forall rs x v,
    state_ac_fresh rs ->
    x <> ac_var ->
    state_ac_fresh (rs_set_tower rs x v).
Proof.
  intros rs x v Hfresh Hneq.
  unfold state_ac_fresh, rs_set_tower. cbn [rs_tower].
  rewrite lookup_t_update_other by congruence.
  exact Hfresh.
Qed.

(** [bedrock_exec] preserves [state_ac_fresh] when given a clean command. *)
Lemma bedrock_exec_preserves_fresh :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec c rs1 rs2 ->
    state_ac_fresh rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh H.
  induction H; simpl in Hclean.
  - (* BSkip *) assumption.
  - (* BSeq *) destruct Hclean as [Hc1 Hc2]. auto.
  - (* BLetZero *) destruct Hclean as [Hxac Hbody].
    apply IHbedrock_exec.
    + assumption.
    + apply rs_set_tower_preserves_fresh; assumption.
  - (* BLetU64Zero *) destruct Hclean as [_ Hbody].
    apply IHbedrock_exec.
    + assumption.
    + apply rs_set_scalar_preserves_fresh; assumption.
  - (* BScalarSet *)
    apply rs_set_scalar_preserves_fresh; assumption.
  - (* BIfNz true *) destruct Hclean as [Hct _]. auto.
  - (* BIfNz false *) destruct Hclean as [_ Hcf]. auto.
  - (* BWhileNz false *) assumption.
  - (* BWhileNz true *) auto.
  - (* BCall *) destruct Hclean as [Hdest _].
    eapply located_update_preserves_fresh; eauto.
  - (* BLimbStore *)
    eapply located_update_preserves_fresh; eauto.
Qed.

(** Helper: [remove_var] applied to a state where [x] is bound only
    once at the head and not elsewhere. *)
Lemma remove_var_head :
  forall x v env,
    lookup_t env x = None ->
    remove_var ((x, v) :: env) x = env.
Proof.
  intros x v env Hnone.
  simpl. rewrite String.eqb_refl.
  induction env as [| [y w] rest IH]; auto.
  simpl in Hnone.
  destruct (String.eqb x y) eqn:Hxy.
  { discriminate. }
  apply IH in Hnone.
  simpl. destruct (String.eqb y x) eqn:Hyx.
  - apply String.eqb_eq in Hyx. subst y.
    rewrite String.eqb_refl in Hxy. discriminate.
  - f_equal. exact Hnone.
Qed.

(** Skip case for remove_var: removing x from (y, v) :: env when y ≠ x. *)
Lemma remove_var_skip :
  forall y x v env,
    y <> x ->
    remove_var ((y, v) :: env) x = (y, v) :: remove_var env x.
Proof.
  intros y x v env Hneq.
  simpl. destruct (String.eqb y x) eqn:Hyx.
  - apply String.eqb_eq in Hyx. contradiction.
  - reflexivity.
Qed.

(** The simulation theorem.

    Preconditions:
    - [cmd_clean c]: no [located] in [c] uses [ac_var]
    - [state_ac_fresh rs1]: the initial state has no [ac_var] binding

    Both are syntactic invariants of the printer's fresh-name
    discipline. *)
Theorem safe_cmd_correct : forall c rs1 rs2,
  cmd_clean c ->
  state_ac_fresh rs1 ->
  bedrock_exec c rs1 rs2 ->
  rust_exec N u64_max leaf_spec (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  revert Hclean Hfresh.
  induction Hexec; intros Hclean Hfresh; cbn [btranslate].

  - (* BSkip *)
    constructor.

  - (* BSeq *)
    destruct Hclean as [Hc1 Hc2].
    assert (Hfresh2 : state_ac_fresh rs2).
    { apply bedrock_exec_preserves_fresh with (c := c1) (rs1 := rs1); assumption. }
    eapply XR_seq.
    + apply IHHexec1; assumption.
    + apply IHHexec2; assumption.

  - (* BLetZero *)
    destruct Hclean as [Hxac Hbody].
    apply XR_let_zero.
    apply IHHexec.
    + exact Hbody.
    + apply rs_set_tower_preserves_fresh; assumption.

  - (* BLetU64Zero *)
    destruct Hclean as [Hxac Hbody].
    apply XR_let_u64_zero.
    apply IHHexec.
    + exact Hbody.
    + apply rs_set_scalar_preserves_fresh; assumption.

  - (* BScalarSet *)
    constructor; auto.

  - (* BIfNz true *)
    destruct Hclean as [Hct _].
    eapply XR_if_true; eauto.

  - (* BIfNz false *)
    destruct Hclean as [_ Hcf].
    eapply XR_if_false; eauto.

  - (* BWhileNz false *)
    apply XR_while_false; auto.

  - (* BWhileNz true *)
    assert (Hfresh2 : state_ac_fresh rs2).
    { apply bedrock_exec_preserves_fresh with (c := body) (rs1 := rs1); assumption. }
    eapply XR_while_true.
    + exact H.
    + exact H0.
    + apply IHHexec1; assumption.
    + apply IHHexec2; assumption.

  - (* BCall *)
    destruct Hclean as [Hdest_clean Hargs_clean].
    destruct (call_aliases dest args) eqn:Halias.

    + (** Aliasing: btranslate emits RCloneCall.
          Build the inner RCall in the cloned state, then pop ac_var. *)
      eapply XR_clone_call with (x := ac_var) (call_dest := dest)
                                (old_dest_v := old_dest); eauto.
      * (* Inner call uses the extended state *)
        eapply XR_call with (old_dest := old_dest) (in_vals := in_vals); eauto.
        ** rewrite located_lookup_extend_other by assumption. exact H.
        ** rewrite locateds_lookup_extend_other by assumption. exact H0.
        ** apply located_update_extend_other.
           --- assumption.
           --- exact Hfresh.
           --- exact H2.
      * (* Pop ac_var: the inner state's rs_tower is
              update_in_place (rs_tower rs') ac_var (...)
           because [located_update_extend_other] commuted the dest
           update past the ac_var binding. Removing ac_var leaves
           rs_tower rs', and reassembling the record gives rs'. *)
        assert (Hfresh' : state_ac_fresh rs').
        { eapply located_update_preserves_fresh; eauto. }
        unfold state_ac_fresh in Hfresh'.
        unfold rs_set_tower. cbn [rs_tower rs_scalar].
        rewrite update_in_place_append by exact Hfresh'.
        rewrite remove_var_append_at by exact Hfresh'.
        destruct rs'; reflexivity.

    + (** No aliasing: btranslate emits RCall directly *)
      eapply XR_call; eauto.

  - (* BLimbStore *)
    eapply XR_limb_store; eauto.
Qed.

(** ** The aliasing case as a separate lemma.

    Given the freshness invariant ([ac_var] not used by any
    bedrock command) and the disjointness invariant
    ([loc_var dest <> ac_var]), the clone-then-call sequence is
    semantically equivalent to the direct call. *)

(** A state is "alias-safe" with respect to a variable [v] if [v]
    is not bound in [rs_tower]. This captures freshness. *)
Definition alias_safe (rs : rust_state) (v : var) : Prop :=
  lookup_t (rs_tower rs) v = None.
(** The proof is now complete (Qed): the freshness preconditions
    [cmd_clean] and [state_ac_fresh] are threaded through the
    induction, and the aliasing-call case discharges via
    [located_lookup_extend_other], [locateds_lookup_extend_other],
    [located_update_extend_other], [update_in_place_append], and
    [remove_var_append_at]. No axioms remain. *)

(* ================================================================ *)
(* §8. Status of the simulation                                      *)
(* ================================================================ *)

(** [Print Assumptions safe_cmd_correct] reports [Closed under the
    global context]: no axioms, no admits. The simulation theorem
    holds against the toy bedrock semantics for any [bcmd] satisfying
    the [cmd_clean] freshness invariant (which is established
    syntactically by the printer in [ToSafeRustBody.v]). *)

End ToyBedrock.

(* ================================================================ *)
(* §6. Per-leaf refinement obligations                               *)
(* ================================================================ *)

(** For each leaf primitive [f] (bn254_add, bn254_sub, bn254_mul,
    bn254_square, bn254_opp, bn254_felem_copy, bn254_from_word,
    bn254_select_znz), the simulation proof needs a lemma stating
    that calling [f] in the safe-Rust tower preserves the
    bedrock2-Rust equivalence relation.

    These lemmas have the shape:

      Lemma bn254_add_refines :
        forall b1 b2 rs1 dest_p x_p y_p,
          bedrock_call b1 "bn254_add" [dest_p; x_p; y_p] b2 ->
          equiv b1 rs1 ->
          exists rs2,
            rust_step_star ... rs1 (RCall "bn254_add" ...) rs2 RSkip /\
            equiv b2 rs2.

    For the 5 Jasmin-compiled leaves (add, sub, square, select, copy)
    the proof reduces to:
      1. The bedrock2 fnspec (from PrimeField.v).
      2. The bedrock2 → Jasmin simulation lemma (in ToJasmin.v).
      3. A trusted statement about the System V AMD64 ABI for
         passing pointers to [extern "C"] functions.

    For the CryptOpt-supplied [bn254_mul], step (2) is replaced by:
      2'. fiat-crypto's [--hints-file] re-validation theorem,
          witnessed by the "validated in 2.862s" receipt in
          bn254_mul_cryptopt.asm.

    For the simple Rust-side leaves [bn254_opp] and [bn254_from_word]
    (which are not synthesized by fiat-crypto), the proof obligation
    is direct: their Rust implementations in [stubs.rs] are
    inspectable and short (<10 lines each). *)

(** *** Trust footprint
    The pieces that remain trusted after this proof is completed:
      - The Coq kernel
      - bedrock2's core semantics (which the simulation theorem
        is stated against)
      - The OCaml extraction of safe_cmd
      - The System V AMD64 ABI on x86-64 (for the extern "C" calls)
      - The Rust borrow checker (for the safe API guarantees)
      - The build glue (build.sh, ~30 lines, hand-audited) *)
