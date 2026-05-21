(** * ToSafeRustBody: bedrock2 tower → fully safe Rust.
 *
 * Translates bedrock2 cmd trees to safe Rust using #[repr(C)] structs.
 * Zero [unsafe] in the generated tower code — only leaf Fp wrappers
 * use [unsafe] for the extern "C" boundary to Jasmin assembly.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
(** [=?] resolves to [Z.eqb]. For string comparison, use [seq]. *)
Local Notation seq := String.eqb.

Definition LF : string :=
  String (Ascii.Ascii false true false true false false false false) "".

Definition z_str (z : Z) : string :=
  DecimalString.NilZero.string_of_int (Z.to_int z).

Fixpoint join (sep : string) (xs : list string) : string :=
  match xs with
  | nil => ""
  | x :: nil => x
  | x :: rest => x ++ sep ++ join sep rest
  end.

(* ================================================================ *)
(* Tower geometry: field sizes and offset → path resolution          *)
(* ================================================================ *)

(** Tower shape: ordered list of [(name, base_name, arity)] entries
    describing each non-base level, from closest-to-base to top.  Base
    type [Fp] is implicit and not listed.  For BLS12-style towers
    (BN254/BN256/BN446/BLS12-381/BLS12-377):
      [("Fp2","Fp",2); ("Fp6","Fp2",3); ("Fp12","Fp6",2)]
    For BLS24-509:
      [("Fp2","Fp",2); ("Fp4","Fp2",2); ("Fp8","Fp4",2); ("Fp24","Fp8",3)]. *)
Record tower_shape : Type := mk_tower {
  ts_levels : list (string * string * Z)
}.

Definition bls12_tower : tower_shape :=
  mk_tower [("Fp2","Fp",2); ("Fp6","Fp2",3); ("Fp12","Fp6",2)].

Definition bls24_509_tower : tower_shape :=
  mk_tower [("Fp2","Fp",2); ("Fp4","Fp2",2);
            ("Fp8","Fp4",2); ("Fp24","Fp8",3)].

Definition bw6_761_tower : tower_shape :=
  mk_tower [("Fp3","Fp",3); ("Fp6","Fp3",2)].

(** All sizes in bytes, parameterized by Fp limb count [n]. *)
Definition fp_sz  (n : Z) := n * 8.
Definition fp2_sz (n : Z) := 2 * n * 8.
Definition fp6_sz (n : Z) := 6 * n * 8.
Definition fp12_sz (n : Z) := 12 * n * 8.

(** Size of a named tower level in bytes.  Walks the shape from base
    upward (each level's size is its arity times its base's size).
    Base [Fp] is [fp_sz n]; [u64] is 8. *)
Fixpoint ts_size_aux (lvls : list (string * string * Z))
    (n : Z) (t : string) (acc : list (string * Z)) : option Z :=
  if seq t "Fp" then Some (fp_sz n)
  else if seq t "u64" then Some 8
  else
    match lvls with
    | nil =>
      match List.find (fun '(k,_) => seq k t) acc with
      | Some (_, sz) => Some sz | None => None
      end
    | (name, base, arity) :: rest =>
      (* Compute size of [base] first via acc lookup or [Fp]. *)
      let base_sz :=
        if seq base "Fp" then fp_sz n
        else match List.find (fun '(k,_) => seq k base) acc with
             | Some (_, sz) => sz | None => 0 end in
      let this_sz := arity * base_sz in
      let acc' := (name, this_sz) :: acc in
      if seq t name then Some this_sz
      else ts_size_aux rest n t acc'
    end.

Definition ts_size (ts : tower_shape) (n : Z) (t : string) : Z :=
  match ts_size_aux (ts_levels ts) n t [] with
  | Some sz => sz | None => fp_sz n
  end.

(** Map a stackalloc byte count to a type name, using the tower shape.
    Falls back to "Fp" for unknown sizes. *)
Fixpoint ts_type_of_bytes_aux (lvls : list (string * string * Z))
    (n : Z) (b : Z) (acc : list (string * Z)) : string :=
  match lvls with
  | nil => ""
  | (name, base, arity) :: rest =>
    let base_sz :=
      if seq base "Fp" then fp_sz n
      else match List.find (fun '(k,_) => seq k base) acc with
           | Some (_, sz) => sz | None => 0 end in
    let this_sz := arity * base_sz in
    if b =? this_sz then name
    else ts_type_of_bytes_aux rest n b ((name, this_sz) :: acc)
  end.

Definition ts_type_of_bytes (ts : tower_shape) (n : Z) (b : Z) : string :=
  if b =? fp_sz n then "Fp"
  else if b =? 8 then "u64"
  else
    let r := ts_type_of_bytes_aux (ts_levels ts) n b [] in
    if seq r "" then "Fp" else r.

(** Map a tower-level name to its [(base, arity)] descriptor.
    [Fp] and [u64] return [None]. *)
Definition ts_lookup (ts : tower_shape) (t : string)
    : option (string * Z) :=
  match List.find (fun '(n,_,_) => seq n t) (ts_levels ts) with
  | Some (_, base, arity) => Some (base, arity)
  | None => None
  end.

(** Tower depth from base [Fp]: 0 for [Fp]/[u64], else 1 + depth(base). *)
Fixpoint ts_rank_aux (lvls : list (string * string * Z))
    (t : string) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f =>
    if seq t "Fp" then 1
    else if seq t "u64" then 0
    else
      match List.find (fun '(n,_,_) => seq n t) lvls with
      | Some (_, base, _) => 1 + ts_rank_aux lvls base f
      | None => 1
      end
  end.

Definition ts_rank (ts : tower_shape) (t : string) : Z :=
  ts_rank_aux (ts_levels ts) t 8%nat.

(** Resolve a byte offset within a parent type to a field path.  Walks
    the tower from [parent] downward, dividing the offset by the current
    level's stride and recursing on the remainder. *)
Fixpoint ts_field_path_aux (ts : tower_shape) (n : Z)
    (parent : string) (off : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S f =>
    if off =? 0 then ""
    else
      match ts_lookup ts parent with
      | None => ""
      | Some (base, _) =>
        let stride := ts_size ts n base in
        if stride =? 0 then ""
        else
          let i := off / stride in
          let r := off mod stride in
          ".c" ++ z_str i ++ ts_field_path_aux ts n base r f
      end
  end.

Definition ts_field_path (ts : tower_shape) (n : Z)
    (parent : string) (off : Z) : string :=
  ts_field_path_aux ts n parent off 8%nat.

(** When a variable of type [vt] is passed to a callee expecting [ct],
    add .c0 suffixes to drill down if [vt] is strictly larger. *)
Fixpoint ts_drill_aux (ts : tower_shape)
    (vt ct : string) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S f =>
    if seq vt ct then ""
    else
      match ts_lookup ts vt with
      | None => ""
      | Some (base, _) => ".c0" ++ ts_drill_aux ts base ct f
      end
  end.

Definition ts_drill (ts : tower_shape) (vt ct : string) : string :=
  if ts_rank ts vt <=? ts_rank ts ct then ""
  else ts_drill_aux ts vt ct 8%nat.

(** Descend [depth] levels in the tower type hierarchy (strip one base
    name at a time). *)
Fixpoint ts_descend (ts : tower_shape) (t : string) (depth : nat) : string :=
  match depth with
  | O => t
  | S d =>
    match ts_lookup ts t with
    | Some (base, _) => ts_descend ts base d
    | None => t
    end
  end.

(* === Backwards-compat: BLS12-style tower defaults === *)

Definition type_of_bytes (n : Z) (b : Z) : string :=
  ts_type_of_bytes bls12_tower n b.

Definition field_path (n : Z) (parent : string) (off : Z) : string :=
  ts_field_path bls12_tower n parent off.

Definition type_rank (t : string) : Z := ts_rank bls12_tower t.

Definition drill (vt ct : string) : string := ts_drill bls12_tower vt ct.

Definition descend (t : string) (depth : nat) : string :=
  ts_descend bls12_tower t depth.

(** Count '.' in a field path to determine depth. *)
Definition dot_char : Ascii.ascii := Ascii.Ascii false true true true false true false false.

Definition path_depth (p : string) : nat :=
  List.length (List.filter (Ascii.eqb dot_char) (list_ascii_of_string p)).

(* ================================================================ *)
(* Variable context                                                  *)
(* ================================================================ *)

Definition ctx := list (string * string).

Definition ctx_get (c : ctx) (x : string) : string :=
  match List.find (fun '(k,_) => seq k x) c with
  | Some (_,t) => t | None => "Fp" end.

(* ================================================================ *)
(* Expression resolution                                             *)
(* ================================================================ *)

Definition esc (x : string) : string :=
  if seq x "in" then "in_" else if seq x "fn" then "fn_"
  else if seq x "type" then "type_" else if seq x "loop" then "loop_"
  else if seq x "self" then "self_" else if seq x "use" then "use_"
  else if seq x "mod" then "mod_" else x.

(** Resolve expr to (var_name, byte_offset). Returns (name, -1) for literals. *)
Fixpoint expr_var_off (e : expr.expr) : string * Z :=
  match e with
  | expr.var x => (esc x, 0)
  | expr.literal z => (z_str z ++ "u64", -1)
  | expr.op bopname.add e1 (expr.literal k) =>
      let '(v, o) := expr_var_off e1 in (v, o + k)
  | expr.op bopname.add (expr.literal k) e2 =>
      let '(v, o) := expr_var_off e2 in (v, o + k)
  | _ => ("/*expr*/", 0)
  end.

(** Resolve an expr in context: produce "var.field_path" string and
    resolved type, using the given tower shape. *)
Definition resolve_ts (ts : tower_shape) (n : Z) (c : ctx) (e : expr.expr)
    : string * string :=
  let '(v, off) := expr_var_off e in
  if off =? -1 then (v, "literal")
  else
    let vt := ctx_get c v in
    if off =? 0 then (v, vt)
    else (v ++ ts_field_path ts n vt off,
          ts_descend ts vt (path_depth (ts_field_path ts n vt off))).

Definition resolve (n : Z) (c : ctx) (e : expr.expr) : string * string :=
  resolve_ts bls12_tower n c e.

(* ================================================================ *)
(* Per-function parameter type table                                 *)
(* ================================================================ *)

Definition param_table : list (string * list string) := [
  ("bn254_add", ["Fp";"Fp";"Fp"]); ("bn254_sub", ["Fp";"Fp";"Fp"]);
  ("bn254_mul", ["Fp";"Fp";"Fp"]); ("bn254_square", ["Fp";"Fp"]);
  ("bn254_opp", ["Fp";"Fp"]); ("bn254_felem_copy", ["Fp";"Fp"]);
  ("bn254_from_word", ["Fp";"Fp"]); ("bn254_select_znz", ["Fp";"Fp";"Fp";"Fp"]);
  ("bn254_Fp2_felem_copy", ["Fp2";"Fp2"]); ("bn254_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_sub", ["Fp2";"Fp2";"Fp2"]); ("bn254_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_square", ["Fp2";"Fp2"]); ("bn254_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bn254_Fp2_conjugate", ["Fp2";"Fp2"]); ("bn254_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  ("bn254_Fp2_opp", ["Fp2";"Fp2"]); ("bn254_Fp2_inv", ["Fp2";"Fp2"]);
  ("bn254_Fp6_felem_copy", ["Fp6";"Fp6"]); ("bn254_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub", ["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_opp", ["Fp6";"Fp6"]);
  ("bn254_Fp6_mul", ["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_square", ["Fp6";"Fp6"]);
  ("bn254_Fp6_inv", ["Fp6";"Fp6"]); ("bn254_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bn254_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bn254_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn254_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn254_Fp12_felem_copy", ["Fp12";"Fp12"]); ("bn254_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_add_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_sub_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_opp", ["Fp12";"Fp12"]);
  ("bn254_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_mul_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_square", ["Fp12";"Fp12"]);
  ("bn254_Fp12_inv", ["Fp12";"Fp12"]); ("bn254_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bn254_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bn254_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp12_frobenius_p3", ["Fp12";"Fp12"]);
  ("bn254_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_gamma1_p2", ["Fp2"]); ("bn254_load_gamma2_p2", ["Fp2"]);
  ("bn254_load_w_frob_p2_c1", ["Fp2"]); ("bn254_load_gamma1", ["Fp2"]);
  ("bn254_load_gamma2", ["Fp2"]); ("bn254_load_w_frob_c1", ["Fp2"]);
  ("bn254_Fp12_pow_u", ["Fp12";"Fp12"]); ("bn254_final_exp_hard_dsd", ["Fp12";"Fp12"]);
  ("bn254_final_exp_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_miller_loop_optimal", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd_optimal", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_inv", ["Fp";"Fp"]);
  ("bn254_Fp2_inv", ["Fp2";"Fp2"]);
  ("bn254_make_line_corrected", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_q1_y_const", ["Fp2"]);

  (* === BLS12-381 entries (mirror of bn254 entries plus BLS12-specific funcs) === *)
  ("bls12_add", ["Fp";"Fp";"Fp"]); ("bls12_sub", ["Fp";"Fp";"Fp"]);
  ("bls12_mul", ["Fp";"Fp";"Fp"]); ("bls12_square", ["Fp";"Fp"]);
  ("bls12_opp", ["Fp";"Fp"]); ("bls12_felem_copy", ["Fp";"Fp"]);
  ("bls12_from_word", ["Fp";"Fp"]); ("bls12_select_znz", ["Fp";"Fp";"Fp";"Fp"]);
  ("bls12_Fp2_felem_copy", ["Fp2";"Fp2"]); ("bls12_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bls12_Fp2_sub", ["Fp2";"Fp2";"Fp2"]); ("bls12_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bls12_Fp2_square", ["Fp2";"Fp2"]); ("bls12_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bls12_Fp2_conjugate", ["Fp2";"Fp2"]); ("bls12_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  ("bls12_Fp2_opp", ["Fp2";"Fp2"]); ("bls12_Fp2_inv", ["Fp2";"Fp2"]);
  ("bls12_Fp6_felem_copy", ["Fp6";"Fp6"]); ("bls12_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bls12_Fp6_sub", ["Fp6";"Fp6";"Fp6"]); ("bls12_Fp6_opp", ["Fp6";"Fp6"]);
  ("bls12_Fp6_mul", ["Fp6";"Fp6";"Fp6"]); ("bls12_Fp6_square", ["Fp6";"Fp6"]);
  ("bls12_Fp6_inv", ["Fp6";"Fp6"]); ("bls12_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bls12_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]); ("bls12_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bls12_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bls12_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bls12_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bls12_Fp12_felem_copy", ["Fp12";"Fp12"]); ("bls12_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_add_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_sub_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_opp", ["Fp12";"Fp12"]);
  ("bls12_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_mul_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls12_Fp12_square", ["Fp12";"Fp12"]);
  ("bls12_Fp12_inv", ["Fp12";"Fp12"]); ("bls12_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bls12_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bls12_Fp12_mul_by_024", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls12_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls12_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls12_Fp12_frobenius_p3", ["Fp12";"Fp12"]);
  ("bls12_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bls12_load_gamma1_p2", ["Fp2"]); ("bls12_load_gamma2_p2", ["Fp2"]);
  ("bls12_load_w_frob_p2_c1", ["Fp2"]); ("bls12_load_gamma1", ["Fp2"]);
  ("bls12_load_gamma2", ["Fp2"]); ("bls12_load_w_frob_c1", ["Fp2"]);
  ("bls12_load_w_frob_p3_c1", ["Fp2"]);
  ("bls12_Fp12_pow_x", ["Fp12";"Fp12"]);
  ("bls12_final_exp_hard_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls12_final_exp", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls12_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bls12_miller_loop_proj", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bls12_pairing", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);

  (* === BLS12-377 entries (mirror of bls12_*, prefix `bls377_*`) === *)
  ("bls377_add", ["Fp";"Fp";"Fp"]); ("bls377_sub", ["Fp";"Fp";"Fp"]);
  ("bls377_mul", ["Fp";"Fp";"Fp"]); ("bls377_square", ["Fp";"Fp"]);
  ("bls377_opp", ["Fp";"Fp"]); ("bls377_felem_copy", ["Fp";"Fp"]);
  ("bls377_from_word", ["Fp";"Fp"]); ("bls377_select_znz", ["Fp";"Fp";"Fp";"Fp"]);
  ("bls377_inv", ["Fp";"Fp"]);
  ("bls377_Fp2_felem_copy", ["Fp2";"Fp2"]); ("bls377_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bls377_Fp2_sub", ["Fp2";"Fp2";"Fp2"]); ("bls377_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bls377_Fp2_square", ["Fp2";"Fp2"]); ("bls377_Fp2_sqr", ["Fp2";"Fp2"]);
  ("bls377_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bls377_Fp2_conjugate", ["Fp2";"Fp2"]); ("bls377_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  ("bls377_Fp2_opp", ["Fp2";"Fp2"]); ("bls377_Fp2_inv", ["Fp2";"Fp2"]);
  ("bls377_Fp6_felem_copy", ["Fp6";"Fp6"]); ("bls377_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bls377_Fp6_sub", ["Fp6";"Fp6";"Fp6"]); ("bls377_Fp6_opp", ["Fp6";"Fp6"]);
  ("bls377_Fp6_mul", ["Fp6";"Fp6";"Fp6"]); ("bls377_Fp6_square", ["Fp6";"Fp6"]);
  ("bls377_Fp6_inv", ["Fp6";"Fp6"]); ("bls377_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bls377_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]); ("bls377_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bls377_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bls377_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bls377_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bls377_Fp12_felem_copy", ["Fp12";"Fp12"]); ("bls377_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_add_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_sub_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_opp", ["Fp12";"Fp12"]);
  ("bls377_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_mul_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bls377_Fp12_square", ["Fp12";"Fp12"]);
  ("bls377_Fp12_inv", ["Fp12";"Fp12"]); ("bls377_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bls377_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bls377_Fp12_mul_by_024", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_Fp12_frobenius_p3", ["Fp12";"Fp12"]);
  ("bls377_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bls377_load_gamma1_p2", ["Fp2"]); ("bls377_load_gamma2_p2", ["Fp2"]);
  ("bls377_load_w_frob_p2_c1", ["Fp2"]); ("bls377_load_gamma1", ["Fp2"]);
  ("bls377_load_gamma2", ["Fp2"]); ("bls377_load_w_frob_c1", ["Fp2"]);
  ("bls377_load_w_frob_p3_c1", ["Fp2"]);
  ("bls377_Fp12_pow_u", ["Fp12";"Fp12"]);
  ("bls377_final_exp_hard_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_final_exp_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_final_exp", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bls377_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bls377_pairing", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bls377_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);

  (* === BN256 entries (parallel to bn254) === *)
  ("bn256_add", ["Fp";"Fp";"Fp"]); ("bn256_sub", ["Fp";"Fp";"Fp"]);
  ("bn256_mul", ["Fp";"Fp";"Fp"]); ("bn256_square", ["Fp";"Fp"]);
  ("bn256_opp", ["Fp";"Fp"]); ("bn256_felem_copy", ["Fp";"Fp"]);
  ("bn256_from_word", ["Fp";"Fp"]); ("bn256_select_znz", ["Fp";"Fp";"Fp";"Fp"]);
  ("bn256_inv", ["Fp";"Fp"]);
  ("bn256_Fp2_felem_copy", ["Fp2";"Fp2"]); ("bn256_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bn256_Fp2_sub", ["Fp2";"Fp2";"Fp2"]); ("bn256_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bn256_Fp2_square", ["Fp2";"Fp2"]); ("bn256_Fp2_sqr", ["Fp2";"Fp2"]);
  ("bn256_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bn256_Fp2_conjugate", ["Fp2";"Fp2"]); ("bn256_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  ("bn256_Fp2_opp", ["Fp2";"Fp2"]); ("bn256_Fp2_inv", ["Fp2";"Fp2"]);
  ("bn256_Fp6_felem_copy", ["Fp6";"Fp6"]); ("bn256_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bn256_Fp6_sub", ["Fp6";"Fp6";"Fp6"]); ("bn256_Fp6_opp", ["Fp6";"Fp6"]);
  ("bn256_Fp6_mul", ["Fp6";"Fp6";"Fp6"]); ("bn256_Fp6_square", ["Fp6";"Fp6"]);
  ("bn256_Fp6_inv", ["Fp6";"Fp6"]); ("bn256_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bn256_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]); ("bn256_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bn256_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bn256_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn256_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn256_Fp12_felem_copy", ["Fp12";"Fp12"]); ("bn256_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_add_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_sub_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_opp", ["Fp12";"Fp12"]);
  ("bn256_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_mul_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn256_Fp12_square", ["Fp12";"Fp12"]);
  ("bn256_Fp12_inv", ["Fp12";"Fp12"]); ("bn256_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bn256_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bn256_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn256_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn256_Fp12_frobenius_p3", ["Fp12";"Fp12"]);
  ("bn256_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn256_load_gamma1_p2", ["Fp2"]); ("bn256_load_gamma2_p2", ["Fp2"]);
  ("bn256_load_w_frob_p2_c1", ["Fp2"]); ("bn256_load_gamma1", ["Fp2"]);
  ("bn256_load_gamma2", ["Fp2"]); ("bn256_load_w_frob_c1", ["Fp2"]);
  ("bn256_Fp12_pow_u", ["Fp12";"Fp12"]); ("bn256_final_exp_hard_dsd", ["Fp12";"Fp12"]);
  ("bn256_final_exp_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn256_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn256_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);

  (* === BN446 entries (parallel to bn254/bn256) === *)
  ("bn446_add", ["Fp";"Fp";"Fp"]); ("bn446_sub", ["Fp";"Fp";"Fp"]);
  ("bn446_mul", ["Fp";"Fp";"Fp"]); ("bn446_square", ["Fp";"Fp"]);
  ("bn446_opp", ["Fp";"Fp"]); ("bn446_felem_copy", ["Fp";"Fp"]);
  ("bn446_from_word", ["Fp";"Fp"]); ("bn446_select_znz", ["Fp";"Fp";"Fp";"Fp"]);
  ("bn446_inv", ["Fp";"Fp"]);
  ("bn446_Fp2_felem_copy", ["Fp2";"Fp2"]); ("bn446_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bn446_Fp2_sub", ["Fp2";"Fp2";"Fp2"]); ("bn446_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bn446_Fp2_square", ["Fp2";"Fp2"]); ("bn446_Fp2_sqr", ["Fp2";"Fp2"]);
  ("bn446_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bn446_Fp2_conjugate", ["Fp2";"Fp2"]); ("bn446_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  ("bn446_Fp2_opp", ["Fp2";"Fp2"]); ("bn446_Fp2_inv", ["Fp2";"Fp2"]);
  ("bn446_Fp6_felem_copy", ["Fp6";"Fp6"]); ("bn446_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bn446_Fp6_sub", ["Fp6";"Fp6";"Fp6"]); ("bn446_Fp6_opp", ["Fp6";"Fp6"]);
  ("bn446_Fp6_mul", ["Fp6";"Fp6";"Fp6"]); ("bn446_Fp6_square", ["Fp6";"Fp6"]);
  ("bn446_Fp6_inv", ["Fp6";"Fp6"]); ("bn446_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bn446_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]); ("bn446_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bn446_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bn446_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn446_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn446_Fp12_felem_copy", ["Fp12";"Fp12"]); ("bn446_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_add_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_sub_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_opp", ["Fp12";"Fp12"]);
  ("bn446_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_mul_nocopy", ["Fp12";"Fp12";"Fp12"]);
  ("bn446_Fp12_square", ["Fp12";"Fp12"]);
  ("bn446_Fp12_inv", ["Fp12";"Fp12"]); ("bn446_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bn446_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bn446_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn446_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn446_Fp12_frobenius_p3", ["Fp12";"Fp12"]);
  ("bn446_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn446_load_gamma1_p2", ["Fp2"]); ("bn446_load_gamma2_p2", ["Fp2"]);
  ("bn446_load_w_frob_p2_c1", ["Fp2"]); ("bn446_load_gamma1", ["Fp2"]);
  ("bn446_load_gamma2", ["Fp2"]); ("bn446_load_w_frob_c1", ["Fp2"]);
  ("bn446_Fp12_pow_u", ["Fp12";"Fp12"]); ("bn446_final_exp_hard_dsd", ["Fp12";"Fp12"]);
  ("bn446_final_exp_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn446_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn446_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);

  (* === BLS24-509 tower entries.  Base Fp ops use the [bls24_509_*]
     prefix (8-limb 509-bit prime, 10-char prefix); tower ops use the
     short [bls24_*] prefix (6 chars).  Tower shape: Fp/Fp2/Fp4/Fp8/Fp24. *)
  ("bls24_509_add", ["Fp";"Fp";"Fp"]); ("bls24_509_sub", ["Fp";"Fp";"Fp"]);
  ("bls24_509_mul", ["Fp";"Fp";"Fp"]); ("bls24_509_square", ["Fp";"Fp"]);
  ("bls24_509_opp", ["Fp";"Fp"]); ("bls24_509_felem_copy", ["Fp";"Fp"]);
  ("bls24_509_from_word", ["Fp";"Fp"]);
  (* bls24_509_select_znz: out, mask, x, y.  Mask is a u64 word
     (not an Fp value); the extern leaf wrapper signature confirms
     [c: u64].  The existing BN/BLS12 entries above use "Fp" as a
     historical artifact — they're never called from a quad-extension
     [Fp{n}_select_znz] body in those crates, so the type-mismatch
     was latent. *)
  ("bls24_509_select_znz", ["Fp";"u64";"Fp";"Fp"]);
  ("bls24_509_inv", ["Fp";"Fp"]);
  ("bls24_509_one", ["Fp"]);  ("bls24_509_zero", ["Fp"]);
  ("bls24_Fp2_felem_copy", ["Fp2";"Fp2"]);
  ("bls24_Fp2_zero", ["Fp2"]); ("bls24_Fp2_one", ["Fp2"]);
  ("bls24_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bls24_Fp2_sub", ["Fp2";"Fp2";"Fp2"]);
  ("bls24_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bls24_Fp2_square", ["Fp2";"Fp2"]);
  ("bls24_Fp2_opp", ["Fp2";"Fp2"]);
  ("bls24_Fp2_mul_xi", ["Fp2";"Fp2"]);
  (* bls24_Fp2_mul_by_nr operates on the BASE field Fp (it multiplies
     an Fp value by the Fp2 non-residue β to compute the Fp2
     reduction in Fp2_mul / Fp2_square). *)
  ("bls24_Fp2_mul_by_nr", ["Fp";"Fp"]);
  (* select_znz: out, mask, x, y.  The mask [c] is a u64 word, NOT a
     field element.  Type-check against the BLS24 leaf wrapper
     declaration: fn bls24_509_select_znz(o, c: u64, x, y).  Each
     Fp{n}_select_znz in the verified tower forwards the [c] mask
     unchanged down to bls24_509_select_znz; emit it as u64. *)
  ("bls24_Fp2_select_znz", ["Fp2";"u64";"Fp2";"Fp2"]);
  ("bls24_Fp4_felem_copy", ["Fp4";"Fp4"]);
  ("bls24_Fp4_zero", ["Fp4"]); ("bls24_Fp4_one", ["Fp4"]);
  ("bls24_Fp4_add", ["Fp4";"Fp4";"Fp4"]);
  ("bls24_Fp4_sub", ["Fp4";"Fp4";"Fp4"]);
  ("bls24_Fp4_mul", ["Fp4";"Fp4";"Fp4"]);
  ("bls24_Fp4_square", ["Fp4";"Fp4"]);
  ("bls24_Fp4_opp", ["Fp4";"Fp4"]);
  ("bls24_Fp4_select_znz", ["Fp4";"u64";"Fp4";"Fp4"]);
  ("bls24_Fp4_mul_by_v", ["Fp4";"Fp4"]);
  ("bls24_Fp4_mul_fp", ["Fp4";"Fp4";"Fp"]);
  ("bls24_Fp4_inv", ["Fp4";"Fp4"]);
  ("bls24_Fp8_felem_copy", ["Fp8";"Fp8"]);
  ("bls24_Fp8_zero", ["Fp8"]); ("bls24_Fp8_one", ["Fp8"]);
  ("bls24_Fp8_add", ["Fp8";"Fp8";"Fp8"]);
  ("bls24_Fp8_sub", ["Fp8";"Fp8";"Fp8"]);
  ("bls24_Fp8_mul", ["Fp8";"Fp8";"Fp8"]);
  ("bls24_Fp8_square", ["Fp8";"Fp8"]);
  ("bls24_Fp8_opp", ["Fp8";"Fp8"]);
  ("bls24_Fp8_select_znz", ["Fp8";"u64";"Fp8";"Fp8"]);
  ("bls24_Fp8_mul_by_w", ["Fp8";"Fp8"]);
  ("bls24_Fp8_inv", ["Fp8";"Fp8"]);
  ("bls24_Fp24_felem_copy", ["Fp24";"Fp24"]);
  ("bls24_Fp24_zero", ["Fp24"]); ("bls24_Fp24_one", ["Fp24"]);
  ("bls24_Fp24_add", ["Fp24";"Fp24";"Fp24"]);
  ("bls24_Fp24_sub", ["Fp24";"Fp24";"Fp24"]);
  ("bls24_Fp24_mul", ["Fp24";"Fp24";"Fp24"]);
  ("bls24_Fp24_square", ["Fp24";"Fp24"]);
  ("bls24_Fp24_opp", ["Fp24";"Fp24"]);
  ("bls24_Fp24_inv", ["Fp24";"Fp24"]);
  (* Note: bedrock2 emits some Fp24-level helpers with lowercase
     [fp24] (frob, conjugate, pow_z, pow_abs_z). *)
  ("bls24_fp24_conjugate", ["Fp24";"Fp24"]);
  ("bls24_fp24_pow_abs_z", ["Fp24";"Fp24"]);
  ("bls24_fp24_pow_z", ["Fp24";"Fp24"]);
  (* Frobenius parameters: gamma_fp4 ∈ Fp2 (constant ξ^{(p−1)/2}),
     gamma_fp8 ∈ Fp4 (v^{(p−1)/2}), gamma_fp24_1 / gamma_fp24_2 ∈ Fp8
     (w^{(p−1)/3} and w^{2(p−1)/3}).  See BLS24_509_FinalExp.v frob doc. *)
  ("bls24_fp24_frob", ["Fp24";"Fp24";"Fp2";"Fp4";"Fp8";"Fp8"]);
  ("bls24_fp24_frob_p2", ["Fp24";"Fp24";"Fp2";"Fp4";"Fp8";"Fp8"]);
  ("bls24_fp24_frob_p4", ["Fp24";"Fp24";"Fp2";"Fp4";"Fp8";"Fp8"]);
  (* bls24_make_line: out_Fp24, lam_Fp4, x_t_Fp4, y_t_Fp4, x_p_Fp, y_p_Fp.
     Lambda and twist coords live in Fp4 (the bottom of Fp8) per the
     BLS24 line construction in BLS24_509_MillerLoop.v:233. *)
  ("bls24_make_line", ["Fp24";"Fp4";"Fp4";"Fp4";"Fp";"Fp"]);
  (* bls24_miller_loop: out_Fp24, P.x_Fp, P.y_Fp, Q.x_Fp4, Q.y_Fp4
     (Q lives on G2 ⊂ E(Fp4) for BLS24-509 — the twist over Fp4). *)
  ("bls24_miller_loop", ["Fp24";"Fp";"Fp";"Fp4";"Fp4"]);
  ("bls24_final_exp_easy", ["Fp24";"Fp24";"Fp2";"Fp4";"Fp8";"Fp8"]);
  ("bls24_final_exp_hard",
    ["Fp24";"Fp24";
     "Fp2";"Fp4";"Fp8";"Fp8";
     "Fp2";"Fp4";"Fp8";"Fp8";
     "Fp2";"Fp4";"Fp8";"Fp8"]);
  ("bls24_final_exp",
    ["Fp24";"Fp24";
     "Fp2";"Fp4";"Fp8";"Fp8";
     "Fp2";"Fp4";"Fp8";"Fp8";
     "Fp2";"Fp4";"Fp8";"Fp8"]);

  (* === BW6-761 tower entries.  Base Fp ops use the [bw6_761_*]
     prefix.  Tower shape: Fp / Fp3 (cubic) / Fp6 (quad over Fp3),
     so a 2-layer tower instead of BLS12's 3.  Fp prefix is the full
     [bw6_761_] (no shorter alias). *)
  ("bw6_761_add", ["Fp";"Fp";"Fp"]); ("bw6_761_sub", ["Fp";"Fp";"Fp"]);
  ("bw6_761_mul", ["Fp";"Fp";"Fp"]); ("bw6_761_square", ["Fp";"Fp"]);
  ("bw6_761_opp", ["Fp";"Fp"]); ("bw6_761_felem_copy", ["Fp";"Fp"]);
  ("bw6_761_from_word", ["Fp";"Fp"]);
  (* select_znz: out, mask:u64, x, y — mask is a one-word predicate. *)
  ("bw6_761_select_znz", ["Fp";"u64";"Fp";"Fp"]);
  ("bw6_761_inv", ["Fp";"Fp"]);
  (* Fp-level mul-by-nonresidue: mul-by-(-4) helper used as the
     [Mul_by_nr_func] slot of the cubic Fp3 emission. *)
  ("bw6_761_mul_by_nr_n4", ["Fp";"Fp"]);

  (* Fp3 tower (cubic-over-Fp).  Emitted by [GenericCubic.CE_funcs]. *)
  ("bw6_761_Fp3_felem_copy", ["Fp3";"Fp3"]);
  ("bw6_761_Fp3_zero", ["Fp3"]); ("bw6_761_Fp3_one", ["Fp3"]);
  ("bw6_761_Fp3_add", ["Fp3";"Fp3";"Fp3"]);
  ("bw6_761_Fp3_sub", ["Fp3";"Fp3";"Fp3"]);
  ("bw6_761_Fp3_mul", ["Fp3";"Fp3";"Fp3"]);
  ("bw6_761_Fp3_square", ["Fp3";"Fp3"]);
  ("bw6_761_Fp3_opp", ["Fp3";"Fp3"]);
  ("bw6_761_Fp3_select_znz", ["Fp3";"u64";"Fp3";"Fp3"]);
  ("bw6_761_Fp3_inv", ["Fp3";"Fp3"]);
  (* Fp3 mul-by-Fp scalar: (out:Fp3, x:Fp3, s:Fp). Used by make_line. *)
  ("bw6_761_Fp3_mul_fp", ["Fp3";"Fp3";"Fp"]);
  (* Fp3-level mul-by-zeta is the [Mul_by_nr_func] slot for the
     quadratic Fp6 layer.  Operates on Fp3 inputs. *)
  ("bw6_761_Fp3_mul_by_zeta", ["Fp3";"Fp3"]);

  (* Fp6 tower (quad-over-Fp3).  Emitted by [GenericQuadratic.QE_funcs]. *)
  ("bw6_761_Fp6_felem_copy", ["Fp6";"Fp6"]);
  ("bw6_761_Fp6_zero", ["Fp6"]); ("bw6_761_Fp6_one", ["Fp6"]);
  ("bw6_761_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bw6_761_Fp6_sub", ["Fp6";"Fp6";"Fp6"]);
  ("bw6_761_Fp6_mul", ["Fp6";"Fp6";"Fp6"]);
  ("bw6_761_Fp6_square", ["Fp6";"Fp6"]);
  ("bw6_761_Fp6_opp", ["Fp6";"Fp6"]);
  ("bw6_761_Fp6_select_znz", ["Fp6";"u64";"Fp6";"Fp6"]);

  (* Miller loop helpers and entry.
     make_line: out:Fp6, lam:Fp3, x_t:Fp3, y_t:Fp3, x_p:Fp, y_p:Fp.
     miller_loop: out:Fp6, p_x:Fp, p_y:Fp, q_x:Fp3, q_y:Fp3. *)
  ("bw6_761_make_line", ["Fp6";"Fp3";"Fp3";"Fp3";"Fp";"Fp"]);
  ("bw6_761_miller_loop", ["Fp6";"Fp";"Fp";"Fp3";"Fp3"]);

  (* Final exponentiation helpers.
     Note: these use the lowercase [bw6_fp6_*] / [bw6_final_exp*]
     prefixes (not [bw6_761_Fp6_*]) — see BW6_761_FinalExp.v Let bindings. *)
  ("bw6_fp6_conjugate", ["Fp6";"Fp6"]);
  ("bw6_fp6_pow_abs_u", ["Fp6";"Fp6"]);
  ("bw6_fp6_pow_u", ["Fp6";"Fp6"]);
  (* frob / frob_p2 / frob_p3 take Fp3 Frobenius constants
     (gamma_fp3 and gamma_fp6 are both Fp3 elements). *)
  ("bw6_fp6_frob", ["Fp6";"Fp6";"Fp3";"Fp3"]);
  ("bw6_fp6_frob_p2", ["Fp6";"Fp6";"Fp3";"Fp3"]);
  ("bw6_fp6_frob_p3", ["Fp6";"Fp6";"Fp3"]);
  (* easy/hard/full final-exp take the same gamma_* Fp3 constants. *)
  ("bw6_final_exp_easy", ["Fp6";"Fp6";"Fp3";"Fp3"]);
  ("bw6_final_exp_hard",
    ["Fp6";"Fp6";"Fp3";"Fp3";"Fp3";"Fp3";"Fp3"]);
  ("bw6_final_exp",
    ["Fp6";"Fp6";"Fp3";"Fp3";"Fp3";"Fp3";"Fp3"])
].

(** Check whether [s] contains [needle] as a contiguous substring.
    Walks every starting position; for small strings this is fine. *)
Fixpoint contains_at (s needle : string) (start : nat) : bool :=
  match start with
  | O => seq (substring 0 (String.length needle) s) needle
  | S k =>
    if seq (substring start (String.length needle) s) needle then true
    else contains_at s needle k
  end.

Definition contains (s needle : string) : bool :=
  let ls := String.length s in
  let ln := String.length needle in
  if Nat.leb ln ls then contains_at s needle (ls - ln)
  else false.

(** Detect the tower level a function operates on by scanning its name
    for an occurrence of any level's name (longer names first, so
    "Fp24" wins over "Fp2"). *)
Definition ts_base_type_of_name (ts : tower_shape) (f : string) : string :=
  (* sort levels descending by name length so "Fp24" matches before "Fp2" *)
  let lvls := ts_levels ts in
  let sorted :=
    List.fold_right
      (fun lvl acc =>
        let '(name, _, _) := lvl in
        let n := String.length name in
        let fix insert (l : list (string * string * Z))
            : list (string * string * Z) :=
          match l with
          | nil => [lvl]
          | ((nm, _, _) as h) :: t =>
            if Nat.leb (String.length nm) n
            then lvl :: l
            else h :: insert t
          end in
        insert acc)
      nil lvls in
  match List.find (fun '(name,_,_) => contains f name) sorted with
  | Some (name, _, _) => name
  | None => "Fp"
  end.

Definition base_type_of_name (f : string) : string :=
  ts_base_type_of_name bls12_tower f.

(** Look up callee parameter types. If the table entry is shorter than
    the actual arg count, pad with the function's base tower type
    (inferred from the name prefix). This handles functions like
    frobenius_p3 which take extra gamma parameters. *)
Definition callee_types_ts (ts : tower_shape) (f : string) (nargs : nat)
    : list string :=
  let base := ts_base_type_of_name ts f in
  match List.find (fun '(k,_) => seq k f) param_table with
  | Some (_, tys) =>
      let n := List.length tys in
      if Nat.leb nargs n then tys
      else tys ++ List.repeat base (nargs - n)
  | None => List.repeat base nargs
  end.

Definition callee_types (f : string) (nargs : nat) : list string :=
  callee_types_ts bls12_tower f nargs.

(* ================================================================ *)
(* In-place aliasing check                                           *)
(* ================================================================ *)

Fixpoint uses_var (x : string) (e : expr.expr) : bool :=
  match e with
  | expr.var y => seq (esc y) x
  | expr.op _ e1 e2 => uses_var x e1 || uses_var x e2
  | _ => false
  end.

Definition any_uses_var (x : string) (es : list expr.expr) : bool :=
  List.existsb (uses_var x) es.

(* ================================================================ *)
(* Scalar expression printing (for cmd.set, cmd.cond, cmd.while)     *)
(* ================================================================ *)

(** Print a bedrock2 binary operator. *)
Definition rust_bop (op : bopname) (a b : string) : string :=
  match op with
  | bopname.add => a ++ ".wrapping_add(" ++ b ++ ")"
  | bopname.sub => a ++ ".wrapping_sub(" ++ b ++ ")"
  | bopname.mul => a ++ ".wrapping_mul(" ++ b ++ ")"
  | bopname.and => "(" ++ a ++ " & " ++ b ++ ")"
  | bopname.or  => "(" ++ a ++ " | " ++ b ++ ")"
  | bopname.xor => "(" ++ a ++ " ^ " ++ b ++ ")"
  | bopname.sru => "(" ++ a ++ " >> (" ++ b ++ " & 63))"
  | bopname.slu => "(" ++ a ++ " << (" ++ b ++ " & 63))"
  | bopname.ltu => "if " ++ a ++ " < " ++ b ++ " { 1u64 } else { 0u64 }"
  | bopname.eq  => "if " ++ a ++ " == " ++ b ++ " { 1u64 } else { 0u64 }"
  | bopname.mulhuu => "((" ++ a ++ " as u128).wrapping_mul(" ++ b ++ " as u128) >> 64) as u64"
  | _ => a ++ " /* unknown_bop */ " ++ b
  end.

(** Print a scalar expression (u64-valued). Used for cmd.set RHS,
    cmd.cond test, cmd.while test.

    The [c] context is consulted only for [expr.load _ ((var x) + off)]:
    if [x] is a struct (Fp / Fp2 / Fp6 / Fp12 / unrecognized) then
    [x.wrapping_add(_)] would call a u64 method on a struct, so the
    address must go through the inner array's byte-pointer.  When [x]
    is a [u64] pointer-typed local (the bedrock2 convention), the
    direct cast is correct. *)
Fixpoint scalar_expr (c : ctx) (e : expr.expr) : string :=
  match e with
  | expr.var x => esc x
  | expr.literal z => z_str z ++ "u64"
  | expr.op op e1 e2 => rust_bop op (scalar_expr c e1) (scalar_expr c e2)
  | expr.load _ addr =>
      (* In the safe tower, loads from stackalloc'd u64 vars are just var reads *)
      match addr with
      | expr.var x => esc x  (* simple load: just read the variable *)
      | expr.op bopname.add (expr.var x) off =>
          let xn := esc x in
          let xt := match List.find (fun '(k,_) => seq k xn) c with
                    | Some (_, t) => t | None => "Fp" end in
          if seq xt "u64" then
            "unsafe { *(" ++ xn ++ ".wrapping_add(" ++ scalar_expr c off ++ ") as *const u64) }"
          else
            "unsafe { *((" ++ xn ++ ".0.as_ptr() as *const u8).wrapping_add("
            ++ scalar_expr c off ++ " as usize) as *const u64) }"
      | _ => "unsafe { *(" ++ scalar_expr c addr ++ " as *const u64) }"
      end
  | expr.ite cnd t f =>
      "if " ++ scalar_expr c cnd ++ " != 0 { " ++ scalar_expr c t ++ " } else { " ++ scalar_expr c f ++ " }"
  | _ => "0u64 /* unsupported_expr */"
  end.

(* ================================================================ *)
(* Command → safe Rust                                               *)
(* ================================================================ *)

(** Format a source argument with appropriate drill-down.  Special
    case: if the callee expects a [u64] (e.g. a select_znz mask), pass
    the local by value without [&]. *)
Definition fmt_src_ts (ts : tower_shape) (n : Z) (c : ctx)
    (ct : string) (e : expr.expr) : string :=
  let '(path, rt) := resolve_ts ts n c e in
  if seq rt "literal" then path (* literal: emit as-is *)
  else if seq ct "u64" then path
  else "&" ++ path ++ ts_drill ts rt ct.

Definition fmt_src (n : Z) (c : ctx) (ct : string) (e : expr.expr) : string :=
  fmt_src_ts bls12_tower n c ct e.

Fixpoint safe_cmd_ts (ts : tower_shape) (ind : string) (n : Z)
    (c : ctx) (ci : nat) (cmd : Syntax.cmd.cmd) : string * ctx * nat :=
  match cmd with
  | cmd.skip => ("", c, ci)
  | cmd.seq c1 c2 =>
      let '(s1, cx1, ci1) := safe_cmd_ts ts ind n c ci c1 in
      let '(s2, cx2, ci2) := safe_cmd_ts ts ind n cx1 ci1 c2 in
      (s1 ++ s2, cx2, ci2)

  | cmd.stackalloc x nbytes body =>
      let xn := esc x in
      let t := ts_type_of_bytes ts n nbytes in
      let init := if seq t "u64" then "0u64" else t ++ "::zero()" in
      let decl := ind ++ "let mut " ++ xn ++ ": " ++ t ++ " = " ++ init ++ ";" ++ LF in
      let '(body_s, cx, ci') := safe_cmd_ts ts ind n ((xn, t) :: c) ci body in
      (decl ++ body_s, cx, ci')

  | cmd.call nil f args =>
      let fname := f in
      let nargs := List.length args in
      let cts := callee_types_ts ts fname nargs in
      match args, cts with
      | dest_e :: src_es, dest_ct :: src_cts =>
        let '(dpath, drt) := resolve_ts ts n c dest_e in
        let dd := ts_drill ts drt dest_ct in
        let dest_full := dpath ++ dd in
        let '(dv, _) := expr_var_off dest_e in
        if any_uses_var dv src_es then
          (* In-place aliasing: clone the dest *)
          let cn := "__ac" ++ z_str (Z.of_nat ci) in
          let copy := ind ++ "let " ++ cn ++ " = " ++ dest_full ++ ".clone();" ++ LF in
          let fix fmt_srcs (cts : list string) (es : list expr.expr) : list string :=
            match cts, es with
            | ct :: cts', e :: es' =>
                let '(sp, srt) := resolve_ts ts n c e in
                let s := if seq (sp ++ ts_drill ts srt ct) dest_full
                         then "&" ++ cn
                         else fmt_src_ts ts n c ct e in
                s :: fmt_srcs cts' es'
            | _, _ => nil
            end in
          let srcs := fmt_srcs src_cts src_es in
          (* B-3 copy elimination: when we already cloned dest, the aliasing
             concern (out vs inx/iny) inside the leaf is no longer needed
             because __ac is a fresh buffer.  If the leaf has a _nocopy
             variant (skips its internal allocx/allocy felem_copies), use it.
             Saves 2 felem_copy calls (2 * sizeof(out)) per cloned-dest call. *)
          let nocopy_name := fname ++ "_nocopy" in
          let fname_eff :=
            if List.existsb (fun '(k,_) => seq k nocopy_name) param_table
            then nocopy_name else fname in
          let call := ind ++ fname_eff ++ "(&mut " ++ dest_full ++ ", " ++
                      join ", " srcs ++ ");" ++ LF in
          (copy ++ call, c, S ci)
        else
          let srcs := List.map (fun '(ct, e) => fmt_src_ts ts n c ct e)
                       (List.combine src_cts src_es) in
          (* B-3 copy elimination: even when there is no caller-side aliasing,
             the regular leaf wraps inputs in allocx/allocy felem_copies for
             defensive aliasing handling.  When dest provably differs from
             every source (the current branch), use _nocopy to skip those
             redundant internal copies. *)
          let nocopy_name := fname ++ "_nocopy" in
          let fname_eff :=
            if List.existsb (fun '(k,_) => seq k nocopy_name) param_table
            then nocopy_name else fname in
          let call := ind ++ fname_eff ++ "(&mut " ++ dest_full ++ ", " ++
                      join ", " srcs ++ ");" ++ LF in
          (call, c, ci)
      | _, _ =>
        (ind ++ fname ++ "();" ++ LF, c, ci)
      end

  | cmd.set x ev =>
      let xn := esc x in
      (* If x is not in context yet, declare it as a mutable u64 local *)
      let is_new := negb (List.existsb (fun '(k,_) => seq k xn) c) in
      let decl := if is_new then ind ++ "let mut " ++ xn ++ ": u64;" ++ LF else "" in
      let s := ind ++ xn ++ " = " ++ scalar_expr c ev ++ ";" ++ LF in
      let c' := if is_new then (xn, "u64") :: c else c in
      (decl ++ s, c', ci)

  | cmd.cond test ct cf =>
      let '(st, _, ci1) := safe_cmd_ts ts ("    " ++ ind) n c ci ct in
      let '(sf, _, ci2) := safe_cmd_ts ts ("    " ++ ind) n c ci1 cf in
      let cond_s := scalar_expr c test in
      (ind ++ "if " ++ cond_s ++ " != 0 {" ++ LF ++
       st ++ ind ++ "} else {" ++ LF ++ sf ++ ind ++ "}" ++ LF, c, ci2)

  | cmd.while test body =>
      let '(body_s, _, ci') := safe_cmd_ts ts ("    " ++ ind) n c ci body in
      let test_s := scalar_expr c test in
      (ind ++ "while " ++ test_s ++ " != 0 {" ++ LF ++
       body_s ++ ind ++ "}" ++ LF, c, ci')

  | cmd.store _ addr val =>
      (* cmd.store writes a single u64 word at a byte address.
         Resolve to struct_field.0[limb_index]. *)
      let '(vname, off) := expr_var_off addr in
      let vt := ctx_get c vname in
      let fp_bytes := fp_sz n in
      (* Find which Fp element contains this limb *)
      let fp_aligned := (off / fp_bytes) * fp_bytes in
      let limb_idx := (off - fp_aligned) / 8 in
      (* Drill all the way down to the Fp that contains this limb *)
      let fp_field := ts_field_path ts n vt fp_aligned in
      let fp_field' :=
        fp_field ++ ts_drill ts (ts_descend ts vt (path_depth fp_field)) "Fp" in
      let fp_path := vname ++ fp_field' in
      let val_s := scalar_expr c val in
      if seq vt "u64" then
        (* Scalar store: just assign *)
        (ind ++ vname ++ " = " ++ val_s ++ ";" ++ LF, c, ci)
      else
        (ind ++ fp_path ++ ".0[" ++ z_str limb_idx ++ "] = " ++ val_s ++ ";" ++ LF, c, ci)

  | cmd.unset _ => ("", c, ci)
  | _ => ("", c, ci)
  end.

Definition safe_cmd (ind : string) (n : Z) (c : ctx) (ci : nat)
    (cmd : Syntax.cmd.cmd) : string * ctx * nat :=
  safe_cmd_ts bls12_tower ind n c ci cmd.

(** Generate a complete safe Rust function.  Param formatting:
    - The first param is the output ([&mut T]).
    - Subsequent params are inputs ([&T] for struct types, [T] by-value
      for [u64] scalars). *)
Definition fmt_input_param (a t : string) : string :=
  if seq t "u64" then esc a ++ ": u64"
  else esc a ++ ": &" ++ t.

Definition safe_rust_fn_ts (ts : tower_shape) (n : Z) (ptypes : list string)
    (func : string * (list string * list string * Syntax.cmd.cmd)) : string :=
  let '(name, (args, _, body)) := func in
  let params := List.combine args ptypes in
  let param_strs := match params with
    | (a, t) :: rest =>
        ("mut " ++ esc a ++ ": &mut " ++ t) ::
        List.map (fun '(a, t) => fmt_input_param a t) rest
    | nil => nil
    end in
  let init_ctx : ctx := List.map (fun '(a, t) => (esc a, t)) params in
  let '(body_s, _, _) := safe_cmd_ts ts "    " n init_ctx 0 body in
  "#[inline]" ++ LF ++
  "pub fn " ++ name ++ "(" ++ join ", " param_strs ++ ") {" ++ LF ++
  body_s ++
  "}" ++ LF.

Definition safe_rust_fn (n : Z) (ptypes : list string)
    (func : string * (list string * list string * Syntax.cmd.cmd)) : string :=
  safe_rust_fn_ts bls12_tower n ptypes func.

(** Tower-aware type declarations.  Emits one [#[repr(C)] struct + impl
    zero] per non-base level, in the order given (base→top, so each
    level can reference its base by name).  The base [Fp] is always
    emitted as the limb-vector wrapper. *)
Fixpoint gen_fields_aux (base : string) (start : Z) (k : nat) : list string :=
  match k with
  | O => nil
  | S k' =>
    ("c" ++ z_str start ++ ": " ++ base)
      :: gen_fields_aux base (start + 1) k'
  end.

Fixpoint gen_zero_fields_aux (base : string) (start : Z) (k : nat) : list string :=
  match k with
  | O => nil
  | S k' =>
    ("c" ++ z_str start ++ ": " ++ base ++ "::zero()")
      :: gen_zero_fields_aux base (start + 1) k'
  end.

Definition ts_emit_level (n : Z)
    (lvl : string * string * Z) : string :=
  let '(name, base, arity) := lvl in
  let an := Z.to_nat arity in
  let fields :=
    List.map (fun s => "pub " ++ s) (gen_fields_aux base 0 an) in
  let zero_fields := gen_zero_fields_aux base 0 an in
  "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct " ++ name ++ " { " ++ join ", " fields ++ " }" ++ LF ++
  "impl " ++ name ++ " { #[inline] pub const fn zero() -> Self { " ++
  name ++ " { " ++ join ", " zero_fields ++ " } } }" ++ LF ++ LF.

Definition type_decls_ts (ts : tower_shape) (n : Z) : string :=
  let ns := z_str n in
  let base_decl :=
    "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
    "pub struct Fp(pub [u64; " ++ ns ++ "]);" ++ LF ++
    "impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; "
    ++ ns ++ "]) } }" ++ LF ++ LF in
  base_decl ++
  List.fold_right (fun lvl acc => ts_emit_level n lvl ++ acc) "" (ts_levels ts).

Definition type_decls (n : Z) : string := type_decls_ts bls12_tower n.

(** Generate safe Rust for a list of tower functions. *)
Definition safe_rust_module_ts (ts : tower_shape) (n : Z)
    (funcs : list (string * (list string * list string * Syntax.cmd.cmd))) : string :=
  join LF (List.map (fun '((name, (args, _, _)) as f) =>
    let ptypes := callee_types_ts ts name (List.length args) in
    safe_rust_fn_ts ts n ptypes f
  ) funcs).

Definition safe_rust_module (n : Z)
    (funcs : list (string * (list string * list string * Syntax.cmd.cmd))) : string :=
  safe_rust_module_ts bls12_tower n funcs.
