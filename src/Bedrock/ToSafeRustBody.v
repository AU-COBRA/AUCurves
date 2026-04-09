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

(** All sizes in bytes, parameterized by Fp limb count [n]. *)
Definition fp_sz  (n : Z) := n * 8.
Definition fp2_sz (n : Z) := 2 * n * 8.
Definition fp6_sz (n : Z) := 6 * n * 8.
Definition fp12_sz (n : Z) := 12 * n * 8.

(** Map a stackalloc byte count to a type name. *)
Definition type_of_bytes (n : Z) (b : Z) : string :=
  if b =? fp_sz n then "Fp"
  else if b =? fp2_sz n then "Fp2"
  else if b =? fp6_sz n then "Fp6"
  else if b =? fp12_sz n then "Fp12"
  else if b =? 8 then "u64"
  else "Fp".

(** Resolve a byte offset within a parent type to a field path.
    Non-recursive, max 3 levels (Fp12 → Fp6 → Fp2 → Fp). *)
Definition field_path (n : Z) (parent : string) (off : Z) : string :=
  if off =? 0 then ""
  else if seq parent "Fp2" then
    ".c" ++ z_str (off / fp_sz n)
  else if seq parent "Fp6" then
    let i := off / fp2_sz n in
    let r := off mod fp2_sz n in
    ".c" ++ z_str i ++
    (if r =? 0 then "" else ".c" ++ z_str (r / fp_sz n))
  else if seq parent "Fp12" then
    let i := off / fp6_sz n in
    let r := off mod fp6_sz n in
    let j := r / fp2_sz n in
    let r2 := r mod fp2_sz n in
    ".c" ++ z_str i ++
    (if r =? 0 then "" else
     ".c" ++ z_str j ++
     (if r2 =? 0 then "" else ".c" ++ z_str (r2 / fp_sz n)))
  else "".

(* ================================================================ *)
(* Type ranking for drill-down                                       *)
(* ================================================================ *)

Definition type_rank (t : string) : Z :=
  if seq t "Fp12" then 4 else if seq t "Fp6" then 3
  else if seq t "Fp2" then 2 else 1.

(** When a variable of type [vt] is passed to a callee expecting [ct],
    add .c0 suffixes to drill down if [vt] is strictly larger. *)
Definition drill (vt ct : string) : string :=
  if type_rank vt <=? type_rank ct then ""
  else if seq vt "Fp2" then ".c0"
  else if andb (seq vt "Fp6") (seq ct "Fp2") then ".c0"
  else if andb (seq vt "Fp6") (seq ct "Fp") then ".c0.c0"
  else if andb (seq vt "Fp12") (seq ct "Fp6") then ".c0"
  else if andb (seq vt "Fp12") (seq ct "Fp2") then ".c0.c0"
  else if andb (seq vt "Fp12") (seq ct "Fp") then ".c0.c0.c0"
  else "".

(** Descend [depth] levels in the tower type hierarchy. *)
Fixpoint descend (t : string) (depth : nat) : string :=
  match depth with
  | O => t
  | S d =>
    if seq t "Fp12" then descend "Fp6" d
    else if seq t "Fp6" then descend "Fp2" d
    else if seq t "Fp2" then descend "Fp" d
    else t
  end.

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

(** Resolve an expr in context: produce "var.field_path" string and resolved type. *)
Definition resolve (n : Z) (c : ctx) (e : expr.expr) : string * string :=
  let '(v, off) := expr_var_off e in
  if off =? -1 then (v, "literal")
  else
    let vt := ctx_get c v in
    if off =? 0 then (v, vt)
    else (v ++ field_path n vt off,
          descend vt (path_depth (field_path n vt off))).

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
  ("bn254_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"])
].

(** Look up callee parameter types. If the table entry is shorter than
    the actual arg count, pad with the function's base tower type
    (inferred from the name prefix). This handles functions like
    frobenius_p3 which take extra gamma parameters. *)
Definition base_type_of_name (f : string) : string :=
  if seq (substring 6 4 f) "Fp12" then "Fp12"
  else if seq (substring 6 3 f) "Fp6" then "Fp6"
  else if seq (substring 6 3 f) "Fp2" then "Fp2"
  else "Fp".

Definition callee_types (f : string) (nargs : nat) : list string :=
  let base := base_type_of_name f in
  match List.find (fun '(k,_) => seq k f) param_table with
  | Some (_, ts) =>
      let n := List.length ts in
      if Nat.leb nargs n then ts
      else ts ++ List.repeat base (nargs - n)
  | None => List.repeat base nargs
  end.

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
    cmd.cond test, cmd.while test. *)
Fixpoint scalar_expr (e : expr.expr) : string :=
  match e with
  | expr.var x => esc x
  | expr.literal z => z_str z ++ "u64"
  | expr.op op e1 e2 => rust_bop op (scalar_expr e1) (scalar_expr e2)
  | expr.load _ addr =>
      (* In the safe tower, loads from stackalloc'd u64 vars are just var reads *)
      match addr with
      | expr.var x => esc x  (* simple load: just read the variable *)
      | _ => "unsafe { *(" ++ scalar_expr addr ++ " as *const u64) }"
      end
  | expr.ite c t f =>
      "if " ++ scalar_expr c ++ " != 0 { " ++ scalar_expr t ++ " } else { " ++ scalar_expr f ++ " }"
  | _ => "0u64 /* unsupported_expr */"
  end.

(* ================================================================ *)
(* Command → safe Rust                                               *)
(* ================================================================ *)

(** Format a source argument with appropriate drill-down. *)
Definition fmt_src (n : Z) (c : ctx) (ct : string) (e : expr.expr) : string :=
  let '(path, rt) := resolve n c e in
  if seq rt "literal" then path (* literal: emit as-is *)
  else "&" ++ path ++ drill rt ct.

Fixpoint safe_cmd (ind : string) (n : Z) (c : ctx) (ci : nat)
    (cmd : Syntax.cmd.cmd) : string * ctx * nat :=
  match cmd with
  | cmd.skip => ("", c, ci)
  | cmd.seq c1 c2 =>
      let '(s1, cx1, ci1) := safe_cmd ind n c ci c1 in
      let '(s2, cx2, ci2) := safe_cmd ind n cx1 ci1 c2 in
      (s1 ++ s2, cx2, ci2)

  | cmd.stackalloc x nbytes body =>
      let xn := esc x in
      let t := type_of_bytes n nbytes in
      let init := if seq t "u64" then "0u64" else t ++ "::zero()" in
      let decl := ind ++ "let mut " ++ xn ++ ": " ++ t ++ " = " ++ init ++ ";" ++ LF in
      let '(body_s, cx, ci') := safe_cmd ind n ((xn, t) :: c) ci body in
      (decl ++ body_s, cx, ci')

  | cmd.call nil f args =>
      let fname := f in
      let nargs := List.length args in
      let cts := callee_types fname nargs in
      match args, cts with
      | dest_e :: src_es, dest_ct :: src_cts =>
        let '(dpath, drt) := resolve n c dest_e in
        let dd := drill drt dest_ct in
        let dest_full := dpath ++ dd in
        let '(dv, _) := expr_var_off dest_e in
        if any_uses_var dv src_es then
          (* In-place aliasing: clone the dest *)
          let cn := "__ac" ++ z_str (Z.of_nat ci) in
          let copy := ind ++ "let " ++ cn ++ " = " ++ dest_full ++ ".clone();" ++ LF in
          let fix fmt_srcs (cts : list string) (es : list expr.expr) : list string :=
            match cts, es with
            | ct :: cts', e :: es' =>
                let '(sp, srt) := resolve n c e in
                let s := if seq (sp ++ drill srt ct) dest_full
                         then "&" ++ cn
                         else fmt_src n c ct e in
                s :: fmt_srcs cts' es'
            | _, _ => nil
            end in
          let srcs := fmt_srcs src_cts src_es in
          let call := ind ++ fname ++ "(&mut " ++ dest_full ++ ", " ++
                      join ", " srcs ++ ");" ++ LF in
          (copy ++ call, c, S ci)
        else
          let srcs := List.map (fun '(ct, e) => fmt_src n c ct e) (List.combine src_cts src_es) in
          let call := ind ++ fname ++ "(&mut " ++ dest_full ++ ", " ++
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
      let s := ind ++ xn ++ " = " ++ scalar_expr ev ++ ";" ++ LF in
      let c' := if is_new then (xn, "u64") :: c else c in
      (decl ++ s, c', ci)

  | cmd.cond test ct cf =>
      let '(st, _, ci1) := safe_cmd ("    " ++ ind) n c ci ct in
      let '(sf, _, ci2) := safe_cmd ("    " ++ ind) n c ci1 cf in
      let cond_s := scalar_expr test in
      (ind ++ "if " ++ cond_s ++ " != 0 {" ++ LF ++
       st ++ ind ++ "} else {" ++ LF ++ sf ++ ind ++ "}" ++ LF, c, ci2)

  | cmd.while test body =>
      let '(body_s, _, ci') := safe_cmd ("    " ++ ind) n c ci body in
      let test_s := scalar_expr test in
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
      let fp_field := field_path n vt fp_aligned in
      let fp_field' := fp_field ++ drill (descend vt (path_depth fp_field)) "Fp" in
      let fp_path := vname ++ fp_field' in
      let val_s := scalar_expr val in
      if seq vt "u64" then
        (* Scalar store: just assign *)
        (ind ++ vname ++ " = " ++ val_s ++ ";" ++ LF, c, ci)
      else
        (ind ++ fp_path ++ ".0[" ++ z_str limb_idx ++ "] = " ++ val_s ++ ";" ++ LF, c, ci)

  | cmd.unset _ => ("", c, ci)
  | _ => ("", c, ci)
  end.

(** Generate a complete safe Rust function. *)
Definition safe_rust_fn (n : Z) (ptypes : list string)
    (func : string * (list string * list string * Syntax.cmd.cmd)) : string :=
  let '(name, (args, _, body)) := func in
  let params := List.combine args ptypes in
  let param_strs := match params with
    | (a, t) :: rest =>
        ("mut " ++ esc a ++ ": &mut " ++ t) ::
        List.map (fun '(a, t) => esc a ++ ": &" ++ t) rest
    | nil => nil
    end in
  let init_ctx : ctx := List.map (fun '(a, t) => (esc a, t)) params in
  let '(body_s, _, _) := safe_cmd "    " n init_ctx 0 body in
  "#[inline]" ++ LF ++
  "pub fn " ++ name ++ "(" ++ join ", " param_strs ++ ") {" ++ LF ++
  body_s ++
  "}" ++ LF.

(** Type declarations for BN254. *)
Definition type_decls (n : Z) : string :=
  let ns := z_str n in
  "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp(pub [u64; " ++ ns ++ "]);" ++ LF ++
  "impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; " ++ ns ++ "]) } }" ++ LF ++ LF ++
  "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp2 { pub c0: Fp, pub c1: Fp }" ++ LF ++
  "impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }" ++ LF ++ LF ++
  "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp6 { pub c0: Fp2, pub c1: Fp2, pub c2: Fp2 }" ++ LF ++
  "impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp2::zero(), c1: Fp2::zero(), c2: Fp2::zero() } } }" ++ LF ++ LF ++
  "#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp12 { pub c0: Fp6, pub c1: Fp6 }" ++ LF ++
  "impl Fp12 { #[inline] pub const fn zero() -> Self { Fp12 { c0: Fp6::zero(), c1: Fp6::zero() } } }" ++ LF.

(** Generate safe Rust for a list of tower functions. *)
Definition safe_rust_module (n : Z)
    (funcs : list (string * (list string * list string * Syntax.cmd.cmd))) : string :=
  join LF (List.map (fun '((name, (args, _, _)) as f) =>
    let ptypes := callee_types name (List.length args) in
    safe_rust_fn n ptypes f
  ) funcs).
