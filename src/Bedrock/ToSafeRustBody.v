(** * ToSafeRustBody: bedrock2 tower functions → fully safe Rust bodies.
 *
 * Translates bedrock2 [cmd] trees for Fp2/Fp6/Fp12 tower functions
 * into safe Rust using [#[repr(C)]] nested structs:
 *
 *   [#[repr(C)]] struct Fp([u64; N]);
 *   [#[repr(C)]] struct Fp2  { c0: Fp,  c1: Fp  }
 *   [#[repr(C)]] struct Fp6  { c0: Fp2, c1: Fp2, c2: Fp2 }
 *   [#[repr(C)]] struct Fp12 { c0: Fp6, c1: Fp6 }
 *
 * Key translations:
 *   ptr + k*felem_size  →  ptr.c<k>  (struct field access)
 *   stackalloc N as v   →  let mut v = T::zero()  (stack local)
 *   call f [dst; args]  →  f(&mut dst_field, &arg1_field, ...)
 *                          with in-place aliasing detected and
 *                          resolved via stack copies.
 *
 * The output contains zero [unsafe] blocks. All pointer arithmetic
 * is replaced by typed struct field access, and the borrow checker
 * verifies non-aliasing at every call site.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition LF : string :=
  String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

(* ================================================================ *)
(* Tower type system                                                  *)
(* ================================================================ *)

(** A tower type: tracks the nesting level and byte size. *)
Inductive tower_type :=
  | TFp
  | TFp2
  | TFp6
  | TFp12.

Definition tt_name (t : tower_type) : string :=
  match t with TFp => "Fp" | TFp2 => "Fp2" | TFp6 => "Fp6" | TFp12 => "Fp12" end.

(** Byte size of a tower type given the base Fp limb count. *)
Definition tt_bytes (limbs : Z) (t : tower_type) : Z :=
  let fp := Z.mul limbs 8 in
  match t with
  | TFp => fp
  | TFp2 => Z.mul 2 fp
  | TFp6 => Z.mul 6 fp
  | TFp12 => Z.mul 12 fp
  end.

(** Number of components at the immediate sub-level. *)
Definition tt_ncomps (t : tower_type) : Z :=
  match t with TFp => 0 | TFp2 => 2 | TFp6 => 3 | TFp12 => 2 end.

(** Type of each component. *)
Definition tt_comp_type (t : tower_type) : tower_type :=
  match t with TFp => TFp | TFp2 => TFp | TFp6 => TFp2 | TFp12 => TFp6 end.

(* ================================================================ *)
(* Offset → field path resolution                                    *)
(* ================================================================ *)

(** Given a byte offset within a tower type, produce the Rust field
    path suffix (e.g., ".c1.c0" for offset 64 within Fp6 when Fp=32). *)
(** Resolve a byte offset within a tower type to a field path.
    Non-recursive: the tower has at most 3 nesting levels. *)
Definition resolve_field_1 (limbs : Z) (t : tower_type) (off : Z) : string :=
  match t with
  | TFp => ""
  | _ =>
    let comp_sz := tt_bytes limbs (tt_comp_type t) in
    ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int (Z.div off comp_sz))
  end.

Definition resolve_field (limbs : Z) (t : tower_type) (off : Z) : string :=
  match t with
  | TFp => ""
  | TFp2 =>
    let fp := Z.mul limbs 8 in
    ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int (Z.div off fp))
  | TFp6 =>
    let fp2 := Z.mul 2 (Z.mul limbs 8) in
    let idx := Z.div off fp2 in
    let rem := Z.modulo off fp2 in
    ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int idx) ++
    resolve_field_1 limbs TFp2 rem
  | TFp12 =>
    let fp6 := Z.mul 6 (Z.mul limbs 8) in
    let fp2 := Z.mul 2 (Z.mul limbs 8) in
    let idx := Z.div off fp6 in
    let rem := Z.modulo off fp6 in
    let idx2 := Z.div rem fp2 in
    let rem2 := Z.modulo rem fp2 in
    ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int idx) ++
    ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int idx2) ++
    resolve_field_1 limbs TFp2 rem2
  end.

(** Map a byte size to the tower type it represents. *)
Definition size_to_type (limbs : Z) (nbytes : Z) : tower_type :=
  let fp := Z.mul limbs 8 in
  if Z.eqb nbytes fp then TFp
  else if Z.eqb nbytes (Z.mul 2 fp) then TFp2
  else if Z.eqb nbytes (Z.mul 6 fp) then TFp6
  else if Z.eqb nbytes (Z.mul 12 fp) then TFp12
  else TFp. (* fallback *)

(* ================================================================ *)
(* Expression → Rust field-access translation                        *)
(* ================================================================ *)

(** A resolved argument: variable name + field path + tower type. *)
Record resolved_arg := {
  ra_var : string;
  ra_path : string;    (* e.g. ".c1.c0" *)
  ra_type : tower_type;
}.

Definition rust_var (x : string) : string :=
  if String.eqb x "in" then "in_"
  else if String.eqb x "fn" then "fn_"
  else if String.eqb x "let" then "let_"
  else if String.eqb x "type" then "type_"
  else if String.eqb x "loop" then "loop_"
  else if String.eqb x "self" then "self_"
  else if String.eqb x "use" then "use_"
  else if String.eqb x "mod" then "mod_"
  else x.

(** Resolve a bedrock2 expression to a variable + field path.
    Handles: [expr.var x], [expr.op add (expr.var x) (expr.literal k)],
    and nested adds. *)
Fixpoint resolve_expr (limbs : Z) (ctx_type : tower_type)
    (e : expr.expr) : resolved_arg :=
  match e with
  | expr.var x =>
      {| ra_var := rust_var x; ra_path := ""; ra_type := ctx_type |}
  | expr.op bopname.add e1 (expr.literal k) =>
      let base := resolve_expr limbs ctx_type e1 in
      let total_off := k in (* e1 already resolved; k is additional offset *)
      {| ra_var := ra_var base;
         ra_path := ra_path base ++ resolve_field limbs ctx_type total_off;
         ra_type := size_to_type limbs (tt_bytes limbs ctx_type - total_off) |}
  | expr.op bopname.add (expr.literal k) e2 =>
      resolve_expr limbs ctx_type (expr.op bopname.add e2 (expr.literal k))
  | _ =>
      {| ra_var := "/*unsupported*/"; ra_path := ""; ra_type := TFp |}
  end.

(** Smarter resolve: given a base variable and its known tower type,
    resolve an expression that is [base + literal_offset]. *)
Definition resolve_with_base (limbs : Z) (base_var : string)
    (base_type : tower_type) (e : expr.expr) : resolved_arg :=
  match e with
  | expr.var x =>
      {| ra_var := rust_var x; ra_path := ""; ra_type := base_type |}
  | expr.op bopname.add (expr.var x) (expr.literal k) =>
      if String.eqb x base_var then
        let comp_type := tt_comp_type base_type in
        let comp_sz := tt_bytes limbs comp_type in
        let idx := Z.div k comp_sz in
        let rem := Z.modulo k comp_sz in
        {| ra_var := rust_var x;
           ra_path := ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int idx) ++
                      resolve_field limbs comp_type rem;
           ra_type := comp_type |}
      else
        {| ra_var := rust_var x; ra_path := "/*unknown_offset*/"; ra_type := TFp |}
  | _ =>
      resolve_expr limbs base_type e
  end.

(* ================================================================ *)
(* Variable context: track types of all in-scope variables           *)
(* ================================================================ *)

Definition var_ctx := list (string * tower_type).

Definition ctx_lookup (ctx : var_ctx) (x : string) : tower_type :=
  match List.find (fun '(n, _) => String.eqb n x) ctx with
  | Some (_, t) => t
  | None => TFp (* default *)
  end.

Definition ctx_add (ctx : var_ctx) (x : string) (t : tower_type) : var_ctx :=
  (x, t) :: ctx.

(* ================================================================ *)
(* In-place aliasing detection                                       *)
(* ================================================================ *)

(** Check whether an expression [e] references the same base variable
    as [dest_var] (possibly at a different offset). *)
Fixpoint expr_uses_var (x : string) (e : expr.expr) : bool :=
  match e with
  | expr.var y => String.eqb x y
  | expr.op _ e1 e2 => expr_uses_var x e1 || expr_uses_var x e2
  | expr.literal _ => false
  | _ => false
  end.

(** Check if any of the source arguments (args after the first, which is
    the destination) reference [dest_var]. *)
Definition has_aliasing (dest_var : string) (src_args : list expr.expr) : bool :=
  List.existsb (expr_uses_var dest_var) src_args.

(* ================================================================ *)
(* Command → safe Rust translation                                   *)
(* ================================================================ *)

(** Map a function name to its safe Rust wrapper name.
    Convention: bn254_add → fp_add, bn254_Fp2_mul → fp2_mul, etc. *)
Definition safe_fn_name (f : string) : string := f.
  (* For now, use the same name. The safe module can re-export. *)

(** Resolve an argument in the context of a function call.
    Uses the variable context to determine the base type. *)
Definition resolve_call_arg (limbs : Z) (ctx : var_ctx) (e : expr.expr)
    : resolved_arg :=
  match e with
  | expr.var x => {| ra_var := rust_var x; ra_path := ""; ra_type := ctx_lookup ctx x |}
  | expr.op bopname.add (expr.var x) (expr.literal k) =>
      let base_type := ctx_lookup ctx x in
      let comp_type := tt_comp_type base_type in
      let comp_sz := tt_bytes limbs comp_type in
      let idx := k / comp_sz in
      let rem := k mod comp_sz in
      {| ra_var := rust_var x;
         ra_path := ".c" ++ DecimalString.NilZero.string_of_int (Z.to_int idx) ++
                    resolve_field limbs comp_type rem;
         ra_type := comp_type |}
  | _ => {| ra_var := "/*expr*/"; ra_path := ""; ra_type := TFp |}
  end.

Definition pp_arg_ref (a : resolved_arg) : string :=
  "&" ++ ra_var a ++ ra_path a.

Definition pp_arg_mut (a : resolved_arg) : string :=
  "&mut " ++ ra_var a ++ ra_path a.

(** Fresh variable name for alias copies. *)
Definition alias_copy_name (n : nat) : string :=
  "__ac" ++ DecimalString.NilZero.string_of_int (Nat.to_int n).

Fixpoint safe_cmd (indent : string) (limbs : Z) (ctx : var_ctx)
    (copy_idx : nat) (c : Syntax.cmd.cmd)
    : string * var_ctx * nat :=
  match c with
  | cmd.skip => ("", ctx, copy_idx)
  | cmd.seq c1 c2 =>
      let '(s1, ctx1, ci1) := safe_cmd indent limbs ctx copy_idx c1 in
      let '(s2, ctx2, ci2) := safe_cmd indent limbs ctx1 ci1 c2 in
      (s1 ++ s2, ctx2, ci2)
  | cmd.stackalloc x nbytes body =>
      let t := size_to_type limbs nbytes in
      let decl := indent ++ "let mut " ++ rust_var x ++ " = " ++ tt_name t ++ "::zero();" ++ LF in
      let ctx' := ctx_add ctx x t in
      let '(body_s, ctx'', ci) := safe_cmd indent limbs ctx' copy_idx body in
      (decl ++ body_s, ctx'', ci)
  | cmd.call nil f args =>
      match args with
      | dest_e :: src_es =>
        let dest := resolve_call_arg limbs ctx dest_e in
        let srcs := List.map (resolve_call_arg limbs ctx) src_es in
        let dest_var := ra_var dest in
        (* Check for in-place aliasing *)
        if has_aliasing dest_var src_es then
          (* Need to copy aliased sources to temporaries *)
          let copy_name := alias_copy_name copy_idx in
          let copy_decl := indent ++ "let " ++ copy_name ++ " = " ++
                           dest_var ++ ra_path dest ++ ";" ++ LF in
          (* Replace references to dest_var in srcs with copy_name *)
          let fix_src (a : resolved_arg) : resolved_arg :=
            if String.eqb (ra_var a) dest_var
            then {| ra_var := copy_name;
                    ra_path := (* strip the matching prefix and keep the rest *)
                      ra_path a; (* TODO: adjust path relative to copy *)
                    ra_type := ra_type a |}
            else a in
          let srcs' := List.map fix_src srcs in
          let call_s := indent ++ safe_fn_name f ++ "(" ++
            pp_arg_mut dest ++
            String.concat "" (List.map (fun a => ", " ++ pp_arg_ref a) srcs') ++
            ");" ++ LF in
          (copy_decl ++ call_s, ctx, S copy_idx)
        else
          let call_s := indent ++ safe_fn_name f ++ "(" ++
            pp_arg_mut dest ++
            String.concat "" (List.map (fun a => ", " ++ pp_arg_ref a) srcs) ++
            ");" ++ LF in
          (call_s, ctx, copy_idx)
      | _ =>
        let call_s := indent ++ safe_fn_name f ++ "();" ++ LF in
        (call_s, ctx, copy_idx)
      end
  | cmd.set x e =>
      let s := indent ++ rust_var x ++ " = /* set */ 0;" ++ LF in
      (s, ctx, copy_idx)
  | cmd.cond e ct cf =>
      let '(st, ctx1, ci1) := safe_cmd ("  " ++ indent) limbs ctx copy_idx ct in
      let '(sf, ctx2, ci2) := safe_cmd ("  " ++ indent) limbs ctx ci1 cf in
      (indent ++ "if /* cond */ {" ++ LF ++ st ++ indent ++ "} else {" ++ LF ++ sf ++ indent ++ "}" ++ LF,
       ctx2, ci2)
  | _ => ("", ctx, copy_idx)
  end.

(** Generate a safe Rust function from a bedrock2 function. *)
Definition safe_rust_func (limbs : Z) (param_types : list tower_type)
    '((name, (args, rets, body)) : string * (list string * list string * Syntax.cmd.cmd))
    : string :=
  (* Build parameter list with types *)
  let params := List.combine args param_types in
  let param_strs :=
    match params with
    | (a, t) :: rest =>
        (rust_var a ++ ": &mut " ++ tt_name t) ::
        List.map (fun '(a, t) => rust_var a ++ ": &" ++ tt_name t) rest
    | nil => nil
    end in
  let ctx : var_ctx := List.map (fun '(a, t) => (a, t)) params in
  let '(body_s, _, _) := safe_cmd "    " limbs ctx 0 body in
  "#[inline]" ++ LF ++
  "pub fn " ++ name ++ "(" ++ String.concat ", " param_strs ++ ") {" ++ LF ++
  body_s ++
  "}" ++ LF.

(* ================================================================ *)
(* Struct type declarations                                          *)
(* ================================================================ *)

Definition safe_type_decls (limbs : Z) : string :=
  let n := DecimalString.NilZero.string_of_int (Z.to_int limbs) in
  "#[repr(C)]" ++ LF ++
  "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp(pub [u64; " ++ n ++ "]);" ++ LF ++
  "impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; " ++ n ++ "]) } }" ++ LF ++ LF ++
  "#[repr(C)]" ++ LF ++
  "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp2 { pub c0: Fp, pub c1: Fp }" ++ LF ++
  "impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }" ++ LF ++ LF ++
  "#[repr(C)]" ++ LF ++
  "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp6 { pub c0: Fp2, pub c1: Fp2, pub c2: Fp2 }" ++ LF ++
  "impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp2::zero(), c1: Fp2::zero(), c2: Fp2::zero() } } }" ++ LF ++ LF ++
  "#[repr(C)]" ++ LF ++
  "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
  "pub struct Fp12 { pub c0: Fp6, pub c1: Fp6 }" ++ LF ++
  "impl Fp12 { #[inline] pub const fn zero() -> Self { Fp12 { c0: Fp6::zero(), c1: Fp6::zero() } } }" ++ LF ++ LF.
