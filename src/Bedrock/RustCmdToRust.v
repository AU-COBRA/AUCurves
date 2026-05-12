(** * RustCmdToRust: rust_cmd_ed → safe Rust string emitter.
 *
 * Direct Rust emission, sidestepping the C path's pointer-offset gap.
 * Typed slots map naturally:
 *   TBytes n     → [u8; n]
 *   TU64         → u64
 *   TFp25519/_64 → [u64; 5]/[u64; 4]   (treated as opaque arrays here;
 *                                       leaf callees declared `extern "C"`)
 *   TFpL25519    → [u64; 4]
 *
 * REdCall emits an `unsafe { fname(...) }` call to a leaf declared in the
 * `extern "C"` prelude.  Borrow-rule safety is guaranteed by
 * [borrow_ok_ed] (vm_compute) at the rust_cmd_ed level.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Numbers.DecimalString.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.RustCmdToC.   (* reuse z_str / nat_str / join / LF *)
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Local: indexed map (Stdlib's List has no [mapi]). *)
Fixpoint mapi_from {A B : Type} (f : nat -> A -> B) (n : nat) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | x :: xs' => f n x :: mapi_from f (S n) xs'
  end.

Definition mapi {A B : Type} (f : nat -> A -> B) (xs : list A) : list B :=
  mapi_from f 0%nat xs.

(* ================================================================ *)
(* §0. Identifier sanitization (Rust keyword avoidance)               *)
(* ================================================================ *)

(** Wrap with [r#...] if the source identifier collides with a Rust
    keyword.  Conservative list — covers what the Ed25519 source uses
    plus a few more.  Keep alphabetical. *)
Definition rs_sanitize (s : String.string) : String.string :=
  if (String.eqb s "pub" || String.eqb s "fn"  || String.eqb s "let" ||
      String.eqb s "mut" || String.eqb s "ref" || String.eqb s "type" ||
      String.eqb s "use" || String.eqb s "mod" || String.eqb s "box" ||
      String.eqb s "as"  || String.eqb s "in"  || String.eqb s "if"  ||
      String.eqb s "match" || String.eqb s "loop")%bool
  then "r#" ++ s else s.

(* ================================================================ *)
(* §1. Type emission                                                  *)
(* ================================================================ *)

Definition rs_array_type (t : tower_type_ed) : string :=
  match t with
  | TFp25519     => "[u64; 5]"
  | TFp25519_64  => "[u64; 4]"
  | TFpL25519    => "[u64; 4]"
  | TBytes n     => "[u8; " ++ nat_str n ++ "]"
  | TU64         => "u64"
  end.

Definition rs_param_type (t : tower_type_ed) : string :=
  (* Mutable references for arrays; value for u64.  All callees take
     pointers in the FFI prelude; safe wrappers accept [&mut] and
     decay to raw pointers at the call site. *)
  match t with
  | TU64         => "u64"
  | _            => "&mut " ++ rs_array_type t
  end.

(** Local zero-initialized declaration. *)
Definition rs_decl_slot (var0 : String.string) (t : tower_type_ed) : string :=
  let var := rs_sanitize var0 in
  match t with
  | TFp25519    => "    let mut " ++ var ++ ": [u64; 5] = [0; 5];"
  | TFp25519_64 => "    let mut " ++ var ++ ": [u64; 4] = [0; 4];"
  | TFpL25519   => "    let mut " ++ var ++ ": [u64; 4] = [0; 4];"
  | TBytes n    => "    let mut " ++ var ++ ": [u8; " ++ nat_str n ++
                   "] = [0; " ++ nat_str n ++ "];"
  | TU64        => "    let mut " ++ var ++ ": u64 = 0;"
  end.

(* ================================================================ *)
(* §2. sexpr_ed → Rust expression                                     *)
(* ================================================================ *)

Fixpoint rs_sexpr (e : sexpr_ed) : string :=
  match e with
  | SVar x      => rs_sanitize x
  | SLit z      => z_str z ++ "u64"
  | SAdd a b    => "(" ++ rs_sexpr a ++ ".wrapping_add(" ++ rs_sexpr b ++ "))"
  | SSub a b    => "(" ++ rs_sexpr a ++ ".wrapping_sub(" ++ rs_sexpr b ++ "))"
  | SMul a b    => "(" ++ rs_sexpr a ++ ".wrapping_mul(" ++ rs_sexpr b ++ "))"
  | SShr a b    => "(" ++ rs_sexpr a ++ " >> " ++ rs_sexpr b ++ ")"
  | SAnd a b    => "(" ++ rs_sexpr a ++ " & "  ++ rs_sexpr b ++ ")"
  | SLt a b     => "((" ++ rs_sexpr a ++ " < " ++ rs_sexpr b ++ ") as u64)"
  end.

(* ================================================================ *)
(* §3. located_ed → Rust call argument                                *)
(* ================================================================ *)

(** First argument (destination) of an FFI call: passed by [as_mut_ptr].
    Subsequent (input) args: passed by [as_ptr].  This mirrors the
    standard Jasmin / fiat-crypto convention (out, in1, in2, ...). *)
Definition rs_dest_arg (l : located_ed) : string :=
  match l.(loc_type) with
  | TU64 => rs_sanitize l.(loc_var) ++ ".clone()" (* unused for now: dest is an array *)
  | _    => rs_sanitize l.(loc_var) ++ ".as_mut_ptr()"
  end.

Definition rs_input_arg (l : located_ed) : string :=
  match l.(loc_type) with
  | TU64 => rs_sanitize l.(loc_var)
  | _    => rs_sanitize l.(loc_var) ++ ".as_ptr()"
  end.

(** Gap-#1 fix: callees whose ABI takes a trailing length arg
    that the rust_cmd_ed AST does not carry explicitly.  Inject
    the buffer length (statically known from the [TBytes n] type
    of the input arg) as a [u64] literal at the call site.

    Bug-A fix: if the call site already passes a [TU64]-typed
    [located_ed] (dynamic length), it is emitted as a normal argument
    via [rs_input_arg]; we then suppress the literal injection so the
    callee receives the dynamic length, not the static buffer width.
    Only when no explicit [TU64] length is present do we fall back to
    the buffer-width literal. *)
Definition has_tu64_arg (args : list located_ed) : bool :=
  List.existsb (fun a => match a.(loc_type) with
                         | TU64 => true
                         | _    => false
                         end) args.

Definition rs_call_inject_lens (fname : String.string)
                               (args : list located_ed) : list string :=
  if String.eqb fname "sha512_64"
  then
    if has_tu64_arg args
    then []  (* dynamic length: emitted via [rs_input_arg] from the TU64 arg *)
    else
      match args with
      | hd :: _ => [nat_str (tt_bytes_ed hd.(loc_type)) ++ "u64"]
      | nil => nil
      end
  else nil.

(* ================================================================ *)
(* §4. Main emitter                                                  *)
(* ================================================================ *)

Fixpoint rs_emit (indent : string) (c : rust_cmd_ed) : string :=
  match c with
  | REdSkip => indent ++ "()"
  | REdSeq c1 c2 =>
      rs_emit indent c1 ++ ";" ++ LF ++ rs_emit indent c2
  | REdLetZero v t body =>
      rs_decl_slot v t ++ LF ++
      rs_emit indent body
  | REdLetU64 v e body =>
      indent ++ "let mut " ++ rs_sanitize v ++ ": u64 = " ++ rs_sexpr e ++ ";" ++ LF ++
      rs_emit indent body
  | REdScalarSet v e =>
      indent ++ rs_sanitize v ++ " = " ++ rs_sexpr e
  | REdCall fname dest args =>
      indent ++ "unsafe { " ++ fname ++ "(" ++
        join ", " (rs_dest_arg dest ::
                   List.map rs_input_arg args ++
                   rs_call_inject_lens fname args) ++
      ") }"
  | REdIfNz e ct cf =>
      indent ++ "if (" ++ rs_sexpr e ++ ") != 0 {" ++ LF ++
      rs_emit ("    " ++ indent) ct ++ LF ++
      indent ++ "} else {" ++ LF ++
      rs_emit ("    " ++ indent) cf ++ LF ++
      indent ++ "}"
  | REdWhileNz e body =>
      indent ++ "while (" ++ rs_sexpr e ++ ") != 0 {" ++ LF ++
      rs_emit ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  | REdByteStore loc idx val =>
      indent ++ rs_sanitize loc.(loc_var) ++ "[(" ++ rs_sexpr idx ++
        ") as usize] = (" ++ rs_sexpr val ++ ") as u8"
  | REdByteLoad v loc idx =>
      indent ++ "let " ++ rs_sanitize v ++ ": u64 = " ++
        rs_sanitize loc.(loc_var) ++ "[(" ++ rs_sexpr idx ++ ") as usize] as u64"
  | REdFor v n body =>
      (* Emit a Rust for-in loop over a literal range; iteration
         variable v binds successive u64 values 0..n-1.  Note: this
         counts UP, not down, so callers should use a body that's
         insensitive to direction or precompute via REdLetU64. *)
      indent ++ "for " ++ rs_sanitize v ++ " in 0u64.." ++ nat_str n ++ "u64 {" ++ LF ++
      rs_emit ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  | REdSelect cond if_t if_f dest =>
      (* CT conditional move via mask-based merge.  The two source
         buffers are ALWAYS read; their bytes are masked and OR'd into
         dest.  No branch on [cond].  The slot type's byte count is
         determined by [dest.(loc_type)] — emitted as the loop bound.
         The iteration counter [_i] is a fresh local hidden inside
         a [{ ... }] block to avoid name collisions. *)
      indent ++ "{ let _mask: u8 = (if (" ++ rs_sexpr cond ++
        ") != 0 { 0xffu8 } else { 0x00u8 });" ++ LF ++
      indent ++ "  for _i in 0..(" ++ rs_sanitize dest.(loc_var) ++
        ".len() as usize) {" ++ LF ++
      indent ++ "    " ++ rs_sanitize dest.(loc_var) ++
        "[_i] = (" ++ rs_sanitize if_t.(loc_var) ++
        "[_i] & _mask) | (" ++ rs_sanitize if_f.(loc_var) ++
        "[_i] & !_mask);" ++ LF ++
      indent ++ "  } }"
  | REdCallN fname dests args =>
      (* Multi-output FFI: pass each dest by [as_mut_ptr], then args. *)
      indent ++ "unsafe { " ++ fname ++ "(" ++
        join ", " (List.map rs_dest_arg dests ++
                   List.map rs_input_arg args) ++
      ") }"
  | REdCallFn fname dest args =>
      (* Verified-helper call: same Rust emit as REdCall — the
         emitted Rust crate links the helper symbol; the verification
         side of the framework just tracks whether the body was
         externally axiomatized (REdCall) or Rocq-verified (REdCallFn). *)
      indent ++ "unsafe { " ++ fname ++ "(" ++
        join ", " (rs_dest_arg dest ::
                   List.map rs_input_arg args ++
                   rs_call_inject_lens fname args) ++
      ") }"
  | REdBlock body =>
      (* Scoped Rust block: { ... }.  Any [REdLetZero] decls inside
         the body have their lifetime end at the closing brace,
         freeing the corresponding stack slot.  Matches Rust's
         block-scoped variables. *)
      indent ++ "{" ++ LF ++
      rs_emit ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  end.

(* ================================================================ *)
(* §5. Function-level emission                                        *)
(* ================================================================ *)

Record rs_func_sig := {
  rfs_name   : String.string;
  rfs_params : list (String.string * tower_type_ed);
}.

Definition rs_param_decl (p : String.string * tower_type_ed) : string :=
  let '(name, t) := p in rs_sanitize name ++ ": " ++ rs_param_type t.

Definition rs_func_emit (sig : rs_func_sig) (body : rust_cmd_ed) : string :=
  "pub fn " ++ sig.(rfs_name) ++ "(" ++
    join ", " (List.map rs_param_decl sig.(rfs_params)) ++
  ") {" ++ LF ++
  rs_emit "    " body ++ ";" ++ LF ++
  "}".

(* ================================================================ *)
(* §5b. Body extraction: function_body_ed → Rust function string     *)
(* ================================================================ *)

(** A [function_body_ed] is a metafunction [located_ed → list located_ed
    → rust_cmd_ed].  To extract a concrete Rust function we need to
    fix the destination and argument signatures and feed the body with
    sentinel locator names ("out", "arg0", "arg1", ...).  *)
Record body_extract_sig := {
  bes_name      : String.string;
  bes_dest_type : tower_type_ed;
  bes_arg_types : list tower_type_ed;
  bes_body      : function_body_ed
}.

Definition rs_arg_name (i : nat) : String.string :=
  "arg" ++ nat_str i.

Definition rs_body_extract (sig : body_extract_sig) : string :=
  let dest_loc :=
    {| loc_var := "out"; loc_type := sig.(bes_dest_type) |} in
  let arg_locs :=
    mapi (fun i t => {| loc_var := rs_arg_name i; loc_type := t |})
         sig.(bes_arg_types) in
  let body := sig.(bes_body) dest_loc arg_locs in
  let rfs :=
    {| rfs_name := sig.(bes_name);
       rfs_params :=
         ("out", sig.(bes_dest_type))
         :: mapi (fun i t => (rs_arg_name i, t)) sig.(bes_arg_types) |} in
  rs_func_emit rfs body.

(** Emit a body function as an [extern "C"] function taking raw
    pointers.  This is the calling convention used by both:
      - other extracted bodies (which dispatch via [REdCallFn] sites
        that emit [unsafe { fname(out.as_mut_ptr(), arg.as_ptr()) }]);
      - the [decomposed_curve_leaves] panic-replacement wrappers in
        [leaves.rs] (which dispatch via raw pointers from the FFI
        prelude).

    Inside the body we rebind each pointer parameter to a mutable
    reference on a fixed-size array, using the SAME variable name as
    the AST.  The body's [out.as_mut_ptr()] / [arg.as_ptr()] then
    typechecks against [&mut [u8; N]] / [&[u8; N]] in the usual way. *)
Definition rs_raw_ptr_param (p : String.string * tower_type_ed) (is_dest : bool) : string :=
  let '(name, t) := p in
  match t with
  | TU64 => rs_sanitize name ++ ": u64"
  | _    => rs_sanitize name ++ "_raw: " ++
            (if is_dest then "*mut u8" else "*const u8")
  end.

(** Cast prelude line: "let var: &mut [u8; N] = unsafe { &mut *(var_raw as *mut [u8; N]) };".
    Pointer cast is via the array type; for [*const u8] we coerce
    through a [*mut] cast to get a mutable reference, since the body
    treats every slot as locally writable inside its scope.  Safety
    rests on the caller honouring the rust_cmd_ed borrow predicate
    [borrow_ok_ed], which the framework already discharges. *)
Definition rs_param_cast (p : String.string * tower_type_ed) (is_dest : bool) : string :=
  let '(name, t) := p in
  match t with
  | TU64 => ""
  | _ =>
      let arrty := rs_array_type t in
      "    let " ++ rs_sanitize name ++ ": &mut " ++ arrty ++
      " = unsafe { &mut *(" ++ rs_sanitize name ++ "_raw as *mut " ++
      arrty ++ ") };" ++ LF
  end.

Fixpoint rs_param_casts (ps : list (String.string * tower_type_ed)) (heads_done : bool) : string :=
  match ps with
  | nil => ""
  | p :: rest =>
      (if heads_done then rs_param_cast p false
       else rs_param_cast p true)
      ++ rs_param_casts rest true
  end.

Definition rs_body_extract_extern_c (sig : body_extract_sig) : string :=
  let dest_loc :=
    {| loc_var := "out"; loc_type := sig.(bes_dest_type) |} in
  let arg_locs :=
    mapi (fun i t => {| loc_var := rs_arg_name i; loc_type := t |})
         sig.(bes_arg_types) in
  let body := sig.(bes_body) dest_loc arg_locs in
  let dest_param := ("out", sig.(bes_dest_type)) in
  let arg_params := mapi (fun i t => (rs_arg_name i, t)) sig.(bes_arg_types) in
  let all_params := dest_param :: arg_params in
  let param_strs :=
    rs_raw_ptr_param dest_param true
    :: List.map (fun p => rs_raw_ptr_param p false) arg_params in
  let cast_prelude := rs_param_casts all_params false in
  "#[unsafe(no_mangle)]" ++ LF ++
  "pub unsafe extern ""C"" fn " ++ sig.(bes_name) ++ "(" ++
    join ", " param_strs ++
  ") {" ++ LF ++
  cast_prelude ++
  rs_emit "    " body ++ ";" ++ LF ++
  "}".

Fixpoint string_concat (sep : String.string) (xs : list String.string) : String.string :=
  match xs with
  | nil => ""
  | [x] => x
  | x :: xs' => x ++ sep ++ string_concat sep xs'
  end.

Definition rs_table_extract (table : list body_extract_sig) : string :=
  string_concat (LF ++ LF) (List.map rs_body_extract_extern_c table).

(** FFI prelude: unsafe extern "C" block declaring all leaf callees that
    REdCall sites name.  Mirrors [c_prelude] but in Rust syntax. *)
Definition rs_prelude : string :=
  "// Generated from rust_cmd_ed.  Avoid editing directly." ++ LF ++
  "// Verification: rust_cmd_ed → safe_cmd_correct_ed (Qed) →" ++ LF ++
  "//   to_bedrock_cmd_semantic_correct (Qed) → bedrock2 fnspec." ++ LF ++ LF ++
  "#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]" ++ LF ++ LF ++
  "unsafe extern ""C"" {" ++ LF ++
  "    fn sha512_64(out: *mut u8, msg: *const u8, len: u64);" ++ LF ++
  "    fn scalar_reduce(out: *mut u8, full: *const u8);" ++ LF ++
  "    fn scalar_muladd(out: *mut u8, r: *const u8, k: *const u8, a: *const u8);" ++ LF ++
  "    fn ed25519_compress(out: *mut u8, xyzt: *const u8);" ++ LF ++
  "    fn ed25519_decompress_R(out: *mut u8, sig: *const u8);" ++ LF ++
  "    fn ed25519_decompress_A(out: *mut u8, pk: *const u8);" ++ LF ++
  "    fn ed25519_scalarmult_base(out: *mut u8, scalar: *const u8);" ++ LF ++
  "    fn ed25519_scalarmult(out: *mut u8, scalar: *const u8, point: *const u8);" ++ LF ++
  "    fn ed25519_xyzt_add(out: *mut u8, p: *const u8, q: *const u8);" ++ LF ++
  "    fn scalar_lt_L(out: *mut u8, scalar: *const u8);" ++ LF ++
  "    fn bytes_equal_32(out: *mut u8, a: *const u8, b: *const u8);" ++ LF ++
  "    fn verify_fail(out: *mut u8);" ++ LF ++
  "    fn clamp_64(sk: *mut u8);" ++ LF ++
  "    // Region-copy helpers (slice memmoves at fixed offsets);" ++ LF ++
  "    // emitted by rust_cmd_ed for byte-region transfers." ++ LF ++
  "    fn memmove_a_from_h(out: *mut u8, h: *const u8);" ++ LF ++
  "    fn memmove_prefix_from_h(out: *mut u8, h: *const u8);" ++ LF ++
  "    fn memmove_nonce_prefix(buf: *mut u8, prefix: *const u8);" ++ LF ++
  "    fn memmove_nonce_msg(buf: *mut u8, msg: *const u8);" ++ LF ++
  "    fn memmove_chal_R(buf: *mut u8, R: *const u8);" ++ LF ++
  "    fn memmove_chal_A(buf: *mut u8, A: *const u8);" ++ LF ++
  "    fn memmove_chal_M(buf: *mut u8, M: *const u8);" ++ LF ++
  "    fn memmove_sig_R(sig: *mut u8, R: *const u8);" ++ LF ++
  "    fn memmove_R_from_sig(R: *mut u8, sig: *const u8);" ++ LF ++
  "    fn memmove_S_from_sig(S: *mut u8, sig: *const u8);" ++ LF ++
  "}" ++ LF ++ LF.

(* ================================================================ *)
(* §6. Concrete extractions: ed25519_sign and ed25519_verify           *)
(* ================================================================ *)

Definition ed25519_sign_rs_sig : rs_func_sig :=
  {| rfs_name := "ed25519_sign";
     rfs_params := [("sig_out", TBytes 64);
                    ("seed",    TBytes 32);
                    ("msg",     TBytes 4096);
                    ("msg_len", TU64)] |}.

Definition ed25519_verify_rs_sig : rs_func_sig :=
  {| rfs_name := "ed25519_verify";
     (* Parameter names must match the var names used inside
        ed25519_verify_rs (REdCall args) so the emitted Rust resolves;
        rs_sanitize handles the [pub] keyword via [r#pub].

        2026-05-12: the accept/reject byte is now exposed via a caller-
        supplied [result_out] slot rather than an internal local — halves
        the cost of [verify] in the cargo wrapper (no more recompute). *)
     rfs_params := [("result_out", TBytes 1);
                    ("sig_in", TBytes 64);
                    ("pub",    TBytes 32);
                    ("msg",    TBytes 4096);
                    ("msg_len", TU64)] |}.

Definition ed25519_sign_rs_string : string :=
  rs_prelude ++ rs_func_emit ed25519_sign_rs_sig ed25519_sign_rs.

Definition ed25519_verify_rs_string : string :=
  rs_prelude ++ rs_func_emit ed25519_verify_rs_sig ed25519_verify_rs.

(* ================================================================ *)
(* §7. Rust target AST + verified factorization (gap #4)              *)
(* ================================================================ *)

(** Typed AST for the subset of Rust we emit.  Per-op constructors
    keep the pretty-printer trivially structural so [rs_emit] equals
    [rs_pretty_stmt indent ∘ cmd_to_ast] by direct induction. *)
Inductive rust_expr_ast : Type :=
| RAVar          (x : String.string)
| RALitU64       (z : Z)
| RAWrappingAdd  (a b : rust_expr_ast)
| RAWrappingSub  (a b : rust_expr_ast)
| RAWrappingMul  (a b : rust_expr_ast)
| RAShr          (a b : rust_expr_ast)
| RAAnd          (a b : rust_expr_ast)
| RALt           (a b : rust_expr_ast).   (** wraps in `(... < ...) as u64` *)

Inductive rust_stmt_ast : Type :=
| RSSkip                                        (* indent ++ "()" *)
| RSSeq        (a b : rust_stmt_ast)            (* a ++ ";" ++ LF ++ b *)
| RSLetZero    (var : String.string) (t : tower_type_ed) (body : rust_stmt_ast)
| RSLetU64     (var : String.string) (e : rust_expr_ast) (body : rust_stmt_ast)
| RSAssign     (var : String.string) (e : rust_expr_ast)
| RSCall       (fname : String.string) (args : list String.string)
                              (** args are pre-rendered argument strings *)
| RSIfNz       (cond : rust_expr_ast) (ct cf : rust_stmt_ast)
| RSWhileNz    (cond : rust_expr_ast) (body : rust_stmt_ast)
| RSByteStore  (v : String.string) (ix val : rust_expr_ast)
| RSByteLoad   (dst v : String.string) (ix : rust_expr_ast)
| RSFor        (v : String.string) (n : nat) (body : rust_stmt_ast)
| RSSelect     (cond : rust_expr_ast)
               (if_t if_f dest : String.string)
| RSCallN      (fname : String.string) (args : list String.string)
                              (** Multi-output: dests + args pre-rendered. *)
| RSCallFn     (fname : String.string) (args : list String.string)
                              (** Verified-helper: same rendering as RSCall. *)
| RSBlock      (body : rust_stmt_ast).
                              (** Scoped block: { body }.  Body's [RSLetZero]
                                  decls have their lifetime end at the brace. *)

(** sexpr_ed → rust_expr_ast. *)
Fixpoint sexpr_to_ast (e : sexpr_ed) : rust_expr_ast :=
  match e with
  | SVar x   => RAVar (rs_sanitize x)
  | SLit z   => RALitU64 z
  | SAdd a b => RAWrappingAdd (sexpr_to_ast a) (sexpr_to_ast b)
  | SSub a b => RAWrappingSub (sexpr_to_ast a) (sexpr_to_ast b)
  | SMul a b => RAWrappingMul (sexpr_to_ast a) (sexpr_to_ast b)
  | SShr a b => RAShr         (sexpr_to_ast a) (sexpr_to_ast b)
  | SAnd a b => RAAnd         (sexpr_to_ast a) (sexpr_to_ast b)
  | SLt  a b => RALt          (sexpr_to_ast a) (sexpr_to_ast b)
  end.

(** rust_cmd_ed → rust_stmt_ast. *)
Fixpoint cmd_to_ast (c : rust_cmd_ed) : rust_stmt_ast :=
  match c with
  | REdSkip => RSSkip
  | REdSeq c1 c2 => RSSeq (cmd_to_ast c1) (cmd_to_ast c2)
  | REdLetZero v t body =>
      RSLetZero v t (cmd_to_ast body)
  | REdLetU64 v e body =>
      RSLetU64 (rs_sanitize v) (sexpr_to_ast e) (cmd_to_ast body)
  | REdScalarSet v e =>
      RSAssign (rs_sanitize v) (sexpr_to_ast e)
  | REdCall fname dest args =>
      RSCall fname (rs_dest_arg dest ::
                    List.map rs_input_arg args ++
                    rs_call_inject_lens fname args)
  | REdIfNz e ct cf =>
      RSIfNz (sexpr_to_ast e) (cmd_to_ast ct) (cmd_to_ast cf)
  | REdWhileNz e body =>
      RSWhileNz (sexpr_to_ast e) (cmd_to_ast body)
  | REdByteStore loc idx val =>
      RSByteStore (rs_sanitize loc.(loc_var)) (sexpr_to_ast idx) (sexpr_to_ast val)
  | REdByteLoad v loc idx =>
      RSByteLoad (rs_sanitize v) (rs_sanitize loc.(loc_var)) (sexpr_to_ast idx)
  | REdFor v n body =>
      RSFor (rs_sanitize v) n (cmd_to_ast body)
  | REdSelect cond if_t if_f dest =>
      RSSelect (sexpr_to_ast cond)
               (rs_sanitize if_t.(loc_var))
               (rs_sanitize if_f.(loc_var))
               (rs_sanitize dest.(loc_var))
  | REdCallN fname dests args =>
      RSCallN fname (List.map rs_dest_arg dests ++
                     List.map rs_input_arg args)
  | REdCallFn fname dest args =>
      RSCallFn fname (rs_dest_arg dest ::
                      List.map rs_input_arg args ++
                      rs_call_inject_lens fname args)
  | REdBlock body =>
      RSBlock (cmd_to_ast body)
  end.

(** **Concrete** pretty-printer for expressions, mirroring
    [rs_sexpr] case-by-case. *)
Fixpoint rs_pretty_expr (e : rust_expr_ast) : String.string :=
  match e with
  | RAVar x          => x
  | RALitU64 z       => z_str z ++ "u64"
  | RAWrappingAdd a b => "(" ++ rs_pretty_expr a ++ ".wrapping_add(" ++ rs_pretty_expr b ++ "))"
  | RAWrappingSub a b => "(" ++ rs_pretty_expr a ++ ".wrapping_sub(" ++ rs_pretty_expr b ++ "))"
  | RAWrappingMul a b => "(" ++ rs_pretty_expr a ++ ".wrapping_mul(" ++ rs_pretty_expr b ++ "))"
  | RAShr a b         => "(" ++ rs_pretty_expr a ++ " >> " ++ rs_pretty_expr b ++ ")"
  | RAAnd a b         => "(" ++ rs_pretty_expr a ++ " & "  ++ rs_pretty_expr b ++ ")"
  | RALt  a b         => "((" ++ rs_pretty_expr a ++ " < " ++ rs_pretty_expr b ++ ") as u64)"
  end.

(** **Concrete** pretty-printer for statements, mirroring [rs_emit]. *)
Fixpoint rs_pretty_stmt (indent : String.string) (s : rust_stmt_ast) : String.string :=
  match s with
  | RSSkip => indent ++ "()"
  | RSSeq a b =>
      rs_pretty_stmt indent a ++ ";" ++ LF ++ rs_pretty_stmt indent b
  | RSLetZero v t body =>
      rs_decl_slot v t ++ LF ++ rs_pretty_stmt indent body
  | RSLetU64 v e body =>
      indent ++ "let mut " ++ v ++ ": u64 = " ++ rs_pretty_expr e ++ ";" ++ LF ++
      rs_pretty_stmt indent body
  | RSAssign v e =>
      indent ++ v ++ " = " ++ rs_pretty_expr e
  | RSCall fname args =>
      indent ++ "unsafe { " ++ fname ++ "(" ++ join ", " args ++ ") }"
  | RSIfNz cond ct cf =>
      indent ++ "if (" ++ rs_pretty_expr cond ++ ") != 0 {" ++ LF ++
      rs_pretty_stmt ("    " ++ indent) ct ++ LF ++
      indent ++ "} else {" ++ LF ++
      rs_pretty_stmt ("    " ++ indent) cf ++ LF ++
      indent ++ "}"
  | RSWhileNz cond body =>
      indent ++ "while (" ++ rs_pretty_expr cond ++ ") != 0 {" ++ LF ++
      rs_pretty_stmt ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  | RSByteStore v ix val =>
      indent ++ v ++ "[(" ++ rs_pretty_expr ix ++
        ") as usize] = (" ++ rs_pretty_expr val ++ ") as u8"
  | RSByteLoad dst v ix =>
      indent ++ "let " ++ dst ++ ": u64 = " ++
        v ++ "[(" ++ rs_pretty_expr ix ++ ") as usize] as u64"
  | RSFor v n body =>
      indent ++ "for " ++ v ++ " in 0u64.." ++ nat_str n ++ "u64 {" ++ LF ++
      rs_pretty_stmt ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  | RSSelect cond if_t if_f dest =>
      indent ++ "{ let _mask: u8 = (if (" ++ rs_pretty_expr cond ++
        ") != 0 { 0xffu8 } else { 0x00u8 });" ++ LF ++
      indent ++ "  for _i in 0..(" ++ dest ++ ".len() as usize) {" ++ LF ++
      indent ++ "    " ++ dest ++ "[_i] = (" ++ if_t ++
        "[_i] & _mask) | (" ++ if_f ++ "[_i] & !_mask);" ++ LF ++
      indent ++ "  } }"
  | RSCallN fname args =>
      indent ++ "unsafe { " ++ fname ++ "(" ++ join ", " args ++ ") }"
  | RSCallFn fname args =>
      indent ++ "unsafe { " ++ fname ++ "(" ++ join ", " args ++ ") }"
  | RSBlock body =>
      indent ++ "{" ++ LF ++
      rs_pretty_stmt ("    " ++ indent) body ++ LF ++
      indent ++ "}"
  end.

(** Helper: pretty-printing expressions agrees with [rs_sexpr]. *)
Lemma rs_pretty_expr_sexpr_to_ast :
  forall e, rs_pretty_expr (sexpr_to_ast e) = rs_sexpr e.
Proof.
  induction e; cbn; try reflexivity; rewrite ?IHe1, ?IHe2; reflexivity.
Qed.

(** **Factorization theorem (gap-#4 closed)**: the existing string
    emitter agrees with the AST-then-pretty-print path. *)
Theorem rs_emit_factors :
  forall c indent,
    rs_pretty_stmt indent (cmd_to_ast c) = rs_emit indent c.
Proof.
  induction c; intros indent; cbn;
    repeat rewrite rs_pretty_expr_sexpr_to_ast;
    rewrite ?IHc, ?IHc1, ?IHc2;
    reflexivity.
Qed.

(** **Corollary**: top-level emission factors via the AST. *)
Definition rs_func_emit_via_ast (sig : rs_func_sig) (body : rust_cmd_ed) : string :=
  "pub fn " ++ sig.(rfs_name) ++ "(" ++
    join ", " (List.map rs_param_decl sig.(rfs_params)) ++
  ") {" ++ LF ++
  rs_pretty_stmt "    " (cmd_to_ast body) ++ ";" ++ LF ++
  "}".

Theorem rs_func_emit_factors :
  forall sig body,
    rs_func_emit_via_ast sig body = rs_func_emit sig body.
Proof.
  intros; unfold rs_func_emit, rs_func_emit_via_ast.
  rewrite (rs_emit_factors body). reflexivity.
Qed.

(* ================================================================ *)
(* §8. Strong correctness theorem statement (gap #3 architecture)     *)
(* ================================================================ *)

(** The current correctness theorem [rust_exec_ed_preserves_wf]
    (in SafeRustEd25519Sim.v) gives only [rs_well_formed rs2].
    Real Ed25519 correctness requires a functional postcondition:
    after [ed25519_sign_rs] runs with seed [s] and message [m], the
    resulting [sig_out] satisfies the Edwards signature equation.

    To state this we need:
    - [decode_compressed_point : list byte → option Edwards.point]
    - [scalar_clamp_decode : list byte → Z]  (RFC 8032 clamp)
    - [Hsha512 : sha512 spec]  — already exists as fnspec axiom
    - [valid_signature : seed → msg → sig → Prop]  — Edwards eq
    - composition of per-callee strong specs
      (ed25519_scalarmult_base correctness, scalar_reduce mod L,
       ed25519_compress projection)

    The theorem statement is below as an [Axiom] (skeleton); the
    accompanying invariant requires a 256-iter loop invariant for
    the scalarmult call's internal ladder.  The work splits cleanly
    along callee bridges:
      strong_sha512_bridge : strong post for sha512_64
      strong_scalar_reduce_bridge : output ≡ input mod L
      strong_scalarmult_base_bridge : decode (out) = a · B
      strong_ed25519_compress_bridge : decode (out) = decode (in)
      strong_scalar_muladd_bridge : output = r + k·a mod L
    plus a top-level composition lemma.

    Each per-callee bridge already has a [_concrete] Qed lemma
    (RemainingBridges.v) that gives [rs_well_formed]; the strong
    version replaces the post with the Edwards-side equation. *)

Section StrongCorrectness.

Variable seed : list nat.        (* Coq nat-bytes for now *)
Variable msg  : list nat.

(** Placeholder predicate: [sig] is a valid Ed25519 signature on
    [msg] under public key derived from [seed].  Concrete definition
    requires importing the Ed25519 abstract spec (Edwards point eq,
    cofactor handling, RFC 8032 clamp).  Shown as a Parameter so
    downstream code can [Existing Instance] a concrete realization. *)
Parameter ed25519_valid_signature : list nat -> list nat -> list nat -> Prop.

(** **Strong post sketch.**  When the rust_cmd_ed protocol completes
    starting from a state where seed and msg are loaded into the
    typed slots, the resulting sig_out slot contains a valid
    Ed25519 signature.

    Skeleton: parameters [post_after_run] and [extract_sig] would
    pull the byte view of [sig_out] from the final rust_state_ed.
    Both are mechanical to define once [Sign_Verify_RustCmd.v]'s
    state-loading helpers are available. *)

Axiom ed25519_sign_strong_correctness :
  forall (rs1 rs2 : rust_state_ed),
    True ->     (* seed and msg loaded into rs1's typed slots *)
    True ->     (* per-callee strong bridges satisfied *)
    rust_exec_ed (fun _ _ _ _ _ => True) (fun _ _ _ _ _ => True) nil
                 ed25519_sign_rs rs1 rs2 ->
    True.       (* placeholder for: ed25519_valid_signature seed msg (sig_of rs2) *)

End StrongCorrectness.

(** Path forward (concrete next steps for #3):

    Step 1 — define [extract_bytes : rust_state_ed → var → list byte]
    that pulls a TBytes slot's contents.

    Step 2 — define [load_inputs : rust_state_ed → list byte → list byte → Prop]
    saying seed is at v_seed, msg is at v_msg with the right lengths.

    Step 3 — strengthen each [bridge_*_concrete] from rs_well_formed
    to its functional spec.  RemainingBridges.v already has the
    fnspec connection; the strong bridge is fnspec → rust_exec_ed
    post predicate, mirroring callee_post_compatible.

    Step 4 — top-level induction over [ed25519_sign_rs]'s 21 REdCall
    sites; each step composes a strong bridge with the running
    state.  Length: roughly 600-800 LoC mechanized; estimated
    1-2 weeks of focused proof work. *)

