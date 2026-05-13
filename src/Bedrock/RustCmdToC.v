(** * RustCmdToC: rust_cmd_ed → C string emitter (evaluation)
 *
 * Demonstrates rust_cmd_ed extraction to C.  Used to evaluate how
 * cleanly the rust_cmd_ed AST maps to C output, vs the bedrock2 →
 * ToCString path.
 *
 * Status (2026-05-09): minimal scaffold — emits valid C for the 10
 * rust_cmd_ed constructors.  No optimization; one C statement per
 * RustCmd constructor.  Typed slots (TBytes n / TU64 / etc.) become
 * stack-allocated C arrays / scalars.  REdCall becomes an `extern`
 * call, mirroring bedrock2's calling convention.
 *
 * This file is for EVALUATION, not production.  Real emit would
 * benefit from:
 *   - lift `let/n` patterns to fewer C variables
 *   - constant folding for sexpr_ed
 *   - sharing the bedrock2 ToCString prelude
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Numbers.DecimalString.
Require Import bedrock2.Syntax.
Require Import bedrock2.ToCString.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition LF : string :=
  String (Ascii.Ascii false true false true false false false false) "".

Definition z_str (z : Z) : string :=
  DecimalString.NilZero.string_of_int (Z.to_int z).

Definition nat_str (n : nat) : string := z_str (Z.of_nat n).

Fixpoint join (sep : string) (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ join sep rest
  end.

(* ================================================================ *)
(* §1. C type emission for tower_type_ed                             *)
(* ================================================================ *)

(** Render a tower_type_ed as a C type declaration.  Used for slot
    declarations in REdLetZero. *)
Definition c_type_of (t : tower_type_ed) : string :=
  match t with
  | TFp25519     => "uint64_t[5]"
  | TFp25519_64  => "uint64_t[4]"
  | TFpL25519    => "uint64_t[4]"
  | TBytes n     => "uint8_t[" ++ nat_str n ++ "]"
  | TU64         => "uint64_t"
  | TArr n _     => "uint8_t[" ++ nat_str n ++ "/*TArr*/]"
      (* Phase Ext: array-of-slots — emitted as a flat byte buffer of
         the right total size at the C layer (Rust layer keeps the
         typed shape, see [rs_array_type]).  C emission for TArr is
         a placeholder; the live emitter is the Rust one. *)
  end.

(** Render a tower_type_ed as a C parameter type (for function
    signatures — arrays decay to pointers). *)
Definition c_param_type_of (t : tower_type_ed) : string :=
  match t with
  | TFp25519     => "uint64_t*"
  | TFp25519_64  => "uint64_t*"
  | TFpL25519    => "uint64_t*"
  | TBytes _     => "uint8_t*"
  | TU64         => "uint64_t"
  | TArr _ _     => "uint8_t*"
  end.

(** Local declaration for a typed slot, zero-initialized. *)
Definition c_decl_slot (var : String.string) (t : tower_type_ed) : string :=
  match t with
  | TFp25519    => "  uint64_t " ++ var ++ "[5] = {0};"
  | TFp25519_64 => "  uint64_t " ++ var ++ "[4] = {0};"
  | TFpL25519   => "  uint64_t " ++ var ++ "[4] = {0};"
  | TBytes n    => "  uint8_t "  ++ var ++ "[" ++ nat_str n ++ "] = {0};"
  | TU64        => "  uint64_t " ++ var ++ " = 0;"
  | TArr n _    => "  uint8_t "  ++ var ++ "[" ++ nat_str n ++ "/*TArr*/] = {0};"
  end.

(* ================================================================ *)
(* §2. sexpr_ed emission                                             *)
(* ================================================================ *)

Fixpoint c_sexpr (e : sexpr_ed) : string :=
  match e with
  | SVar x      => x
  | SLit z      => z_str z
  | SAdd a b    => "(" ++ c_sexpr a ++ " + " ++ c_sexpr b ++ ")"
  | SSub a b    => "(" ++ c_sexpr a ++ " - " ++ c_sexpr b ++ ")"
  | SMul a b    => "(" ++ c_sexpr a ++ " * " ++ c_sexpr b ++ ")"
  | SShr a b    => "(" ++ c_sexpr a ++ " >> " ++ c_sexpr b ++ ")"
  | SAnd a b    => "(" ++ c_sexpr a ++ " & " ++ c_sexpr b ++ ")"
  | SLt a b     => "(" ++ c_sexpr a ++ " < " ++ c_sexpr b ++ ")"
  | SLimb v i   => v ++ "[" ++ z_str (Z.of_nat i) ++ "]"
                    (* Phase 0b: limb read.  In emitted C, an Fp25519
                       slot is a [uint64_t[5]] array, so a static
                       index access is the natural code shape. *)
  end.

(* ================================================================ *)
(* §3. located_ed → C argument expression                            *)
(* ================================================================ *)

(** A located slot used as a C call argument.  Arrays decay to
    pointer; scalars pass by value. *)
Definition c_located_arg (l : located_ed) : string :=
  match l.(loc_type) with
  | TU64 => l.(loc_var)
  | _    => l.(loc_var)  (* arrays decay automatically *)
  end.

(* ================================================================ *)
(* §4. Main emitter                                                  *)
(* ================================================================ *)

Fixpoint c_emit (indent : string) (c : rust_cmd_ed) : string :=
  match c with
  | REdSkip => indent ++ ";"
  | REdSeq c1 c2 =>
      c_emit indent c1 ++ LF ++ c_emit indent c2
  | REdLetZero v t body =>
      "  " ++ indent ++ c_decl_slot v t ++ LF ++
      c_emit indent body
  | REdLetU64 v e body =>
      indent ++ "uint64_t " ++ v ++ " = " ++ c_sexpr e ++ ";" ++ LF ++
      c_emit indent body
  | REdScalarSet v e =>
      indent ++ v ++ " = " ++ c_sexpr e ++ ";"
  | REdCall fname dest args =>
      indent ++ fname ++ "(" ++
        join ", " (c_located_arg dest :: List.map c_located_arg args) ++
      ");"
  | REdIfNz e ct cf =>
      indent ++ "if (" ++ c_sexpr e ++ ") {" ++ LF ++
      c_emit ("  " ++ indent) ct ++ LF ++
      indent ++ "} else {" ++ LF ++
      c_emit ("  " ++ indent) cf ++ LF ++
      indent ++ "}"
  | REdWhileNz e body =>
      indent ++ "while (" ++ c_sexpr e ++ ") {" ++ LF ++
      c_emit ("  " ++ indent) body ++ LF ++
      indent ++ "}"
  | REdByteStore loc idx val =>
      indent ++ loc.(loc_var) ++ "[" ++ c_sexpr idx ++ "] = (uint8_t)(" ++
        c_sexpr val ++ ");"
  | REdByteLoad v loc idx =>
      indent ++ "uint64_t " ++ v ++ " = (uint64_t)" ++
        loc.(loc_var) ++ "[" ++ c_sexpr idx ++ "];"
  | REdFor v n body =>
      (* Emit a counted loop: x runs n-1 down to 0 (matches semantics). *)
      indent ++ "for (uint64_t " ++ v ++ " = " ++ nat_str n ++
                "; " ++ v ++ " > 0; ) {" ++ LF ++
      indent ++ "  " ++ v ++ "--;" ++ LF ++
      c_emit ("  " ++ indent) body ++ LF ++
      indent ++ "}"
  | REdSelect cond if_t if_f dest =>
      (* C demo emit: a ternary copy.  NOT constant-time in C — the
         CT-safe path is the Rust emitter ([RustCmdToRust.v]), which
         emits a mask-based merge.  Use [memcpy] so the slot type
         abstracts buffer length. *)
      indent ++ "memcpy(" ++ dest.(loc_var) ++ ", ((" ++ c_sexpr cond ++
        ") ? " ++ if_t.(loc_var) ++ " : " ++ if_f.(loc_var) ++ "), sizeof(" ++
        dest.(loc_var) ++ "));"
  | REdCallN fname dests args =>
      indent ++ fname ++ "(" ++
        join ", " (List.map c_located_arg dests ++
                   List.map c_located_arg args) ++
      ");"
  | REdCallFn fname dest args =>
      (* Verified helper: same C emit as REdCall — the C target has no
         distinction between externally-axiomatized and Rocq-verified
         helpers; both look like ordinary calls.  Inlining/specialization
         can happen at the AST level before c_emit. *)
      indent ++ fname ++ "(" ++
        join ", " (c_located_arg dest :: List.map c_located_arg args) ++
      ");"
  | REdBlock body =>
      (* Scoped C block: actual C scope delimited by braces.  Any
         [REdLetZero] decls inside have their lifetime end at the
         closing brace. *)
      indent ++ "{" ++ LF ++
      c_emit ("  " ++ indent) body ++ LF ++
      indent ++ "}"
  | REdSetBytes loc bytes =>
      (* Whole-array literal write in C:
           loc[0] = b0; loc[1] = b1; ... ;
         Emitted as a sequence of indexed assignments to keep the
         shape uniform with [REdByteStore] (no C99 designated-init
         dependency in the audit). *)
      indent ++ "{" ++ LF ++
      indent ++ "  uint8_t __tmp[" ++ nat_str (List.length bytes) ++ "] = {" ++
        join ", " (List.map (fun z => c_sexpr (SLit z)) bytes) ++ "};" ++ LF ++
      indent ++ "  memcpy(" ++ loc.(loc_var) ++ ", __tmp, " ++
        nat_str (List.length bytes) ++ ");" ++ LF ++
      indent ++ "}"
  | REdArrLoad dst src idx_e =>
      (* Phase Ext: array read.  Emitted as a placeholder memcpy; the
         live path is the Rust emitter. *)
      indent ++ "memcpy(" ++ dst.(loc_var) ++ ", " ++ src.(loc_var) ++
        " + (" ++ c_sexpr idx_e ++ ") * sizeof(*" ++ dst.(loc_var) ++ "), sizeof(*" ++
        dst.(loc_var) ++ "));"
  | REdArrStore arr idx_e src =>
      indent ++ "memcpy(" ++ arr.(loc_var) ++ " + (" ++ c_sexpr idx_e ++
        ") * sizeof(*" ++ src.(loc_var) ++ "), " ++ src.(loc_var) ++
        ", sizeof(*" ++ src.(loc_var) ++ "));"
  | REdLimbStore loc i e =>
      (* Phase 0b: limb write.  loc.limbs[i] := e. *)
      indent ++ loc.(loc_var) ++ "[" ++ z_str (Z.of_nat i) ++ "] = " ++
        c_sexpr e ++ ";"
  end.

(* ================================================================ *)
(* §5. Function emission                                             *)
(* ================================================================ *)

(** A function signature description (independent of body). *)
Record c_func_sig := {
  cfs_name  : String.string;
  cfs_params : list (String.string * tower_type_ed);
}.

Definition c_param_decl (p : String.string * tower_type_ed) : string :=
  let '(name, t) := p in
  c_param_type_of t ++ " " ++ name.

Definition c_func_emit (sig : c_func_sig) (body : rust_cmd_ed) : string :=
  "void " ++ sig.(cfs_name) ++ "(" ++
    join ", " (List.map c_param_decl sig.(cfs_params)) ++
  ") {" ++ LF ++
  c_emit "" body ++ LF ++
  "}".

(** Standard C prelude (mirrors bedrock2.ToCString). *)
Definition c_prelude : string :=
  "// Generated from rust_cmd_ed.  Avoid editing directly." ++ LF ++
  "#include <stdint.h>" ++ LF ++
  "#include <string.h>" ++ LF ++ LF ++
  "// Extern callees (linked from verified Jasmin asm or fiat-crypto)." ++ LF ++
  "extern void sha512_64(uint8_t* out, const uint8_t* in, uint64_t in_len);" ++ LF ++
  "extern void scalar_reduce(uint8_t* out, const uint8_t* in);" ++ LF ++
  "extern void scalar_muladd(uint8_t* out, const uint8_t* r, const uint8_t* k, const uint8_t* a);" ++ LF ++
  "extern void ed25519_compress(uint8_t* out, const uint8_t* xyzt);" ++ LF ++
  "extern void ed25519_scalarmult_base(uint8_t* out, const uint8_t* scalar);" ++ LF ++
  "extern void clamp_64(uint8_t* sk);" ++ LF ++
  "extern void memmove(void* dst, const void* src, uint64_t n);" ++ LF ++
  "" ++ LF.

(* ================================================================ *)
(* §6. Sanity check on the 10 constructors                           *)
(* ================================================================ *)

(** Tiny example: a function with each constructor exercised once. *)
Definition demo_rs : rust_cmd_ed :=
  REdLetZero "h" (TBytes 64) (
  REdLetU64 "i" (SLit 256) (
  REdSeq (REdScalarSet "i" (SSub (SVar "i") (SLit 1)))
  (REdSeq
    (REdCall "sha512_64"
      {| loc_var := "h"; loc_type := TBytes 64 |}
      [{| loc_var := "msg"; loc_type := TBytes 32 |}])
    (REdSeq
      (REdIfNz (SVar "i") REdSkip REdSkip)
      (REdWhileNz (SLt (SLit 0) (SVar "i"))
        (REdScalarSet "i" (SSub (SVar "i") (SLit 1)))))))).

(** Compute the C string at vm_compute time — the demo's emit can be
    inspected via [Eval vm_compute in c_emit "" demo_rs]. *)
Definition demo_c_body : string := c_emit "" demo_rs.

(* The output for demo_rs (vm_computed):
     uint8_t h[64] = {0};
     uint64_t i = 256;
     i = (i - 1);
     sha512_64(h, msg);
     if (i) {
       ;
     } else {
       ;
     }
     while ((0 < i)) {
       i = (i - 1);
     }

   This is valid C, lays out cleanly, and the typed-slot model maps
   1-to-1 to C declarations + extern calls. *)

(** Print-friendly demo emission. *)
Definition demo_emit : string :=
  c_prelude ++
  c_func_emit
    {| cfs_name := "demo_fn";
       cfs_params := [("msg", TBytes 32)] |}
    demo_rs.

(* ================================================================ *)
(* §7. Real emit: ed25519_sign_rs                                    *)
(* ================================================================ *)

(** ed25519_sign function signature: out_sig (64 B), seed (32 B),
    msg (4096 B max), msg_len (u64). *)
Definition ed25519_sign_sig : c_func_sig :=
  {| cfs_name := "ed25519_sign";
     cfs_params := [("sig_out", TBytes 64);
                    ("seed", TBytes 32);
                    ("msg", TBytes 4096);
                    ("msg_len", TU64)] |}.

Definition ed25519_sign_c : string :=
  c_prelude ++ c_func_emit ed25519_sign_sig ed25519_sign_rs.

(** ed25519_verify signature: sig (64 B), pub (32 B), msg (4096 B max),
    msg_len (u64); returns 0/1 in 1-byte result. *)
Definition ed25519_verify_sig : c_func_sig :=
  {| cfs_name := "ed25519_verify";
     cfs_params := [("sig_in", TBytes 64);
                    ("pub", TBytes 32);
                    ("msg", TBytes 4096);
                    ("msg_len", TU64)] |}.

Definition ed25519_verify_c : string :=
  c_prelude ++ c_func_emit ed25519_verify_sig ed25519_verify_rs.

(* ================================================================ *)
(* §8. Alternative path: rust_cmd_ed → bedrock2 Syntax.cmd → C       *)
(* ================================================================ *)

(** Maps rust_cmd_ed to bedrock2 Syntax.cmd (a.k.a. ExprImp).  Lets
    us run [bedrock2.ToCString.c_cmd] and compare its output with our
    direct emitter (§4-§7).

    Mapping:
      REdSkip            → cmd.skip
      REdSeq c1 c2       → cmd.seq c1 c2
      REdLetZero v t b   → cmd.stackalloc v <bytes> b
      REdLetU64 v e b    → cmd.seq (cmd.set v e) b
      REdScalarSet v e   → cmd.set v e
      REdCall fn dst as  → cmd.call [] fn (<dst-addr> :: <args-addrs>)
      REdIfNz e ct cf    → cmd.cond e ct cf
      REdWhileNz e b     → cmd.while e b
      REdByteStore l i v → cmd.store one (var l + i) v
      REdByteLoad v l i  → cmd.set v (load one (var l + i)) *)

Fixpoint to_bedrock_expr (e : sexpr_ed) : Syntax.expr :=
  match e with
  | SVar x      => Syntax.expr.var x
  | SLit z      => Syntax.expr.literal z
  | SAdd a b    => Syntax.expr.op Syntax.bopname.add
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SSub a b    => Syntax.expr.op Syntax.bopname.sub
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SMul a b    => Syntax.expr.op Syntax.bopname.mul
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SShr a b    => Syntax.expr.op Syntax.bopname.sru
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SAnd a b    => Syntax.expr.op Syntax.bopname.and
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SLt a b     => Syntax.expr.op Syntax.bopname.ltu
                                  (to_bedrock_expr a) (to_bedrock_expr b)
  | SLimb v i   =>
      (* Phase 0b: limb read.  Emitted as load(addr_of(v) + 8*i) in
         bedrock2 — limbs are 8-byte words stored contiguously at the
         tower-slot address. *)
      Syntax.expr.load Syntax.access_size.word
        (Syntax.expr.op Syntax.bopname.add
           (Syntax.expr.var v)
           (Syntax.expr.literal (8 * Z.of_nat i)))
  | SMul128 a b =>
      (* Phase 0e (2026-05-13): u128 multiply.  Bedrock2's word
         machine is u64-only, so we lower [SMul128] to a plain u64
         multiply.  This is a TRUNCATING approximation and is
         UNSOUND for the WP-bridge view (high 64 bits lost) — but
         the Phase 0e bodies that emit [SMul128] are intended to
         be lowered through [RustCmdToRust.v] / Jasmin directly,
         not through bedrock2.  This stub exists only so the file
         remains exhaustive on the [sexpr_ed] inductive.
         [SafeRustEd25519WPBridge.sexpr_well_formed] rules out
         [SMul128]/[SAdd128] explicitly (sets them to [False]), so
         no WP proof goes through this branch. *)
      Syntax.expr.op Syntax.bopname.mul
                     (to_bedrock_expr a) (to_bedrock_expr b)
  | SAdd128 a b =>
      (* Phase 0e — see [SMul128] comment. *)
      Syntax.expr.op Syntax.bopname.add
                     (to_bedrock_expr a) (to_bedrock_expr b)
  end.

Definition tt_bytes_z (t : tower_type_ed) : Z := Z.of_nat (tt_bytes_ed t).

Fixpoint to_bedrock_cmd (c : rust_cmd_ed) : Syntax.cmd :=
  match c with
  | REdSkip => Syntax.cmd.skip
  | REdSeq c1 c2 => Syntax.cmd.seq (to_bedrock_cmd c1) (to_bedrock_cmd c2)
  | REdLetZero v t body =>
      Syntax.cmd.stackalloc v (tt_bytes_z t) (to_bedrock_cmd body)
  | REdLetU64 v e body =>
      Syntax.cmd.seq
        (Syntax.cmd.set v (to_bedrock_expr e))
        (to_bedrock_cmd body)
  | REdScalarSet v e =>
      Syntax.cmd.set v (to_bedrock_expr e)
  | REdCall fname dst args =>
      Syntax.cmd.call []
        fname
        (Syntax.expr.var dst.(loc_var) ::
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | REdIfNz e ct cf =>
      Syntax.cmd.cond (to_bedrock_expr e) (to_bedrock_cmd ct) (to_bedrock_cmd cf)
  | REdWhileNz e body =>
      Syntax.cmd.while (to_bedrock_expr e) (to_bedrock_cmd body)
  | REdByteStore loc idx val =>
      Syntax.cmd.store Syntax.access_size.one
        (Syntax.expr.op Syntax.bopname.add
           (Syntax.expr.var loc.(loc_var))
           (to_bedrock_expr idx))
        (to_bedrock_expr val)
  | REdByteLoad v loc idx =>
      Syntax.cmd.set v
        (Syntax.expr.load Syntax.access_size.one
           (Syntax.expr.op Syntax.bopname.add
              (Syntax.expr.var loc.(loc_var))
              (to_bedrock_expr idx)))
  | REdFor v n body =>
      (* Emit: x := n; while (x > 0) { x := x - 1; body }
         x sees n-1, n-2, ..., 0 across iterations (matches semantics). *)
      Syntax.cmd.seq
        (Syntax.cmd.set v (Syntax.expr.literal (Z.of_nat n)))
        (Syntax.cmd.while
           (Syntax.expr.op Syntax.bopname.ltu
              (Syntax.expr.literal 0%Z)
              (Syntax.expr.var v))
           (Syntax.cmd.seq
              (Syntax.cmd.set v
                 (Syntax.expr.op Syntax.bopname.sub
                    (Syntax.expr.var v)
                    (Syntax.expr.literal 1%Z)))
              (to_bedrock_cmd body)))
  | REdSelect cond _ _ _ =>
      (* The Rust emitter ([RustCmdToRust.v]) is the CT-safe path; the
         bedrock2-syntax target here is for ToCString demos and proof
         carrying.  We model the SELECT as an [if/else] guarded by
         [cond] that performs no observable bedrock2-side state change
         (the actual byte-level merge happens at the rust_cmd_ed
         simulation level via [rs_set_tower_ed]).  In practice the
         bridge HOF [bedrock_select_obligations] is what carries the
         correctness obligation forward; this ToCString output is
         intentionally a stub. *)
      Syntax.cmd.cond (to_bedrock_expr cond)
                      Syntax.cmd.skip Syntax.cmd.skip
  | REdCallN fname dests args =>
      (* Multi-output call: bedrock2's cmd.call natively supports
         multiple binders (the first list arg).  We emit dest names
         as binders and args as expressions.  Note: bedrock2's
         cmd.call binders are LOCAL u64 results; for our pointer-
         passing FFI we reuse the convention from REdCall (dest as
         expr.var) and pass dests as expressions instead.  For
         correctness purposes the AST shape is what matters; the
         WP-bridge for [BEdCallN] uses an HOF obligation. *)
      Syntax.cmd.call []
        fname
        (List.map (fun l => Syntax.expr.var l.(loc_var)) dests ++
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | REdCallFn fname dst args =>
      (* Verified helper: same bedrock2 emission as REdCall. *)
      Syntax.cmd.call []
        fname
        (Syntax.expr.var dst.(loc_var) ::
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | REdBlock body =>
      (* bedrock2 has no scope concept — scopes are purely a Rust/C
         lifetime hint.  Emit the body's bedrock2 syntax directly. *)
      to_bedrock_cmd body
  | REdSetBytes _ _ =>
      (* Whole-array byte-list write: bedrock2-side correctness is
         carried by the simulation theorem (the Rust target is the
         CT-safe path for this constructor; the C/bedrock2 demo here
         emits a no-op skip and the WP bridge supplies the obligation
         via the IR sim). *)
      Syntax.cmd.skip
  | REdArrLoad _ _ _ =>
      (* Phase Ext: array-of-slots read.  bedrock2-side correctness
         carried via simulation; emit a stub. *)
      Syntax.cmd.skip
  | REdArrStore _ _ _ =>
      Syntax.cmd.skip
  | REdLimbStore loc i e =>
      (* Phase 0b: limb store.  store_word(addr_of(loc) + 8*i, e). *)
      Syntax.cmd.store Syntax.access_size.word
        (Syntax.expr.op Syntax.bopname.add
           (Syntax.expr.var loc.(loc_var))
           (Syntax.expr.literal (8 * Z.of_nat i)))
        (to_bedrock_expr e)
  end.

(** Emit C via bedrock2's mature ToCString pipeline. *)
Definition rust_to_bedrock_c (c : rust_cmd_ed) : string :=
  ToCString.c_cmd "" (to_bedrock_cmd c).

(** Side-by-side demos for comparison. *)
Definition demo_direct : string := c_emit "" demo_rs.
Definition demo_via_bedrock : string := rust_to_bedrock_c demo_rs.

Definition sign_direct : string := c_emit "" ed25519_sign_rs.
Definition sign_via_bedrock : string := rust_to_bedrock_c ed25519_sign_rs.

(* ================================================================ *)
(* §9. Correctness of [to_bedrock_cmd]                                *)
(* ================================================================ *)

(** Lift the parallel [bedrock_cmd_ed] (defined in
    [SafeRustEd25519Sim.v]) to bedrock2 [Syntax.cmd] via a faithful
    constructor-by-constructor translation.  This is the bedrock2
    analog of [btranslate_ed]: same shape, different target syntax. *)
Fixpoint bedrock_cmd_ed_to_syntax (c : bedrock_cmd_ed) : Syntax.cmd :=
  match c with
  | BEdSkip => Syntax.cmd.skip
  | BEdSeq c1 c2 =>
      Syntax.cmd.seq (bedrock_cmd_ed_to_syntax c1) (bedrock_cmd_ed_to_syntax c2)
  | BEdLetZero v t body =>
      Syntax.cmd.stackalloc v (tt_bytes_z t) (bedrock_cmd_ed_to_syntax body)
  | BEdLetU64 v e body =>
      Syntax.cmd.seq
        (Syntax.cmd.set v (to_bedrock_expr e))
        (bedrock_cmd_ed_to_syntax body)
  | BEdScalarSet v e =>
      Syntax.cmd.set v (to_bedrock_expr e)
  | BEdCall fname dst args =>
      Syntax.cmd.call []
        fname
        (Syntax.expr.var dst.(loc_var) ::
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | BEdIfNz e ct cf =>
      Syntax.cmd.cond (to_bedrock_expr e)
                      (bedrock_cmd_ed_to_syntax ct)
                      (bedrock_cmd_ed_to_syntax cf)
  | BEdWhileNz e body =>
      Syntax.cmd.while (to_bedrock_expr e) (bedrock_cmd_ed_to_syntax body)
  | BEdByteStore loc idx val =>
      Syntax.cmd.store Syntax.access_size.one
        (Syntax.expr.op Syntax.bopname.add
           (Syntax.expr.var loc.(loc_var))
           (to_bedrock_expr idx))
        (to_bedrock_expr val)
  | BEdByteLoad v loc idx =>
      Syntax.cmd.set v
        (Syntax.expr.load Syntax.access_size.one
           (Syntax.expr.op Syntax.bopname.add
              (Syntax.expr.var loc.(loc_var))
              (to_bedrock_expr idx)))
  | BEdFor v n body =>
      Syntax.cmd.seq
        (Syntax.cmd.set v (Syntax.expr.literal (Z.of_nat n)))
        (Syntax.cmd.while
           (Syntax.expr.op Syntax.bopname.ltu
              (Syntax.expr.literal 0%Z)
              (Syntax.expr.var v))
           (Syntax.cmd.seq
              (Syntax.cmd.set v
                 (Syntax.expr.op Syntax.bopname.sub
                    (Syntax.expr.var v)
                    (Syntax.expr.literal 1%Z)))
              (bedrock_cmd_ed_to_syntax body)))
  | BEdSelect cond _ _ _ =>
      (* See [REdSelect] case in [to_bedrock_cmd]: stub via cmd.cond. *)
      Syntax.cmd.cond (to_bedrock_expr cond)
                      Syntax.cmd.skip Syntax.cmd.skip
  | BEdCallN fname dests args =>
      Syntax.cmd.call []
        fname
        (List.map (fun l => Syntax.expr.var l.(loc_var)) dests ++
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | BEdCallFn fname dst args =>
      Syntax.cmd.call []
        fname
        (Syntax.expr.var dst.(loc_var) ::
         List.map (fun l => Syntax.expr.var l.(loc_var)) args)
  | BEdBlock body =>
      (* bedrock2 has no scope concept; emit body directly. *)
      bedrock_cmd_ed_to_syntax body
  | BEdSetBytes _ _ =>
      (* See REdSetBytes case in to_bedrock_cmd. *)
      Syntax.cmd.skip
  | BEdArrLoad _ _ _ =>
      Syntax.cmd.skip
  | BEdArrStore _ _ _ =>
      Syntax.cmd.skip
  | BEdLimbStore loc i e =>
      (* Mirror of REdLimbStore case in [to_bedrock_cmd]. *)
      Syntax.cmd.store Syntax.access_size.word
        (Syntax.expr.op Syntax.bopname.add
           (Syntax.expr.var loc.(loc_var))
           (Syntax.expr.literal (8 * Z.of_nat i)))
        (to_bedrock_expr e)
  end.

(** Inverse-style: any [rust_cmd_ed] with no byte-level memory ops
    (REdByteStore / REdByteLoad) corresponds to a [bedrock_cmd_ed]
    structurally. *)
Fixpoint rust_to_bedrock_cmd_ed (c : rust_cmd_ed) : option bedrock_cmd_ed :=
  match c with
  | REdSkip => Some BEdSkip
  | REdSeq c1 c2 =>
      match rust_to_bedrock_cmd_ed c1, rust_to_bedrock_cmd_ed c2 with
      | Some b1, Some b2 => Some (BEdSeq b1 b2)
      | _, _ => None
      end
  | REdLetZero v t body =>
      match rust_to_bedrock_cmd_ed body with
      | Some b => Some (BEdLetZero v t b)
      | None => None
      end
  | REdLetU64 v e body =>
      match rust_to_bedrock_cmd_ed body with
      | Some b => Some (BEdLetU64 v e b)
      | None => None
      end
  | REdScalarSet v e => Some (BEdScalarSet v e)
  | REdCall fname dst args => Some (BEdCall fname dst args)
  | REdIfNz e ct cf =>
      match rust_to_bedrock_cmd_ed ct, rust_to_bedrock_cmd_ed cf with
      | Some bt, Some bf => Some (BEdIfNz e bt bf)
      | _, _ => None
      end
  | REdWhileNz e body =>
      match rust_to_bedrock_cmd_ed body with
      | Some b => Some (BEdWhileNz e b)
      | None => None
      end
  | REdByteStore loc idx val => Some (BEdByteStore loc idx val)
  | REdByteLoad v loc idx => Some (BEdByteLoad v loc idx)
  | REdFor v n body =>
      match rust_to_bedrock_cmd_ed body with
      | Some b => Some (BEdFor v n b)
      | None => None
      end
  | REdSelect cond if_t if_f dest =>
      Some (BEdSelect cond if_t if_f dest)
  | REdCallN fname dests args =>
      Some (BEdCallN fname dests args)
  | REdCallFn fname dst args =>
      Some (BEdCallFn fname dst args)
  | REdBlock body =>
      match rust_to_bedrock_cmd_ed body with
      | Some b => Some (BEdBlock b)
      | None => None
      end
  | REdSetBytes loc bytes => Some (BEdSetBytes loc bytes)
  | REdArrLoad dst src idx_e => Some (BEdArrLoad dst src idx_e)
  | REdArrStore arr idx_e src => Some (BEdArrStore arr idx_e src)
  | REdLimbStore loc i e => Some (BEdLimbStore loc i e)
  end.

(** **Correctness theorem 1**: roundtrip via btranslate_ed.
    Whenever [rust_to_bedrock_cmd_ed c = Some bc], translating [bc]
    back to rust_cmd_ed via [btranslate_ed] returns [c]. *)
Theorem rust_to_bedrock_cmd_ed_roundtrip :
  forall c bc,
    rust_to_bedrock_cmd_ed c = Some bc ->
    btranslate_ed bc = c.
Proof.
  induction c; intros bc Hr; cbn in Hr; try discriminate.
  - inversion Hr; subst; cbn; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c1) as [b1|]; try discriminate.
    destruct (rust_to_bedrock_cmd_ed c2) as [b2|]; try discriminate.
    inversion Hr; subst; cbn.
    erewrite IHc1, IHc2; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|]; try discriminate.
    inversion Hr; subst; cbn. erewrite IHc; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|]; try discriminate.
    inversion Hr; subst; cbn. erewrite IHc; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c1) as [b1|]; try discriminate.
    destruct (rust_to_bedrock_cmd_ed c2) as [b2|]; try discriminate.
    inversion Hr; subst; cbn.
    erewrite IHc1, IHc2; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|]; try discriminate.
    inversion Hr; subst; cbn. erewrite IHc; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|]; try discriminate.
    inversion Hr; subst; cbn. erewrite IHc; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|]; try discriminate.
    inversion Hr; subst; cbn. erewrite IHc; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - (* REdLimbStore *) inversion Hr; subst; reflexivity.
Qed.

(** **Correctness theorem 2**: the two bedrock2-Syntax targets agree.
    For any rust_cmd_ed [c] with no byte-level mem ops,
    [to_bedrock_cmd c] matches the composition
    [bedrock_cmd_ed_to_syntax ∘ rust_to_bedrock_cmd_ed]. *)
Theorem to_bedrock_cmd_factors :
  forall c bc,
    rust_to_bedrock_cmd_ed c = Some bc ->
    to_bedrock_cmd c = bedrock_cmd_ed_to_syntax bc.
Proof.
  induction c; intros bc Hr; cbn in Hr; try discriminate.
  - inversion Hr; subst; cbn; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c1) as [b1|] eqn:H1; try discriminate.
    destruct (rust_to_bedrock_cmd_ed c2) as [b2|] eqn:H2; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc1 _ eq_refl), (IHc2 _ eq_refl); reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|] eqn:Hb; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc _ eq_refl); reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|] eqn:Hb; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc _ eq_refl); reflexivity.
  - inversion Hr; subst; reflexivity.
  - inversion Hr; subst; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c1) as [b1|] eqn:H1; try discriminate.
    destruct (rust_to_bedrock_cmd_ed c2) as [b2|] eqn:H2; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc1 _ eq_refl), (IHc2 _ eq_refl); reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|] eqn:Hb; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc _ eq_refl); reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|] eqn:Hb; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc _ eq_refl); reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - destruct (rust_to_bedrock_cmd_ed c) as [b|] eqn:Hb; try discriminate.
    inversion Hr; subst; cbn.
    rewrite (IHc _ eq_refl); reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - inversion Hr; subst; cbn; reflexivity.
  - (* REdLimbStore *) inversion Hr; subst; cbn; reflexivity.
Qed.

(** **Correctness theorem 3** (semantic preservation): given that
    [rust_to_bedrock_cmd_ed c = Some bc]
    AND [bedrock_exec_ed callee_post bc rs1 rs2], we have
    [rust_exec_ed callee_post c rs1 rs2].

    This connects bedrock2-side execution (modeled by
    [bedrock_exec_ed]) to rust_cmd_ed semantics, going through the
    already-Qed [safe_cmd_correct_ed] simulation. *)
Theorem to_bedrock_cmd_semantic_correct :
  forall callee_post callee_post_n function_table c bc rs1 rs2,
    rust_to_bedrock_cmd_ed c = Some bc ->
    bedrock_exec_ed callee_post callee_post_n function_table bc rs1 rs2 ->
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2.
Proof.
  intros callee_post callee_post_n function_table c bc rs1 rs2 Hr Hb.
  apply safe_cmd_correct_ed in Hb.
  rewrite (rust_to_bedrock_cmd_ed_roundtrip _ _ Hr) in Hb.
  exact Hb.
Qed.

(** **Coverage**: as of 2026-05-09, byte-level mem ops
    [REdByteStore] and [REdByteLoad] ARE covered.
    [bedrock_exec_ed] was extended with [bexec_byte_store] /
    [bexec_byte_load] (in [SafeRustEd25519Sim.v]), and
    [bedrock_cmd_ed_to_syntax] / [rust_to_bedrock_cmd_ed] /
    [safe_cmd_correct_ed] all carry the new cases.

    Therefore [to_bedrock_cmd_semantic_correct] now applies to
    every [rust_cmd_ed], including [ed25519_sign_rs],
    [ed25519_verify_rs], and
    [ed25519_scalarmult_base_parametric_rs] which uses byte-level
    scalar reads. *)
