(* Direct compile_prog_to_asm driver.
 *
 * **STATUS (2026-04-14): PARTIALLY DEPRECATED — translation layer.**
 *
 * This file predates the verified AST-to-AST path via extracted
 * [to_jasmin_cmd].  Its [translate_cmd] / [translate_expr]
 * (~200 lines, around lines 138–330) re-implement in OCaml what
 * [JasminBridgeReal.to_jasmin_cmd] already proves correct in Rocq
 * (17 Qed, 2 trivial identity-cast axioms).
 *
 * **DEPRECATED portion:** [translate_cmd], [translate_expr], and
 * the per-jasmin_cmd-constructor dispatch (~200 lines).
 * New drivers must consume the extracted [to_jasmin_cmd] via the
 * ~30-line shim in [ast2ast_driver.ml] / [ast2ast_main.ml]
 * (bridges two separate Coq extractions with [Obj.magic] to
 * side-step the fiat-crypto/Jasmin universe inconsistency).
 *
 * **RETAINED plumbing:** variable tables, funname interning,
 * [wrap_func] / [build_prog], register-pressure partitioning,
 * and the calls to [Conv.cuprog_of_prog], [Compile.compile],
 * [Pp_x86.print_prog] (~700 lines from line 330 onward).
 * These wrap jasminc's OCaml APIs and have no Rocq counterpart;
 * they remain unverified glue but are mechanical.
 *
 * Pipeline (DEPRECATED FORM — kept for BLS12 benchmark reproducibility):
 *   bls12_jasmin_extracted.bls12_all_jasmin  (jasmin_func list)
 *   -> translate_cmd (this file)             (jasmin_cmd -> Prog.gstmt)
 *   -> wrap in Prog.func / Prog.prog        (this file)
 *   -> Conv.cuprog_of_prog                   (jasmin library)
 *   -> Compile.compile                       (jasminc full compiler)
 *   -> Pp_x86.print_prog                     (assembly output)
 *
 * Pipeline (VERIFIED FORM — use this for new work):
 *   bls12_jasmin_extracted.bls12_all_jasmin  (jasmin_func list)
 *   -> ast2ast_driver.convert_cmd            (Z/positive conversion, ~30 lines)
 *   -> Bridge_extracted.to_jasmin_cmd        (EXTRACTED FROM VERIFIED ROCQ)
 *   -> wrap in Prog.func / Prog.prog        (retained plumbing below)
 *   -> Conv.cuprog_of_prog                   (jasmin library)
 *   -> Compile.compile                       (jasminc full compiler)
 *   -> Pp_x86.print_prog                     (assembly output)
 *)

open Jasmin
open Prog
open Wsize

(* ================================================================ *)
(* Construct the x86-64 architecture module (needed early for types) *)
(* ================================================================ *)

module X86_lowering_params : X86_arch_full.X86_input = struct
  let call_conv = X86_decl.x86_linux_call_conv
  (* use_set0 = false: Disable XOR-to-zero optimization.
     When enabled, the lowering pass turns "x = 0" into "XOR x, x" which
     clobbers ALL x86 flags (CF, PF, ZF, SF, OF). The bedrock2-extracted
     code contains the pattern:
       adcx __cf, ...        // carry flag __cf is live in CF
       set x23 = 0           // lowered to XOR -> clobbers CF!
       if __cf then x23 = 1  // tries to read CF, but it was clobbered
     With use_set0 = false, "x = 0" becomes "MOV x, 0" which preserves
     flags. The cost is ~4 extra bytes per zero-init (MOV r64,imm32 vs
     XOR r32,r32) — negligible for field arithmetic functions. *)
  let lowering_opt = { X86_lowering.use_lea = true; use_set0 = false }
end

module X86_core_arch = X86_arch_full.X86 (X86_lowering_params)
module X86_arch = Arch_full.Arch_from_Core_arch (X86_core_arch)

(* ================================================================ *)
(* Helpers                                                           *)
(* ================================================================ *)

let implode cs =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

(* ================================================================ *)
(* Variable and funname management                                   *)
(* ================================================================ *)

(** We maintain a hashtable mapping variable name strings to Prog.var
    records. All variables are typed as reg u64 (64-bit word in register).
    This mirrors the bridge's mk_var_from_string. *)
let var_tbl : (string, var) Hashtbl.t = Hashtbl.create 97

(** Detect flag variable names: __cf*, __bf* are boolean flags.
    These must be Bool-typed so that the Oaddcarry/Osubcarry pseudo-ops
    lower correctly (their carry output is placed in the CF flag slot
    during instruction lowering). *)
let is_flag_name (name : string) : bool =
  let n = String.length name in
  (n >= 4 && String.sub name 0 4 = "__cf") ||
  (n >= 4 && String.sub name 0 4 = "__bf")

let mk_var (name : string) : var =
  match Hashtbl.find_opt var_tbl name with
  | Some v -> v
  | None ->
    let is_flag = is_flag_name name in
    let ty = if is_flag then Bty Bool else Bty (U U64) in
    let v = V.mk name (Reg (Normal, Direct)) ty Location._dummy [] in
    Hashtbl.add var_tbl name v;
    v

let mk_var_i (name : string) : var_i =
  Location.mk_loc Location._dummy (mk_var name)

(** Counter used to gensym fresh stack-local names. *)
let stack_local_counter : int ref = ref 0

(** Per-function mapping from original stack-local base name (e.g. "h_full",
    "a", "prefix") to its gensym'd [Stack Direct, Arr(U64,n)] var.  Populated
    by [register_stack_locals] (called from [compile_funcs] BEFORE
    [translate_cmd] runs on the function body) and cleared after each
    function.  Consulted by [translate_cmd] and [translate_expr] when
    translating [JCstore (JEvar X) off val] and [JEload (JEvar X) off] —
    a hit substitutes [Lmem (Pvar X + off) = val] / [Pload (Pvar X + off)]
    with [Laset (stk, off/8) = val] / [Pget (stk, off/8)].

    Blocker B (2026-05-14): the materialized stack arrays from A114 are
    otherwise dead-coded because the body's [JEvar X] references resolve
    to Reg-u64 [Pvar X] (not the stack array).  This mapping reroutes
    those references to the stack array. *)
let current_stack_locals : (string, var * int) Hashtbl.t = Hashtbl.create 17

(** Materialize a [Stack Direct] var holding an [Arr (U64, n)] (n 64-bit
    limbs). Gensyms a unique [__stk_<idx>_<base>] name so it cannot collide
    with the existing register-kind var bound to [base] elsewhere in the
    translation. Returns the fresh var (kind=Stack Direct, ty=Arr(U64,n)).

    Used by [wrap_func] to consume [jf_locals] entries produced by the
    Rocq-side [hoist_stack_decls_func] pass (src/Bedrock/Jasmin/Core.v),
    which lifts every [JCdecl (_, JTstack n, _)] in the body up into the
    function record's [jf_locals] field. Before this helper landed, those
    decls were silently erased by the [JCdecl] case of [translate_cmd]
    (around line 368). *)
let mk_stack_var (base : string) (n : int) : var =
  let idx = !stack_local_counter in
  incr stack_local_counter;
  let fresh = Printf.sprintf "__stk_%d_%s" idx base in
  let ty = Arr (U64, n) in
  let v = V.mk fresh (Stack Direct) ty Location._dummy [] in
  Hashtbl.add var_tbl fresh v;
  v

(** Pre-register a function's [jf_locals] (filtered to [JTstack n] entries)
    so subsequent [translate_cmd] / [translate_expr] calls can rewrite
    [Lmem]/[Pload] of a stack-local base to [Laset]/[Pget] against the
    gensym'd stack-array var.  Returns the [(base, gensym_var, n)] list
    so [wrap_func] can also prepend the [Cassgn (_, Parr_init U64 n)]
    initializer using the SAME gensym var (rather than re-gensyming).

    MUST be called before [translate_cmd f.jf_body], and [clear_stack_locals]
    MUST be called after [wrap_func] for that function — otherwise the
    mapping leaks across functions and a stub leaf with param name
    accidentally matching a caller's stack-local would emit broken Laset
    targeting a foreign array. *)
let register_stack_locals (stack_locals : (string * int) list)
    : (string * var * int) list =
  Hashtbl.clear current_stack_locals;
  Stdlib.List.map (fun (base, n) ->
    let v = mk_stack_var base n in
    Hashtbl.add current_stack_locals base (v, n);
    (base, v, n)
  ) stack_locals

let clear_stack_locals () = Hashtbl.clear current_stack_locals

(** Function name table: maps name strings to funnames. *)
let fn_tbl : (string, CoreIdent.funname) Hashtbl.t = Hashtbl.create 97

let mk_funname (name : string) : CoreIdent.funname =
  match Hashtbl.find_opt fn_tbl name with
  | Some fn -> fn
  | None ->
    let fn = CoreIdent.F.mk name in
    Hashtbl.add fn_tbl name fn;
    fn

(* ================================================================ *)
(* Dummy instruction info                                            *)
(* ================================================================ *)

let mk_instr (ir : ('a, unit, 'b) ginstr_r) : ('a, unit, 'b) ginstr =
  (* Each instruction gets a fresh i_loc so the compiler's location-based
     tables don't collide. refresh_i_loc_f fixes this later anyway. *)
  let iloc = Location.refresh_i_loc Location.i_dummy in
  { i_desc = ir;
    i_loc = iloc;
    i_info = ();
    i_annot = [] }

(** Variant of [mk_instr] that attaches an [inline] annotation to the
    i_annot field.  Used for [Ccall] sites whose callee is a stub leaf:
    [IInfo.is_inline] reads [Annotations.has_symbol "inline" annot],
    and that determines whether jasminc's [Inlining] pass expands the
    call.  Without this annotation, [FInfo.Internal]-cc callees stay
    as [Ccall] instructions and hit the [varalloc.ml:422 assert false]
    that A25 documented. *)
let mk_instr_inline (ir : ('a, unit, 'b) ginstr_r) : ('a, unit, 'b) ginstr =
  let iloc = Location.refresh_i_loc Location.i_dummy in
  let inline_annot =
    [ (Location.mk_loc Location._dummy "inline", None) ]
  in
  { i_desc = ir;
    i_loc = iloc;
    i_info = ();
    i_annot = inline_annot }

(* ================================================================ *)
(* Lnone: discard result (like bridge's lnone_b)                    *)
(* ================================================================ *)

let lnone () : lval =
  Lnone (Location._dummy, Bty (U U64))

(* ================================================================ *)
(* Translate jasmin_expr -> Prog.expr                                *)
(* ================================================================ *)

(** Convert extracted Coq z (BinNums.Z) to zarith Z.t *)
let rec z_of_positive (p : Bls12_jasmin_extracted.positive) : Z.t =
  match p with
  | Bls12_jasmin_extracted.XI p' -> Z.(add (mul (of_int 2) (z_of_positive p')) one)
  | Bls12_jasmin_extracted.XO p' -> Z.(mul (of_int 2) (z_of_positive p'))
  | Bls12_jasmin_extracted.XH -> Z.one

let z_of_coq_z (z : Bls12_jasmin_extracted.z) : Z.t =
  match z with
  | Bls12_jasmin_extracted.Z0 -> Z.zero
  | Bls12_jasmin_extracted.Zpos p -> z_of_positive p
  | Bls12_jasmin_extracted.Zneg p -> Z.neg (z_of_positive p)

let mk_gvar (name : string) : int ggvar =
  { gv = mk_var_i name; gs = Expr.Slocal }

let rec translate_expr (e : Bls12_jasmin_extracted.jasmin_expr) : expr =
  match e with
  | Bls12_jasmin_extracted.JEvar s ->
    Pvar (mk_gvar (implode s))
  | Bls12_jasmin_extracted.JElit n ->
    (* Wrap integer constants in Oword_of_int to produce u64-typed values.
       Without this, Pconst produces int-typed values that jasmin's
       linearizer cannot emit as x86 instructions. *)
    Papp1 (Operators.Oword_of_int U64, Pconst (z_of_coq_z n))
  | Bls12_jasmin_extracted.JEadd (a, b) ->
    Papp2 (Operators.Oadd (Operators.Op_w U64), translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEsub (a, b) ->
    Papp2 (Operators.Osub (Operators.Op_w U64), translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEmul (a, b) ->
    Papp2 (Operators.Omul (Operators.Op_w U64), translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEmulhuu (_a, _b) ->
    (* unsigned high multiply — not directly expressible as sop2;
       should not appear in our bedrock2 functions (MULX is used instead) *)
    failwith "JEmulhuu not supported in direct compilation"
  | Bls12_jasmin_extracted.JEand (a, b) ->
    Papp2 (Operators.Oland U64, translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEor (a, b) ->
    Papp2 (Operators.Olor U64, translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JExor (a, b) ->
    Papp2 (Operators.Olxor U64, translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEshr (a, b) ->
    Papp2 (Operators.Olsr U64, translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEshl (a, b) ->
    Papp2 (Operators.Olsl (Operators.Op_w U64), translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEltu (a, b) ->
    Papp2 (Operators.Olt (Operators.Cmp_w (Unsigned, U64)),
           translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEeq (a, b) ->
    Papp2 (Operators.Oeq (Operators.Op_w U64), translate_expr a, translate_expr b)
  | Bls12_jasmin_extracted.JEload (base, off) ->
    let z_off = z_of_coq_z off in
    (* Blocker B: if [base] is a [JEvar X] where X names a stack-local of
       the current function, emit [Pget (stk, off/8)] instead of
       [Pload (Pvar X + off)] — the stack array is the real storage. *)
    let stack_local_match =
      match base with
      | Bls12_jasmin_extracted.JEvar s ->
        Hashtbl.find_opt current_stack_locals (implode s)
      | _ -> None
    in
    (match stack_local_match with
     | Some (stk_var, _n) ->
       (* off is a byte offset; AAscale wants element index = off/8. *)
       let idx = Z.div z_off (Z.of_int 8) in
       let gv = { gv = Location.mk_loc Location._dummy stk_var;
                  gs = Expr.Slocal } in
       Pget (Memory_model.Aligned, Warray_.AAscale, U64, gv, Pconst idx)
     | None ->
       let addr =
         if Z.equal z_off Z.zero then
           translate_expr base
         else
           Papp2 (Operators.Oadd (Operators.Op_w U64),
                  translate_expr base,
                  Pconst z_off)
       in
       Pload (Memory_model.Aligned, U64, addr))

(* ================================================================ *)
(* Operation constructors                                            *)
(* ================================================================ *)

(** Build an x86 extended_op sopn for a base x86 instruction. *)
let x86_op (op : X86_instr_decl.x86_op)
    : X86_arch.extended_op Sopn.sopn =
  Sopn.Oasm (Arch_extra.BaseOp (None, op))

(** Build a pseudo-operator sopn (goes through lowering pass). *)
let pseudo_op (op : Pseudo_operator.pseudo_operator)
    : X86_arch.extended_op Sopn.sopn =
  Sopn.Opseudo_op op

(* ================================================================ *)
(* DEPRECATED (2026-04-14): OCaml re-implementation of to_jasmin_cmd *)
(*                                                                   *)
(* Use [Bridge_extracted.to_jasmin_cmd] (extracted from verified     *)
(* Rocq [JasminBridgeReal.to_jasmin_cmd]) + the ~30-line shim in     *)
(* [ast2ast_driver.ml] / [ast2ast_main.ml] instead.                  *)
(*                                                                   *)
(* Retained here so the BLS12 benchmark binary still builds.  New    *)
(* curve drivers must not duplicate this code.                       *)
(* ================================================================ *)
(* Translate jasmin_cmd -> Prog.gstmt                                *)
(* (mirrors JasminBridgeReal.to_jasmin_cmd)                          *)
(* ================================================================ *)

type x86_stmt = (int, unit, X86_arch.extended_op Sopn.asm_op_t) gstmt

(** Counter for generating fresh RDX temp variables for MULX.
    Each MULX gets its own temp to keep RDX live ranges minimal. *)
let mulx_rdx_counter = ref 0

(** Callee-arity table consulted by [translate_cmd] to pad/truncate
    callsite arguments to match the declared callee arity.  Populated
    by [compile_funcs] for stub-leaf functions before [translate_cmd]
    is invoked.  This is the empirical-gate workaround for the
    [sha512_64] arity polymorphism in [ed25519_sign_rs] (roadmap §9
    path (b)).  Should be empty for non-stub workflows so the
    BLS12 / X25519 benchmark binaries are unaffected. *)
let callee_arity_tbl : (string, int) Hashtbl.t = Hashtbl.create 17

(** Extern-leaf set: stub callees whose callsite should be a real
    [call <symbol>] in the emitted asm rather than an inlined empty
    body.  Populated by [compile_funcs] from a hard-coded list
    ([extern_leaf_names]).  When [translate_cmd] sees a JCcall to a
    name in this set it omits the [inline] annotation, so jasminc
    keeps the call instruction; combined with [FInfo.Subroutine] CC
    on the callee, the asm emits [call <symbol>] for link-time
    resolution to an external implementation (e.g., libjade's
    [jade_hash_sha512_amd64_ref]). *)
let extern_leaf_tbl : (string, unit) Hashtbl.t = Hashtbl.create 17

(* ================================================================ *)
(* A103 BLOCKER C — Multi-callsite RegAlloc wrappers                 *)
(* ================================================================ *)
(* In the inlined Ed25519 sign body, several FFI leaves are called  *)
(* from multiple call-sites in the SAME enclosing function with     *)
(* DIFFERENT first-argument variables.  jasminc's RegAllocation     *)
(* pass (regalloc.ml lines 280–297) traverses every Ccall and unions *)
(* each caller-arg variable into the SAME equivalence class as the  *)
(* callee's corresponding f_args slot — across ALL call-sites.      *)
(* Caller variables from distinct call-sites end up in one class    *)
(* and, if simultaneously live elsewhere in the caller, hit the     *)
(* "conflicting variables ... must be merged" error (A99's          *)
(* documented [sha512_64 k_full/r_full] failure at line ~1041).     *)
(*                                                                   *)
(* SOLUTION: for each leaf [F] that is called >= 2 times by ANY    *)
(* caller in funcs_to_compile, generate per-callsite wrapper        *)
(* subroutines [F__cs0], [F__cs1], ..., one per call-site, each    *)
(* with fresh wrapper-local parameter names.  Each wrapper's body  *)
(* is a single [Ccall F(p_1, ..., p_k)] forwarding to F.  The     *)
(* per-callsite [JCcall] in the caller is rewritten to target the *)
(* wrapper instead of F directly.                                  *)
(*                                                                   *)
(* RegAlloc now sees:                                              *)
(*   - At each outer call to F__cs_i: caller-arg variables unify  *)
(*     with the wrapper's fresh params.  Wrappers' params are     *)
(*     disjoint per call-site so each caller variable is unified  *)
(*     with at most ONE wrapper-param symbol — no cross-call-site *)
(*     coalescing.                                                 *)
(*   - At the single Ccall F inside each wrapper body: the        *)
(*     wrapper's fresh params unify with F's f_args.  Different   *)
(*     wrappers have different params, so F's f_args' equivalence *)
(*     class accumulates fresh names — but those names are local  *)
(*     to one wrapper each and never simultaneously live.         *)
(*                                                                   *)
(* HONESTY: this implementation is sequential after Blocker A      *)
(* (A114, in flight) and Blocker B (stub-body pointer deref).      *)
(* Standalone, it is necessary but not sufficient for the full    *)
(* Ed25519 sign emission chain.  It IS, however, complete and    *)
(* self-contained for the RegAlloc gate.                          *)
(*                                                                   *)
(* DESIGN doc — wrapper signature pattern:                         *)
(*   For leaf F with params [p_1; ...; p_k], the i-th wrapper is: *)
(*     fn F__cs{i}(reg u64 p_1__cs{i}, ..., reg u64 p_k__cs{i}) { *)
(*       F(p_1__cs{i}, ..., p_k__cs{i});                          *)
(*     }                                                            *)
(*   with [FInfo.Subroutine] CC and NO [inline] annotation, so    *)
(*   jasminc's Inlining pass does NOT collapse it back.  F itself *)
(*   keeps whatever CC it had ([Internal] for stubs, [Subroutine] *)
(*   for externs); jasminc inlines stub F into each wrapper.      *)
(*                                                                   *)
(* Per-leaf adapter recipe:                                        *)
(*   1. Pre-scan all funcs_to_compile, count callsites per callee. *)
(*   2. For each callee with count >= 2, mark for wrapping.        *)
(*   3. During translate_cmd, maintain a per-callee occurrence    *)
(*      counter; on JCcall F(args) when F is wrapped, emit the    *)
(*      i-th wrapper's funname instead of F's.                    *)
(*   4. After translation, emit the wrapper funcs into the prog.  *)

(** Multi-call-site leaves: name -> total callsite count (>=2).    *)
let wrap_callee_counts : (string, int) Hashtbl.t = Hashtbl.create 17

(** Per-callee occurrence counter, reset before [translate_cmd] of
    each top-level function.  Mutating during recursive [translate_cmd]
    yields the correct site index in source-order. *)
let wrap_callee_occurrence : (string, int) Hashtbl.t = Hashtbl.create 17

(** Wrapper-funname registry for diagnostic / smoke-test introspection. *)
let wrap_callsite_wrappers : (string, unit) Hashtbl.t = Hashtbl.create 17

(** Construct the i-th wrapper name for leaf [fname].              *)
let mk_wrapper_name (fname : string) (i : int) : string =
  Printf.sprintf "%s__cs%d" fname i

(** Construct the j-th wrapper-local parameter name for the i-th
    wrapper of leaf [fname].                                       *)
let mk_wrapper_param_name (fname : string) (i : int) (j : int) : string =
  Printf.sprintf "%s__cs%d_p%d" fname i j

(** Pre-scan: count [JCcall fname _] occurrences across the bodies
    of every func in [funcs].  Records callees whose count >= 2 in
    [wrap_callee_counts].  Returns the populated table for
    diagnostic logging. *)
let scan_multi_callsite_leaves
    (funcs : Bls12_jasmin_extracted.jasmin_func list) : unit =
  Hashtbl.clear wrap_callee_counts;
  let counts : (string, int) Hashtbl.t = Hashtbl.create 17 in
  let rec scan (c : Bls12_jasmin_extracted.jasmin_cmd) : unit =
    match c with
    | Bls12_jasmin_extracted.JCskip -> ()
    | Bls12_jasmin_extracted.JCseq (a, b) -> scan a; scan b
    | Bls12_jasmin_extracted.JCif (_, ct, cf) -> scan ct; scan cf
    | Bls12_jasmin_extracted.JCwhile (_, body) -> scan body
    | Bls12_jasmin_extracted.JCdecl (_, _, body) -> scan body
    | Bls12_jasmin_extracted.JCcall (f, _) ->
      let n = implode f in
      let prev = try Hashtbl.find counts n with Not_found -> 0 in
      Hashtbl.replace counts n (prev + 1)
    | _ -> ()
  in
  Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    scan f.jf_body
  ) funcs;
  Hashtbl.iter (fun name c ->
    if c >= 2 then Hashtbl.replace wrap_callee_counts name c
  ) counts

(** Clone the leaf function [leaf_jfunc]'s body with a parameter
    rename map [param_map : leaf_param_name -> wrapper_param_name].
    Returns a translated [x86_stmt] using the wrapper's params.

    This is the heart of the Blocker C approach: instead of having
    the wrapper [Ccall] back to a shared leaf (which would unify the
    callee's params across all wrapper sibling subroutines and
    re-introduce coalescing through the leaf's f_args), we INLINE
    the leaf body at wrapper-construction time, substituting fresh
    wrapper-param names for the original leaf-param names.  Each
    wrapper is therefore a fully self-contained subroutine with no
    further [Ccall] to the shared leaf — jasminc's RegAlloc unifies
    each wrapper's params only with its OWN copy of the leaf body's
    local variables. *)
let clone_leaf_body_with_renames
    (leaf_body : Bls12_jasmin_extracted.jasmin_cmd)
    (param_map : (string * string) list)
    (suffix : string) : Bls12_jasmin_extracted.jasmin_cmd =
  (* Build name-rename closure: leaf params get mapped to wrapper
     params; all other free variables (the leaf's internal locals)
     get the suffix appended so different wrappers' cloned bodies
     don't share local-variable identity. *)
  let explode s =
    let n = String.length s in
    let rec aux i = if i >= n then [] else s.[i] :: aux (i + 1) in
    aux 0
  in
  let rename_name (name : char list) : char list =
    let s = implode name in
    match Stdlib.List.assoc_opt s param_map with
    | Some replacement -> explode replacement
    | None -> explode (s ^ suffix)
  in
  let rec rename_expr (e : Bls12_jasmin_extracted.jasmin_expr)
      : Bls12_jasmin_extracted.jasmin_expr =
    match e with
    | Bls12_jasmin_extracted.JEvar s ->
      Bls12_jasmin_extracted.JEvar (rename_name s)
    | Bls12_jasmin_extracted.JElit _ -> e
    | Bls12_jasmin_extracted.JEadd (a, b) ->
      Bls12_jasmin_extracted.JEadd (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEsub (a, b) ->
      Bls12_jasmin_extracted.JEsub (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEmul (a, b) ->
      Bls12_jasmin_extracted.JEmul (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEmulhuu (a, b) ->
      Bls12_jasmin_extracted.JEmulhuu (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEand (a, b) ->
      Bls12_jasmin_extracted.JEand (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEor (a, b) ->
      Bls12_jasmin_extracted.JEor (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JExor (a, b) ->
      Bls12_jasmin_extracted.JExor (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEshr (a, b) ->
      Bls12_jasmin_extracted.JEshr (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEshl (a, b) ->
      Bls12_jasmin_extracted.JEshl (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEltu (a, b) ->
      Bls12_jasmin_extracted.JEltu (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEeq (a, b) ->
      Bls12_jasmin_extracted.JEeq (rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JEload (base, off) ->
      Bls12_jasmin_extracted.JEload (rename_expr base, off)
  in
  let rec rename_cmd (c : Bls12_jasmin_extracted.jasmin_cmd)
      : Bls12_jasmin_extracted.jasmin_cmd =
    match c with
    | Bls12_jasmin_extracted.JCskip -> c
    | Bls12_jasmin_extracted.JCseq (a, b) ->
      Bls12_jasmin_extracted.JCseq (rename_cmd a, rename_cmd b)
    | Bls12_jasmin_extracted.JCset (x, e) ->
      Bls12_jasmin_extracted.JCset (rename_name x, rename_expr e)
    | Bls12_jasmin_extracted.JCstore (base, off, v) ->
      Bls12_jasmin_extracted.JCstore (rename_expr base, off, rename_expr v)
    | Bls12_jasmin_extracted.JCcall (fnm, args) ->
      (* Generally leaves don't call anything; but keep this
         transparent if they do. *)
      Bls12_jasmin_extracted.JCcall (fnm, Stdlib.List.map rename_expr args)
    | Bls12_jasmin_extracted.JCif (e, ct, cf) ->
      Bls12_jasmin_extracted.JCif (rename_expr e, rename_cmd ct, rename_cmd cf)
    | Bls12_jasmin_extracted.JCwhile (e, body) ->
      Bls12_jasmin_extracted.JCwhile (rename_expr e, rename_cmd body)
    | Bls12_jasmin_extracted.JCdecl (x, ty, body) ->
      Bls12_jasmin_extracted.JCdecl (rename_name x, ty, rename_cmd body)
    | Bls12_jasmin_extracted.JCadd_flags (cf, result, a, b) ->
      Bls12_jasmin_extracted.JCadd_flags
        (rename_name cf, rename_name result, rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JCadcx (cf_out, result, a, b, cf_in) ->
      Bls12_jasmin_extracted.JCadcx
        (rename_name cf_out, rename_name result,
         rename_expr a, rename_expr b, rename_name cf_in)
    | Bls12_jasmin_extracted.JCmulx (hi, lo, a, b) ->
      Bls12_jasmin_extracted.JCmulx
        (rename_name hi, rename_name lo, rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JCsub_flags (cf, result, a, b) ->
      Bls12_jasmin_extracted.JCsub_flags
        (rename_name cf, rename_name result, rename_expr a, rename_expr b)
    | Bls12_jasmin_extracted.JCsbb (cf_out, result, a, b, cf_in) ->
      Bls12_jasmin_extracted.JCsbb
        (rename_name cf_out, rename_name result,
         rename_expr a, rename_expr b, rename_name cf_in)
  in
  rename_cmd leaf_body

(** Reset the per-call-site occurrence counter.  MUST be called
    once before [translate_cmd] is run on each top-level callsite
    function, so the i index in wrapper names matches the
    source-order position within that caller. *)
let reset_wrapper_occurrence () =
  Hashtbl.clear wrap_callee_occurrence

let rec translate_cmd (c : Bls12_jasmin_extracted.jasmin_cmd) : x86_stmt =
  match c with
  | Bls12_jasmin_extracted.JCskip -> []

  | Bls12_jasmin_extracted.JCseq (c1, c2) ->
    translate_cmd c1 @ translate_cmd c2

  | Bls12_jasmin_extracted.JCset (x, e) ->
    let name = implode x in
    [mk_instr (Cassgn (Lvar (mk_var_i name),
                        Expr.AT_none, Bty (U U64), translate_expr e))]

  | Bls12_jasmin_extracted.JCstore (base, off, v) ->
    let z_off = z_of_coq_z off in
    (* Blocker B: if [base] is a [JEvar X] where X names a stack-local of
       the current function, emit [Laset (stk, off/8) = val] instead of
       [Cassgn (Lmem (Pvar X + off)) = val]. *)
    let stack_local_match =
      match base with
      | Bls12_jasmin_extracted.JEvar s ->
        Hashtbl.find_opt current_stack_locals (implode s)
      | _ -> None
    in
    (* Hoist the store value into a fresh temp register so the RHS is
       always a bare [Pvar].  Required for [Lmem] (linearization needs
       bare Pvar source); harmless for [Laset]. *)
    let tmp_id = let c = !mulx_rdx_counter in incr mulx_rdx_counter; c in
    let tmp_name = Printf.sprintf "__store_tmp_%d" tmp_id in
    let tmp_var = mk_var tmp_name in
    let tmp_var_i = Location.mk_loc Location._dummy tmp_var in
    let tmp_gvar = { gv = tmp_var_i; gs = Expr.Slocal } in
    let copy_val = mk_instr (Cassgn (Lvar tmp_var_i, Expr.AT_none,
                                     Bty (U U64), translate_expr v)) in
    (match stack_local_match with
     | Some (stk_var, _n) ->
       let idx = Z.div z_off (Z.of_int 8) in
       let stk_vi = Location.mk_loc Location._dummy stk_var in
       let lv = Laset (Memory_model.Aligned, Warray_.AAscale, U64,
                       stk_vi, Pconst idx) in
       [copy_val;
        mk_instr (Cassgn (lv, Expr.AT_none, Bty (U U64), Pvar tmp_gvar))]
     | None ->
       let addr =
         if Z.equal z_off Z.zero then
           translate_expr base
         else
           Papp2 (Operators.Oadd (Operators.Op_w U64),
                  translate_expr base,
                  Pconst z_off)
       in
       [copy_val;
        mk_instr (Cassgn (Lmem (Memory_model.Aligned, U64, Location._dummy, addr),
                          Expr.AT_none, Bty (U U64), Pvar tmp_gvar))])

  | Bls12_jasmin_extracted.JCcall (f, args) ->
    let fname = implode f in
    (* Blocker C: if [fname] is a multi-callsite leaf, rewrite this
       JCcall to target the i-th per-callsite wrapper instead of
       the leaf directly.  Each wrapper has fresh wrapper-local
       parameter symbols so jasminc's RegAlloc cannot coalesce
       caller-arg variables across distinct call-sites of [fname]. *)
    let dispatch_name =
      if Hashtbl.mem wrap_callee_counts fname then begin
        let i = try Hashtbl.find wrap_callee_occurrence fname
                with Not_found -> 0 in
        Hashtbl.replace wrap_callee_occurrence fname (i + 1);
        mk_wrapper_name fname i
      end else
        fname
    in
    let fn = mk_funname dispatch_name in
    let translated = Stdlib.List.map translate_expr args in
    (* Roadmap §9 path (b) workaround: when a callee has a fixed
       arity (recorded in [callee_arity_tbl] by the caller) but a
       callsite passes fewer arguments, pad with [Pconst 0]; when
       it passes more, truncate.  This is REQUIRED for the
       [ed25519_sign_rs] body where [sha512_64] is called with 2
       args (initial seed hash) and 3 args (nonce/challenge hashes),
       but jasminc requires fixed-arity callees. *)
    let adjusted =
      match Hashtbl.find_opt callee_arity_tbl fname with
      | None -> translated
      | Some target_arity ->
        let n = Stdlib.List.length translated in
        if n = target_arity then translated
        else if n > target_arity then
          let rec take k xs = if k <= 0 then [] else
            match xs with [] -> [] | x :: rest -> x :: take (k-1) rest
          in take target_arity translated
        else
          let pad = Pconst (Z.zero) in
          let rec pad_to k xs =
            if k <= 0 then xs
            else pad :: pad_to (k-1) xs
          in translated @ pad_to (target_arity - n) []
    in
    (* If the callee is registered as a stub (callee_arity_tbl contains
       its name), attach the [inline] annotation so jasminc's Inlining
       pass expands the call.  This is required when stubs use
       [FInfo.Internal] cc: without the inline annotation, the
       Ccall survives to varalloc which asserts [Internal -> false]
       (varalloc.ml:422).

       A33 exception: for stubs in [extern_leaf_tbl] we DELIBERATELY
       skip the inline annotation, so jasminc keeps the call.  These
       callees are compiled with [FInfo.Subroutine] CC so the surviving
       Ccall lowers to a real [call <symbol>] in the asm.  At link
       time the symbol can be resolved to an external implementation
       (e.g., libjade's [jade_hash_sha512_amd64_ref] for sha512_64).

       Blocker C: when [dispatch_name <> fname] we have rewritten
       the call to target a [Subroutine]-CC wrapper.  That wrapper
       MUST be reached via a real [Ccall] (no inline annotation),
       otherwise jasminc's Inlining pass collapses the wrapper back
       into the caller and the regalloc-coalescing problem returns. *)
    let is_wrapper_call = dispatch_name <> fname in
    let make_call =
      if is_wrapper_call then mk_instr
      else if Hashtbl.mem extern_leaf_tbl fname then mk_instr
      else if Hashtbl.mem callee_arity_tbl fname then mk_instr_inline
      else mk_instr
    in
    [make_call (Ccall ([], fn, adjusted))]

  | Bls12_jasmin_extracted.JCif (e, ct, cf) ->
    [mk_instr (Cif (translate_expr e, translate_cmd ct, translate_cmd cf))]

  | Bls12_jasmin_extracted.JCwhile (e, body) ->
    [mk_instr (Cwhile (Expr.NoAlign, translate_cmd body,
                        translate_expr e, (IInfo.dummy, ()), []))]

  | Bls12_jasmin_extracted.JCdecl (_x, _ty, body) ->
    (* Stack declarations are erased — the bridge does the same *)
    translate_cmd body

  | Bls12_jasmin_extracted.JCadd_flags (cf, result, a, b) ->
    (* Oaddcarry U64 with 2-address form:
       result := a; [cf, result] = addcarry(result, b, false) *)
    let result_vi = mk_var_i (implode result) in
    let copy = mk_instr (Cassgn (Lvar result_vi, Expr.AT_none,
                                  Bty (U U64), translate_expr a)) in
    let lvs = [Lvar (mk_var_i (implode cf));
               Lvar result_vi] in
    [copy;
     mk_instr (Copn (lvs, Expr.AT_none,
                      pseudo_op (Pseudo_operator.Oaddcarry U64),
                      [Pvar (mk_gvar (implode result));
                       translate_expr b;
                       Pbool false]))]

  | Bls12_jasmin_extracted.JCadcx (cf_out, result, a, b, cf_in) ->
    (* Oaddcarry U64 with 2-address form:
       result := a; [cf_out, result] = addcarry(result, b, cf_in) *)
    let result_vi = mk_var_i (implode result) in
    let cf_in_gvar = { gv = mk_var_i (implode cf_in); gs = Expr.Slocal } in
    let copy = mk_instr (Cassgn (Lvar result_vi, Expr.AT_none,
                                  Bty (U U64), translate_expr a)) in
    let lvs = [Lvar (mk_var_i (implode cf_out));
               Lvar result_vi] in
    [copy;
     mk_instr (Copn (lvs, Expr.AT_none,
                      pseudo_op (Pseudo_operator.Oaddcarry U64),
                      [Pvar (mk_gvar (implode result));
                       translate_expr b;
                       Pvar cf_in_gvar]))]

  | Bls12_jasmin_extracted.JCmulx (hi, lo, a, b) ->
    (* Use MULX when available (BMI2), with fresh RDX temp to minimize
       register pressure. Falls back to Omulu otherwise. *)
    let use_mulx = true in
    if use_mulx then begin
      let rdx_tmp = Printf.sprintf "__rdx_%d" (let c = !mulx_rdx_counter in
                                                 incr mulx_rdx_counter; c) in
      let rdx_vi = mk_var_i rdx_tmp in
      let copy_to_rdx = mk_instr (Cassgn (Lvar rdx_vi, Expr.AT_none,
                                           Bty (U U64), translate_expr a)) in
      let lvs = [Lvar (mk_var_i (implode lo));
                 Lvar (mk_var_i (implode hi))] in
      [copy_to_rdx;
       mk_instr (Copn (lvs, Expr.AT_none,
                        x86_op (X86_instr_decl.MULX_lo_hi U64),
                        [Pvar (mk_gvar rdx_tmp); translate_expr b]))]
    end else begin
      let lvs = [Lvar (mk_var_i (implode hi));
                 Lvar (mk_var_i (implode lo))] in
      [mk_instr (Copn (lvs, Expr.AT_none,
                        pseudo_op (Pseudo_operator.Omulu U64),
                        [translate_expr a; translate_expr b]))]
    end

  | Bls12_jasmin_extracted.JCsub_flags (cf, result, a, b) ->
    (* Osubcarry U64 with 2-address form:
       result := a; [cf, result] = subcarry(result, b, false) *)
    let result_vi = mk_var_i (implode result) in
    let copy = mk_instr (Cassgn (Lvar result_vi, Expr.AT_none,
                                  Bty (U U64), translate_expr a)) in
    let lvs = [Lvar (mk_var_i (implode cf));
               Lvar result_vi] in
    [copy;
     mk_instr (Copn (lvs, Expr.AT_none,
                      pseudo_op (Pseudo_operator.Osubcarry U64),
                      [Pvar (mk_gvar (implode result));
                       translate_expr b;
                       Pbool false]))]

  | Bls12_jasmin_extracted.JCsbb (cf_out, result, a, b, cf_in) ->
    (* Osubcarry U64 with 2-address form:
       result := a; [cf_out, result] = subcarry(result, b, cf_in) *)
    let result_vi = mk_var_i (implode result) in
    let cf_in_gvar = { gv = mk_var_i (implode cf_in); gs = Expr.Slocal } in
    let copy = mk_instr (Cassgn (Lvar result_vi, Expr.AT_none,
                                  Bty (U U64), translate_expr a)) in
    let lvs = [Lvar (mk_var_i (implode cf_out));
               Lvar result_vi] in
    [copy;
     mk_instr (Copn (lvs, Expr.AT_none,
                      pseudo_op (Pseudo_operator.Osubcarry U64),
                      [Pvar (mk_gvar (implode result));
                       translate_expr b;
                       Pvar cf_in_gvar]))]

(* ================================================================ *)
(* Montgomery multiplication partitioning pass                       *)
(*                                                                   *)
(* The flat ~1096-instruction body of bls12_mul/bls12_square exceeds *)
(* the 15 GPRs available on x86-64.  We split the flat instruction   *)
(* sequence into smaller chunks, each wrapped as a jasmin inline fn. *)
(* Jasminc's inliner re-expands them, but the register allocator     *)
(* processes each inline function separately before inlining, so     *)
(* register pressure never exceeds ~50 per chunk.                    *)
(* ================================================================ *)

module VarSet = Set.Make(struct
  type t = var
  let compare = V.compare
end)

(** Extract variables used (read) by an expression. *)
let rec expr_vars (e : expr) : VarSet.t =
  match e with
  | Pconst _ -> VarSet.empty
  | Pbool _ -> VarSet.empty
  | Parr_init _ -> VarSet.empty
  | Pvar gv -> VarSet.singleton (Location.unloc gv.gv)
  | Pget (_, _, _, gv, idx) ->
    VarSet.add (Location.unloc gv.gv) (expr_vars idx)
  | Psub (_, _, _, gv, idx) ->
    VarSet.add (Location.unloc gv.gv) (expr_vars idx)
  | Pload (_, _, addr) -> expr_vars addr
  | Papp1 (_, e1) -> expr_vars e1
  | Papp2 (_, e1, e2) -> VarSet.union (expr_vars e1) (expr_vars e2)
  | PappN (_, es) ->
    List.fold_left (fun acc e1 -> VarSet.union acc (expr_vars e1)) VarSet.empty es
  | Pif (_, c, t, f) ->
    VarSet.union (expr_vars c) (VarSet.union (expr_vars t) (expr_vars f))

let exprs_vars (es : expr list) : VarSet.t =
  List.fold_left (fun acc e -> VarSet.union acc (expr_vars e)) VarSet.empty es

(** Extract variables defined (written) by an lvalue. *)
let lval_def (lv : lval) : VarSet.t =
  match lv with
  | Lvar vi -> VarSet.singleton (Location.unloc vi)
  | _ -> VarSet.empty

(** Extract variables used (read) by an lvalue (e.g. address in Lmem). *)
let lval_use (lv : lval) : VarSet.t =
  match lv with
  | Lnone _ -> VarSet.empty
  | Lvar _ -> VarSet.empty
  | Lmem (_, _, _, addr) -> expr_vars addr
  | Laset (_, _, _, _vi, idx) -> expr_vars idx
  | Lasub (_, _, _, _vi, idx) -> expr_vars idx

let lvals_def (lvs : lval list) : VarSet.t =
  List.fold_left (fun acc lv -> VarSet.union acc (lval_def lv)) VarSet.empty lvs

let lvals_use (lvs : lval list) : VarSet.t =
  List.fold_left (fun acc lv -> VarSet.union acc (lval_use lv)) VarSet.empty lvs

type x86_instr = (int, unit, X86_arch.extended_op Sopn.asm_op_t) ginstr

(** Compute (defs, uses) for a single flat instruction.
    Only handles flat instructions (Cassgn, Copn, Ccall).
    For Cif we conservatively include all variables. *)
let instr_def_use (i : x86_instr) : VarSet.t * VarSet.t =
  match i.i_desc with
  | Cassgn (lv, _, _, e) ->
    (lval_def lv, VarSet.union (lval_use lv) (expr_vars e))
  | Copn (lvs, _, _, es) ->
    (lvals_def lvs, VarSet.union (lvals_use lvs) (exprs_vars es))
  | Ccall (lvs, _, es) ->
    (lvals_def lvs, VarSet.union (lvals_use lvs) (exprs_vars es))
  | Csyscall (lvs, _, es) ->
    (lvals_def lvs, VarSet.union (lvals_use lvs) (exprs_vars es))
  | Cif (e, _ct, _cf) ->
    (* Conservative: treat as using the condition variables *)
    (VarSet.empty, expr_vars e)
  | _ ->
    (VarSet.empty, VarSet.empty)

(** Backward liveness analysis on a flat instruction list.
    Returns an array of live-variable sets, one per instruction.
    live_after[i] = variables live immediately after instruction i. *)
let liveness_analysis (instrs : x86_instr array) : VarSet.t array =
  let n = Array.length instrs in
  let live_after = Array.make n VarSet.empty in
  (* Backward pass: live_after[i] = use[i+1] ∪ (live_after[i+1] \ def[i+1]) *)
  for i = n - 2 downto 0 do
    let (def_next, use_next) = instr_def_use instrs.(i + 1) in
    live_after.(i) <- VarSet.union use_next (VarSet.diff live_after.(i + 1) def_next)
  done;
  live_after

(** Find optimal split points in a flat instruction list.
    Liveness-driven: cut wherever live_after[pos] is below a pressure
    threshold, regardless of chunk size.  This lets us avoid splitting
    in the middle of a dense accumulator section where >30 vars are
    simultaneously live.

    If no low-pressure points exist, falls back to size-based cuts at
    the local minimum within each window.

    Returns a list of split indices (positions to cut BEFORE). *)
let find_split_points (instrs : x86_instr array) (live_after : VarSet.t array)
    ~(target_chunk_size : int) : int list =
  let n = Array.length instrs in
  if n <= target_chunk_size then []
  else begin
    (* Maximum number of vars allowed to cross a chunk boundary.
       Above ~12 jasminc's Subroutine calling convention struggles to
       allocate the call args across the 6 SysV integer registers plus
       stack slots — so we prefer cutting only at genuine low-pressure
       points below this threshold. *)
    let pressure_threshold = 12 in
    let min_chunk_gap = target_chunk_size / 4 in
    let splits = ref [] in
    let last_split = ref 0 in
    (* Scan forward: at each position with liveness <= threshold,
       if we're far enough from the last split, cut here. *)
    for pos = 1 to n - 1 do
      let card = VarSet.cardinal live_after.(pos) in
      if card <= pressure_threshold && pos - !last_split >= min_chunk_gap then begin
        splits := pos :: !splits;
        last_split := pos
      end
    done;
    (* Fill long gaps: for any gap between consecutive splits (or between
       start and first split, or last split and end) larger than
       2 * target_chunk_size, insert fallback cuts at the local liveness
       minimum.  This handles dense sections like fe25519_mul's
       partial-product accumulator that have no low-pressure points. *)
    let find_local_min lo hi =
      let best_pos = ref lo in
      let best_live = ref (VarSet.cardinal live_after.(lo)) in
      for pos = lo + 1 to hi do
        let card = VarSet.cardinal live_after.(pos) in
        if card < !best_live then begin
          best_pos := pos;
          best_live := card
        end
      done;
      !best_pos
    in
    let boundaries = 0 :: List.rev !splits @ [n] in
    let extra_splits = ref [] in
    let rec walk = function
      | [] | [_] -> ()
      | a :: ((b :: _) as rest) ->
        let gap = b - a in
        if gap > 2 * target_chunk_size then begin
          let num_subchunks = (gap + target_chunk_size - 1) / target_chunk_size in
          let window = target_chunk_size / 3 in
          for sub = 1 to num_subchunks - 1 do
            let ideal = a + sub * gap / num_subchunks in
            let lo = max (a + 1) (ideal - window) in
            let hi = min (b - 1) (ideal + window) in
            let pos = find_local_min lo hi in
            extra_splits := pos :: !extra_splits
          done
        end;
        walk rest
    in
    walk boundaries;
    (* Merge and sort splits *)
    let all_splits = List.sort_uniq compare (!splits @ !extra_splits) in
    all_splits
  end

(** Partition a flat instruction list into chunks at the given split points.
    Returns a list of (chunk_instrs, live_in, live_out) triples. *)
let partition_at_splits (instrs : x86_instr array) (live_after : VarSet.t array)
    (splits : int list) : (x86_instr list * VarSet.t * VarSet.t) list =
  let n = Array.length instrs in
  (* Add boundaries: 0 at start, n at end *)
  let boundaries = 0 :: splits @ [n] in
  let chunks = ref [] in
  let rec process = function
    | [] | [_] -> ()
    | start :: ((next :: _) as rest) ->
      let chunk = Array.to_list (Array.sub instrs start (next - start)) in
      (* live_in: variables used in this chunk that were defined before it *)
      (* = use ∪ (live_out \ def) computed over the whole chunk *)
      let live_out = if next < n then
        (* live just before instruction [next] = use[next] ∪ (live_after[next] \ def[next]) ...
           but we already have live_after[next-1] which IS live just after instruction next-1,
           i.e. live just before instruction next *)
        live_after.(next - 1)
      else
        VarSet.empty (* nothing live after the last chunk *)
      in
      (* Compute live_in by forward-propagating from chunk start:
         live_in = variables in live_after[start-1] that are used in this chunk
         OR: do backward liveness starting from live_out over this chunk *)
      let live_in = ref live_out in
      for i = next - 1 downto start do
        let (def_i, use_i) = instr_def_use instrs.(i) in
        live_in := VarSet.union use_i (VarSet.diff !live_in def_i)
      done;
      chunks := (chunk, !live_in, live_out) :: !chunks;
      process rest
  in
  process boundaries;
  List.rev !chunks

(** Unique counter for generated inline function names. *)
let inline_fn_counter = ref 0

(** Rename internal variables in a chunk to make them unique per chunk.
    Variables in [interface_vars] (live-in ∪ live-out) keep their original
    names so the caller can pass them through function calls.
    All other variables get chunk-specific names to avoid cross-function
    interference in jasminc's global register allocator. *)
let rename_chunk_vars (chunk_idx : int) (chunk : x86_instr list)
    (interface_vars : VarSet.t) : x86_instr list =
  (* Build renaming table: old var name -> new var *)
  let rename_tbl : (string, var) Hashtbl.t = Hashtbl.create 97 in
  let rename_var (v : var) : var =
    if VarSet.mem v interface_vars then v
    else
      match Hashtbl.find_opt rename_tbl v.v_name with
      | Some v' -> v'
      | None ->
        let new_name = Printf.sprintf "%s_c%d" v.v_name chunk_idx in
        let v' = V.mk new_name v.v_kind v.v_ty Location._dummy [] in
        Hashtbl.add rename_tbl v.v_name v';
        v'
  in
  let rename_vi (vi : var_i) : var_i =
    Location.mk_loc (Location.loc vi) (rename_var (Location.unloc vi))
  in
  let rename_gvar (gv : int ggvar) : int ggvar =
    { gv = rename_vi gv.gv; gs = gv.gs }
  in
  let rec rename_expr (e : expr) : expr =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> e
    | Pvar gv -> Pvar (rename_gvar gv)
    | Pget (a, aa, ws, gv, idx) -> Pget (a, aa, ws, rename_gvar gv, rename_expr idx)
    | Psub (aa, ws, len, gv, idx) -> Psub (aa, ws, len, rename_gvar gv, rename_expr idx)
    | Pload (a, ws, addr) -> Pload (a, ws, rename_expr addr)
    | Papp1 (op, e1) -> Papp1 (op, rename_expr e1)
    | Papp2 (op, e1, e2) -> Papp2 (op, rename_expr e1, rename_expr e2)
    | PappN (op, es) -> PappN (op, List.map rename_expr es)
    | Pif (ty, c, t, f) -> Pif (ty, rename_expr c, rename_expr t, rename_expr f)
  in
  let rename_lval (lv : lval) : lval =
    match lv with
    | Lnone _ -> lv
    | Lvar vi -> Lvar (rename_vi vi)
    | Lmem (a, ws, loc, addr) -> Lmem (a, ws, loc, rename_expr addr)
    | Laset (a, aa, ws, vi, idx) -> Laset (a, aa, ws, rename_vi vi, rename_expr idx)
    | Lasub (aa, ws, len, vi, idx) -> Lasub (aa, ws, len, rename_vi vi, rename_expr idx)
  in
  let rec rename_instr (i : x86_instr) : x86_instr =
    { i with i_desc = rename_instr_r i.i_desc }
  and rename_instr_r ir =
    match ir with
    | Cassgn (lv, tag, ty, e) -> Cassgn (rename_lval lv, tag, ty, rename_expr e)
    | Copn (lvs, tag, op, es) -> Copn (List.map rename_lval lvs, tag, op, List.map rename_expr es)
    | Ccall (lvs, fn, es) -> Ccall (List.map rename_lval lvs, fn, List.map rename_expr es)
    | Csyscall (lvs, op, es) -> Csyscall (List.map rename_lval lvs, op, List.map rename_expr es)
    | Cif (e, s1, s2) -> Cif (rename_expr e, rename_stmt s1, rename_stmt s2)
    | Cfor (vi, r, s) -> Cfor (rename_vi vi, r, rename_stmt s)
    | Cwhile (a, s1, e, info, s2) -> Cwhile (a, rename_stmt s1, rename_expr e, info, rename_stmt s2)
    | Cassert (msg, e) -> Cassert (msg, rename_expr e)
  and rename_stmt s = List.map rename_instr s
  in
  List.map rename_instr chunk

(** Wrap a chunk of instructions as a subroutine function and produce
    the corresponding call instruction.
    Returns (subroutine_func, call_instr). *)
let wrap_chunk_as_subroutine (base_name : string) (chunk_idx : int)
    (chunk : x86_instr list) (live_in : VarSet.t) (live_out : VarSet.t)
    : (unit, X86_arch.extended_op Sopn.asm_op_t) func * x86_instr =
  incr inline_fn_counter;
  let fn_name = Printf.sprintf "%s__chunk_%d" base_name chunk_idx in
  let fn = mk_funname fn_name in
  (* Rename internal variables to be unique per chunk *)
  let interface_vars = VarSet.union live_in live_out in
  let renamed_chunk = rename_chunk_vars chunk_idx chunk interface_vars in
  (* Sort variables for deterministic ordering *)
  let in_vars = List.sort V.compare (VarSet.elements live_in) in
  let out_vars = List.sort V.compare (VarSet.elements live_out) in
  let in_var_is = List.map (fun v -> Location.mk_loc Location._dummy v) in_vars in
  let out_var_is = List.map (fun v -> Location.mk_loc Location._dummy v) out_vars in
  (* Build the subroutine function *)
  let ifunc : (unit, X86_arch.extended_op Sopn.asm_op_t) func = {
    f_loc = Location._dummy;
    f_annot = FInfo.f_annot_empty;
    f_info = ();
    f_cc = FInfo.Subroutine;
    f_name = fn;
    f_tyin = List.map (fun v -> v.v_ty) in_vars;
    f_args = in_vars;
    f_body = renamed_chunk;
    f_tyout = List.map (fun v -> v.v_ty) out_vars;
    (* ret_annot must have the same length as f_ret for Array_expansion.expand_fd *)
    f_ret_info = { FInfo.ret_annot = List.map (fun _ -> []) out_var_is;
                   ret_loc = Location._dummy };
    f_ret = out_var_is;
  } in
  (* Build the call instruction (no "inline" annotation — we want Subroutine
     calling convention so each chunk gets register-allocated independently) *)
  let call_lvs = List.map (fun vi -> Lvar vi) out_var_is in
  let call_args = List.map (fun vi ->
    Pvar { gv = vi; gs = Expr.Slocal }
  ) in_var_is in
  let call_instr = mk_instr (Ccall (call_lvs, fn, call_args)) in
  (ifunc, call_instr)

(** Main partitioning entry point.
    Takes a function name, its parameter names, and its flat body.
    If the body is large enough (>200 instructions), partitions it.
    Returns (inline_funcs_to_prepend, new_body). *)
let partition_for_regalloc ?(verbose=false) ?(threshold=200)
    ?(target_chunk_size=180)
    (func_name : string) (body : x86_stmt)
    : (unit, X86_arch.extended_op Sopn.asm_op_t) func list * x86_stmt =
  let n = List.length body in
  if n <= threshold then begin
    if verbose then
      Printf.eprintf "  [partition] %s: %d instrs <= threshold %d, skipping\n"
        func_name n threshold;
    ([], body)
  end else begin
    let instrs = Array.of_list body in
    let live_after = liveness_analysis instrs in
    let splits = find_split_points instrs live_after ~target_chunk_size in
    if verbose then begin
      let num_chunks = List.length splits + 1 in
      Printf.eprintf "  [partition] %s: %d instrs -> %d chunks (function outlining)\n"
        func_name n num_chunks;
      List.iter (fun sp ->
        Printf.eprintf "    cut at instr %d: %d live vars\n"
          sp (VarSet.cardinal live_after.(sp))
      ) splits
    end;
    (* Outline each chunk as a subroutine: live_in vars become args,
       live_out vars become returns.  The main function body becomes a
       sequence of JCcalls to the helpers.  Each helper gets its own
       jasminc register-allocation scope (bounded by live_in ∪ live_out),
       which is what breaks the >16-variable pressure on BLS12/X25519
       mul/square. *)
    let chunks = partition_at_splits instrs live_after splits in
    let helpers = ref [] in
    let new_body = ref [] in
    List.iteri (fun idx (chunk, live_in, live_out) ->
      (* Outline every chunk regardless of size, since liveness-driven
         splitting ensures the boundary is already low-pressure.  Each
         helper gets its own jasminc register-allocation scope. *)
      if List.length chunk = 0 then ()
      else begin
        let (helper, call_instr) =
          wrap_chunk_as_subroutine func_name idx chunk live_in live_out
        in
        helpers := helper :: !helpers;
        new_body := !new_body @ [call_instr];
        if verbose then
          Printf.eprintf "    outlined %s__chunk_%d: %d instrs, %d live_in, %d live_out\n"
            func_name idx (List.length chunk)
            (VarSet.cardinal live_in) (VarSet.cardinal live_out)
      end
    ) chunks;
    if verbose then
      Printf.eprintf "  [partition] outlined %d helpers; main body: %d instrs\n"
        (List.length !helpers) (List.length !new_body);
    (List.rev !helpers, !new_body)
  end

(* ================================================================ *)
(* Wrap gstmt into Prog.func / Prog.prog                            *)
(* ================================================================ *)

(** Build a Prog.func from a translated function.
    All our bedrock2 functions take pointers via registers (System V ABI:
    rdi, rsi, rdx, rcx, r8, r9) and return nothing. We declare each
    parameter as [reg u64].

    The optional [?cc] parameter overrides the default Export calling
    convention.  Stub-leaf callees (used for the empirical pass-15+
    Jasmin gate / roadmap §9 path (b)) must be [Subroutine] so jasminc's
    MakeReferenceArguments pass accepts the callsite-to-callee linkage. *)
let wrap_func ?(cc=FInfo.Export) ?(locals=[]) (name : string)
    (param_names : string list)
    (body : x86_stmt) : (unit, X86_arch.extended_op Sopn.asm_op_t) func =
  let fn = mk_funname name in
  let args = Stdlib.List.map mk_var param_names in
  let tyin = Stdlib.List.map (fun _ -> Bty (U U64)) param_names in
  (* Materialize each [(base, n)] in [locals] as a [Stack Direct] var of
     type [Arr (U64, n)] and prepend a [Cassgn (_, Parr_init U64 n)]
     initializer so jasminc's [Prog.locals] scan (which discovers locals
     from variables used in the body) picks it up. The Rocq side
     ([hoist_stack_decls_func] in src/Bedrock/Jasmin/Core.v) computes
     these entries from in-body [JCdecl (_, JTstack n, _)] nodes that
     the [translate_cmd] [JCdecl] case would otherwise erase. *)
  let stack_inits =
    Stdlib.List.map (fun (base, n) ->
      (* Reuse the var [register_stack_locals] (if called) already
         gensym'd and put into [current_stack_locals], so the body's
         [Laset]/[Pget] (emitted by [translate_cmd]/[translate_expr])
         and the init [Cassgn] reference the SAME var.  Otherwise
         gensym a fresh one. *)
      let v =
        match Hashtbl.find_opt current_stack_locals base with
        | Some (v', _) -> v'
        | None -> mk_stack_var base n
      in
      let lv = Lvar (Location.mk_loc Location._dummy v) in
      let ty = Arr (U64, n) in
      mk_instr (Cassgn (lv, Expr.AT_none, ty, Parr_init (U64, n)))
    ) locals
  in
  let body = stack_inits @ body in
  (* Export functions get [nospill] to protect from the CF.90 bug in jasminc
     that manifests when AutoSpill is applied to large functions. Inline chunk
     functions are small enough to not trigger this bug.
     Subroutine functions don't need nospill since they're typically small
     leaves (stubs / outlined chunks). *)
  let annot =
    if cc = FInfo.Export then
      { FInfo.f_annot_empty with
        FInfo.f_user_annot =
          [(Location.mk_loc Location._dummy "nospill", None)] }
    else
      FInfo.f_annot_empty
  in
  { f_loc = Location._dummy;
    f_annot = annot;
    f_info = ();
    f_cc = cc;
    f_name = fn;
    f_tyin = tyin;
    f_args = args;
    f_body = body;
    f_tyout = [];
    f_ret_info = { FInfo.ret_annot = []; ret_loc = Location._dummy };
    f_ret = [] }

(** Build a prog from a list of funcs. No global declarations. *)
let build_prog funcs : (unit, X86_arch.extended_op Sopn.asm_op_t) prog =
  ([], funcs)

(** Blocker C: build the i-th per-callsite wrapper subroutine for
    leaf described by [leaf_jfunc].  The wrapper has the same
    arity and parameter types as the leaf, but with fresh
    parameter names [F__cs{i}_p{j}].  The wrapper's body is a
    CLONE of the leaf's body with parameters substituted and
    internal locals suffixed with __cs{i}__ to make them
    per-wrapper-unique.  CC = [Subroutine] (call boundary
    preserved by jasminc's inliner).  No further [Ccall F(...)]
    survives in the wrapper, so jasminc's RegAlloc cannot
    coalesce the leaf's f_args across distinct wrapper sibling
    subroutines.

    Placed AFTER [wrap_func] and [translate_cmd] so it can
    consume them — defining it among the wrapper-bookkeeping
    helpers (alongside [build_wrapper_func]'s earlier
    declarations) would cause an OCaml forward-reference. *)
let build_wrapper_func
    (leaf_jfunc : Bls12_jasmin_extracted.jasmin_func) (i : int)
    : (unit, X86_arch.extended_op Sopn.asm_op_t) func =
  let fname = implode leaf_jfunc.Bls12_jasmin_extracted.jf_name in
  let leaf_param_names =
    Stdlib.List.map (fun (n, _ty) -> implode n)
      leaf_jfunc.Bls12_jasmin_extracted.jf_params
  in
  let arity = Stdlib.List.length leaf_param_names in
  let wname = mk_wrapper_name fname i in
  Hashtbl.replace wrap_callsite_wrappers wname ();
  let wrapper_param_names =
    let rec range j = if j >= arity then []
      else mk_wrapper_param_name fname i j :: range (j + 1)
    in range 0
  in
  (* Build parameter rename map: leaf-param name -> wrapper-param name. *)
  let param_map = Stdlib.List.combine leaf_param_names wrapper_param_names in
  let suffix = Printf.sprintf "__cs%d__" i in
  let cloned_body =
    clone_leaf_body_with_renames
      leaf_jfunc.Bls12_jasmin_extracted.jf_body param_map suffix
  in
  (* Reset wrapper-occurrence counter before translating the
     cloned body: the body should NOT itself trigger further
     wrapper-rewrite of nested JCcalls (these would be calls
     INSIDE the leaf's body, not callsites of the leaf itself). *)
  let saved =
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) wrap_callee_occurrence []
  in
  reset_wrapper_occurrence ();
  let body : x86_stmt = translate_cmd cloned_body in
  Hashtbl.clear wrap_callee_occurrence;
  Stdlib.List.iter (fun (k, v) ->
    Hashtbl.replace wrap_callee_occurrence k v
  ) saved;
  wrap_func ~cc:FInfo.Subroutine ~locals:[]
    wname wrapper_param_names body

(* ================================================================ *)
(* Main: translate all functions, compile, emit assembly             *)
(* ================================================================ *)

let usage () =
  Printf.eprintf "usage: %s <output.s> [--func <name>] [--verbose]\n" Sys.argv.(0);
  Printf.eprintf "  --func <name>  compile only the named function (must be a leaf)\n";
  exit 2

(** Parse command-line arguments.  Returns (outfile, func_filter, verbose). *)
let parse_args () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; out] -> (out, None, false)
  | [_; out; "--verbose"] -> (out, None, true)
  | [_; out; "--func"; fname] -> (out, Some fname, false)
  | [_; out; "--func"; fname; "--verbose"] -> (out, Some fname, true)
  | _ -> usage ()

(** Curve-agnostic entry point.  Per-curve drivers (see [bls12_main.ml],
    [x25519_64_main.ml]) call this with their extracted [jasmin_func]
    list, possibly via [Obj.magic] to coerce the structurally-identical
    type from a different extraction.

    The legacy [let () = compile_funcs ~funcs:Bls12_jasmin_extracted.bls12_all_jasmin]
    entry point at the bottom of this file is preserved so the BLS12
    benchmark binary (built directly from this file) still works. *)
let compile_funcs ~outfile ~func_filter ~verbose ~funcs =
  (* Step 1: Deduplicate by name (keep first) *)
  let all_funcs = funcs in
  let seen = Hashtbl.create 97 in
  let funcs = Stdlib.List.filter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    if Hashtbl.mem seen name then false
    else (Hashtbl.add seen name (); true)
  ) all_funcs in
  let n = Stdlib.List.length funcs in
  Printf.eprintf "[compile_direct] loaded %d unique functions\n" n;

  (* Step 2: Filter to a single function if --func was given,
     INCLUDING its transitive callees (jasminc's MakeReferenceArguments
     pass needs every called function to be present in the program). *)
  let funcs_to_compile =
    match func_filter with
    | None -> funcs
    | Some fname ->
      (* Build name->func lookup *)
      let tbl = Hashtbl.create 97 in
      Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
        Hashtbl.replace tbl (implode f.jf_name) f
      ) funcs;
      (* Collect direct callees of a jasmin_cmd *)
      let rec collect_calls acc (c : Bls12_jasmin_extracted.jasmin_cmd) =
        match c with
        | Bls12_jasmin_extracted.JCskip -> acc
        | Bls12_jasmin_extracted.JCseq (a, b) ->
          collect_calls (collect_calls acc a) b
        | Bls12_jasmin_extracted.JCcall (f, _) ->
          let n = implode f in
          if Stdlib.List.mem n acc then acc else n :: acc
        | Bls12_jasmin_extracted.JCif (_, ct, cf) ->
          collect_calls (collect_calls acc ct) cf
        | Bls12_jasmin_extracted.JCwhile (_, body) ->
          collect_calls acc body
        | Bls12_jasmin_extracted.JCdecl (_, _, body) ->
          collect_calls acc body
        | _ -> acc
      in
      (* BFS transitive closure *)
      let rec closure visited worklist =
        match worklist with
        | [] -> visited
        | n :: rest ->
          if Stdlib.List.mem n visited then closure visited rest
          else begin
            match Hashtbl.find_opt tbl n with
            | None -> closure (n :: visited) rest
            | Some f ->
              let callees = collect_calls [] f.Bls12_jasmin_extracted.jf_body in
              closure (n :: visited) (callees @ rest)
          end
      in
      if not (Hashtbl.mem tbl fname) then begin
        Printf.eprintf "[compile_direct] ERROR: function '%s' not found.\n" fname;
        Printf.eprintf "Available functions:\n";
        Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
          Printf.eprintf "  %s\n" (implode f.jf_name)
        ) funcs;
        exit 1
      end;
      let reachable_names = closure [] [fname] in
      let matches = Stdlib.List.filter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
        Stdlib.List.mem (implode f.jf_name) reachable_names
      ) funcs in
      Printf.eprintf "[compile_direct] filtering to function '%s' + %d transitive callees\n"
        fname (Stdlib.List.length matches - 1);
      matches
  in

  (* Step 3: Pre-register function names for functions we will compile *)
  Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    ignore (mk_funname name)
  ) funcs_to_compile;

  (* Step 3b: Populate the callee-arity table for stub leaves.
     For non-stub functions (real bedrock2-generated bodies) we don't
     touch the table — the BLS12 / X25519 benchmark binaries continue
     to pass args verbatim.

     Stub detection (2026-05-13): A25's original test was [body = JCskip].
     That was extended to also cover the identity read-write chain
     introduced by [Ed25519_Sign_StubLeaves.mk_stub_body] (path 1 of
     RegAllocation closure: gives jasminc visible writes through the
     dest param so regalloc cannot merge dest-arg registers across
     consecutive stub callsites with overlapping liveness).

     We detect new-style stubs structurally: a sequence (possibly
     length-1) where every leaf is a [JCstore base 0 (JEload _ 0)]
     — the identity-write-through-param pattern.  This is robust to
     N=1 (single store) and N>=2 (JCseq chain) stubs alike. *)
  (* A33 extension: also accept [JCstore (JEadd (JEvar _, JElit _), _, _)]
     so the implementing-body refinement (real Jasmin code for clamp +
     memmove leaves) is still detected as a stub.  The implementing
     bodies use [JEadd (JEvar p) (JElit off)] addresses to encode
     non-zero offsets — this is the addressing pattern jasminc's asmgen
     accepts; offsets in [JCstore base off ...] beyond 0 are not
     directly assembleable to x86 [mov [base+off], val].
     A99 extension: also accept [JCset x e] leaves, so the
     pre-loaded-constant clamp body (see [Ed25519_Sign_StubLeaves.
     clamp_64_body]) is detected as a stub leaf.  JCsets emit
     scalar Cassgns; they cannot escape the stub leaf's frame so
     they are safe to inline. *)
  let rec is_identity_store_chain (b : Bls12_jasmin_extracted.jasmin_cmd) : bool =
    let is_store_with_var_base e =
      match e with
      | Bls12_jasmin_extracted.JEvar _ -> true
      | Bls12_jasmin_extracted.JEadd (Bls12_jasmin_extracted.JEvar _,
                                       Bls12_jasmin_extracted.JElit _) -> true
      | _ -> false
    in
    match b with
    | Bls12_jasmin_extracted.JCskip -> true
    | Bls12_jasmin_extracted.JCstore (base, _, _) -> is_store_with_var_base base
    | Bls12_jasmin_extracted.JCset (_, _) -> true
    | Bls12_jasmin_extracted.JCseq (c1, c2) ->
      is_identity_store_chain c1 && is_identity_store_chain c2
    | _ -> false
  in
  let is_stub_body (b : Bls12_jasmin_extracted.jasmin_cmd) : bool =
    match b with
    | Bls12_jasmin_extracted.JCskip -> true
    | _ -> is_identity_store_chain b
  in
  (* A99 (sha512_64 GAP (B) attempt): wire sha512_64 + 4 other large
     externs into [extern_leaf_names] to test whether jasminc's
     RegAllocation has been (or can be) coaxed past A98's documented
     register-coalescing conflict.  Each name in this list:
       - keeps [FInfo.Subroutine] CC instead of [Internal];
       - omits the [inline] annotation at the callsite, so jasminc
         keeps the [Ccall];
       - lowers to a real [call <symbol>] in the emitted asm.

     A99 result: with the (default) [extern_leaf_names] empty list,
     emission succeeds with 0 calls (A98 baseline).  With [sha512_64]
     in the list (uncomment below) we re-trigger A98's documented
     RegAllocation failure ("conflicting variables k_full and r_full
     must be merged") because the 3 callsites in [ed25519_sign] all
     pass different first arguments through the SysV first-arg slot
     (RDI), and jasminc's coalescing pass cannot break that
     equivalence class without an explicit wrapper.

     Resolution paths considered, none mechanical with the current
     extraction:
       (a) Per-callsite wrapper functions ([sha512_64_h_full],
           [sha512_64_r_full], [sha512_64_k_full]) — requires
           modifying the extracted sign body, which is forbidden
           (Ed25519_Sign_Inlined.v is the verified extraction).
       (b) Driver-side callsite rewriting: detect [JCcall sha512_64 _]
           and rewrite to one of three per-callsite wrapper names
           depending on the first argument.  Mechanical but invasive
           — the rewrite is unverified and adds 50+ lines of OCaml
           dispatch glue.
       (c) Pre-load callsite first-arg into a fresh local var via
           [JCset] before each [JCcall], so jasminc's coalescer sees
           three distinct first-arg variables.  Tested by hand —
           jasminc still coalesces because the three locals all flow
           into RDI at the same instruction-index across the three
           callsites.

     HONEST CONCLUSION: with the present jasminc + extraction the
     [sha512_64] call cannot be emitted as a real [call <symbol>].
     The sha512 work in the protocol is performed by the surrounding
     Rust code (curve25519-jasmin-rs's libsodium / libjade harness),
     NOT by the Jasmin emission.  This is consistent with how the
     other 4 EXTERN leaves ([ed25519_scalarmult_base], [_compress],
     [scalar_reduce], [scalar_muladd]) are handled today.

     This list stays EMPTY in production.  Setting it to e.g.
     [["sha512_64"]] reproduces the documented RegAlloc failure
     for diagnostic purposes. *)
  let extern_leaf_names : string list =
    match Sys.getenv_opt "JASMIN_EXTERN_LEAVES" with
    | Some s when s <> "" -> String.split_on_char ',' s
    | _ -> []
  in

  Hashtbl.clear callee_arity_tbl;
  Hashtbl.clear extern_leaf_tbl;
  Stdlib.List.iter (fun name ->
    Hashtbl.replace extern_leaf_tbl name ()
  ) extern_leaf_names;
  Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    if is_stub_body f.Bls12_jasmin_extracted.jf_body then begin
      let name = implode f.Bls12_jasmin_extracted.jf_name in
      let arity = Stdlib.List.length f.Bls12_jasmin_extracted.jf_params in
      Hashtbl.replace callee_arity_tbl name arity;
      if verbose then
        Printf.eprintf "[compile_direct] callee_arity_tbl[%s] = %d (extern=%b)\n"
          name arity (Hashtbl.mem extern_leaf_tbl name)
    end
  ) funcs_to_compile;

  (* Step 3c (Blocker C): pre-scan for multi-callsite leaves.
     A callee is wrapped iff it is a registered stub leaf
     (in callee_arity_tbl) AND it has >=2 distinct call-sites
     across [funcs_to_compile].  Non-stub callees are left
     unwrapped — the BLS12 / X25519 benchmark binaries never
     hit the multi-callsite-same-arg coalescing problem because
     their schoolbook-mul leaves are called only once at the top
     of each operation. *)
  scan_multi_callsite_leaves funcs_to_compile;
  (* Restrict to stubs: drop counts for non-stub callees. *)
  Hashtbl.filter_map_inplace (fun name c ->
    if Hashtbl.mem callee_arity_tbl name then Some c else None
  ) wrap_callee_counts;
  Hashtbl.clear wrap_callsite_wrappers;
  if verbose then
    Hashtbl.iter (fun name c ->
      Printf.eprintf "[compile_direct] multi-callsite leaf [%s] count=%d -> %d wrappers\n"
        name c c
    ) wrap_callee_counts;

  (* Step 4: Translate each function, applying register-pressure partitioning.
     Functions with a JCskip body are treated as stub leaves (e.g. the FFI
     symbols used by Ed25519 sign for the empirical Jasmin gate of roadmap
     §9 path (b)).  Stubs are wrapped with [Subroutine] calling convention
     so jasminc's MakeReferenceArguments pass accepts them as callees. *)
  let all_inline_funcs = ref [] in
  let prog_funcs =
    Stdlib.List.map (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
      let name = implode f.jf_name in
      let params = Stdlib.List.map (fun (n, _ty) -> implode n) f.jf_params in
      (* Blocker C: reset per-callee occurrence counter before each
         top-level caller so wrapper indices i=0..N-1 correspond to
         the source-order JCcall positions within this caller. *)
      reset_wrapper_occurrence ();
      (* Blocker B: pre-compute [(base, n)] stack-locals from [jf_locals]
         and register them in [current_stack_locals] BEFORE [translate_cmd]
         so [JCstore]/[JEload] of a stack-local base get rewritten to
         [Laset]/[Pget] against the gensym'd stack-array var. *)
      let stack_locals_pre =
        Stdlib.List.filter_map (fun (nm, ty) ->
          match ty with
          | Bls12_jasmin_extracted.JTstack zn ->
            Some (implode nm, Z.to_int (z_of_coq_z zn))
          | _ -> None
        ) f.Bls12_jasmin_extracted.jf_locals
      in
      let _ = register_stack_locals stack_locals_pre in
      let body = translate_cmd f.jf_body in
      let stub = is_stub_body f.Bls12_jasmin_extracted.jf_body in
      if verbose then
        Printf.eprintf "  %-30s -> %d Prog instrs, %d params%s\n"
          name (Stdlib.List.length body) (Stdlib.List.length params)
          (if stub then " [stub leaf — Subroutine]" else "");
      (* Partition large functions into inline chunks *)
      let do_partition = true in (* set to false to skip partitioning *)
      let (inline_funcs, new_body) =
        if do_partition && not stub then
          (* Phase 2 outlining (partial, 2026-04-15):
             - Infrastructure: wrap_chunk_as_subroutine + partition_at_splits
               + liveness-driven find_split_points with gap-filling fallback.
             - With threshold=80, fe25519_mul splits into 11 chunks.  Chunks
               4-10 work fine (<=13 vars crossing), but chunks 0-3 have
               20-36 vars crossing because the schoolbook partial-product
               accumulation has no low-pressure point anywhere in its
               first half.  20+ u64 SysV args overwhelms jasminc's RegAlloc.
             - threshold=200 disables outlining so the 7 working functions
               + BLS12 byte-identical regression are preserved.
             - Next step (future work): pass cross-chunk state via stack
               struct instead of individual register/stack args. *)
          partition_for_regalloc ~verbose ~threshold:200 ~target_chunk_size:180
            name body
        else
          ([], body) in
      all_inline_funcs := inline_funcs @ !all_inline_funcs;
      (* For stub leaves the body is either [JCskip] (legacy) or an
         identity read-write chain ([JCstore (JEvar p) 0 (JEload q 0)]
         for params p,q — see [Ed25519_Sign_StubLeaves.mk_stub_body]).

         Calling convention selection (2026-05-13, A26 closure of A25's
         pass-28 RegAllocation conflict):
         - [Subroutine] fails at RegAllocation because the SysV-style
           param-register slots force [R_bytes] and [A_bytes] to coalesce
           into the same physical register at callsites where they are
           simultaneously live (the chal_A/chal_R/sig_R follow-up calls).
         - [Internal] inlines the stub body at each callsite so there
           are no cross-callsite register constraints; the identity
           load-store body lets the inliner succeed (A25's [JCskip]
           hit [varalloc.ml:422 assert false]; with non-empty body
           that assertion is bypassed). *)
      let cc =
        if stub then
          (* A33: extern leaves use Subroutine so jasminc keeps the call.
             Other stubs use Internal so inlining DCEs them.

             Blocker C: when this stub is the target of per-callsite
             wrappers (in [wrap_callee_counts]), the wrappers carry
             a CLONE of its body so the leaf itself is no longer
             called from any caller.  [Internal] CC + the
             RemoveUnusedFunction pass DCEs it away in that case. *)
          if Hashtbl.mem extern_leaf_tbl name then FInfo.Subroutine
          else FInfo.Internal
        else FInfo.Export
      in
      (* Consume [jf_locals]: each [(name, JTstack n)] becomes a
         [Stack Direct] var of type [Arr (U64, n)] in the emitted func.
         JTu64 and JTptr entries (if any) are ignored — those are
         scalar locals discovered by jasminc's [Prog.locals] scan from
         body references, identical to the legacy path. *)
      let stack_locals =
        Stdlib.List.filter_map (fun (nm, ty) ->
          match ty with
          | Bls12_jasmin_extracted.JTstack zn ->
            Some (implode nm, Z.to_int (z_of_coq_z zn))
          | _ -> None
        ) f.Bls12_jasmin_extracted.jf_locals
      in
      if verbose && stack_locals <> [] then
        Printf.eprintf "    [%s] hoisted %d stack locals: %s\n"
          name (Stdlib.List.length stack_locals)
          (String.concat ", "
            (Stdlib.List.map (fun (n,sz) -> Printf.sprintf "%s[%d]" n sz)
              stack_locals));
      let wrapped = wrap_func ~cc ~locals:stack_locals name params new_body in
      (* Blocker B: clear the per-function stack-local mapping AFTER
         [wrap_func] has consumed [current_stack_locals] for the
         [Cassgn Parr_init] initializer.  Otherwise a subsequent stub
         leaf's [JCstore (JEvar p) ...] could accidentally match a
         stale caller-stack-local name and emit broken [Laset]
         against an array from another function. *)
      clear_stack_locals ();
      wrapped
    ) funcs_to_compile
  in
  (* Blocker C: build per-callsite wrapper subroutines for every
     leaf in [wrap_callee_counts] (count >= 2).  Each wrapper
     forwards to the underlying leaf; the i-th wrapper has the i-th
     position among that leaf's callsites in source order.  The
     wrappers must be ordered AFTER the callers but BEFORE the
     leaves in [prog_funcs] so jasminc's inliner (foldr) processes
     them after the leaves are "available", letting Internal-CC
     stub bodies inline into each wrapper. *)
  (* Build a name -> jasmin_func lookup so we can clone each leaf's
     body into its per-callsite wrappers. *)
  let leaf_lookup : (string, Bls12_jasmin_extracted.jasmin_func) Hashtbl.t =
    Hashtbl.create 17
  in
  Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    Hashtbl.replace leaf_lookup (implode f.jf_name) f
  ) funcs_to_compile;
  let wrapper_funcs : (unit, X86_arch.extended_op Sopn.asm_op_t) func list =
    Hashtbl.fold (fun fname n acc ->
      match Hashtbl.find_opt leaf_lookup fname with
      | None -> acc
      | Some leaf_jfunc ->
        let rec build i acc =
          if i >= n then acc
          else build (i + 1) (build_wrapper_func leaf_jfunc i :: acc)
        in build 0 acc
    ) wrap_callee_counts []
  in
  if verbose then
    Printf.eprintf "[compile_direct] generated %d per-callsite wrapper subroutines\n"
      (Stdlib.List.length wrapper_funcs);

  (* Inline functions must appear AFTER the export functions that call them,
     because jasminc's inliner (inline_prog) uses foldr, processing the list
     from right to left.  Functions later in the list are available to inline
     into functions earlier in the list.

     Layout: [callers...; wrapper_funcs...; stub_leaves...; chunk_helpers...].
     The callers reference the wrappers via Ccall (no inline) — wrappers must
     follow.  The wrappers' bodies call the underlying stub leaf with inline
     annotation — the leaf must follow the wrappers.  Note that with stub leaves
     and chunk helpers both already living in prog_funcs / all_inline_funcs,
     splicing the wrappers between callers and leaves requires reordering. *)
  let (caller_funcs, leaf_funcs) =
    Stdlib.List.partition (fun (f : (unit, X86_arch.extended_op Sopn.asm_op_t) func) ->
      (* Discriminate by whether the function's name is registered as a stub
         (i.e., appears in callee_arity_tbl); stubs are leaves and must
         follow their wrappers in the program list so the inliner can fold
         the stub body into each wrapper. *)
      let func_name_str = f.f_name.CoreIdent.fn_name in
      not (Hashtbl.mem callee_arity_tbl func_name_str)
    ) prog_funcs
  in
  let prog = build_prog (caller_funcs @ wrapper_funcs @ leaf_funcs @ !all_inline_funcs) in

  Printf.eprintf "[compile_direct] built prog with %d functions (%d inline helpers)\n"
    (Stdlib.List.length (snd prog)) (Stdlib.List.length !all_inline_funcs);

  (* Step 4b: Run automatic spilling pass.
     This inserts spill/unspill pseudo-ops around every register variable
     definition/use, which breaks long live ranges and dramatically reduces
     register pressure.  The LowerSpill pass in the compiler then converts
     these to real MOV instructions between registers and stack slots.
     OptIn strategy: only spill variables explicitly annotated [#spill].
     We don't use OptOut because it can interfere with flag variables. *)
  (* AutoSpill pass: insert spill/unspill pseudo-ops to break long live ranges.

     Blocker D investigation (A117, 2026-05-14): the 23-instr [ed25519_sign]
     body has ~20 simultaneously-live Reg variables crossing the 9
     callsite-wrapper [Ccall]s — see A117 design notes below.  RegAllocation
     fails with "no more free register" (only 15 GPRs available).

     AutoSpill is intentionally LEFT DISABLED here.  Reasoning:

       - [OptOut] would spill every Reg variable in functions NOT annotated
         [nospill].  [ed25519_sign] is currently annotated [nospill] (line
         ~1213 below).  Removing that annotation lets [OptOut] try to spill
         the export's locals, but it then trips [LowerSpill] with:
           "The variable h_full.152 needs to be spilled before"
         The root cause: [translate_expr (JEvar "h_full")] creates a
         phantom Reg-kind var that is READ (passed as a [Ccall] arg) but
         never WRITTEN in [ed25519_sign]'s body.  The materialized stack
         array [__stk_N_h_full] is a SEPARATE var that is only referenced
         in the [Cassgn _ (Parr_init U64 n)] init at the function entry,
         not by the body's [Pvar h_full] arg pass.  AutoSpill assumes every
         Reg var is either a function arg (spilled at entry) or assigned
         before being read; the phantom Reg vars satisfy neither.

       - [OptIn] requires explicit [#[spill]] annotations on each
         variable, which the bedrock2-extracted bodies don't carry.

     Path-out options (all >100 LoC, not landed in this commit):
       (1) Rework [translate_expr (JEvar s)] to consult [current_stack_locals]
           and redirect to the stack array.  Needs a [Reg Pointer]-kind
           alias declared at the function entry that points to the stack
           array, plus type changes in the wrapper subroutines' params
           (currently typed [Reg u64]).  Roughly a 200-LoC OCaml change.
       (2) Convert ALL stub leaves to [Subroutine] cc and generate
           per-callsite wrappers for every one (not just multi-callsite).
           Today's [scan_multi_callsite_leaves] handles count>=2 only;
           extending to count>=1 produces wrappers for clamp_64 and all 8
           memmove leaves.  This would break the per-Ccall live ranges by
           giving each wrapper distinct param symbols.  Probably 50-80
           LoC, but the wrappers themselves still need their args allocated
           inside [ed25519_sign].
       (3) Manual outlining: split [ed25519_sign] into 3-4 helper
           subroutines (e.g. seed-hash, clamp+nonce-build, ml+final-hash,
           compress+output).  This is the cleanest reduction of per-function
           live sets but the cut points are non-obvious without rerunning
           liveness analysis and the cross-helper state passing needs
           stack-struct args.

     For now AutoSpill stays off and the regalloc failure stays as the
     gate.  Blocker D remains open; this commit documents what was tried
     and what didn't work. *)
  let use_autospill = false in
  let prog =
    if use_autospill then begin
      Printf.eprintf "[compile_direct] running AutoSpill (OptOut strategy)...\n%!";
      let prog' = AutoSpill.doit AutoSpill.OptOut prog in
      Printf.eprintf "[compile_direct] AutoSpill done\n%!";
      prog'
    end else
      prog
  in

  (* Step 5: Run jasminc's full compiler pipeline *)
  Printf.eprintf "[compile_direct] calling Conv.cuprog_of_prog ...\n%!";
  let cprog =
    try Conv.cuprog_of_prog prog
    with e ->
      Printf.eprintf "[compile_direct] Conv.cuprog_of_prog raised: %s\n"
        (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      exit 1
  in
  Printf.eprintf "[compile_direct] Conv succeeded, calling Compile.compile ...\n%!";
  let step_name (s : Compiler.compiler_step) =
    match s with
    | Typing -> "Typing" | ParamsExpansion -> "ParamsExpansion"
    | RemoveAssertion -> "RemoveAssertion" | InsertRenaming -> "InsertRenaming"
    | WintWord -> "WintWord" | ArrayCopy -> "ArrayCopy"
    | AddArrInit -> "AddArrInit" | LowerSpill -> "LowerSpill"
    | Inlining -> "Inlining" | RemoveUnusedFunction -> "RemoveUnusedFunction"
    | Unrolling -> "Unrolling" | Splitting -> "Splitting"
    | Renaming -> "Renaming" | RemovePhiNodes -> "RemovePhiNodes"
    | DeadCode_Renaming -> "DeadCode_Renaming" | RemoveArrInit -> "RemoveArrInit"
    | MakeRefArguments -> "MakeRefArguments"
    | RegArrayExpansion -> "RegArrayExpansion"
    | RemoveGlobal -> "RemoveGlobal"
    | LoadConstantsInCond -> "LoadConstantsInCond"
    | LowerInstruction -> "LowerInstruction"
    | PropagateInline -> "PropagateInline"
    | SLHLowering -> "SLHLowering" | LowerAddressing -> "LowerAddressing"
    | StackAllocation -> "StackAllocation" | RemoveReturn -> "RemoveReturn"
    | RegAllocation -> "RegAllocation"
    | DeadCode_RegAllocation -> "DeadCode_RegAllocation"
    | Linearization -> "Linearization" | StackZeroization -> "StackZeroization"
    | Tunneling -> "Tunneling" | Assembly -> "Assembly"
  in
  let visit_prog_after_pass ~debug:_ step _prog =
    if verbose then Printf.eprintf "  [pass] %s OK\n%!" (step_name step)
  in
  let result =
    try Compile.compile (module X86_arch) visit_prog_after_pass prog cprog
    with
    | Utils.HiError hierr ->
      Printf.eprintf "[compile_direct] Compile.compile raised HiError:\n";
      Format.eprintf "  %a\n" Utils.pp_hierror hierr;
      exit 1
    | e ->
      Printf.eprintf "[compile_direct] Compile.compile raised: %s\n"
        (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      exit 1
  in
  begin
    match result with
    | Utils0.Ok asm_prog ->
      Printf.eprintf "[compile_direct] compilation succeeded!\n";

      (* Step 6: Emit assembly *)
      let oc = open_out outfile in
      let fmt = Format.formatter_of_out_channel oc in
      Pp_x86.print_prog fmt (Obj.magic asm_prog);
      Format.pp_print_flush fmt ();
      close_out oc;
      Printf.eprintf "[compile_direct] wrote assembly to %s\n" outfile

    | Utils0.Error err ->
      let hierr = Conv.error_of_cerror
        (Printer.pp_err ~debug:true) err in
      Printf.eprintf "[compile_direct] compilation FAILED (error result):\n";
      Format.eprintf "  %a\n" Utils.pp_hierror hierr;
      exit 1
  end

(** No top-level [let () = ...] here so this file can be used as a
    library by per-curve drivers ([bls12_main.ml], [x25519_64_main.ml]).
    Each curve has its own thin driver that loads its extracted funcs
    and calls [compile_funcs]. *)
