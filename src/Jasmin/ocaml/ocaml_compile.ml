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
    let addr =
      if Z.equal z_off Z.zero then
        translate_expr base
      else
        Papp2 (Operators.Oadd (Operators.Op_w U64),
               translate_expr base,
               Pconst z_off)
    in
    Pload (Memory_model.Aligned, U64, addr)

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
    let addr =
      if Z.equal z_off Z.zero then
        translate_expr base
      else
        Papp2 (Operators.Oadd (Operators.Op_w U64),
               translate_expr base,
               Pconst z_off)
    in
    (* Hoist the store value into a fresh temp register so the RHS of
       [Cassgn (Lmem ...)] is always a bare [Pvar]. Partial fix for
       linearization issues; deeper nested-load patterns (clamp) still
       hit jasminc limitations in asmgen. *)
    let tmp_id = let c = !mulx_rdx_counter in incr mulx_rdx_counter; c in
    let tmp_name = Printf.sprintf "__store_tmp_%d" tmp_id in
    let tmp_var = mk_var tmp_name in
    let tmp_var_i = Location.mk_loc Location._dummy tmp_var in
    let tmp_gvar = { gv = tmp_var_i; gs = Expr.Slocal } in
    [mk_instr (Cassgn (Lvar tmp_var_i, Expr.AT_none, Bty (U U64),
                       translate_expr v));
     mk_instr (Cassgn (Lmem (Memory_model.Aligned, U64, Location._dummy, addr),
                        Expr.AT_none, Bty (U U64), Pvar tmp_gvar))]

  | Bls12_jasmin_extracted.JCcall (f, args) ->
    let fname = implode f in
    let fn = mk_funname fname in
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
       (varalloc.ml:422). *)
    let make_call =
      if Hashtbl.mem callee_arity_tbl fname then mk_instr_inline
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
let wrap_func ?(cc=FInfo.Export) (name : string) (param_names : string list)
    (body : x86_stmt) : (unit, X86_arch.extended_op Sopn.asm_op_t) func =
  let fn = mk_funname name in
  let args = Stdlib.List.map mk_var param_names in
  let tyin = Stdlib.List.map (fun _ -> Bty (U U64)) param_names in
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
  let rec is_identity_store_chain (b : Bls12_jasmin_extracted.jasmin_cmd) : bool =
    match b with
    | Bls12_jasmin_extracted.JCskip -> true
    | Bls12_jasmin_extracted.JCstore (Bls12_jasmin_extracted.JEvar _, _, _) -> true
    | Bls12_jasmin_extracted.JCseq (c1, c2) ->
      is_identity_store_chain c1 && is_identity_store_chain c2
    | _ -> false
  in
  let is_stub_body (b : Bls12_jasmin_extracted.jasmin_cmd) : bool =
    match b with
    | Bls12_jasmin_extracted.JCskip -> true
    | _ -> is_identity_store_chain b
  in
  Hashtbl.clear callee_arity_tbl;
  Stdlib.List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    if is_stub_body f.Bls12_jasmin_extracted.jf_body then begin
      let name = implode f.Bls12_jasmin_extracted.jf_name in
      let arity = Stdlib.List.length f.Bls12_jasmin_extracted.jf_params in
      Hashtbl.replace callee_arity_tbl name arity;
      if verbose then
        Printf.eprintf "[compile_direct] callee_arity_tbl[%s] = %d\n" name arity
    end
  ) funcs_to_compile;

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
      let cc = if stub then FInfo.Internal else FInfo.Export in
      wrap_func ~cc name params new_body
    ) funcs_to_compile
  in
  (* Inline functions must appear AFTER the export functions that call them,
     because jasminc's inliner (inline_prog) uses foldr, processing the list
     from right to left.  Functions later in the list are available to inline
     into functions earlier in the list. *)
  let prog = build_prog (prog_funcs @ !all_inline_funcs) in

  Printf.eprintf "[compile_direct] built prog with %d functions (%d inline helpers)\n"
    (Stdlib.List.length (snd prog)) (Stdlib.List.length !all_inline_funcs);

  (* Step 4b: Run automatic spilling pass.
     This inserts spill/unspill pseudo-ops around every register variable
     definition/use, which breaks long live ranges and dramatically reduces
     register pressure.  The LowerSpill pass in the compiler then converts
     these to real MOV instructions between registers and stack slots.
     OptIn strategy: only spill variables explicitly annotated [#spill].
     We don't use OptOut because it can interfere with flag variables. *)
  (* AutoSpill pass: insert spill/unspill pseudo-ops to break long live ranges *)
  let use_autospill = false in
  let prog =
    if use_autospill then begin
      Printf.eprintf "[compile_direct] running AutoSpill (OptIn strategy)...\n%!";
      let prog' = AutoSpill.doit AutoSpill.OptIn prog in
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
