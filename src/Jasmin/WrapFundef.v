(** * WrapFundef: lift the per-leaf [rust_cmd_ed_to_real_jasmin] body
 *    into a full Jasmin [fundef] (function definition with signature).
 *
 *  Currently each leaf extraction (ExtractFe25519MulReal.v etc.)
 *  emits just a [Jasmin.expr.cmd] — the function body.  The
 *  surrounding [.jazz] declaration (fn name + parameter list +
 *  return type + array layout) is hand-written.
 *
 *  This file closes that gap: takes the body plus the [located_ed]
 *  metadata that produced it ([loc_var] names + [loc_type] types)
 *  and constructs the matching [Jasmin.expr._fundef] record, so the
 *  whole function (signature included) is now Rocq-generated.
 *
 *  Remaining hand work: the [.jazz] *text* rendering.  Jasmin has an
 *  OCaml-side pretty-printer in its toolchain; the AUCurves OCaml
 *  driver can call into it once linked.  Closing that loop is
 *  smaller than this file and is tracked separately.
 *)

From HB Require Import structures.
From Jasmin Require Import expr x86_instr_decl x86_extra arch_extra
                            warray_ var type sopn wsize ident utils.
From mathcomp Require Import ssreflect ssrfun ssrnat seq.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import JasminBridge.RealJasminInstance.
Require Import JasminBridge.BridgeReal.

(* RealJasminInstance has `Axiom atoI` + `#[local] Existing Instance atoI`,
   but the locality means downstream files re-export the axiom but not
   the Existing Instance hint.  Re-arm it here so x86_extended_op
   resolves. *)
#[local] Existing Instance atoI | 0.

Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Map a located_ed to a Jasmin [var]                            *)
(*                                                                  *)
(* Every located_ed carries a [loc_var] (string name) and a         *)
(* [loc_type : tower_type_ed].  In current Jasmin, syntax types are *)
(* [atype = abool | aint | aarr wsize positive | aword wsize].      *)
(* Field-element buffers map to [aarr U64 k] where k = bytes/8       *)
(* (matches libjade's [reg ptr u64[k]] convention).  Generic byte    *)
(* buffers map to [aarr U8 n].  Scalars are [aword U64].             *)
(* ================================================================ *)

Definition jasmin_type_of_loc_type (t : tower_type_ed) : atype :=
  match t with
  | TFp25519     => aarr U64 5  (* 5×u64 = 40 bytes (radix-2^51)  *)
  | TFp25519_64  => aarr U64 4  (* 4×u64 = 32 bytes (saturated)   *)
  | TFpL25519    => aarr U64 4  (* 4×u64 = 32 bytes (scalar)      *)
  | TBytes n     => aarr U8 (Pos.of_nat (S n))
                                (* [S] guards degenerate n=0      *)
  | TU64         => aword U64
  | TArr n t'    => aarr U8 (Pos.of_nat (S (n * tt_bytes_ed t')))
                                (* flatten to bytes; nested arrays
                                   collapsed to byte view         *)
  end.

(** Build a [var_i] from a located_ed.  [v_info] is a stub
    [VarInfo.witness] for now; the OCaml pretty-printer can override. *)
Definition var_i_of_located (l : located_ed) : var_i :=
  {| v_var :=
       {| vtype := jasmin_type_of_loc_type l.(loc_type);
          vname := BridgeReal.int_to_ident
                     (BridgeReal.string_to_ident l.(loc_var)) |};
     v_info := VarInfo.witness |}.

(* ================================================================ *)
(* §2. Wrap a body + locals into a Jasmin [_fundef]                  *)
(* ================================================================ *)

(** Returns a [_fundef unit] (no extra-info payload).  The convention
    in our pipeline is: the destination buffer is an output parameter
    (memory write), so it appears in [f_params] but NOT in [f_res]; the
    function returns no value.  This matches the C-ABI shape libjade
    uses for [fe25519_mul(out, x, y)] etc. *)
Definition wrap_fundef
  (dest : located_ed)
  (args : list located_ed)
  (body : cmd)
  : @_fundef x86_extended_op _ unit :=
  let all_locals := dest :: args in
  let param_vars := List.map var_i_of_located all_locals in
  let param_tys :=
        List.map (fun l => jasmin_type_of_loc_type l.(loc_type)) all_locals in
  {| f_info     := FunInfo.witness;
     f_contract := None;
     f_tyin     := param_tys;
     f_params   := param_vars;
     f_body     := body;
     f_tyout    := nil;
     f_res      := nil;
     f_extra    := tt;
  |}.

(* ================================================================ *)
(* §3. Convenience: assemble a complete one-function [prog]          *)
(* ================================================================ *)

Definition wrap_prog
  (fname : string)
  (dest : located_ed)
  (args : list located_ed)
  (body : cmd)
  : @_prog x86_extended_op _ unit unit :=
  let fd := wrap_fundef dest args body in
  {| p_funcs := [(BridgeReal.int_to_funname
                    (BridgeReal.string_to_ident fname), fd)];
     p_globs := nil;
     p_extra := tt |}.
