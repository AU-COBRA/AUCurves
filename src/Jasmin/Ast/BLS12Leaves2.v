(** * The BLS12-381 Fp leaves through the optimising translation [Carry.xcmd]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize expr arch_extra x86_extra.
From Stdlib Require Import String.
Require Import bedrock2.Syntax.
Require Import Bedrock.JasminAst.BLS12LeafBodies.
Require Import JasminBridge.Ast.Trans JasminBridge.Ast.Comp JasminBridge.Ast.Fun
  JasminBridge.Ast.BLS12Leaves JasminBridge.Ast.Carry JasminBridge.Ast.SpillChoice.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Section L.
  Context {atoI : arch_toIdent}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.
  (** Supplied by the driver: names of the [u64] variables, the identifier of the boolean
      carry variable, names of functions, function and instruction information. *)
  Variables (name : string -> Ident.ident) (cfn : Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info).
  (** The register budget of the spill choice [SpillChoice.spill_live]. *)
  Variable budget : nat.

  Definition spill2 (ps : list string) (b : cmd) : string -> bool := spill_live name cfn budget ps b.

  (** The optimised code, or the code of [Comp.ccmd_sp] if the optimised translation fails. *)
  Definition leaf_code2 (ps : list string) (b : cmd) : jcmd :=
    match xcmd name cfn (spill2 ps b) ps b with
    | Some c => c
    | None => odflt [::] (ccmd_sp name (spill2 ps b) b)
    end.

  Definition leaf2 (fn : string) (ps : list string) (b : cmd) : ufun_decl :=
    (fname fn, jfun name iinfo (spill2 ps b) (finfo fn) ps (leaf_code2 ps b)).

  Definition bls12_leaves2_funcs : seq ufun_decl :=
    [:: leaf2 "bls12_add" params3 bls12_add_body;
        leaf2 "bls12_sub" params3 bls12_sub_body;
        leaf2 "bls12_mul" params3 bls12_mul_body;
        leaf2 "bls12_square" params2 bls12_square_body].

  Definition bls12_leaves2_prog : uprog :=
    {| p_funcs := bls12_leaves2_funcs; p_globs := [::]; p_extra := tt |}.
End L.
