(** * The BLS12-381 Fp leaves add, sub, mul, square as a Jasmin program built in Rocq. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize expr arch_extra x86_extra.
From Stdlib Require Import String.
Require Import bedrock2.Syntax.
Require Import Bedrock.JasminAst.BLS12LeafBodies.
Require Import JasminBridge.Ast.Trans JasminBridge.Ast.Comp JasminBridge.Ast.Fun.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Section L.
  Context {atoI : arch_toIdent}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.
  (** Supplied by the driver: names of variables and functions, function and instruction
      information (all abstract in Jasmin's Rocq development). *)
  Variables (name : string -> Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info).

  Definition params3 : list string := [:: "out0"; "in0"; "in1"].
  Definition params2 : list string := [:: "out0"; "in0"].

  (** Spill choice (any choice is proved correct): a source variable is kept in a stack slot
      when two consecutive occurrences of it (definition or use; parameters occur at entry)
      are more than [K] statements apart. *)
  Variable K : nat.

  Fixpoint stmts (c : cmd) : list cmd :=
    match c with cmd.seq a b => stmts a ++ stmts b | c => [:: c] end.

  Definition occ_vars (c : cmd) : list string :=
    match c with
    | cmd.set y e => y :: vars_e e
    | cmd.store _ a v => vars_e a ++ vars_e v
    | _ => [::]
    end.

  Fixpoint lookup (l : list (string * nat)) (x : string) : option nat :=
    match l with [::] => None | (y, j) :: l => if String.eqb x y then Some j else lookup l x end.

  Fixpoint scan (i : nat) (cs : list cmd) (last : list (string * nat)) (long : list string) :=
    match cs with
    | [::] => long
    | c :: cs =>
        let xs := occ_vars c in
        let long' := foldl (fun acc x =>
                       match lookup last x with
                       | Some j => if (K < i - j)%nat then x :: acc else acc
                       | None => acc
                       end) long xs in
        let last' := foldl (fun acc x => (x, i) :: acc) last xs in
        scan i.+1 cs last' long'
    end.

  Definition spill_choice (ps : list string) (b : cmd) : string -> bool :=
    let long := scan 1 (stmts b) [seq (p, 0%nat) | p <- ps] [::] in
    fun x => has (String.eqb x) long.

  Definition leaf_code (ps : list string) (b : cmd) : jcmd :=
    odflt [::] (ccmd_sp name (spill_choice ps b) b).

  Definition leaf (fn : string) (ps : list string) (b : cmd) : ufun_decl :=
    (fname fn, jfun name iinfo (spill_choice ps b) (finfo fn) ps (leaf_code ps b)).

  Definition bls12_leaves_funcs : seq ufun_decl :=
    [:: leaf "bls12_add" params3 bls12_add_body;
        leaf "bls12_sub" params3 bls12_sub_body;
        leaf "bls12_mul" params3 bls12_mul_body;
        leaf "bls12_square" params2 bls12_square_body].

  Definition bls12_leaves_prog : uprog :=
    {| p_funcs := bls12_leaves_funcs; p_globs := [::]; p_extra := tt |}.

  (** All four bodies are in the translated fragment. *)
  Lemma ccmd_add : ccmd_sp name (spill_choice params3 bls12_add_body) bls12_add_body =
    Some (leaf_code params3 bls12_add_body).
  Proof.
    have h : isSome (ccmd name bls12_add_body) by vm_compute.
    have := ccmd_sp_some name (spill_choice params3 bls12_add_body) bls12_add_body h.
    by rewrite /leaf_code; case: (ccmd_sp name (spill_choice params3 bls12_add_body) bls12_add_body).
  Qed.
  Lemma ccmd_sub : ccmd_sp name (spill_choice params3 bls12_sub_body) bls12_sub_body =
    Some (leaf_code params3 bls12_sub_body).
  Proof.
    have h : isSome (ccmd name bls12_sub_body) by vm_compute.
    have := ccmd_sp_some name (spill_choice params3 bls12_sub_body) bls12_sub_body h.
    by rewrite /leaf_code; case: (ccmd_sp name (spill_choice params3 bls12_sub_body) bls12_sub_body).
  Qed.
  Lemma ccmd_mul : ccmd_sp name (spill_choice params3 bls12_mul_body) bls12_mul_body =
    Some (leaf_code params3 bls12_mul_body).
  Proof.
    have h : isSome (ccmd name bls12_mul_body) by vm_compute.
    have := ccmd_sp_some name (spill_choice params3 bls12_mul_body) bls12_mul_body h.
    by rewrite /leaf_code; case: (ccmd_sp name (spill_choice params3 bls12_mul_body) bls12_mul_body).
  Qed.
  Lemma ccmd_square : ccmd_sp name (spill_choice params2 bls12_square_body) bls12_square_body =
    Some (leaf_code params2 bls12_square_body).
  Proof.
    have h : isSome (ccmd name bls12_square_body) by vm_compute.
    have := ccmd_sp_some name (spill_choice params2 bls12_square_body) bls12_square_body h.
    by rewrite /leaf_code; case: (ccmd_sp name (spill_choice params2 bls12_square_body) bls12_square_body).
  Qed.
End L.
