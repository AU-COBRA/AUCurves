(** * Straight-line bedrock2 commands to Jasmin instructions, and their semantics. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String.
Require bedrock2.Syntax bedrock2.Semantics.
Require Import JasminBridge.Ast.Base.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

Section T.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  Context {wsw : WithSubWord}.

  (** Naming: an injective map from bedrock2 names to Jasmin identifiers, supplied by the
      program that builds the Jasmin program (the OCaml driver).  Jasmin's [Ident.ident] is
      abstract (a sealed module), so the translation is parametric in it. *)
  Variable name : string -> Ident.ident.

  Definition vv (x : string) : var := {| vtype := aword U64; vname := name x |}.
  Definition vi (x : string) : var_i := {| v_var := vv x; v_info := dummy_var_info |}.
  Definition pv (x : string) : pexpr := Plvar (vi x).
  Definition lv (x : string) : lval := Lvar (vi x).
  Definition I (i : instr_r) : instr := MkI dummy_instr_info i.
  Definition asg (x : string) (e : pexpr) : instr := I (Cassgn (lv x) AT_none (aword U64) e).
  Definition cst (z : Z) : pexpr := Papp1 (Oword_of_int U64) (Pconst (z mod 2 ^ 64)).
  Definition addr (b : string) (k : Z) : pexpr := Papp2 (Oadd (Op_w U64)) (pv b) (cst k).

  Definition jcmd := seq instr.

  (** An executable semantics of the assignments and operations, as Jasmin's [sem] runs them. *)
  Context (gd : glob_decls).

  Definition run_i (s : estate) (i : instr) : exec estate :=
    match i with
    | MkI _ (Cassgn x _ ty e) =>
        Let v := sem_pexpr true gd s e in
        Let v' := truncate_val (eval_atype ty) v in
        write_lval true gd x v' s
    | MkI _ (Copn xs _ o es) => sem_sopn gd o s xs es
    | _ => Error ErrType
    end.

  Fixpoint run (s : estate) (c : jcmd) : exec estate :=
    match c with
    | [::] => ok s
    | i :: c' => Let s' := run_i s i in run s' c'
    end.

  Lemma run_cat s c1 c2 :
    run s (c1 ++ c2) = Let s' := run s c1 in run s' c2.
  Proof. elim: c1 s => [|i c1 ih] s //=; case: run_i => //= s'; exact: ih. Qed.

  Context {dc : DirectCall} {pT : progT} {scP : semCallParams} (P : prog) (ev : extra_val_t).
  Hypothesis P_gd : p_globs P = gd.

  Lemma run_sem s c s' : run s c = ok s' -> sem P ev s c s'.
  Proof.
    elim: c s => [|[ii [x tg ty e|xs tg o es| | | | | |]] c ih] s //=.
    + by move=> [<-]; constructor.
    + t_xrbindP => s1 v he v' ht hw /ih hc.
      apply: Eseq hc; constructor; econstructor; rewrite ?P_gd; eauto.
    + t_xrbindP => s1 ho /ih hc.
      apply: Eseq hc; constructor; constructor; by rewrite P_gd.
  Qed.

  (** ** One instruction *)
  Local Notation get vm x := (Vm.get vm x).

  Lemma pv_eval s x : sem_pexpr true gd s (pv x) = get_var true (evm s) (vv x).
  Proof. reflexivity. Qed.

  Lemma gvar_eval vm x : get_gvar true gd vm (mk_lvar (vi x)) = get_var true vm (vv x).
  Proof. reflexivity. Qed.

  Lemma get_var_word {vm x} {w : u64} : get vm (vv x) = Vword w -> get_var true vm (vv x) = ok (Vword w).
  Proof. by rewrite /get_var => ->. Qed.

  Lemma cst_eval s z : sem_pexpr true gd s (cst z) = ok (Vword (wrepr U64 z)).
  Proof. by rewrite /= /sem_sop1 /= wrepr_mod. Qed.

  Ltac tw := repeat (rewrite truncate_word_u /=).

  Lemma truncate_word64 (w : u64) : truncate_val (eval_atype (aword U64)) (Vword w) = ok (Vword w).
  Proof. by rewrite /truncate_val /= truncate_word_u. Qed.

  Lemma write_word s x (w : u64) :
    write_lval true gd (lv x) (Vword w) s = ok (with_vm s (evm s).[vv x <- Vword w]).
  Proof. by rewrite /= /write_var /set_var /= !orbT. Qed.

  Lemma run_asg s x e (w : u64) :
    sem_pexpr true gd s e = ok (Vword w) ->
    run_i s (asg x e) = ok (with_vm s (evm s).[vv x <- Vword w]).
  Proof. by move=> he; rewrite /run_i /asg /I he /= truncate_word64 /= /write_var /set_var /= !orbT. Qed.

  Lemma run_asg_var s x y (w : u64) :
    get (evm s) (vv y) = Vword w ->
    run_i s (asg x (pv y)) = ok (with_vm s (evm s).[vv x <- Vword w]).
  Proof. by move=> h; apply: run_asg; rewrite pv_eval (get_var_word h). Qed.

  Lemma run_asg_cst s x z :
    run_i s (asg x (cst z)) = ok (with_vm s (evm s).[vv x <- Vword (wrepr U64 z)]).
  Proof. by apply: run_asg; rewrite cst_eval. Qed.

  (** Binary word operations used by the translation. *)
  Inductive wop := WAdd | WSub | WMul | WAnd | WOr | WXor.

  Definition wop_sop2 (o : wop) : sop2 :=
    match o with
    | WAdd => Oadd (Op_w U64) | WSub => Osub (Op_w U64) | WMul => Omul (Op_w U64)
    | WAnd => Oland U64 | WOr => Olor U64 | WXor => Olxor U64
    end.

  Definition wop_sem (o : wop) (a b : u64) : u64 :=
    match o with
    | WAdd => (a + b)%R | WSub => (a - b)%R | WMul => (a * b)%R
    | WAnd => wand a b | WOr => wor a b | WXor => wxor a b
    end.

  Lemma subw_R (a b : u64) : (a - b)%w = (a - b)%R.
  Proof.
    apply: wunsigned_inj; rewrite /wunsigned word.subwE /word.sub_word word.mkwordK //.
  Qed.

  Lemma run_asg_op2 s o x y (wa wb : u64) :
    get (evm s) (vv x) = Vword wa -> get (evm s) (vv y) = Vword wb ->
    run_i s (asg x (Papp2 (wop_sop2 o) (pv x) (pv y))) =
      ok (with_vm s (evm s).[vv x <- Vword (wop_sem o wa wb)]).
  Proof.
    move=> ha hb; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word ha) (get_var_word hb) /=.
    by case: o; rewrite /sem_sop2 /=; tw; rewrite ?subw_R.
  Qed.

  Lemma run_asg_load s x b k (wb w : u64) :
    get (evm s) (vv b) = Vword wb ->
    read (emem s) Unaligned (pt (wb + wrepr U64 k)%R) U64 = ok w ->
    run_i s (asg x (Pload Unaligned U64 (addr b k))) = ok (with_vm s (evm s).[vv x <- Vword w]).
  Proof.
    move=> hb hr; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word hb) /= /sem_sop1 /= wrepr_mod /sem_sop2 /=.
    tw; rewrite /to_pointer /=; tw; by rewrite hr.
  Qed.

  Lemma run_asg_loadv s x b (wb w : u64) :
    get (evm s) (vv b) = Vword wb ->
    read (emem s) Unaligned (pt wb) U64 = ok w ->
    run_i s (asg x (Pload Unaligned U64 (pv b))) = ok (with_vm s (evm s).[vv x <- Vword w]).
  Proof.
    move=> hb hr; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word hb) /=.
    rewrite /to_pointer /=; tw; by rewrite hr.
  Qed.

  Inductive wcmp := CLtu | CEq.
  Definition wcmp_sop2 (c : wcmp) : sop2 :=
    match c with CLtu => Olt (Cmp_w Unsigned U64) | CEq => Oeq (Op_w U64) end.
  Definition wcmp_sem (c : wcmp) (a b : u64) : bool :=
    match c with CLtu => wlt Unsigned a b | CEq => a == b end.

  Lemma run_asg_pif s c t a b o (wa wb w1 w0 : u64) :
    get (evm s) (vv a) = Vword wa -> get (evm s) (vv b) = Vword wb ->
    get (evm s) (vv o) = Vword w1 -> get (evm s) (vv t) = Vword w0 ->
    run_i s (asg t (Pif (aword U64) (Papp2 (wcmp_sop2 c) (pv a) (pv b)) (pv o) (pv t))) =
      ok (with_vm s (evm s).[vv t <- Vword (if wcmp_sem c wa wb then w1 else w0)]).
  Proof.
    move=> ha hb ho ht; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word ha) (get_var_word hb) (get_var_word ho) (get_var_word ht) /=.
    rewrite /sem_sop2 /=; tw; rewrite !truncate_word64 /=.
    case: c => /=; tw; by case: ifP.
  Qed.

  Definition mulx (lo hi a b : string) : instr :=
    I (Copn [:: lv lo; lv hi] AT_none (Oasm (BaseOp (None, MULX_lo_hi U64))) [:: pv a; pv b]).

  Lemma run_mulx s lo hi a b (wa wb : u64) :
    get (evm s) (vv a) = Vword wa -> get (evm s) (vv b) = Vword wb ->
    run_i s (mulx lo hi a b) =
      ok (with_vm s (evm s).[vv lo <- Vword (wumul wa wb).2].[vv hi <- Vword (wumul wa wb).1]).
  Proof.
    move=> ha hb.
    rewrite /= /sem_sopn /= /sem_pexprs /= !gvar_eval (get_var_word ha) (get_var_word hb) /=.
    rewrite /exec_sopn /=; tw.
    rewrite /x86_MULX_lo_hi; case: (wumul wa wb) => hiw low /=.
    by rewrite /write_var /set_var /= !orbT.
  Qed.

  Definition store (b : string) (k : Z) (r : string) : instr :=
    I (Cassgn (Lmem Unaligned U64 dummy_var_info (addr b k)) AT_none (aword U64) (pv r)).
  Definition storev (b r : string) : instr :=
    I (Cassgn (Lmem Unaligned U64 dummy_var_info (pv b)) AT_none (aword U64) (pv r)).

  Lemma run_store s b k r (wb wr : u64) m' :
    get (evm s) (vv b) = Vword wb -> get (evm s) (vv r) = Vword wr ->
    write (emem s) Unaligned (pt (wb + wrepr U64 k)%R) wr = ok m' ->
    run_i s (store b k r) = ok (with_mem s m').
  Proof.
    move=> hb hr hw.
    rewrite /= !gvar_eval (get_var_word hr) (get_var_word hb) /= truncate_word64 /=.
    rewrite /sem_sop2 /= wrepr_mod; tw; by rewrite hw.
  Qed.

  Lemma run_storev s b r (wb wr : u64) m' :
    get (evm s) (vv b) = Vword wb -> get (evm s) (vv r) = Vword wr ->
    write (emem s) Unaligned (pt wb) wr = ok m' ->
    run_i s (storev b r) = ok (with_mem s m').
  Proof.
    move=> hb hr hw.
    rewrite /= !gvar_eval (get_var_word hr) (get_var_word hb) /= truncate_word64 /=.
    tw; by rewrite hw.
  Qed.

  (** Spill and unspill pseudo-instructions: no-ops in the source semantics, implemented by
      the compiler's verified [lower_spill] pass as moves to and from stack slots. *)
  Definition spill1 (o : pseudo_operator.spill_op) (x : string) : instr :=
    I (Copn [::] AT_none (Opseudo_op (pseudo_operator.Ospill o [:: aword U64])) [:: pv x]).

  Lemma run_spill1 s o x (w : u64) :
    get (evm s) (vv x) = Vword w -> run_i s (spill1 o x) = ok s.
  Proof.
    move=> hx.
    rewrite /= /sem_sopn /= /sem_pexprs /= gvar_eval (get_var_word hx) /=.
    by rewrite /exec_sopn /=; tw.
  Qed.
End T.
