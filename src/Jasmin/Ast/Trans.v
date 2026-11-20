(** * Straight-line bedrock2 commands to Jasmin instructions, and their semantics. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String.
Require bedrock2.Syntax bedrock2.Semantics.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.PsemBig.
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

  (** An executable semantics of the assignments and operations, as Jasmin's [sem] runs them.
      [run_sem] concludes [PsemBig.sem], Jasmin's big-step semantics without ITree, so that the
      translation loads with fiat-crypto's synthesis modules; [FunPsem.run_sem_psem] states it
      for Jasmin's [psem.sem]. *)
  Context (gd : glob_decls).

  (** [Cif] runs the branch selected by its condition; the other instructions are not run. *)
  Fixpoint run_i (s : estate) (i : instr) {struct i} : exec estate :=
    match i with
    | MkI _ (Cassgn x _ ty e) =>
        Let v := sem_pexpr true gd s e in
        Let v' := truncate_val (eval_atype ty) v in
        write_lval true gd x v' s
    | MkI _ (Copn xs _ o es) => sem_sopn gd o s xs es
    | MkI _ (Cif e c1 c2) =>
        Let v := sem_pexpr true gd s e in
        Let b := to_bool v in
        let run_c := fix run_c (s : estate) (c : seq instr) {struct c} : exec estate :=
          match c with
          | [::] => ok s
          | i :: c' => Let s' := run_i s i in run_c s' c'
          end in
        if b then run_c s c1 else run_c s c2
    | _ => Error ErrType
    end.

  Fixpoint run (s : estate) (c : jcmd) : exec estate :=
    match c with
    | [::] => ok s
    | i :: c' => Let s' := run_i s i in run s' c'
    end.

  Lemma run_i_if s ii e c1 c2 :
    run_i s (MkI ii (Cif e c1 c2)) =
      Let v := sem_pexpr true gd s e in Let b := to_bool v in
      if b then run s c1 else run s c2.
  Proof. reflexivity. Qed.

  Lemma run_cat s c1 c2 :
    run s (c1 ++ c2) = Let s' := run s c1 in run s' c2.
  Proof. elim: c1 s => [|i c1 ih] s //=; case: run_i => //= s'; exact: ih. Qed.

  Context {dc : DirectCall} {pT : progT} {scP : semCallParams} (P : prog) (ev : extra_val_t).
  Hypothesis P_gd : p_globs P = gd.

  Let Pr (ir : instr_r) := forall ii s s', run_i s (MkI ii ir) = ok s' -> sem_i P ev s ir s'.
  Let Pi (i : instr) := forall s s', run_i s i = ok s' -> sem_I P ev s i s'.
  Let Pc (c : cmd) := forall s s', run s c = ok s' -> sem P ev s c s'.

  Lemma run_sem_all :
    (forall i s s', run_i s i = ok s' -> sem_I P ev s i s') /\
    (forall c s s', run s c = ok s' -> sem P ev s c s').
  Proof.
    have hmk : forall ir ii, Pr ir -> Pi (MkI ii ir).
    { by move=> ir ii h s s' /h hs; constructor. }
    have hnil : Pc [::] by move=> s s' [<-]; constructor.
    have hcons : forall i c, Pi i -> Pc c -> Pc (i :: c).
    { move=> i c hi hc s s' /=; t_xrbindP => s1 /hi h1 /hc h2; exact: Eseq h1 h2. }
    have hasgn : forall x tg ty e, Pr (Cassgn x tg ty e).
    { move=> x tg ty e ii s s' /=; t_xrbindP => v he v' ht hw.
      by econstructor; rewrite ?P_gd; eauto. }
    have hopn : forall xs t o es, Pr (Copn xs t o es).
    { by move=> xs t o es ii s s' /= ho; constructor; rewrite P_gd. }
    have hif : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
    { move=> e c1 c2 h1 h2 ii s s'; rewrite run_i_if; t_xrbindP => v he b hb.
      have hv := to_boolI hb; subst v.
      case: b he hb => he _ hr.
      - by apply: Eif_true; [rewrite P_gd | exact: h1].
      - by apply: Eif_false; [rewrite P_gd | exact: h2]. }
    have hsys : forall xs o es, Pr (Csyscall xs o es) by [].
    have hass : forall a, Pr (Cassert a) by [].
    have hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c) by [].
    have hwhile : forall a c e info c', Pc c -> Pc c' -> Pr (Cwhile a c e info c') by [].
    have hcall : forall xs f es, Pr (Ccall xs f es) by [].
    split.
    - exact: (instr_Rect hmk hnil hcons hasgn hopn hsys hass hif hfor hwhile hcall).
    - exact: (cmd_rect hmk hnil hcons hasgn hopn hsys hass hif hfor hwhile hcall).
  Qed.

  Lemma run_sem s c s' : run s c = ok s' -> sem P ev s c s'.
  Proof. exact: (proj2 run_sem_all). Qed.

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

  (** ** Conditionals: [Cif] on [r != 0] *)
  Definition ne0 (r : string) : pexpr := Papp2 (Oneq (Op_w U64)) (pv r) (cst 0).
  Definition cif (r : string) (c1 c2 : jcmd) : instr := I (Cif (ne0 r) c1 c2).

  Lemma ne0_eval s r (w : u64) :
    get (evm s) (vv r) = Vword w -> sem_pexpr true gd s (ne0 r) = ok (Vbool (w != 0%R)).
  Proof.
    move=> h; rewrite /ne0 /= gvar_eval (get_var_word h) /= /sem_sop1 /= wrepr_mod /sem_sop2 /=.
    by tw; rewrite wrepr0.
  Qed.

  Lemma run_cif s r c1 c2 (w : u64) :
    get (evm s) (vv r) = Vword w ->
    run_i s (cif r c1 c2) = if w != 0%R then run s c1 else run s c2.
  Proof. by move=> h; rewrite /cif /I run_i_if (ne0_eval _ _ _ h). Qed.

  (** ** Shifts by a literal amount [0 <= k < 64] *)
  Inductive shop := ShR | ShL.
  Definition shop_sop2 (o : shop) : sop2 :=
    match o with ShR => Olsr U64 | ShL => Olsl (Op_w U64) end.
  Definition shop_sem (o : shop) (a : u64) (k : Z) : u64 :=
    match o with ShR => wshr a k | ShL => wshl a k end.

  Lemma wunsigned_u8_of k : 0 <= k < 64 ->
    wunsigned (zero_extend U8 (wrepr U64 k)) = k.
  Proof.
    move=> hk; rewrite zero_extend_wrepr // wunsigned_repr_small //.
    by rewrite (_ : wbase U8 = 256); [lia | reflexivity].
  Qed.

  Lemma run_asg_shift s o t k (wt : u64) : 0 <= k < 64 ->
    get (evm s) (vv t) = Vword wt ->
    run_i s (asg t (Papp2 (shop_sop2 o) (pv t) (cst k))) =
      ok (with_vm s (evm s).[vv t <- Vword (shop_sem o wt k)]).
  Proof.
    move=> hk ht; apply: run_asg.
    rewrite /= gvar_eval (get_var_word ht) /= /sem_sop1 /= wrepr_mod /sem_sop2 /=.
    case: o => /=; rewrite truncate_word_u /= truncate_word_le //=.
    - by rewrite /sem_shr /sem_shift wunsigned_u8_of.
    - by rewrite /sem_shl /sem_shift wunsigned_u8_of.
  Qed.

  (** ** Shifts by a variable amount: [t >> (k & 63)], [t << (k & 63)]
      Jasmin's [Olsr]/[Olsl] shift by the [u8] truncation of the amount and give [0] past the
      width, so the amount is masked to [k mod 64]; x86 lowering ([check_shift_amount]) drops
      the mask, as [SHR]/[SHL] mask the count themselves. *)
  Definition shamt (k : string) : pexpr := Papp2 (Oland U64) (pv k) (cst 63).

  Lemma wunsigned_shamt (wk : u64) :
    wunsigned (zero_extend U8 (wand wk (wrepr U64 63))) = wunsigned wk mod 64.
  Proof.
    have h := wand_modulo wk 6.
    rewrite (_ : 2 ^ Z.of_nat 6 - 1 = 63) // (_ : 2 ^ Z.of_nat 6 = 64) // in h.
    rewrite /zero_extend wunsigned_repr h.
    have [h0 h1] : 0 <= wunsigned wk mod 64 < 64 by apply: Z.mod_pos_bound; lia.
    by rewrite Z.mod_small //; split => //; apply: (Z.lt_le_trans _ 64).
  Qed.

  Lemma run_asg_vshift s o t k (wt wk : u64) :
    get (evm s) (vv t) = Vword wt -> get (evm s) (vv k) = Vword wk ->
    run_i s (asg t (Papp2 (shop_sop2 o) (pv t) (shamt k))) =
      ok (with_vm s (evm s).[vv t <- Vword (shop_sem o wt (wunsigned wk mod 64))]).
  Proof.
    move=> ht hk; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word ht) (get_var_word hk) /= /sem_sop1 /= wrepr_mod /sem_sop2 /=.
    rewrite !truncate_word_u /=.
    case: o => /=; rewrite truncate_word_u /= truncate_word_le //=.
    - by rewrite /sem_shr /sem_shift wunsigned_shamt.
    - by rewrite /sem_shl /sem_shift wunsigned_shamt.
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
