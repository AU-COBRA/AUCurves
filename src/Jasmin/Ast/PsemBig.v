(** * Jasmin's big-step source semantics, without ITree.

    A verbatim copy of section [SEM] of Jasmin's [psem.v] (lines 30-324 of the installed
    library: [sem], [sem_I], [sem_i], [sem_for], [sem_call] and the mutual induction principle
    of [SEM_IND]), requiring the imports of [psem.v] except [it_sems_core], [hoare_logic] and
    [relational_logic], which load ITree.  Jasmin's library loads ITree and ExtLib, whose
    template universes (ITree's [Basics/Function.v], [Pair_Fun]) close a universe cycle with
    fiat-crypto's bedrock2 synthesis modules; this file loads neither, so a statement about
    [PsemBig.sem_call] can be made in fiat-crypto's environment.  [PsemBigIff] proves
    [PsemBig.sem_call P ev ... <-> psem.sem_call P ev ...] in Jasmin's environment. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From Jasmin Require Import xseq.
From Jasmin Require Export type expr gen_map warray_ sem_type sem_op_typed values varmap
  expr_facts low_memory syscall_sem psem_defs psem_core flag_combination sem_params.
Import Utf8.

(* The flags Jasmin's library is compiled with (its _CoqProject). *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

Section WSW.
Context {wsw:WithSubWord}.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Context
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (P : prog)
  (ev : extra_val_t).

Notation gd := (p_globs P).

Definition get_lvar_i (x: lval) : exec var_i :=
  if x is Lvar x then ok x else type_error.

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2:
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr true gd s1 e = ok v ->
    truncate_val (eval_atype ty) v = ok v' →
    write_lval true gd x v' s1 = ok s2 ->
    sem_i s1 (Cassgn x tag ty e) s2

| Eopn s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

| Esyscall s1 scs m s2 o xs es ves vs:
    sem_pexprs true gd s1 es = ok ves →
    exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
    write_lvals true gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
    sem_i s1 (Csyscall xs o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 a c e ei c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile a c e ei c') s4 ->
    sem_i s1 (Cwhile a c e ei c') s4

| Ewhile_false s1 s2 a c e ei c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile a c e ei c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr true gd s1 lo = ok (Vint vlo) ->
    sem_pexpr true gd s1 hi = ok (Vint vhi) ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 scs2 m2 s2 xs f args vargs vs :
    sem_pexprs (~~direct_call) gd s1 args = ok vargs ->
    sem_call s1.(escs) s1.(emem) f vargs scs2 m2 vs ->
    write_lvals (~~direct_call) gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 ->
    sem_i s1 (Ccall xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var true i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop :=
| EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyin)) vargs' = ok vargs ->
    init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vm.init) = ok s0 ->
    write_vars (~~direct_call) f.(f_params) vargs s0 = ok s1 ->
    sem s1 f.(f_body) s2 ->
    get_var_is (~~ direct_call) s2.(evm) f.(f_res) = ok vres ->
    mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyout)) vres = ok vres' ->
    scs2 = s2.(escs) ->
    m2 = finalize f.(f_extra) s2.(emem)  ->
    sem_call scs1 m1 fn vargs' scs2 m2 vres'.

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi   : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
      sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr true gd s1 e = ok v →
      truncate_val (eval_atype ty) v = ok v' →
      write_lval true gd x v' s1 = ok s2 →
      Pi_r s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = ok s2 →
      Pi_r s1 (Copn xs t o es) s2.

  Definition sem_Ind_syscall : Prop :=
    forall  s1 scs m s2 o xs es ves vs,
      sem_pexprs true gd s1 es = ok ves →
      exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
      write_lvals true gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
      Pi_r s1 (Csyscall xs o es) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (ei: instr_info) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 -> Pc s2 c' s3 ->
    sem_i s3 (Cwhile a c e ei c') s4 -> Pi_r s3 (Cwhile a c e ei c') s4 -> Pi_r s1 (Cwhile a c e ei c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (ei: instr_info) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e ei c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hsyscall: sem_Ind_syscall)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) (d : dir)
           (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
      sem_pexpr true gd s1 lo = ok (Vint vlo) ->
      sem_pexpr true gd s1 hi = ok (Vint vhi) ->
      sem_for i (wrange d vlo vhi) s1 c s2 ->
      Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd), Pfor i [::] s c s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i)
           (w : Z) (ws : seq Z) (c : cmd),
      write_var true i w s1 = Ok error s1' ->
      sem s1' c s2 -> Pc s1' c s2 ->
      sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (scs2 : syscall_state_t) (m2 : mem) (s2 : estate)
           (xs : lvals) (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs (~~direct_call) gd s1 args = ok vargs →
      sem_call (escs s1) (emem s1) fn vargs scs2 m2 vs →
      Pfun (escs s1) (emem s1) fn vargs scs2 m2 vs →
      write_lvals (~~direct_call) gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 →
      Pi_r s1 (Ccall xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (scs1 : syscall_state_t) (m1 : mem) (scs2 : syscall_state_t) (m2 : mem)
           (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s0 s1 s2: estate) (vres vres': seq value),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyin)) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vm.init) = ok s0 ->
      write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
      sem s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      get_var_is (~~ direct_call) s2.(evm) (f_res f) = ok vres ->
      mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyout)) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in sem e1 l0 e2 return Pc e1 l0 e2 with
    | @Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in sem_i e1 i0 e2 return Pi_r e1 i0 e2 with
    | @Eassgn s1 s2 x tag ty e1 v v' h1 h2 h3 =>
      @Hasgn s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn s1 s2 t o xs es e1 =>
      @Hopn s1 s2 t o xs es e1
    | @Esyscall s1 scs m s2 o xs es ves vs h1 h2 h3 =>
      @Hsyscall s1 scs m s2 o xs es ves vs h1 h2 h3
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 ei c' s0 e2 s5 s6 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 ei c' s0 (@sem_Ind s1 c s2 s0) e2 s5 (@sem_Ind s2 c' s3 s5) s6
          (@sem_i_Ind s3 (Cwhile a c e1 ei c') s4 s6)
    | @Ewhile_false s1 s2 a c e1 ei c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 ei c' s0 (@sem_Ind s1 c s2 s0) e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 scs2 m2 s2 xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 scs2 m2 s2 xs f13 args vargs vs e2 s0
        (@sem_call_Ind (escs s1) (emem s1) f13 vargs scs2 m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in sem_I e1 i0 e2 return Pi e1 i0 e2 with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in sem_for v0 l1 e1 l2 e2 return Pfor v0 l1 e1 l2 e2 with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (scs : syscall_state_t) (m : mem) (f13 : funname) (l : seq value) (scs0 : syscall_state_t) (m0 : mem)
         (l0 : seq value) (s : sem_call scs m f13 l scs0 m0 l0) {struct s} : Pfun scs m f13 l scs0 m0 l0 :=
    match s with
    | @EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem Hvres Hcr hscs Hfi=>
      @Hproc scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem (sem_Ind Hsem) Hvres Hcr hscs Hfi
    end.

End SEM_IND.

End SEM.

End WSW.
