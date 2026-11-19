(** * [PsemBig] and Jasmin's [psem] define the same semantics.

    Loaded in Jasmin's environment (it requires [psem], hence ITree).  Both directions by the
    mutual induction principles ([PsemBig.sem_call_Ind], [psem.sem_call_Ind] and their
    siblings): the two inductive families have the same constructors with the same premises. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Jasmin Require Import utils expr psem_defs psem_core sem_params.
From Jasmin Require psem.
Require JasminBridge.Ast.PsemBig.
Set SsrOldRewriteGoalsOrder.

Section IFF.
  Context {wsw : WithSubWord} {dc : DirectCall} {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state} {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state} {pT : progT} {scP : semCallParams}
    (P : prog) (ev : extra_val_t).

  Lemma big_psem_all :
    (forall s c s', PsemBig.sem P ev s c s' -> psem.sem P ev s c s') /\
    (forall s i s', PsemBig.sem_i P ev s i s' -> psem.sem_i P ev s i s') /\
    (forall s i s', PsemBig.sem_I P ev s i s' -> psem.sem_I P ev s i s') /\
    (forall x ws s c s', PsemBig.sem_for P ev x ws s c s' -> psem.sem_for P ev x ws s c s') /\
    (forall scs m fn va scs' m' vr,
        PsemBig.sem_call P ev scs m fn va scs' m' vr -> psem.sem_call P ev scs m fn va scs' m' vr).
  Proof.
    have Hnil : PsemBig.sem_Ind_nil (psem.sem P ev) by move=> s; constructor.
    have Hcons : PsemBig.sem_Ind_cons P ev (psem.sem P ev) (psem.sem_I P ev) by move=> *; econstructor; eassumption.
    have HmkI : PsemBig.sem_Ind_mkI P ev (psem.sem_i P ev) (psem.sem_I P ev) by move=> *; econstructor; eassumption.
    have Hasgn : PsemBig.sem_Ind_assgn P (psem.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hopn : PsemBig.sem_Ind_opn P (psem.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hsys : PsemBig.sem_Ind_syscall P (psem.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hift : PsemBig.sem_Ind_if_true P ev (psem.sem P ev) (psem.sem_i P ev) by move=> *; apply: psem.Eif_true; eassumption.
    have Hiff : PsemBig.sem_Ind_if_false P ev (psem.sem P ev) (psem.sem_i P ev) by move=> *; apply: psem.Eif_false; eassumption.
    have Hwt : PsemBig.sem_Ind_while_true P ev (psem.sem P ev) (psem.sem_i P ev) by move=> *; apply: psem.Ewhile_true; eassumption.
    have Hwf : PsemBig.sem_Ind_while_false P ev (psem.sem P ev) (psem.sem_i P ev) by move=> *; apply: psem.Ewhile_false; eassumption.
    have Hfor : PsemBig.sem_Ind_for P ev (psem.sem_i P ev) (psem.sem_for P ev) by move=> *; econstructor; eassumption.
    have Hfn : PsemBig.sem_Ind_for_nil (psem.sem_for P ev) by move=> *; constructor.
    have Hfc : PsemBig.sem_Ind_for_cons P ev (psem.sem P ev) (psem.sem_for P ev) by move=> *; econstructor; eassumption.
    have Hcall : PsemBig.sem_Ind_call P ev (psem.sem_i P ev) (psem.sem_call P ev) by move=> *; econstructor; eassumption.
    have Hproc : PsemBig.sem_Ind_proc P ev (psem.sem P ev) (psem.sem_call P ev) by move=> *; econstructor; eassumption.
    split; [|split; [|split; [|split]]].
    - exact: (PsemBig.sem_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (PsemBig.sem_i_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (PsemBig.sem_I_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (PsemBig.sem_for_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (PsemBig.sem_call_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
  Qed.

  Lemma psem_big_all :
    (forall s c s', psem.sem P ev s c s' -> PsemBig.sem P ev s c s') /\
    (forall s i s', psem.sem_i P ev s i s' -> PsemBig.sem_i P ev s i s') /\
    (forall s i s', psem.sem_I P ev s i s' -> PsemBig.sem_I P ev s i s') /\
    (forall x ws s c s', psem.sem_for P ev x ws s c s' -> PsemBig.sem_for P ev x ws s c s') /\
    (forall scs m fn va scs' m' vr,
        psem.sem_call P ev scs m fn va scs' m' vr -> PsemBig.sem_call P ev scs m fn va scs' m' vr).
  Proof.
    have Hnil : psem.sem_Ind_nil (PsemBig.sem P ev) by move=> s; constructor.
    have Hcons : psem.sem_Ind_cons P ev (PsemBig.sem P ev) (PsemBig.sem_I P ev) by move=> *; econstructor; eassumption.
    have HmkI : psem.sem_Ind_mkI P ev (PsemBig.sem_i P ev) (PsemBig.sem_I P ev) by move=> *; econstructor; eassumption.
    have Hasgn : psem.sem_Ind_assgn P (PsemBig.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hopn : psem.sem_Ind_opn P (PsemBig.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hsys : psem.sem_Ind_syscall P (PsemBig.sem_i P ev) by move=> *; econstructor; eassumption.
    have Hift : psem.sem_Ind_if_true P ev (PsemBig.sem P ev) (PsemBig.sem_i P ev) by move=> *; apply: PsemBig.Eif_true; eassumption.
    have Hiff : psem.sem_Ind_if_false P ev (PsemBig.sem P ev) (PsemBig.sem_i P ev) by move=> *; apply: PsemBig.Eif_false; eassumption.
    have Hwt : psem.sem_Ind_while_true P ev (PsemBig.sem P ev) (PsemBig.sem_i P ev) by move=> *; apply: PsemBig.Ewhile_true; eassumption.
    have Hwf : psem.sem_Ind_while_false P ev (PsemBig.sem P ev) (PsemBig.sem_i P ev) by move=> *; apply: PsemBig.Ewhile_false; eassumption.
    have Hfor : psem.sem_Ind_for P ev (PsemBig.sem_i P ev) (PsemBig.sem_for P ev) by move=> *; econstructor; eassumption.
    have Hfn : psem.sem_Ind_for_nil (PsemBig.sem_for P ev) by move=> *; constructor.
    have Hfc : psem.sem_Ind_for_cons P ev (PsemBig.sem P ev) (PsemBig.sem_for P ev) by move=> *; econstructor; eassumption.
    have Hcall : psem.sem_Ind_call P ev (PsemBig.sem_i P ev) (PsemBig.sem_call P ev) by move=> *; econstructor; eassumption.
    have Hproc : psem.sem_Ind_proc P ev (PsemBig.sem P ev) (PsemBig.sem_call P ev) by move=> *; econstructor; eassumption.
    split; [|split; [|split; [|split]]].
    - exact: (psem.sem_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (psem.sem_i_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (psem.sem_I_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (psem.sem_for_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
    - exact: (psem.sem_call_Ind Hnil Hcons HmkI Hasgn Hopn Hsys Hift Hiff Hwt Hwf Hfor Hfn Hfc Hcall Hproc).
  Qed.

  Theorem sem_call_iff scs m fn va scs' m' vr :
    PsemBig.sem_call P ev scs m fn va scs' m' vr <-> psem.sem_call P ev scs m fn va scs' m' vr.
  Proof.
    split; [exact: (proj2 (proj2 (proj2 (proj2 big_psem_all)))) |
            exact: (proj2 (proj2 (proj2 (proj2 psem_big_all))))].
  Qed.

  Theorem sem_iff s c s' : PsemBig.sem P ev s c s' <-> psem.sem P ev s c s'.
  Proof. split; [exact: (proj1 big_psem_all) | exact: (proj1 psem_big_all)]. Qed.
End IFF.
