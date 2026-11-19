(** * Programs: bedrock2 functions that call each other, translated to a Jasmin program.

    [ccmdc] extends [Comp.ccmd] with calls (no arrays: arguments and results are [u64] words in
    registers): the arguments are evaluated into variables by [cexpr] and passed, after the
    stack pointer [$sp], to [Ccall [Lvar b | b <- binds] (fname f) ($sp :: args)].  A function
    becomes [jfunc]: parameters [$sp :: params], results [rets].  [$sp] is not used by the
    translated code (there is no [stackalloc]); every function passes it on to its callees.

    [prog_correct]: if bedrock2's [Semantics.call] of [fn] reaches [post] and every function of
    [fenv] is translated in [P] ([prog_rel]), Jasmin's [sem_call] ([PsemBig], Jasmin's
    big-step semantics) of [fname fn] on [Vword sp :: args] returns the bedrock2 results, in a
    memory related to a bedrock2 memory satisfying [post], and changes no byte outside the
    bedrock2 domain.  Memory is flat: bedrock2 pointers are [u64] words, loads and stores are
    [Pload]/[Lmem] on Jasmin's global memory. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String Ascii.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require Import JasminBridge.Ast.PsemBig JasminBridge.Ast.Base JasminBridge.Ast.Trans
  JasminBridge.Ast.Comp JasminBridge.Ast.Sim JasminBridge.Ast.Fun.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Import bedrock2.Syntax.
Module map := coqutil.Map.Interface.map.

(** The stack-pointer parameter: not a bedrock2 name ([ok_name]) and not a temporary. *)
Definition sp_name : string := "$sp".

Lemma sp_not_ok : ok_name sp_name = false.
Proof. by []. Qed.

Lemma sp_ne_tmp k : sp_name <> tmp k.
Proof. by case: k => [|k] //. Qed.

Lemma sp_ne_ok x : ok_name x -> sp_name <> x.
Proof. by move=> h e; subst x. Qed.

Section P.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  Context {wsw : WithSubWord}.
  #[local] Existing Instance progUnit.
  Variable name : string -> Ident.ident.
  Hypothesis name_inj : injective name.
  Variable fname : string -> funname.
  Variable finfo : string -> fun_info.
  Variable iinfo : positive -> instr_info.

  Local Notation vv := (vv name).
  Local Notation vi := (vi name).
  Local Notation pv := (pv name).
  Local Notation lv := (lv name).
  Local Notation vsp := (vv sp_name).
  Local Notation get vm x := (Vm.get vm x).

  (** ** The translation *)
  Fixpoint cargs (n : nat) (es : list expr) : option (jcmd * list string * nat) :=
    match es with
    | nil => Some ([::], [::], n)
    | e :: es =>
        match cexpr name n e with
        | Some (c, r, n1) =>
            match cargs n1 es with
            | Some (cs, rs, n2) => Some (c ++ cs, r :: rs, n2)
            | None => None
            end
        | None => None
        end
    end.

  Definition ccall (binds : list string) (f : string) (rs : list string) : instr :=
    I (Ccall [seq lv b | b <- binds] (fname f) (pv sp_name :: [seq pv r | r <- rs])).

  Fixpoint ccmdc (c : cmd) : option jcmd :=
    match c with
    | cmd.seq a b =>
        match ccmdc a, ccmdc b with Some ca, Some cb => Some (ca ++ cb) | _, _ => None end
    | cmd.cond e c1 c2 =>
        match cexpr name 0 e, ccmdc c1, ccmdc c2 with
        | Some (ce, r, _), Some j1, Some j2 => Some (ce ++ [:: cif name r j1 j2])
        | _, _, _ => None
        end
    | cmd.call binds f args =>
        if all ok_name binds then
          match cargs 0 args with
          | Some (ca, rs, _) => Some (ca ++ [:: ccall binds f rs])
          | None => None
          end
        else None
    | _ => ccmd name c
    end.

  Definition jfunc (fi : fun_info) (ps rs : list string) (jc : jcmd) : ufundef :=
    {| f_info := fi; f_contract := None;
       f_tyin := aword U64 :: [seq aword U64 | _ <- ps];
       f_params := vi sp_name :: [seq vi p | p <- ps];
       f_body := renumber iinfo 1 jc;
       f_tyout := [seq aword U64 | _ <- rs]; f_res := [seq vi r | r <- rs];
       f_extra := tt |}.

  Definition translate_fun (fd : string * func) : option ufun_decl :=
    let '(fn, (ps, rs, body)) := fd in
    if all ok_name ps && all ok_name rs then
      match ccmdc body with
      | Some jb => Some (fname fn, jfunc (finfo fn) ps rs jb)
      | None => None
      end
    else None.

  Fixpoint translate_funs (fs : list (string * func)) : option (seq ufun_decl) :=
    match fs with
    | nil => Some [::]
    | fd :: fs =>
        match translate_fun fd, translate_funs fs with
        | Some d, Some ds => Some (d :: ds)
        | _, _ => None
        end
    end.

  Definition translate_prog (fs : list (string * func)) : option uprog :=
    match translate_funs fs with
    | Some ds => Some {| p_funcs := ds; p_globs := [::]; p_extra := tt |}
    | None => None
    end.

  (** Every function of [fenv] is translated in [P]. *)
  Definition prog_rel (fenv : @map.rep _ _ bedrock2.Semantics.env) (P : uprog) : Prop :=
    forall f ps rs body, map.get fenv f = Some (ps, rs, body) ->
      [/\ all ok_name ps, all ok_name rs &
        exists jb, ccmdc body = Some jb /\
          get_fundef (p_funcs P) (fname f) = Some (jfunc (finfo f) ps rs jb)].

  Lemma translate_prog_get fs P :
    injective fname -> translate_prog fs = Some P -> prog_rel (map.of_list fs) P.
  Proof.
    move=> hinj; rewrite /translate_prog; case hds: (translate_funs fs) => [ds|] // [<-] /=.
    elim: fs ds hds => [|[fn [[ps rs] body]] fs ih] ds.
    - move=> _ f ps rs body; rewrite (_ : map.of_list [::] = (map.empty : @map.rep _ _ bedrock2.Semantics.env)) //.
    - cbn [translate_funs]; case hf: (translate_fun _) => [d|] //; case hfs: (translate_funs fs) => [ds'|] // [<-].
      move: hf; rewrite /translate_fun; case: ifP => // /andP [hps hrs].
      case hb: (ccmdc body) => [jb|] // [<-] f ps' rs' body'.
      rewrite (@coqutil.Map.Properties.map.get_put_dec _ _ _ bedrock2.Semantics.env_ok
        String.eqb coqutil.Decidable.String.eqb_spec).
      rewrite /get_fundef /=.
      case: (String.eqb_spec fn f) => [<- [<- <- <-] | hne hget].
      + by rewrite eqxx; split => //; exists jb.
      + case: eqP => [/hinj e | _]; first by exfalso; apply: hne; rewrite e.
        exact: ih _ hfs f ps' rs' body' hget.
  Qed.

  (** ** Big-step facts *)
  Section BIG.
    Context {dc : DirectCall} (P : uprog) (ev : extra_val_t).

    Lemma sem_cat s c1 s1 c2 s2 : sem P ev s c1 s1 -> sem P ev s1 c2 s2 -> sem P ev s (c1 ++ c2) s2.
    Proof.
      elim: c1 s => [|i c1 ih] s /=; first by move=> h; inversion h; subst.
      move=> h h2; inversion h; subst; apply: Eseq; [eassumption | exact: ih].
    Qed.

    Lemma sem_renumber k s c s' : sem P ev s c s' -> sem P ev s (renumber iinfo k c) s'.
    Proof.
      elim: c k s => [|[ii i] c ih] k s /= h; inversion h; subst => //.
      match goal with H : sem_I _ _ _ _ _ |- _ => inversion H; subst end.
      apply: Eseq; [constructor; eassumption | exact: ih].
    Qed.
  End BIG.
  (** ** Values: arguments, results, bindings *)
  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Context {BW : coqutil.Word.Bitwidth.Bitwidth 64}.
  Local Notation w64 := (@CW.rep 64 W).
  Context {Mem : map.map w64 coqutil.Byte.byte} {Mem_ok : map.ok Mem}.
  Context {L : map.map string w64} {L_ok : map.ok L}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Local Notation exec := (@bedrock2.Semantics.exec.exec 64 BW W Mem L ext_spec).
  Local Notation eval_expr := (@bedrock2.Semantics.eval_expr 64 W Mem L).
  Local Notation eval_call_args := (@bedrock2.Semantics.eval_call_args 64 W Mem L).
  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].
  Local Notation RL := (RL name).
  Local Notation agree_except := (agree_except name).
  Local Notation estate_x := (@estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem)).

  Lemma res_ok_widen {n n1 n' r} : res_ok n1 n' r -> (n <= n1)%coq_nat -> res_ok n n' r.
  Proof. case=> [h | [k [hk ->]]] hn; [by left | right; exists k; split => //; lia]. Qed.

  Lemma res_ok_widen_r {n n1 n' r} : res_ok n n1 r -> (n1 <= n')%coq_nat -> res_ok n n' r.
  Proof. case=> [h | [k [hk ->]]] hn; [by left | right; exists k; split => //; lia]. Qed.

  Lemma vsp_agree {n n' vm vm'} : agree_except n n' vm vm' -> get vm' vsp = get vm vsp.
  Proof. by move=> h; apply: h => -[k [_ /(vv_inj name name_inj)]]; apply: sp_ne_tmp. Qed.

  Lemma cargs_correct gd es : forall n c rs n', cargs n es = Some (c, rs, n') ->
    (n <= n')%coq_nat /\ (forall r, List.In r rs -> res_ok n n' r) /\
    forall m l vs (s : estate_x), eval_call_args m l es = Some vs -> RL l (evm s) -> mem_rel m (emem s) ->
      exists vm', Trans.run gd s c = ok (with_vm s vm') /\
        [seq get vm' (vv r) | r <- rs] = jargs vs /\ agree_except n n' (evm s) vm'.
  Proof.
    elim: es => [|e es ih] n c rs n' /=.
    - move=> [<- <- <-]; split; first lia; split => //.
      move=> m l vs s [<-] _ _; exists (evm s); rewrite with_vm_id; split => //; split => //; exact: agree_refl.
    - case he: (cexpr name n e) => [[[c1 r] n1]|] //.
      case hes: (cargs n1 es) => [[[cs rs'] n2]|] // [<- <- <-].
      have [hn1 [hr hsem1]] := cexpr_correct name name_inj gd e n c1 r n1 he.
      have [hn2 [hrs hsem2]] := ih _ _ _ _ hes.
      split; first lia; split.
      { move=> x [<- | hx]; first exact: res_ok_widen_r hr hn2.
        exact: res_ok_widen (hrs x hx) hn1. }
      move=> m l vs s; case hev: (eval_expr m l e) => [v|] //.
      case hevs: (eval_call_args m l es) => [vs'|] // [<-] hl hm.
      have [vm1 [hr1 [hv1 hag1]]] := hsem1 _ _ _ _ hev hl hm.
      have [vm2 [hr2 [hvs hag2]]] :=
        hsem2 m l vs' (with_vm s vm1) hevs (RL_agree name name_inj hl hag1) hm.
      exists vm2; split; first by rewrite run_cat hr1 /= hr2.
      split; first by rewrite /= hvs (res_keep name name_inj hr (le_n _) hag2) hv1.
      apply: (agree_trans' name hag1 hag2); lia.
  Qed.

  Lemma get_var_vword wdb vm x (w : u64) :
    get vm (vv x) = Vword w -> get_var wdb vm (vv x) = ok (Vword w).
  Proof. by rewrite /get_var => ->; case: wdb. Qed.

  Lemma pexprs_vals wdb gd (s : estate_x) rs vs :
    [seq get (evm s) (vv r) | r <- rs] = jargs vs ->
    sem_pexprs wdb gd s [seq pv r | r <- rs] = ok (jargs vs).
  Proof.
    elim: rs vs => [|r rs ih] [|v vs] //= [hr /ih].
    rewrite /sem_pexprs /= => h; rewrite /get_gvar /= (get_var_vword _ _ _ _ hr) /=.
    by move: h; rewrite /sem_pexprs => ->.
  Qed.

  Lemma get_var_is_vals wdb vm rs (st : @map.rep _ _ L) retvs :
    RL st vm -> map.getmany_of_list st rs = Some retvs ->
    get_var_is wdb vm [seq vi r | r <- rs] = ok (jargs retvs).
  Proof.
    move=> hl; elim: rs retvs => [|r rs ih] retvs; first by move=> [<-].
    rewrite /map.getmany_of_list /=; case hr: (map.get st r) => [v|] //.
    case hrs: (List.option_all _) => [vs|] // [<-].
    have [_ hv] := hl _ _ hr.
    by rewrite /= (get_var_vword _ _ _ _ hv) /= (ih vs hrs).
  Qed.

  Lemma write_binds wdb gd binds : forall retvs (l l' : @map.rep _ _ L) (s : estate_x),
    all ok_name binds -> map.putmany_of_list_zip binds retvs l = Some l' -> RL l (evm s) ->
    exists vm', write_lvals wdb gd s [seq lv b | b <- binds] (jargs retvs) = ok (with_vm s vm') /\
      RL l' vm' /\ get vm' vsp = get (evm s) vsp.
  Proof.
    elim: binds => [|b binds ih] [|v retvs] l l' s //=.
    - by move=> _ [<-] hl; exists (evm s); rewrite with_vm_id.
    - move=> /andP [hb hbs] h hl.
      have hl1 : RL (map.put l b v) (evm s).[vv b <- Vword (jw v)] by exact: RL_put.
      have [vm' [hw [hl' hsp]]] := ih retvs _ _ (with_vm s (evm s).[vv b <- Vword (jw v)]) hbs h hl1.
      exists vm'; split; last split => //.
      + rewrite /write_var /set_var /=.
        have -> : DB wdb (Vword (jw v)) by rewrite /DB /= orbT.
        by rewrite !orbT /= hw.
      + by rewrite hsp /= (get_set_neq name name_inj) //; apply: sp_ne_ok.
  Qed.

  Lemma set_params_sp vm ps (args : list w64) :
    all ok_name ps -> get (set_params name vm ps args) vsp = get vm vsp.
  Proof.
    elim: ps args vm => [|p ps ih] [|a args] vm //= /andP [hp hps].
    by rewrite ih // (get_set_neq name name_inj) //; apply: sp_ne_ok.
  Qed.
  Lemma getmany_size (st : @map.rep _ _ L) rs retvs :
    map.getmany_of_list st rs = Some retvs -> size rs = size retvs.
  Proof.
    elim: rs retvs => [|r rs ih] retvs; first by move=> [<-].
    rewrite /map.getmany_of_list /=; case: (map.get st r) => [v|] //.
    case hrs: (List.option_all _) => [vs|] // [<-] /=; by rewrite (ih vs hrs).
  Qed.

  (** The simulation relation: [Sim.sim_post], and [$sp] is kept. *)
  Definition simp (m : @map.rep _ _ Mem) (s : estate_x)
      (post : @bedrock2.Semantics.trace 64 BW W Mem -> @map.rep _ _ Mem -> @map.rep _ _ L -> Prop)
      (t : @bedrock2.Semantics.trace 64 BW W Mem) (s' : estate_x) : Prop :=
    sim_post name m s post t s' /\ get (evm s') vsp = get (evm s) vsp.

  Section CALL.
    Context {dc : DirectCall} (P : uprog) (ev : extra_val_t).
    Context (fenv : @map.rep _ _ bedrock2.Semantics.env).
    Hypothesis hP : prog_rel fenv P.
    Local Notation gd := (p_globs P).

    (** A call of a translated function whose body simulates its bedrock2 execution. *)
    Lemma call_sim f ps rs jb t m args (lf : @map.rep _ _ L) mid scs jm (sp : u64) :
      get_fundef (p_funcs P) (fname f) = Some (jfunc (finfo f) ps rs jb) ->
      all ok_name ps ->
      map.of_list_zip ps args = Some lf ->
      (forall s : estate_x, RL lf (evm s) -> get (evm s) vsp = Vword sp -> mem_rel m (emem s) ->
         exists s', sem P ev s jb s' /\ simp m s mid t s') ->
      mem_rel m jm ->
      exists jm' m' (st : @map.rep _ _ L), [/\ mid t m' st, mem_rel m' jm',
        (forall k, map.get m' k = None <-> map.get m k = None),
        (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8) &
        forall retvs, map.getmany_of_list st rs = Some retvs ->
          sem_call P ev scs jm (fname f) (Vword sp :: jargs args) scs jm' (jargs retvs)].
    Proof.
      move=> hget hps hz hbody hm.
      have hsz := size_zip_args hz.
      pose (s0 := @Estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem) scs jm Vm.init).
      pose (vm1 := set_params name (Vm.init.[vsp <- Vword sp]) ps args).
      pose (s1 := with_vm s0 vm1).
      have hl1 : RL lf vm1 by apply: (RL_params name name_inj) hps hz; exact: RL_empty.
      have hsp1 : get vm1 vsp = Vword sp by rewrite /vm1 set_params_sp // get_set_eq.
      have [s2 [hsem [[m' [st [hmid hl2 hm2 hscs [hdom hfr]]]] _]]] := hbody s1 hl1 hsp1 hm.
      exists (emem s2), m', st; split => // retvs hrets.
      have hszr := getmany_size _ _ _ hrets.
      eapply EcallRun with (f := jfunc (finfo f) ps rs jb) (s0 := s0) (s1 := s1) (s2 := s2)
        (vres := jargs retvs).
      - exact: hget.
      - rewrite /= (truncate_args ps args hsz).
        have -> : dc_truncate_val (eval_atype (aword U64)) (Vword sp) = ok (Vword sp).
        { by rewrite /dc_truncate_val; case: direct_call => //; exact: truncate_word64. }
        by [].
      - by [].
      - rewrite /= /write_var /set_var /=.
        have -> : DB (~~ direct_call) (Vword sp) by rewrite /DB /= orbT.
        by rewrite !orbT /= (write_params name).
      - exact: sem_renumber.
      - exact: get_var_is_vals hl2 hrets.
      - exact: truncate_args.
      - by rewrite hscs.
      - by [].
    Qed.

    Local Notation cexpr_correct := (cexpr_correct name name_inj gd).
    Local Notation RL_agree := (RL_agree name name_inj).
    Local Notation RL_put := (RL_put name name_inj).
    Local Notation res_keep := (res_keep name name_inj).

    Lemma sim_skip m (s : estate_x) (post : _ -> _ -> _ -> Prop) t l :
      post t m l -> RL l (evm s) -> mem_rel m (emem s) -> simp m s post t s.
    Proof. by move=> hp hl hm; split => //; exists m, l; split. Qed.

    Theorem ccmdc_correct c jc : ccmdc c = Some jc ->
      forall t m l post, exec fenv c t m l post ->
      forall (s : estate_x) (sp : u64), RL l (evm s) -> get (evm s) vsp = Vword sp -> mem_rel m (emem s) ->
      exists s', sem P ev s jc s' /\ simp m s post t s'.
    Proof.
      move=> hc0 t m l post hex; move: jc hc0.
      induction hex as [t m l post hpost | x e t m l post v hev hpost | x t m l post hpost
        | sz ea ev' t m l post a v m' hea hev hst hpost
        | x n body t mSmall l post hmod hbody IHbody
        | t m l e c1 c2 post v hev hnz hc1 IHc1 | e c1 c2 t m l post v hev hz hc2 IHc2
        | c1 c2 t m l post mid hc1 IHc1 hc2 IHc2
        | e c t m l post v hev hz hpost | e c t m l post v mid hev hnz hcw IHc hw IHw
        | binds f arges t m l post params rets fbody args lf mid hget hargs hlf hbody IHbody hrets
        | binds action arges args t m l post mKeep mGive mid hsplit hargs hext hmid];
        move=> jc hcj s sp hl hsp hm; cbn [ccmdc] in hcj; try (simpl in hcj; discriminate).
      - (* skip *)
        simpl in hcj; case: hcj => <-; exists s; split; [exact: Eskip | exact: sim_skip hpost hl hm].
      - (* set *)
        move: hcj => /=; case: ifP => // hok; case he: (cexpr name 0 e) => [[[ce r] n']|] // [<-].
        have [_ [hr hsem]] := cexpr_correct e 0 ce r n' he.
        have [vm1 [hr1 [hv1 hag1]]] := hsem _ _ _ _ hev hl hm.
        exists (with_vm s vm1.[vv x <- Vword (jw v)]); split.
        + apply: (run_sem gd P ev erefl).
          by rewrite (run_app_ok _ _ hr1) run_cons (run_asg_var _ _ _ _ _ (jw v)) // bind_ok.
        + split; first by exists m, (map.put l x v); split => //; exact: RL_put (RL_agree hl hag1) hok.
          by rewrite /= (get_set_neq name name_inj) ?(vsp_agree hag1) //; apply: sp_ne_ok.
      - (* unset *)
        simpl in hcj; case: hcj => <-; exists s; split; first exact: Eskip.
        split => //; exists m, (map.remove l x); split => //; exact: RL_remove.
      - (* store *)
        move: hcj => /=; case: sz hst => // hst.
        case hv: (cexpr name 0 ev') => [[[cv rv] n1]|] //.
        have [hn1 [hrv hsv]] := cexpr_correct ev' 0 cv rv n1 hv.
        have [vm1 [hr1 [hv1 hag1]]] := hsv _ _ _ _ hev hl hm.
        have [jm' [hw hrel hdom hframe]] := mem_rel_store hm hst.
        case hf: (addr_fast ea) => [[b k]|].
        + move=> [<-]; have [heq hob] := addr_fast_spec hf; subst ea.
          move: hea => /=; case hb: (map.get l b) => [vb|] // [ha].
          have [_ hvb] := hl _ _ hb.
          have hvb1 : get vm1 (vv b) = Vword (jw vb).
          { rewrite -hvb; apply: hag1 => -[k' [_ e]]; exact: (ok_name_tmp hob (vv_inj name name_inj e)). }
          exists (with_mem (with_vm s vm1) jm'); split.
          * apply: (run_sem gd P ev erefl).
            rewrite (run_app_ok _ _ hr1) run_cons (run_store _ _ _ _ _ _ (jw vb) (jw v) jm') //.
            by move: hw; rewrite -ha /jp jw_add_of_Z.
          * split; last exact: vsp_agree hag1.
            by exists m', l; split => //; exact: RL_agree hl hag1.
        + case ha: (cexpr name n1 ea) => [[[ca ra] n2]|] // [<-].
          have [hn2 [hra hsa]] := cexpr_correct ea n1 ca ra n2 ha.
          have [vm2 [hr2 [hv2 hag2]]] := hsa _ _ _ (with_vm s vm1) hea (RL_agree hl hag1) hm.
          have hrv2 : get vm2 (vv rv) = Vword (jw v) by rewrite (res_keep hrv (le_n _) hag2).
          exists (with_mem (with_vm s vm2) jm'); split.
          * apply: (run_sem gd P ev erefl).
            rewrite (run_app_ok _ _ hr1) (run_app_ok _ _ hr2) run_cons.
            by rewrite (run_storev _ _ _ _ _ (jw a) (jw v) jm').
          * split; last by rewrite /= (vsp_agree hag2) (vsp_agree hag1).
            by exists m', l; split => //; exact: RL_agree (RL_agree hl hag1) hag2.
      - (* if_true *)
        move: hcj; case he: (cexpr name 0 e) => [[[ce r] n']|] //.
        case h1: (ccmdc c1) => [j1|] //; case h2: (ccmdc c2) => [j2|] // [<-].
        have [_ [hr hsem]] := cexpr_correct e 0 ce r n' he.
        have [vm1 [hr1 [hv1 hag1]]] := hsem _ _ _ _ hev hl hm.
        have hsp1 : get vm1 vsp = Vword sp by rewrite (vsp_agree hag1).
        have [s2 [hs2 [hpost hsp2]]] := IHc1 _ h1 (with_vm s vm1) sp (RL_agree hl hag1) hsp1 hm.
        exists s2; split; last by split => //; rewrite hsp2 /= (vsp_agree hag1).
        apply: sem_cat; first exact: (run_sem gd P ev erefl _ _ _ hr1).
        apply: Eseq; last exact: Eskip; constructor; apply: Eif_true => //.
        rewrite (ne0_eval name gd (with_vm s vm1) r (jw v) hv1) jw_ne0.
        by have -> : (CW.unsigned v =? 0)%Z = false by apply/Z.eqb_neq.
      - (* if_false *)
        move: hcj; case he: (cexpr name 0 e) => [[[ce r] n']|] //.
        case h1: (ccmdc c1) => [j1|] //; case h2: (ccmdc c2) => [j2|] // [<-].
        have [_ [hr hsem]] := cexpr_correct e 0 ce r n' he.
        have [vm1 [hr1 [hv1 hag1]]] := hsem _ _ _ _ hev hl hm.
        have hsp1 : get vm1 vsp = Vword sp by rewrite (vsp_agree hag1).
        have [s2 [hs2 [hpost hsp2]]] := IHc2 _ h2 (with_vm s vm1) sp (RL_agree hl hag1) hsp1 hm.
        exists s2; split; last by split => //; rewrite hsp2 /= (vsp_agree hag1).
        apply: sem_cat; first exact: (run_sem gd P ev erefl _ _ _ hr1).
        apply: Eseq; last exact: Eskip; constructor; apply: Eif_false => //.
        by rewrite (ne0_eval name gd (with_vm s vm1) r (jw v) hv1) jw_ne0 hz.
      - (* seq *)
        move: hcj; case h1: (ccmdc c1) => [ca|] //; case h2: (ccmdc c2) => [cb|] // [<-].
        have [s2 [hs2 [[m2 [l2 [hmid hl2 hm2 hscs2 [hdom2 hfr2]]]] hsp2]]] := IHc1 _ h1 _ sp hl hsp hm.
        have hsp2' : get (evm s2) vsp = Vword sp by rewrite hsp2.
        have [s3 [hs3 [[m3 [l3 [hpost hl3 hm3 hscs3 [hdom3 hfr3]]]] hsp3]]] :=
          IHc2 _ _ _ hmid _ h2 _ sp hl2 hsp2' hm2.
        exists s3; split; first exact: sem_cat hs2 hs3.
        split; last by rewrite hsp3 hsp2.
        exists m3, l3; split => //; first by rewrite hscs3.
        split.
        + by move=> k; rewrite hdom3 hdom2.
        + move=> p hp; rewrite hfr3; first exact: hfr2.
          by move=> a' ha'; rewrite -/(map.get m2 a' = None) hdom2; apply: hp.
      - (* call *)
        move: hcj; case: ifP => // hbinds; case hca: (cargs 0 arges) => [[[ca rs] n']|] // [<-].
        have [_ [_ hsa]] := cargs_correct gd arges 0 ca rs n' hca.
        have [vm1 [hr1 [hvals hag1]]] := hsa _ _ _ _ hargs hl hm.
        have hsp1 : get vm1 vsp = Vword sp by rewrite (vsp_agree hag1).
        have [hps [hrs [jb [hjb hgetP]]]] := hP _ _ _ _ hget.
        have [jm' [m' [st [hmid hm' hdom hfr hcall]]]] :=
          call_sim f params rets jb t m args lf mid (escs s) (emem s) sp hgetP hps hlf
            (fun s1 hl1 hsp1 hm1 => IHbody jb hjb s1 sp hl1 hsp1 hm1) hm.
        have [retvs [hgm [l' [hput hpost]]]] := hrets _ _ _ hmid.
        pose s2 : estate_x := with_scs (with_mem (with_vm s vm1) jm') (escs s).
        have [vm3 [hw [hl3 hsp3]]] :=
          write_binds (~~ direct_call) gd binds retvs l l' s2 hbinds hput (RL_agree hl hag1).
        exists (with_vm s2 vm3); split.
        + apply: sem_cat; first exact: (run_sem gd P ev erefl _ _ _ hr1).
          apply: Eseq; last exact: Eskip; constructor.
          apply: (Ecall (vargs := Vword sp :: jargs args) (vs := jargs retvs)).
          * rewrite /sem_pexprs /= /get_gvar /= (get_var_vword _ _ _ _ hsp1) /=.
            by have := pexprs_vals (~~ direct_call) gd (with_vm s vm1) rs args hvals;
              rewrite /sem_pexprs => ->.
          * exact: hcall retvs hgm.
          * exact: hw.
        + split; last by rewrite hsp3 /= (vsp_agree hag1).
          by exists m', l'; split.
      Qed.

    (** ** The program theorem *)
    Theorem prog_correct fn t m args post jm scs (sp : u64) :
      bedrock2.Semantics.call fenv fn t m args post -> mem_rel m jm ->
      exists jm' vres,
        sem_call P ev scs jm (fname fn) (Vword sp :: jargs args) scs jm' vres /\
        exists m' rets, [/\ post t m' rets, vres = jargs rets, mem_rel m' jm',
          (forall k, map.get m' k = None <-> map.get m k = None) &
          (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
    Proof.
      move=> [ps [rs [body [hget [lf [hz hex]]]]]] hm.
      have [hps [hrs [jb [hjb hgetP]]]] := hP _ _ _ _ hget.
      have [jm' [m' [st [[rets [hgm hpost]] hm' hdom hfr hcall]]]] :=
        call_sim fn ps rs jb t m args lf _ scs jm sp hgetP hps hz
          (fun s1 hl1 hsp1 hm1 => ccmdc_correct body jb hjb _ _ _ _ hex s1 sp hl1 hsp1 hm1) hm.
      exists jm', (jargs rets); split; first exact: hcall rets hgm.
      by exists m', rets; split.
    Qed.
  End CALL.
End P.
