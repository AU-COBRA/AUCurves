(** * Simulation: bedrock2's [exec] of a translated command implies Jasmin's execution. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String Ascii.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Import bedrock2.Syntax.
Module map := coqutil.Map.Interface.map.

Section S.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  Context {wsw : WithSubWord}.
  Variable name : string -> Ident.ident.
  Hypothesis name_inj : injective name.

  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Context {BW : coqutil.Word.Bitwidth.Bitwidth 64}.
  Local Notation w64 := (@CW.rep 64 W).
  Context {Mem : map.map w64 coqutil.Byte.byte} {Mem_ok : map.ok Mem}.
  Context {L : map.map string w64} {L_ok : map.ok L}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context (gd : glob_decls).

  Local Notation vv := (vv name).
  Local Notation get vm x := (Vm.get vm x).
  Local Notation run := (Trans.run gd).

  Lemma vv_inj {x y} : vv x = vv y -> x = y.
  Proof. by move=> [] /name_inj. Qed.

  Lemma vv_neq x y : x <> y -> vv x != vv y.
  Proof. by move=> h; apply/eqP => /vv_inj. Qed.

  Lemma get_set_eq vm x (w : u64) : get vm.[vv x <- Vword w] (vv x) = Vword w.
  Proof. by rewrite Vm.setP_eq /= /vm_truncate_val /= !orbT. Qed.

  Lemma get_set_neq vm x y v : y <> x -> get vm.[vv x <- v] (vv y) = get vm (vv y).
  Proof. by move=> h; rewrite Vm.setP_neq // vv_neq // => e; apply: h. Qed.

  (** The locals of bedrock2 are in the Jasmin variable map; none is a temporary. *)
  Definition RL (l : @map.rep _ _ L) (vm : Vm.t) : Prop :=
    forall x v, map.get l x = Some v -> ok_name x /\ get vm (vv x) = Vword (jw v).

  Definition is_tmp (n n' : nat) (y : var) : Prop := exists k, (n <= k /\ k < n')%coq_nat /\ y = vv (tmp k).

  Definition agree_except (n n' : nat) (vm vm' : Vm.t) : Prop :=
    forall y, ~ is_tmp n n' y -> get vm' y = get vm y.

  Definition res_ok (n n' : nat) (r : string) : Prop := ok_name r \/ exists k, (n <= k /\ k < n')%coq_nat /\ r = tmp k.

  Lemma RL_agree {l vm vm' n n'} : RL l vm -> agree_except n n' vm vm' -> RL l vm'.
  Proof.
    move=> hl ha x v hx; have [hok hv] := hl _ _ hx; split => //.
    have hn : ~ is_tmp n n' (vv x).
    { move=> [k [_ e]]; exact: (ok_name_tmp hok (vv_inj e)). }
    by rewrite (ha _ hn).
  Qed.

  Lemma agree_refl n n' vm : agree_except n n' vm vm.
  Proof. by []. Qed.

  Lemma agree_trans n1 n2 n3 vm1 vm2 vm3 :
    (n1 <= n2)%coq_nat -> (n2 <= n3)%coq_nat ->
    agree_except n1 n2 vm1 vm2 -> agree_except n2 n3 vm2 vm3 -> agree_except n1 n3 vm1 vm3.
  Proof.
    move=> h12 h23 a12 a23 y hy; rewrite a23 ?a12 // => -[k [hk e]]; apply: hy; exists k; split => //; lia.
  Qed.

  Lemma agree_set n n' vm k (w : u64) : (n <= k /\ k < n')%coq_nat ->
    agree_except n n' vm vm.[vv (tmp k) <- Vword w].
  Proof.
    move=> hk y hy; rewrite Vm.setP_neq //; apply/eqP => e; apply: hy; exists k; split => //.
  Qed.

  Lemma agree_weaken n n' m m' vm vm' : (m <= n)%coq_nat -> (n' <= m')%coq_nat ->
    agree_except n n' vm vm' -> agree_except m m' vm vm'.
  Proof. move=> h1 h2 ha y hy; apply: ha => -[k [hk e]]; apply: hy; exists k; split => //; lia. Qed.

  (** A value held by a variable that is not a temporary of [n, n'] survives. *)
  Lemma res_keep {n n' m m' r vm vm'} : res_ok n n' r -> (n' <= m)%coq_nat ->
    agree_except m m' vm vm' -> get vm' (vv r) = get vm (vv r).
  Proof.
    move=> hr hm ha; apply: ha => -[k [hk e]]; have {}e := vv_inj e.
    case: hr => [hok | [k' [hk' e']]].
    - exact: (ok_name_tmp hok e).
    - rewrite e' in e; have := tmp_inj e; lia.
  Qed.

  Lemma res_neq_tmp {n n' r k} : res_ok n n' r -> (n' <= k)%coq_nat -> r <> tmp k.
  Proof.
    case => [hok | [k' [hk' ->]]] hk; first exact: ok_name_tmp.
    by move=> /tmp_inj; lia.
  Qed.

  Lemma agree_weaken' {n n' m m' vm vm'} : agree_except n n' vm vm' ->
    (m <= n)%coq_nat -> (n' <= m')%coq_nat -> agree_except m m' vm vm'.
  Proof. move=> h h1 h2; exact: agree_weaken h1 h2 h. Qed.

  Lemma agree_trans' {n1 n2 n3 vm1 vm2 vm3} :
    agree_except n1 n2 vm1 vm2 -> agree_except n2 n3 vm2 vm3 ->
    (n1 <= n2)%coq_nat -> (n2 <= n3)%coq_nat -> agree_except n1 n3 vm1 vm3.
  Proof. move=> a b h1 h2; exact: agree_trans h1 h2 a b. Qed.

  Lemma agree_set' n n' vm vm' k v : agree_except n n' vm vm' -> (n <= k /\ k < n')%coq_nat ->
    agree_except n n' vm vm'.[vv (tmp k) <- v].
  Proof.
    move=> ha hk y hy; rewrite Vm.setP_neq; first exact: ha.
    by apply/eqP => e; apply: hy; exists k; split.
  Qed.

  Lemma run_cons s i c : run s (i :: c) = Let s' := run_i gd s i in run s' c.
  Proof. by []. Qed.

  Lemma bind_ok {A B : Type} (v : A) (f : A -> exec B) : (Let x := ok v in f x) = f v.
  Proof. by []. Qed.

  Lemma run_app_ok {s c1} c2 {s1} : run s c1 = ok s1 -> run s (c1 ++ c2) = run s1 c2.
  Proof. by move=> h; rewrite run_cat h. Qed.

  Lemma with_vm2 (s : estate) vm1 vm2 : with_vm (with_vm s vm1) vm2 = with_vm s vm2.
  Proof. by []. Qed.

  Lemma with_vm_id (s : estate) : with_vm s (evm s) = s.
  Proof. by case: s. Qed.

  Local Notation eval_expr := (@bedrock2.Semantics.eval_expr 64 W Mem L).

  Lemma wop_of_sem {o w} (a b : w64) : wop_of o = Some w ->
    jw (bedrock2.Semantics.interp_binop o a b) = wop_sem w (jw a) (jw b).
  Proof.
    case: o => //= -[<-] /=; rewrite ?jw_add ?jw_sub ?jw_mul ?jw_and ?jw_or ?jw_xor //.
  Qed.

  Lemma jw_cmp (b : bool) :
    jw (if b then CW.of_Z (word:=W) 1 else CW.of_Z 0) = if b then 1%R else 0%R.
  Proof. by case: b; rewrite ?jw1 ?jw0. Qed.

  Lemma cexpr_correct e : forall n c r n',
    cexpr name n e = Some (c, r, n') ->
    (n <= n')%coq_nat /\ res_ok n n' r /\
    forall m l v s, eval_expr m l e = Some v -> RL l (evm s) -> mem_rel m (emem s) ->
      exists vm', run s c = ok (with_vm s vm') /\ get vm' (vv r) = Vword (jw v) /\
                  agree_except n n' (evm s) vm'.
  Proof.
    elim: e => [z | x | sz a iha | sz tbl idx ihi | o1 a iha | o a iha b ihb | ec ihc e1 ih1 e2 ih2] n c r n' //=.
    - (* literal *)
      move=> [<- <- <-]; split; first lia; split; first by right; exists n; split; [lia|].
      move=> m l v s [<-] hl hm; eexists; split.
      + by rewrite run_cons run_asg_cst.
      + split; first by rewrite get_set_eq jw_of_Z.
      by apply: agree_set; lia.
    - (* variable *)
      case: ifP => // hok [<- <- <-]; split; first lia; split; first by left.
      move=> m l v s hx hl hm; exists (evm s); split; first by rewrite with_vm_id.
      by split; [have [_ ->] := hl _ _ hx | apply: agree_refl].
    - (* load *)
      case: sz => //.
      case hf: (addr_fast a) => [[b k]|].
      + move=> [<- <- <-]; split; first lia; split; first by right; exists n; split; [lia|].
        move: hf; rewrite /addr_fast.
        case: a iha => // -[] // [] // b' [] // k' _; case: ifP => // /andP [hob _] [<- <-].
        move=> m l v s hev hl hm; simpl in hev.
        case hb: (map.get l b') hev => [vb|] // hev.
        case hld: (bedrock2.Memory.load _ m _) hev => [v'|] // [<-].
        have [_ hvb] := hl _ _ hb.
        eexists; split.
        * rewrite run_cons (run_asg_load _ _ _ _ _ _ (jw vb) (jw v')) //.
          have := mem_rel_load hm hld; rewrite /jp jw_add_of_Z; exact.
        * split; first by rewrite get_set_eq.
        by apply: agree_set; lia.
      + case ha: (cexpr name n a) => [[[ca ra] n1]|] // [<- <- <-].
        have [hn1 [hra hsa]] := iha _ _ _ _ ha.
        split; first lia; split; first by right; exists n1; split; [lia|].
        move=> m l v s hev hl hm; simpl in hev.
        case hea: (eval_expr m l a) hev => [va|] // hld.
        have [vm1 [hr1 [hv1 hag1]]] := hsa _ _ _ _ hea hl hm.
        eexists; split.
        * rewrite (run_app_ok _ hr1) run_cons (run_asg_loadv _ _ _ _ _ (jw va) (jw v)) //.
          have := mem_rel_load hm hld; rewrite /jp; exact.
        * split; first by rewrite get_set_eq.
        apply: agree_set'; last lia; apply: (agree_weaken' hag1); lia.
    - (* op1 *)
      case: o1 => //.
      case ha: (cexpr name n a) => [[[ca ra] n1]|] // [<- <- <-].
      have [hn1 [hra hsa]] := iha _ _ _ _ ha.
      split; first lia; split; first by right; exists n1; split; [lia|].
      move=> m l v s hev hl hm; simpl in hev.
      case hea: (eval_expr m l a) hev => [va|] // [<-].
      have [vm1 [hr1 [hv1 hag1]]] := hsa _ _ _ _ hea hl hm.
      have hne : ra <> tmp n1 by apply: (res_neq_tmp hra); lia.
      eexists; split.
      + rewrite (run_app_ok _ hr1) run_cons run_asg_cst bind_ok run_cons.
        rewrite (run_asg_op2 _ _ _ WSub _ _ (wrepr U64 0) (jw va)) //=.
        * by rewrite get_set_eq.
        * by rewrite get_set_neq.
      + split; first by rewrite get_set_eq /= jw_opp wrepr0.
      apply: agree_set'; last lia; apply: agree_set'; last lia; apply: (agree_weaken' hag1); lia.
    - (* op *)
      case ha: (cexpr name n a) => [[[ca ra] n1]|] //.
      case hb: (cexpr name n1 b) => [[[cb rb] n2]|] //.
      have [hn1 [hra hsa]] := iha _ _ _ _ ha.
      have [hn2 [hrb hsb]] := ihb _ _ _ _ hb.
      have hevab : forall m l v (s : @estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem)), eval_expr m l (expr.op o a b) = Some v -> RL l (evm s) -> mem_rel m (emem s) ->
        exists va vb vm2, [/\ v = bedrock2.Semantics.interp_binop o va vb,
          run s (ca ++ cb) = ok (with_vm s vm2), get vm2 (vv ra) = Vword (jw va),
          get vm2 (vv rb) = Vword (jw vb) & agree_except n n2 (evm s) vm2].
      { move=> m l v s hev hl hm; simpl in hev.
        case hea: (eval_expr m l a) hev => [va|] // hev.
        case heb: (eval_expr m l b) hev => [vb|] // [<-].
        have [vm1 [hr1 [hv1 hag1]]] := hsa _ _ _ _ hea hl hm.
        have [vm2 [hr2 [hv2 hag2]]] := hsb m l vb (with_vm s vm1) heb (RL_agree hl hag1) hm.
        exists va, vb, vm2; split => //.
        - by rewrite (run_app_ok _ hr1) hr2.
        - by rewrite (res_keep hra (le_n _) hag2).
        - apply: (agree_trans' hag1 hag2); lia. }
      have hra2 : ra <> tmp n2 by apply: (res_neq_tmp hra); lia.
      have hrb2 : rb <> tmp n2 by apply: (res_neq_tmp hrb); lia.
      have hra3 : ra <> tmp (S n2) by apply: (res_neq_tmp hra); lia.
      have hrb3 : rb <> tmp (S n2) by apply: (res_neq_tmp hrb); lia.
      have htt : tmp n2 <> tmp (S n2) by move=> /tmp_inj; lia.
      case hw: (wop_of o) => [w|].
      { (* add, sub, mul, and, or, xor *)
        move=> [<- <- <-]; split; first lia; split; first by right; exists n2; split; [lia|].
        move=> m l v s hev hl hm.
        have [va [vb [vm2 [-> hr2 hva hvb hag2]]]] := hevab _ _ _ _ hev hl hm.
        eexists; split.
        - rewrite catA (run_app_ok _ hr2) run_cons (run_asg_var _ _ _ _ _ (jw va)) // bind_ok run_cons.
          rewrite (run_asg_op2 _ _ _ _ _ _ (jw va) (jw vb)) //=.
          + by rewrite get_set_eq.
          + by rewrite get_set_neq.
        - split; first by rewrite get_set_eq (wop_of_sem _ _ hw).
        apply: agree_set'; last lia; apply: agree_set'; last lia; apply: (agree_weaken' hag2); lia. }
      case: o hw hevab => // _ hevab.
      + (* mulhuu *)
        move=> [<- <- <-]; split; first lia; split; first by right; exists n2; split; [lia|].
        have htt3 : rb <> tmp (S (S n2)) by apply: (res_neq_tmp hrb); lia.
        move=> m l v s hev hl hm.
        have [va [vb [vm2 [-> hr2 hva hvb hag2]]]] := hevab _ _ _ _ hev hl hm.
        eexists; split.
        * rewrite catA (run_app_ok _ hr2) run_cons (run_asg_var _ _ _ _ _ (jw va)) // bind_ok run_cons.
          rewrite (run_mulx _ _ _ _ _ _ _ (jw va) (jw vb)) //=.
          -- by rewrite get_set_eq.
          -- by rewrite get_set_neq.
        * split; first by rewrite get_set_eq /= jw_mulhuu.
        apply: agree_set'; last lia; apply: agree_set'; last lia; apply: agree_set'; last lia.
        apply: (agree_weaken' hag2); lia.
      + (* ltu *)
        move=> [<- <- <-]; split; first lia; split; first by right; exists n2; split; [lia|].
        move=> m l v s hev hl hm.
        have [va [vb [vm2 [-> hr2 hva hvb hag2]]]] := hevab _ _ _ _ hev hl hm.
        eexists; split.
        * rewrite catA (run_app_ok _ hr2) run_cons run_asg_cst bind_ok run_cons run_asg_cst bind_ok run_cons.
          rewrite (run_asg_pif _ _ _ CLtu _ _ _ _ (jw va) (jw vb) (wrepr U64 1) (wrepr U64 0)) //=.
          -- by rewrite !get_set_neq.
          -- by rewrite !get_set_neq.
          -- by rewrite get_set_eq.
          -- by rewrite get_set_neq // get_set_eq.
        * split; first by rewrite get_set_eq /= jw_cmp jw_ltu wrepr0 wrepr1.
        apply: agree_set'; last lia; apply: agree_set'; last lia; apply: agree_set'; last lia.
        apply: (agree_weaken' hag2); lia.
      + (* eq *)
        move=> [<- <- <-]; split; first lia; split; first by right; exists n2; split; [lia|].
        move=> m l v s hev hl hm.
        have [va [vb [vm2 [-> hr2 hva hvb hag2]]]] := hevab _ _ _ _ hev hl hm.
        eexists; split.
        * rewrite catA (run_app_ok _ hr2) run_cons run_asg_cst bind_ok run_cons run_asg_cst bind_ok run_cons.
          rewrite (run_asg_pif _ _ _ CEq _ _ _ _ (jw va) (jw vb) (wrepr U64 1) (wrepr U64 0)) //=.
          -- by rewrite !get_set_neq.
          -- by rewrite !get_set_neq.
          -- by rewrite get_set_eq.
          -- by rewrite get_set_neq // get_set_eq.
        * split; first by rewrite get_set_eq /= jw_cmp jw_eqb wrepr0 wrepr1.
        apply: agree_set'; last lia; apply: agree_set'; last lia; apply: agree_set'; last lia.
        apply: (agree_weaken' hag2); lia.
  Qed.

  Lemma addr_fast_spec {a b k} : addr_fast a = Some (b, k) ->
    a = expr.op bopname.add (expr.var b) (expr.literal k) /\ ok_name b.
  Proof.
    rewrite /addr_fast; case: a => // -[] // [] // b' [] // k'.
    by case: ifP => // /andP [hob _] [<- <-].
  Qed.

  Local Notation exec := (@bedrock2.Semantics.exec.exec 64 BW W Mem L ext_spec).

  Lemma RL_put l vm x (v : w64) : RL l vm -> ok_name x ->
    RL (map.put l x v) vm.[vv x <- Vword (jw v)].
  Proof.
    move=> hl hok y w; rewrite (@coqutil.Map.Properties.map.get_put_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec).
    case: (String.eqb_spec x y) => [<- [<-] | hne hy]; first by rewrite get_set_eq.
    have [hoky hw] := hl _ _ hy; split => //; rewrite get_set_neq //; congruence.
  Qed.

  Lemma RL_remove l vm x : RL l vm -> RL (map.remove l x) vm.
  Proof.
    move=> hl y w; rewrite (@coqutil.Map.Properties.map.get_remove_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec).
    by case: (String.eqb x y) => //; apply: hl.
  Qed.

  Definition sim_post (m : @map.rep _ _ Mem) (s : @estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem))
    (post : @bedrock2.Semantics.trace 64 BW W Mem -> @map.rep _ _ Mem -> @map.rep _ _ L -> Prop) (t : @bedrock2.Semantics.trace 64 BW W Mem) (s' : @estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem)) : Prop :=
    exists m' l', [/\ post t m' l', RL l' (evm s'), mem_rel m' (emem s'), escs s' = escs s &
      (forall k, map.get m' k = None <-> map.get m k = None) /\
      (forall p, outside m p -> read (emem s') Aligned p U8 = read (emem s) Aligned p U8)].

  (** The simulation theorem for straight-line code: when bedrock2 runs [c] from [(m, l)] to a
      postcondition, the translated Jasmin code runs from any related state to a related state,
      the final bedrock2 state satisfying the postcondition; it writes no Jasmin memory outside
      the bedrock2 domain. *)
  Theorem ccmd_correct (fenv : @map.rep _ _ bedrock2.Semantics.env) c jc :
    ccmd name c = Some jc ->
    forall t m l post, exec fenv c t m l post ->
    forall s, RL l (evm s) -> mem_rel m (emem s) ->
    exists s', run s jc = ok s' /\ sim_post m s post t s'.
  Proof.
    move=> hc0 t m l post hex; move: jc hc0.
    induction hex as [t m l post hpost | x e t m l post v hev hpost | x t m l post hpost
      | sz ea ev t m l post a v m' hea hev hst hpost
      | x n body t mSmall l post hmod hbody IHbody
      | t m l e c1 c2 post v hev hnz hc1 IHc1 | e c1 c2 t m l post v hev hz hc2 IHc2
      | c1 c2 t m l post mid hc1 IHc1 hc2 IHc2
      | e c t m l post v hev hz hpost | e c t m l post v mid hev hnz hc IHc hw IHw
      | binds fname arges t m l post params rets fbody args lf mid hget hargs hlf hbody IHbody hrets
      | binds action arges args t m l post mKeep mGive mid hsplit hargs hext hmid];
      move=> jc hcj s hl hm; simpl in hcj; try discriminate.
    - (* skip *)
      case: hcj => <-; exists s; split => //; exists m, l; split => //.
    - (* set *)
      move: hcj; case: ifP => // hok; case he: (cexpr name 0 e) => [[[ce r] n']|] // [<-].
      have [_ [hr hsem]] := cexpr_correct e 0 ce r n' he.
      have [vm1 [hr1 [hv1 hag1]]] := hsem _ _ _ _ hev hl hm.
      exists (with_vm s vm1.[vv x <- Vword (jw v)]); split.
      + by rewrite (run_app_ok _ hr1) run_cons (run_asg_var _ _ _ _ _ (jw v)) // bind_ok.
      + exists m, (map.put l x v); split => //.
      exact: RL_put (RL_agree hl hag1) hok.
    - (* unset *)
      case: hcj => <-; exists s; split => //; exists m, (map.remove l x); split => //.
      exact: RL_remove.
    - (* store *)
      move: hcj; case: sz hst => // hst.
      case hv: (cexpr name 0 ev) => [[[cv rv] n1]|] //.
      have [hn1 [hrv hsv]] := cexpr_correct ev 0 cv rv n1 hv.
      have [vm1 [hr1 [hv1 hag1]]] := hsv _ _ _ _ hev hl hm.
      have [jm' [hw hrel hdom hframe]] := mem_rel_store hm hst.
      case hf: (addr_fast ea) => [[b k]|].
      + move=> [<-]; have [heq hob] := addr_fast_spec hf; subst ea.
        move: hea => /=; case hb: (map.get l b) => [vb|] // [ha].
        have [_ hvb] := hl _ _ hb.
        have hvb1 : get vm1 (vv b) = Vword (jw vb).
        { rewrite -hvb; apply: hag1 => -[k' [_ e]]; exact: (ok_name_tmp hob (vv_inj e)). }
        exists (with_mem (with_vm s vm1) jm'); split.
        * rewrite (run_app_ok _ hr1) run_cons (run_store _ _ _ _ _ _ (jw vb) (jw v) jm') //.
          by move: hw; rewrite -ha /jp jw_add_of_Z.
        * exists m', l; split => //; exact: RL_agree hl hag1.
      + case ha: (cexpr name n1 ea) => [[[ca ra] n2]|] // [<-].
        have [hn2 [hra hsa]] := cexpr_correct ea n1 ca ra n2 ha.
        have [vm2 [hr2 [hv2 hag2]]] := hsa _ _ _ (with_vm s vm1) hea (RL_agree hl hag1) hm.
        have hrv2 : get vm2 (vv rv) = Vword (jw v) by rewrite (res_keep hrv (le_n _) hag2).
        exists (with_mem (with_vm s vm2) jm'); split.
        * rewrite (run_app_ok _ hr1) (run_app_ok _ hr2) run_cons.
          by rewrite (run_storev _ _ _ _ _ (jw a) (jw v) jm').
        * exists m', l; split => //.
        exact: RL_agree (RL_agree hl hag1) hag2.
    - (* seq *)
      move: hcj; case h1: (ccmd name c1) => [ca|] //; case h2: (ccmd name c2) => [cb|] // [<-].
      have [s2 [hr2 [m2 [l2 [hmid hl2 hm2 hscs2 [hdom2 hfr2]]]]]] := IHc1 _ h1 _ hl hm.
      have [s3 [hr3 [m3 [l3 [hpost hl3 hm3 hscs3 [hdom3 hfr3]]]]]] := IHc2 _ _ _ hmid _ h2 _ hl2 hm2.
      exists s3; split; first by rewrite run_cat hr2.
      exists m3, l3; split => //; first by rewrite hscs3.
      split.
      + by move=> k; rewrite hdom3 hdom2.
      + move=> p hp; rewrite hfr3; first exact: hfr2.
      by move=> a' ha'; rewrite -/(map.get m2 a' = None) hdom2; apply: hp.
  Qed.

  (** ** With spill hints *)
  Variable spillp : string -> bool.

  Lemma eval_vars {m l e v} : eval_expr m l e = Some v ->
    forall x, List.In x (vars_e e) -> exists w, map.get l x = Some w.
  Proof.
    elim: e v => [z | y | sz a iha | sz tbl a iha | o1 a iha | o a iha b ihb | ec ihc e1 ih1 e2 ih2] v //=.
    - by move=> h x [<- | []]; exists v.
    - by case ha: (eval_expr m l a) => [va|] // _; apply: iha ha.
    - by case ha: (eval_expr m l a) => [va|] // _; apply: iha ha.
    - by case ha: (eval_expr m l a) => [va|] // _; apply: iha ha.
    - case ha: (eval_expr m l a) => [va|] //; case hb: (eval_expr m l b) => [vb|] // _ x.
      rewrite List.in_app_iff => -[hx | hx]; [exact: iha _ ha x hx | exact: ihb _ hb x hx].
  Qed.

  Lemma run_spills s o xs :
    (forall x, List.In x xs -> exists w : u64, get (evm s) (vv x) = Vword w) ->
    run s (spills name spillp o xs) = ok s.
  Proof.
    elim: xs => [|x xs ih] // h; cbn [spills].
    have ih' : run s (spills name spillp o xs) = ok s by apply: ih => y hy; apply: h; right.
    case: (spillp x) => //.
    have [w hw] := h x (or_introl erefl).
    by rewrite run_cons (run_spill1 _ _ _ _ _ w hw) bind_ok.
  Qed.

  Lemma RL_defined {l vm xs} : RL l vm ->
    (forall x, List.In x xs -> exists w, map.get l x = Some w) ->
    forall x, List.In x xs -> exists w : u64, get vm (vv x) = Vword w.
  Proof. move=> hl h x hx; have [w hw] := h x hx; have [_ ->] := hl _ _ hw; by exists (jw w). Qed.

  Theorem ccmd_sp_correct (fenv : @map.rep _ _ bedrock2.Semantics.env) c jc :
    ccmd_sp name spillp c = Some jc ->
    forall t m l post, exec fenv c t m l post ->
    forall s, RL l (evm s) -> mem_rel m (emem s) ->
    exists s', run s jc = ok s' /\ sim_post m s post t s'.
  Proof.
    move=> hc0 t m l post hex; move: jc hc0.
    induction hex as [t m l post hpost | x e t m l post v hev hpost | x t m l post hpost
      | sz ea ev t m l post a v m' hea hev hst hpost
      | x n body t mSmall l post hmod hbody IHbody
      | t m l e c1 c2 post v hev hnz hc1 IHc1 | e c1 c2 t m l post v hev hz hc2 IHc2
      | c1 c2 t m l post mid hc1 IHc1 hc2 IHc2
      | e c t m l post v hev hz hpost | e c t m l post v mid hev hnz hcw IHc hw IHw
      | binds fname arges t m l post params rets fbody args lf mid hget hargs hlf hbody IHbody hrets
      | binds action arges args t m l post mKeep mGive mid hsplit hargs hext hmid];
      move=> jc hcj s hl hm; cbn [ccmd_sp] in hcj; try (simpl in hcj; discriminate).
    - (* skip *)
      simpl in hcj; case: hcj => <-; exists s; split => //; exists m, l; split => //.
    - (* set *)
      move: hcj; case hce: (ccmd name (cmd.set x e)) => [ce|] // [<-].
      have hex1 : exec fenv (cmd.set x e) t m l
          (fun t' m' l' => t' = t /\ m' = m /\ l' = map.put l x v).
      { by econstructor; [exact: hev | ]. }
      have [s1 [hr1 [m1 [l1 [[_ [-> ->]] hl1 hm1 hscs1 [hdom1 hfr1]]]]]] :=
        ccmd_correct fenv _ _ hce _ _ _ _ hex1 _ hl hm.
      exists s1; split.
      + rewrite run_cat run_spills; last first.
        { apply: (RL_defined hl); exact: eval_vars hev. }
        rewrite bind_ok run_cat hr1 bind_ok.
        have [_ hx] := hl1 x v (coqutil.Map.Interface.map.get_put_same _ _ _).
        by case: (spillp x) => //; rewrite run_cons (run_spill1 _ _ _ _ _ (jw v) hx) bind_ok.
      + by exists m, (map.put l x v); split.
    - (* unset *)
      simpl in hcj; case: hcj => <-; exists s; split => //; exists m, (map.remove l x); split => //.
      exact: RL_remove.
    - (* store *)
      move: hcj; case hcs: (ccmd name (cmd.store sz ea ev)) => [cs|] // [<-].
      have hex1 : exec fenv (cmd.store sz ea ev) t m l post.
      { by econstructor; eauto. }
      have [s1 [hr1 hpost1]] := ccmd_correct fenv _ _ hcs _ _ _ _ hex1 _ hl hm.
      exists s1; split => //.
      rewrite run_cat run_spills //.
      apply: (RL_defined hl) => y; rewrite List.in_app_iff => -[].
      + exact: eval_vars hea y.
      + exact: eval_vars hev y.
    - (* seq *)
      move: hcj; case h1: (ccmd_sp name spillp c1) => [ca|] //; case h2: (ccmd_sp name spillp c2) => [cb|] // [<-].
      have [s2 [hr2 [m2 [l2 [hmid hl2 hm2 hscs2 [hdom2 hfr2]]]]]] := IHc1 _ h1 _ hl hm.
      have [s3 [hr3 [m3 [l3 [hpost hl3 hm3 hscs3 [hdom3 hfr3]]]]]] := IHc2 _ _ _ hmid _ h2 _ hl2 hm2.
      exists s3; split; first by rewrite run_cat hr2.
      exists m3, l3; split => //; first by rewrite hscs3.
      split.
      + by move=> k; rewrite hdom3 hdom2.
      + move=> p hp; rewrite hfr3; first exact: hfr2.
        by move=> a' ha'; rewrite -/(map.get m2 a' = None) hdom2; apply: hp.
  Qed.
End S.
