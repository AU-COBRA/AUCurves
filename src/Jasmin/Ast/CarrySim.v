(** * Simulation for [Carry.xcmd]: bedrock2's [exec] of a leaf body implies Jasmin's run of the
    optimised code, to related states. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String Ascii.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp
  JasminBridge.Ast.Sim JasminBridge.Ast.Carry JasminBridge.Ast.CarryArith.
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
  Variable cfn : Ident.ident.

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
  Local Notation run_i := (Trans.run_i gd).
  Local Notation cfv := (cfv cfn).
  Local Notation pcf := (pcf cfn).
  Local Notation estate := (@estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem)).
  Local Notation eval_expr := (@bedrock2.Semantics.eval_expr 64 W Mem L).
  Local Notation exec := (@bedrock2.Semantics.exec.exec 64 BW W Mem L ext_spec).
  Local Notation locals := (@map.rep _ _ L).
  Local Notation mem := (@map.rep _ _ Mem).

  (** ** The functional semantics of flattened bodies *)
  Definition bstep (m : mem) (l : locals) (st : stmt) : option (mem * locals) :=
    match st with
    | SSet x e => match eval_expr m l e with Some v => Some (m, map.put l x v) | None => None end
    | SStore a v =>
        match eval_expr m l a, eval_expr m l v with
        | Some a', Some v' =>
            match bedrock2.Memory.store access_size.word m a' v' with
            | Some m' => Some (m', l)
            | None => None
            end
        | _, _ => None
        end
    end.

  Fixpoint brun (m : mem) (l : locals) (ss : list stmt) : option (mem * locals) :=
    match ss with
    | [::] => Some (m, l)
    | st :: ss => match bstep m l st with Some (m', l') => brun m' l' ss | None => None end
    end.

  Lemma brun_app m l s1 s2 :
    brun m l (s1 ++ s2) = match brun m l s1 with Some (m', l') => brun m' l' s2 | None => None end.
  Proof.
    elim: s1 m l => [|st s1 ih] m l //=.
    by case: bstep => [[m' l']|] //.
  Qed.

  Lemma exec_flat (fenv : @map.rep _ _ bedrock2.Semantics.env) c ss :
    flat c = Some ss -> forall t m l post, exec fenv c t m l post ->
    exists m' l', brun m l ss = Some (m', l') /\ post t m' l'.
  Proof.
    move=> hf t m l post hex; move: ss hf.
    induction hex as [t m l post hpost | x e t m l post v hev hpost | x t m l post hpost
      | sz ea ev t m l post a v m' hea hev hst hpost
      | x n body t mSmall l post hmod hbody IHbody
      | t m l e c1 c2 post v hev hnz hc1 IHc1 | e c1 c2 t m l post v hev hz hc2 IHc2
      | c1 c2 t m l post mid hc1 IHc1 hc2 IHc2
      | e c t m l post v hev hz hpost | e c t m l post v mid hev hnz hc IHc hw IHw
      | binds fname arges t m l post params rets fbody args lf mid hget hargs hlf hbody IHbody hrets
      | binds action arges args t m l post mKeep mGive mid hsplit hargs hext hmid];
      move=> ss hf; simpl in hf; try discriminate.
    - case: hf => <-; by exists m, l.
    - case: hf => <-; exists m, (map.put l x v); by rewrite /= hev.
    - move: hf; case: sz hst => // hst [<-]; exists m', l; by rewrite /= hea hev hst.
    - move: hf; case h1: (flat c1) => [s1|] //; case h2: (flat c2) => [s2|] // [<-].
      have [m2 [l2 [hr2 hmid]]] := IHc1 _ h1.
      have [m3 [l3 [hr3 hpost]]] := IHc2 _ _ _ hmid _ h2.
      by exists m3, l3; rewrite brun_app hr2.
  Qed.

  (** ** Load-free evaluation *)
  Fixpoint leval (l : locals) (e : expr) : option w64 :=
    match e with
    | expr.literal v => Some (CW.of_Z v)
    | expr.var x => map.get l x
    | expr.op1 o a => match leval l a with Some x => Some (bedrock2.Semantics.interp_op1 o x) | None => None end
    | expr.op o a b =>
        match leval l a, leval l b with
        | Some x, Some y => Some (bedrock2.Semantics.interp_binop o x y)
        | _, _ => None
        end
    | _ => None
    end.

  Lemma leval_eval m l e v : leval l e = Some v -> eval_expr m l e = Some v.
  Proof.
    elim: e v => [z | x | sz a iha | sz t a iha | o a iha | o a iha b ihb | c ihc a iha b ihb] v //=.
    - by case h: (leval l a) => [x|] // [<-]; rewrite (iha _ h).
    - case ha: (leval l a) => [x|] //; case hb: (leval l b) => [y|] // [<-].
      by rewrite (iha _ ha) (ihb _ hb).
  Qed.

  Lemma smem_cat x a b : smem x (a ++ b) = smem x a || smem x b.
  Proof. by rewrite /smem has_cat. Qed.

  Lemma smem_cons x y a : smem x (y :: a) = String.eqb x y || smem x a.
  Proof. by []. Qed.

  Lemma smem_nil x : smem x [::] = false. Proof. by []. Qed.

  Lemma leval_agree l l' e : (forall x, smem x (evars e) -> map.get l' x = map.get l x) ->
    leval l' e = leval l e.
  Proof.
    elim: e => [z | x | sz a iha | sz t a iha | o a iha | o a iha b ihb | c ihc a iha b ihb] //= h.
    - by apply: h; rewrite /smem /= String.eqb_refl.
    - by rewrite iha.
    - rewrite iha ?ihb // => x hx; apply: h; by rewrite smem_cat hx ?orbT.
  Qed.

  Lemma get_put_neq (l : locals) x y v : x <> y -> map.get (map.put l x v) y = map.get l y.
  Proof. move=> h; rewrite coqutil.Map.Interface.map.get_put_diff //; congruence. Qed.

  Lemma get_put_eq (l : locals) x v : map.get (map.put l x v) x = Some v.
  Proof. exact: coqutil.Map.Interface.map.get_put_same. Qed.

  Lemma smem_neq x y : ~~ smem x [:: y] -> x <> y.
  Proof. by rewrite smem_cons smem_nil orbF => h e; subst; rewrite String.eqb_refl in h. Qed.

  Lemma smemP x a : reflect (List.In x a) (smem x a).
  Proof.
    elim: a => [|y a ih]; first by constructor.
    rewrite smem_cons; case h: (String.eqb x y) => /=.
    - by move/String.eqb_eq: h => ->; constructor; left.
    - case: ih => hi; constructor; first by right.
      by move=> [e | hh]; [subst; rewrite String.eqb_refl in h | exact: hi hh].
  Qed.

  Lemma leval_put l x v e : ~~ smem x (evars e) -> leval (map.put l x v) e = leval l e.
  Proof.
    move=> h; apply: leval_agree => y hy; apply: get_put_neq => e'; subst y.
    by rewrite hy in h.
  Qed.

  (** ** Jasmin variables *)
  Lemma vv_inj' {x y} : vv x = vv y -> x = y.
  Proof. by move=> [] /name_inj. Qed.

  Lemma vv_neq' x y : x <> y -> vv x != vv y.
  Proof. by move=> h; apply/eqP => /vv_inj'. Qed.

  Lemma cfv_neq x : cfv != vv x. Proof. by []. Qed.
  Lemma vv_cfv_neq x : vv x != cfv. Proof. by []. Qed.

  Lemma gset_eq vm x (w : u64) : get vm.[vv x <- Vword w] (vv x) = Vword w.
  Proof. by rewrite Vm.setP_eq /= /vm_truncate_val /= !orbT. Qed.

  Lemma gset_neq vm x y v : y <> x -> get vm.[vv x <- v] (vv y) = get vm (vv y).
  Proof. by move=> h; rewrite Vm.setP_neq //; apply: vv_neq'; congruence. Qed.

  Lemma gset_cf_eq vm (b : bool) : get vm.[cfv <- Vbool b] cfv = Vbool b.
  Proof. by rewrite Vm.setP_eq. Qed.

  Lemma gset_cf_neq vm x v : get vm.[cfv <- v] (vv x) = get vm (vv x).
  Proof. by rewrite Vm.setP_neq. Qed.

  Lemma gset_vv_cf vm x v : get vm.[vv x <- v] cfv = get vm cfv.
  Proof. by rewrite Vm.setP_neq. Qed.

  Lemma ok_name_neq_tmp x k : ok_name x -> x <> tmp k.
  Proof. by move=> h e; subst. Qed.

  Lemma ok_name_neq_h x k : ok_name x -> x <> hname k.
  Proof. by move=> h e; subst. Qed.

  Lemma tmp_neq_h j k : tmp j <> hname k.
  Proof. by case: j. Qed.

  Lemma tmp_neq j k : j <> k -> tmp j <> tmp k.
  Proof. by move=> h /tmp_inj. Qed.

  Lemma hname_inj j k : hname j = hname k -> j = k.
  Proof. by move=> [] /ts_inj. Qed.

  (** ** Jasmin instructions *)
  Ltac tw := repeat (rewrite truncate_word_u /=).

  Lemma pcf_eval (s : estate) (b : bool) : get (evm s) cfv = Vbool b -> sem_pexpr true gd s pcf = ok (Vbool b).
  Proof. by move=> h; rewrite /= /get_gvar /= /get_var h. Qed.

  Lemma run_carryop (s : estate) sub r b cin (wr wb : u64) (c : bool) :
    get (evm s) (vv r) = Vword wr -> get (evm s) (vv b) = Vword wb ->
    sem_pexpr true gd s cin = ok (Vbool c) ->
    run_i s (carryop name cfn sub r b cin) =
      ok (with_vm s (evm s).[cfv <- Vbool (if sub then wsubcarry wr wb c else waddcarry wr wb c).1]
                            .[vv r <- Vword (if sub then wsubcarry wr wb c else waddcarry wr wb c).2]).
  Proof.
    move=> hr hb hc.
    rewrite /= /sem_sopn /= /sem_pexprs /= !gvar_eval (get_var_word name hr) (get_var_word name hb) hc /=.
    by case: sub; rewrite /exec_sopn /=; tw; rewrite /write_var /set_var /= ?orbT /=.
  Qed.

  Lemma run_sbbself (s : estate) r (wr : u64) (c : bool) :
    get (evm s) (vv r) = Vword wr -> get (evm s) cfv = Vbool c ->
    run_i s (sbbself name cfn r) = ok (with_vm s (evm s).[vv r <- Vword (wsubcarry wr wr c).2]).
  Proof.
    move=> hr hc.
    rewrite /= /sem_sopn /= /sem_pexprs /= !gvar_eval (get_var_word name hr) /get_gvar /= /get_var hc /=.
    by rewrite /exec_sopn /=; tw; rewrite /write_var /set_var /= ?orbT /=.
  Qed.

  Lemma run_pif_cf (s : estate) x a t (wa wt : u64) (c : bool) :
    get (evm s) (vv a) = Vword wa -> get (evm s) (vv t) = Vword wt -> get (evm s) cfv = Vbool c ->
    run_i s (asg name x (Pif (aword U64) pcf (pv name a) (pv name t))) =
      ok (with_vm s (evm s).[vv x <- Vword (if c then wa else wt)]).
  Proof.
    move=> ha ht hc; apply: run_asg.
    rewrite /= !gvar_eval (get_var_word name ha) (get_var_word name ht) /get_gvar /= /get_var hc /=.
    by rewrite !truncate_word64 /=; case: (c) hc.
  Qed.

  Lemma run_matcf (s : estate) x (c : bool) : ok_name x ->
    get (evm s) cfv = Vbool c ->
    run s (matcf name cfn x) =
      ok (with_vm s (evm s).[vv x <- Vword (wrepr U64 0)].[vv (tmp 1) <- Vword (wrepr U64 1)]
                            .[vv x <- Vword (if c then wrepr U64 1 else wrepr U64 0)]).
  Proof.
    move=> hx hc; rewrite /matcf run_cons run_asg_cst bind_ok run_cons run_asg_cst bind_ok run_cons.
    rewrite (run_pif_cf _ _ _ _ (wrepr U64 1) (wrepr U64 0) c) //=.
    - by rewrite gset_eq.
    - by rewrite gset_neq ?gset_eq //; apply: ok_name_neq_tmp.
    - by rewrite !gset_vv_cf.
  Qed.
  (** ** The simulation relation *)
  Definition is_h (h : string) : Prop := exists k, h = hname k.

  Definition RX (D Wd : list string) (F : option expr) (AV : avail) (l : locals) (vm : Vm.t) : Prop :=
    [/\ forall x v, map.get l x = Some v -> ok_name x /\ (~~ smem x D -> get vm (vv x) = Vword (jw v)),
        forall x, smem x Wd -> exists v, map.get l x = Some v,
        (if F is Some ce then exists b, get vm cfv = Vbool b /\ leval l ce = Some (b2w b) else True) &
        forall h e, List.In (h, e) AV -> is_h h /\ exists v, leval l e = Some v /\ get vm (vv h) = Vword (jw v)].

  Definition mem_post (m m' : mem) (s s' : estate) : Prop :=
    [/\ mem_rel m' (emem s'), escs s' = escs s,
        (forall k, map.get m' k = None <-> map.get m k = None) &
        (forall p, outside m p -> read (emem s') Aligned p U8 = read (emem s) Aligned p U8)].

  Lemma mem_post_refl m (s : estate) vm : mem_rel m (emem s) -> mem_post m m s (with_vm s vm).
  Proof. by move=> h; split. Qed.

  (** What a rule establishes. *)
  Definition rspec (AV : avail) (F : option expr) (ss : list stmt) (r : res) : Prop :=
    exists cons, ss = cons ++ r_rest r /\
    forall D Wd m l (s : estate) m' l',
      brun m l cons = Some (m', l') -> RX D Wd F AV l (evm s) -> mem_rel m (emem s) ->
      all (fun x => ~~ smem x D) (r_reads r) ->
      exists s', run s (r_code r) = ok s' /\ [/\
        forall x v, map.get l' x = Some v -> ok_name x /\
          (~~ smem x (r_stale r ++ minus D (r_writes r)) -> get (evm s') (vv x) = Vword (jw v)),
        (if r_fact r is Some ce then exists b, get (evm s') cfv = Vbool b /\ leval l' ce = Some (b2w b) else True),
        forall k, get (evm s') (vv (hname k)) = get (evm s) (vv (hname k)),
        (forall x, smem x (r_reads r) -> exists w : u64, get (evm s) (vv x) = Vword w) /\
        (forall x, smem x (r_writes r) -> exists w : u64, get (evm s') (vv x) = Vword w) &
        mem_post m m' s s'].

  (** ** Generic facts *)
  Lemma flatten_cons (st : stmt) cons :
    flatten (map ssets (st :: cons)) = ssets st ++ flatten (map ssets cons).
  Proof. by []. Qed.

  Lemma brun_keep m l cons m' l' : brun m l cons = Some (m', l') ->
    forall x, ~~ smem x (flatten (map ssets cons)) -> map.get l' x = map.get l x.
  Proof.
    elim: cons m l => [|st cons ih] m l; first by move=> [_ <-].
    move=> h x; rewrite flatten_cons smem_cat negb_or => /andP [hx1 hx2].
    move: h; case: st hx1 => [y e | a v] hx1 /=.
    - case: (eval_expr m l e) => [v|] // h; rewrite (ih _ _ h x hx2) get_put_neq //.
      by move=> e'; subst y; move: hx1; rewrite /ssets smem_cons String.eqb_refl.
    - case: (eval_expr m l a) => [a'|] //; case: (eval_expr m l v) => [v'|] //.
      case: bedrock2.Memory.store => [m1|] // h; exact: ih _ _ h x hx2.
  Qed.

  Lemma brun_def m l cons m' l' : brun m l cons = Some (m', l') ->
    forall x v, map.get l x = Some v -> exists v', map.get l' x = Some v'.
  Proof.
    elim: cons m l => [|st cons ih] m l; first by move=> [_ <-] x v h; exists v.
    case: st => [y e | a v] /=.
    - case: (eval_expr m l e) => [v|] // h x w hx.
      apply: (ih _ _ h x (if String.eqb y x then v else w)).
      rewrite (@coqutil.Map.Properties.map.get_put_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec).
      by case: String.eqb.
    - case: (eval_expr m l a) => [a'|] //; case: (eval_expr m l v) => [v'|] //.
      case: bedrock2.Memory.store => [m1|] // h; exact: ih _ _ h.
  Qed.

  Lemma brun_sets m l cons m' l' : brun m l cons = Some (m', l') ->
    forall x, smem x (flatten (map ssets cons)) -> exists v, map.get l' x = Some v.
  Proof.
    elim: cons m l => [|st cons ih] m l //.
    move=> h x; rewrite flatten_cons smem_cat => /orP [hx | hx]; last first.
    - move: h; case: st => [y e | a v] /=.
      + by case: (eval_expr m l e) => [v|] // h; exact: ih _ _ h x hx.
      + case: (eval_expr m l a) => [a'|] //; case: (eval_expr m l v) => [v'|] //.
        by case: bedrock2.Memory.store => [m1|] // h; exact: ih _ _ h x hx.
    - move: h hx; case: st => [y e | a v] // h.
      rewrite /ssets smem_cons smem_nil orbF => /String.eqb_eq ->.
      move: h => /=; case: (eval_expr m l e) => [v|] // h.
      exact: (brun_def _ _ _ _ _ h _ _ (get_put_eq _ _ _)).
  Qed.


  Lemma brun_mem m l cons m' l' : brun m l cons = Some (m', l') ->
    all (fun st => if st is SSet _ _ then true else false) cons -> m' = m.
  Proof.
    elim: cons m l => [|st cons ih] m l; first by move=> [<-].
    case: st => [y e | a v] //= h hall; move: h.
    by case: (eval_expr m l e) => [v|] // h; apply: ih h hall.
  Qed.

  Lemma av_find_in AV e h : av_find AV e = Some h -> exists e', List.In (h, e') AV /\ e' = e.
  Proof.
    elim: AV => [|[h' e'] AV ih] //=.
    case he: (eeqb e' e); first by move=> [<-]; exists e'; split; [left | exact: eeqbP].
    by move=> /ih [e'' [hi he2]]; exists e''; split; [right|].
  Qed.

  (** An operand. *)
  Lemma opnd_sim AV k b cb rb D Wd F (s : estate) m l vb :
    opnd name AV k b = Some (cb, rb) -> RX D Wd F AV l (evm s) -> eval_expr m l b = Some vb ->
    all (fun x => ~~ smem x D) (opnd_vars b) ->
    exists vm1, [/\ run s cb = ok (with_vm s vm1), get vm1 (vv rb) = Vword (jw vb),
      leval l b = Some vb,
      (forall y, y <> vv (tmp k) -> get vm1 y = get (evm s) y) &
      (rb = tmp k \/ is_h rb \/ (ok_name rb /\ opnd_vars b = [:: rb]))].
  Proof.
    move=> ho [hl hW hF hAV] hev hD.
    case: b ho hev hD => [z | y | sz a | sz t a | o a | o a b' | c a b'].
    1: { rewrite /=; move=> [<- <-] [<-] _; exists (evm s).[vv (tmp k) <- Vword (wrepr U64 z)]; split => //.
      + by rewrite run_cons run_asg_cst.
      + by rewrite gset_eq jw_of_Z.
      + by move=> y hy; rewrite Vm.setP_neq //; apply/eqP; congruence.
      + by left. }
    1: { rewrite /=; case: ifP => // hok [<- <-] hy; rewrite andbT => hD.
      exists (evm s); split => //; first by rewrite with_vm_id.
      + by have [_ ->] := hl _ _ hy.
      + by right; right. }
    all: move=> ho hev _; move: ho; rewrite [opnd _ _ _ _]/=; case hf: av_find => [h|] // [<- <-].
    all: have [e' [hin he']] := av_find_in _ _ _ hf; subst e'.
    all: have [hh [v [hle hv]]] := hAV _ _ hin.
    all: have := leval_eval m _ _ _ hle; rewrite hev => -[?]; subst v.
    all: exists (evm s); split; [by rewrite with_vm_id | done | done | done | by right; left].
  Qed.


  (** ** Rule lemmas *)
  Ltac andsplit := repeat match goal with
    | h : is_true (_ && _) |- _ => move/andP: h => [? ?]
    end.

  Lemma minus_cons z D xs : minus (z :: D) xs = if smem z xs then minus D xs else z :: minus D xs.
  Proof. by rewrite /minus /=; case: smem. Qed.

  Lemma smem_minus y D xs : smem y (minus D xs) = smem y D && ~~ smem y xs.
  Proof.
    elim: D => [|z D ih] //; rewrite minus_cons smem_cons.
    case hz: (smem z xs); rewrite ?smem_cons ih; case hyz: (String.eqb y z) => //=.
    - by move/String.eqb_eq: hyz => ->; rewrite hz andbF.
    - by move/String.eqb_eq: hyz => ->; rewrite hz.
  Qed.

  Lemma opnd_var b y : opnd_vars b = [:: y] -> b = expr.var y.
  Proof. by case: b => //= y' [->]. Qed.

  Lemma with_vm2' (s : estate) vm1 vm2 : with_vm (with_vm s vm1) vm2 = with_vm s vm2.
  Proof. by []. Qed.

  Lemma vneq x y : x <> y -> vv x != vv y.
  Proof. exact: vv_neq'. Qed.

  Lemma okn_tmp x k : ok_name x -> vv x != vv (tmp k).
  Proof. by move=> h; apply: vneq; apply: ok_name_neq_tmp. Qed.
  Lemma tmp_okn x k : ok_name x -> vv (tmp k) != vv x.
  Proof. by move=> h; rewrite eq_sym; apply: okn_tmp. Qed.
  Lemma h_okn x k : ok_name x -> vv (hname k) != vv x.
  Proof. by move=> h; apply: vneq => e; apply: (ok_name_neq_h x k h); rewrite e. Qed.
  Lemma okn_h x k : ok_name x -> vv x != vv (hname k).
  Proof. by move=> h; rewrite eq_sym; apply: h_okn. Qed.
  Lemma h_tmp j k : vv (hname k) != vv (tmp j).
  Proof. by apply: vneq => e; apply: (tmp_neq_h j k); rewrite e. Qed.
  Lemma tmp_h j k : vv (tmp j) != vv (hname k).
  Proof. by rewrite eq_sym; apply: h_tmp. Qed.

  Ltac frame := repeat first
    [ rewrite Vm.setP_neq; last first; [ by first [ apply: okn_tmp | apply: tmp_okn | apply: h_okn
          | apply: okn_h | apply: h_tmp | apply: tmp_h | apply: vneq; congruence | done ] | ] ].

  Lemma neqP x y : ~~ String.eqb x y -> x <> y.
  Proof. by move=> h e; subst; rewrite String.eqb_refl in h. Qed.

  Lemma rb_neq AV k b cb rb x : opnd name AV k b = Some (cb, rb) -> ok_name x ->
    all (fun y => ~~ String.eqb y x) (evars b) ->
    (rb = tmp k \/ is_h rb \/ (ok_name rb /\ opnd_vars b = [:: rb])) -> vv rb != vv x.
  Proof.
    move=> _ hx hb [-> | [[j ->] | [_ /opnd_var he]]].
    - exact: tmp_okn.
    - exact: h_okn.
    - by subst b; move: hb => /= /andP [/neqP h _]; apply: vneq.
  Qed.

  Lemma smem_opnd y b : smem y (opnd_vars b) -> b = expr.var y.
  Proof. case: b => // y'; rewrite /opnd_vars smem_cons smem_nil orbF => /String.eqb_eq -> //. Qed.

  Lemma get_put_dec' (l : locals) x y v :
    map.get (map.put l x v) y = if String.eqb x y then Some v else map.get l y.
  Proof. exact: (@coqutil.Map.Properties.map.get_put_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec). Qed.

  Lemma rule_a0_ok AV F ss r : rule_a0 name cfn AV ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_a0; case: ss => [|[x e1|a1 v1] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // a.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    exists [:: SSet x (expr.op bopname.add (expr.var a) b)]; split => //.
    move=> D Wd m l s m' l' hb [hl hW hF hAV] hm hreads.
    move: hc => /= /andP [/andP [/andP [hokx /andP [hoka _]] /neqP hxa] hbx].
    move: hb; rewrite /brun /bstep; case hv: eval_expr => [v|] // [<- <-].
    move: hv => /=; case ha: (map.get l a) => [va|] //; case hbv: (eval_expr m l b) => [vb|] // [<-].
    move: hreads => /= /andP [hra hrbD].
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd F s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx := rb_neq AV 0 b cb rb x ho hokx hbx hrbs.
    have [hw hc] := addcarry0 va vb.
    set c := waddcarry (jw va) (jw vb) false.
    pose vm3 := vm1.[vv x <- Vword (jw va)].[cfv <- Vbool c.1].[vv x <- Vword c.2].
    exists (with_vm s vm3); split.
    { rewrite run_cat hr1 bind_ok run_cons (run_asg_var name gd _ _ _ (jw va)) // bind_ok run_cons.
      rewrite (run_carryop _ false x rb (Pbool false) (jw va) (jw vb) false) //.
      - by rewrite gset_eq.
      - by rewrite Vm.setP_neq // eq_sym. }
    split.
    - move=> y w; rewrite get_put_dec'; case hxy: (String.eqb x y).
      + move/String.eqb_eq: hxy => <- [<-].
        by split => // _; rewrite /vm3 gset_eq hw.
      + move/String.eqb_neq: hxy => hne hy.
        have [hoky hvy] := hl _ _ hy; split => // hD.
        rewrite smem_minus negb_and negbK in hD.
        rewrite /vm3 Vm.setP_neq; last by apply: vneq.
        rewrite gset_cf_neq Vm.setP_neq; last by apply: vneq.
        rewrite hfr1; last by apply/eqP; apply: okn_tmp.
        apply: hvy; move: hD => /orP [// | ]; rewrite smem_cons smem_nil orbF => /String.eqb_eq e.
        by case: hne.
    - exists c.1; split; first by rewrite /vm3 gset_vv_cf gset_cf_eq.
      by rewrite get_put_eq (get_put_neq _ _ _ _ hxa) ha -hc /ltw.
    - move=> k; rewrite /vm3 Vm.setP_neq ?gset_cf_neq ?Vm.setP_neq ?hfr1 //; try exact: okn_h.
      by apply/eqP; apply: h_tmp.
    - split.
      + move=> y /orP [/String.eqb_eq -> | hy]; first by have [_ ->] := hl _ _ ha; [exists (jw va) | ].
        move/smem_opnd: hy => hby; subst b; move: hbv hrbD => /= hy; rewrite andbT => hyD.
        by have [_ ->] := hl _ _ hy; [exists (jw vb) | ].
      + move=> y; rewrite orbF => /String.eqb_eq ->; exists c.2; by rewrite /vm3 gset_eq.
    - exact: mem_post_refl.
  Qed.


  (** Generic postconditions of a rule. *)
  Lemma smem_all (p : string -> bool) x ws : smem x ws -> all p ws -> p x.
  Proof.
    elim: ws => // y ws ih; rewrite smem_cons => /orP [/String.eqb_eq -> /andP [] // | hx /andP [_ h]].
    exact: ih.
  Qed.

  Definition vframe (ws : list string) (vm vm' : Vm.t) : Prop :=
    forall y, (forall x, smem x ws -> y <> vv x) -> (forall k, y <> vv (tmp k)) -> y <> cfv ->
      get vm' y = get vm y.

  Lemma vframe_okn ws vm vm' x : vframe ws vm vm' -> ok_name x -> ~~ smem x ws ->
    get vm' (vv x) = get vm (vv x).
  Proof.
    move=> hf hx hws; apply: hf.
    - by move=> z hz /vv_inj' e; subst; rewrite hz in hws.
    - by move=> k /vv_inj' e; apply: (ok_name_neq_tmp _ _ hx e).
    - by [].
  Qed.

  Lemma vframe_h ws vm vm' k : vframe ws vm vm' -> all ok_name ws ->
    get vm' (vv (hname k)) = get vm (vv (hname k)).
  Proof.
    move=> hf hws; apply: hf.
    - move=> z hz /vv_inj' e; subst.
      by have := smem_all ok_name _ _ hz hws.
    - by move=> j /vv_inj' e; apply: (tmp_neq_h j k); rewrite e.
    - by [].
  Qed.

  (** The bedrock2 variables after a rule: [cons] sets [ws ++ st] only, the code computes the
      values of [ws], and leaves every other source variable alone. *)
  Lemma rx_vars D ws st l l' vm vm' m m' cons :
    brun m l cons = Some (m', l') ->
    (forall x, smem x (flatten (map ssets cons)) -> smem x (ws ++ st)) ->
    all ok_name (ws ++ st) ->
    (forall x v, map.get l x = Some v -> ok_name x /\ (~~ smem x D -> get vm (vv x) = Vword (jw v))) ->
    (forall x v, smem x ws -> map.get l' x = Some v -> get vm' (vv x) = Vword (jw v)) ->
    vframe ws vm vm' ->
    forall x v, map.get l' x = Some v -> ok_name x /\
      (~~ smem x (st ++ minus D ws) -> get vm' (vv x) = Vword (jw v)).
  Proof.
    move=> hb hset hok hl hws hfr x v hx.
    case hxw: (smem x ws).
    { split; first by apply: (smem_all _ x _ _ hok); rewrite smem_cat hxw.
      by move=> _; exact: hws. }
    case hxs: (smem x (flatten (map ssets cons))).
    - have hx' := hset _ hxs; split; first exact: smem_all hx' hok.
      by move: hx'; rewrite !smem_cat hxw /= => ->.
    - have := brun_keep m l cons m' l' hb x; rewrite hxs => /(_ isT) e; rewrite e in hx.
      have [hokx hv] := hl _ _ hx; split => // hD.
      rewrite (vframe_okn _ _ _ _ hfr hokx); last by rewrite hxw.
      apply: hv; move: hD; rewrite smem_cat smem_minus hxw andbT negb_or => /andP [_ //].
  Qed.


  Lemma vframe_tmpf ws vm vm1 k : (forall y, y <> vv (tmp k) -> get vm1 y = get vm y) -> vframe ws vm vm1.
  Proof. by move=> h y _ hk _; apply: h; apply: hk. Qed.

  Lemma vframe_set ws vm vm' x v : vframe ws vm vm' -> smem x ws -> vframe ws vm vm'.[vv x <- v].
  Proof.
    move=> h hx y hy hk hc; rewrite Vm.setP_neq; first exact: h.
    by apply/eqP => e; apply: (hy x hx); rewrite e.
  Qed.

  Lemma vframe_cf ws vm vm' v : vframe ws vm vm' -> vframe ws vm vm'.[cfv <- v].
  Proof. move=> h y hy hk hc; rewrite Vm.setP_neq; first exact: h. by apply/eqP => e; apply: hc. Qed.

  Lemma vframe_tmp ws vm vm' k v : vframe ws vm vm' -> vframe ws vm vm'.[vv (tmp k) <- v].
  Proof. move=> h y hy hk hc; rewrite Vm.setP_neq; first exact: h. by apply/eqP => e; apply: (hk k). Qed.

  Definition cres (sub : bool) (wa wb : u64) (c : bool) : bool * u64 :=
    if sub then wsubcarry wa wb c else waddcarry wa wb c.

  Lemma carry_run (s : estate) vm1 sub r a rb cin (wa wb : u64) (c : bool) :
    get vm1 (vv a) = Vword wa -> get vm1 (vv rb) = Vword wb -> vv rb != vv r ->
    sem_pexpr true gd (with_vm s vm1.[vv r <- Vword wa]) cin = ok (Vbool c) ->
    run (with_vm s vm1) [:: asg name r (pv name a); carryop name cfn sub r rb cin] =
      ok (with_vm s vm1.[vv r <- Vword wa].[cfv <- Vbool (cres sub wa wb c).1]
                       .[vv r <- Vword (cres sub wa wb c).2]).
  Proof.
    move=> ha hb hne hc.
    rewrite run_cons (run_asg_var name gd _ _ _ wa) // bind_ok run_cons.
    rewrite (run_carryop _ sub r rb cin wa wb c) //.
    - by rewrite gset_eq.
    - by rewrite Vm.setP_neq // eq_sym.
  Qed.

  (** The common end of the carry rules: [cb] computes the operand, then [r := a; (cf, r) := r
      +/- rb +/- cin]; [cons] sets [r] and the stale [st]. *)
  Lemma finish_carry D Wd F AV l l' m m' (s : estate) vm1 cons sub r a rb cin cb st
      (va vb v : w64) (c : bool) fact :
    brun m l cons = Some (m', l') -> m' = m ->
    (forall x, smem x (flatten (map ssets cons)) -> smem x ([:: r] ++ st)) ->
    all ok_name ([:: r] ++ st) ->
    RX D Wd F AV l (evm s) -> mem_rel m (emem s) ->
    run s cb = ok (with_vm s vm1) -> (forall y, y <> vv (tmp 0) -> get vm1 y = get (evm s) y) ->
    get vm1 (vv a) = Vword (jw va) -> get vm1 (vv rb) = Vword (jw vb) -> vv rb != vv r ->
    sem_pexpr true gd (with_vm s vm1.[vv r <- Vword (jw va)]) cin = ok (Vbool c) ->
    map.get l' r = Some v -> jw v = (cres sub (jw va) (jw vb) c).2 ->
    leval l' fact = Some (b2w (cres sub (jw va) (jw vb) c).1) ->
    exists s', run s (cb ++ [:: asg name r (pv name a); carryop name cfn sub r rb cin]) = ok s' /\ [/\
        forall x v, map.get l' x = Some v -> ok_name x /\
          (~~ smem x (st ++ minus D [:: r]) -> get (evm s') (vv x) = Vword (jw v)),
        exists b, get (evm s') cfv = Vbool b /\ leval l' fact = Some (b2w b),
        forall k, get (evm s') (vv (hname k)) = get (evm s) (vv (hname k)),
        (forall x, smem x [:: r] -> exists w : u64, get (evm s') (vv x) = Vword w) &
        mem_post m m' s s'].
  Proof.
    move=> hb hmm hset hok [hl hW hF hAV] hm hr1 hfr1 ha hrb hne hc hv hjv hfact.
    pose vm3 := vm1.[vv r <- Vword (jw va)].[cfv <- Vbool (cres sub (jw va) (jw vb) c).1]
                   .[vv r <- Vword (cres sub (jw va) (jw vb) c).2].
    have hfr : vframe [:: r] (evm s) vm3.
    { apply: vframe_set; last by rewrite smem_cons String.eqb_refl.
      apply: vframe_cf; apply: vframe_set; last by rewrite smem_cons String.eqb_refl.
      exact: vframe_tmpf hfr1. }
    exists (with_vm s vm3); split.
    { by rewrite run_cat hr1 bind_ok (carry_run s vm1 sub r a rb cin (jw va) (jw vb) c). }
    subst m'; split.
    - apply: (rx_vars D [:: r] st l l' (evm s) vm3 m m cons hb hset hok hl) => //.
      move=> x w; rewrite smem_cons smem_nil orbF => /String.eqb_eq -> hx.
      by rewrite hv in hx; case: hx => <-; rewrite /vm3 gset_eq hjv.
    - by exists (cres sub (jw va) (jw vb) c).1; rewrite /vm3 gset_vv_cf gset_cf_eq.
    - by move=> k; apply: (vframe_h _ _ _ _ hfr); move: hok => /= /andP [-> _].
    - move=> x; rewrite smem_cons smem_nil orbF => /String.eqb_eq ->.
      by exists (cres sub (jw va) (jw vb) c).2; rewrite /vm3 gset_eq.
    - exact: mem_post_refl.
  Qed.


  Lemma eval_agree m l l' e : (forall x, smem x (evars e) -> map.get l' x = map.get l x) ->
    eval_expr m l' e = eval_expr m l e.
  Proof.
    elim: e => [z | x | sz a iha | sz t a iha | o a iha | o a iha b ihb | c ihc a iha b ihb] //= h.
    - by apply: h; rewrite /smem /= String.eqb_refl.
    - by rewrite iha.
    - by rewrite iha.
    - by rewrite iha.
    - rewrite iha ?ihb // => x hx; apply: h; by rewrite smem_cat hx ?orbT.
    - rewrite ihc; last by move=> x hx; apply: h; rewrite !smem_cat hx.
      case: eval_expr => // vc; case: CW.eqb.
      + apply: ihb => x hx; apply: h; by rewrite !smem_cat hx !orbT.
      + apply: iha => x hx; apply: h; by rewrite !smem_cat hx !orbT.
  Qed.

  Lemma not_smem_put (l : locals) x v e : ~~ smem x (evars e) ->
    forall y, smem y (evars e) -> map.get (map.put l x v) y = map.get l y.
  Proof. by move=> h y hy; apply: get_put_neq => e'; subst; rewrite hy in h. Qed.

  Lemma all_notin (xs l : list string) x : all (fun y => ~~ smem y xs) l -> smem x xs ->
    all (fun y => ~~ String.eqb y x) l.
  Proof.
    move=> /allP h hx; apply/allP => y hy; apply/negP => /String.eqb_eq e; subst.
    by move: (h _ hy); rewrite hx.
  Qed.

  Lemma all_notin_smem (xs l : list string) x : all (fun y => ~~ smem y xs) l -> smem x xs ->
    ~~ smem x l.
  Proof.
    elim: l => // z l ih; rewrite [all _ (_ :: _)]/= => /andP [hz hl] hx; rewrite smem_cons negb_or; apply/andP; split.
    - by apply/negP => /String.eqb_eq e; subst; rewrite hx in hz.
    - exact: ih hl hx.
  Qed.

  Lemma dist3 x y z : dist [:: x; y; z] -> [/\ x <> y, x <> z & y <> z].
  Proof.
    rewrite /dist /= !inE !negb_or andbT => /andP [/andP [h1 h2] h3].
    by split; apply/eqP.
  Qed.

  Lemma reads_def D l vm (xs : list string) :
    (forall x v, map.get l x = Some v -> ok_name x /\ (~~ smem x D -> get vm (vv x) = Vword (jw v))) ->
    (forall x, smem x xs -> exists v, map.get l x = Some v) -> all (fun x => ~~ smem x D) xs ->
    forall x, smem x xs -> exists w : u64, get vm (vv x) = Vword w.
  Proof.
    move=> hl hd hD x hx; have [v hv] := hd x hx; have [_ h] := hl _ _ hv.
    by exists (jw v); apply: h; apply: smem_all hx hD.
  Qed.

  Lemma smemP_in x (l : list string) : smem x l -> x \in l.
  Proof. by elim: l => // y l ih; rewrite smem_cons inE => /orP [/String.eqb_eq -> | /ih ->]; rewrite ?eqxx ?orbT. Qed.

  Lemma oeqbP F ce : oeqb F ce -> F = Some ce.
  Proof. by case: F => //= ce' /eeqbP ->. Qed.

  Lemma rx_fact D Wd ce AV l vm m : RX D Wd (Some ce) AV l vm ->
    exists b, get vm cfv = Vbool b /\ eval_expr m l ce = Some (b2w b) /\ leval l ce = Some (b2w b).
  Proof. by case=> _ _ [b [hb hce]] _; exists b; split => //; split => //; apply: leval_eval. Qed.

  Lemma rule_ac_ok AV F ss r : rule_ac name cfn AV F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_ac; case: ss => [|[s0 e1|??] rest] //.
    case: e1 => // o ce e1; case: o => //; case: e1 => // a.
    case: rest => [|[r0 e2|??] rest] //.
    case: e2 => // o e2 b; case: o => //; case: e2 => // s1.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    move: hc => /andP [/andP [/andP [/andP [/andP [/oeqbP hF /String.eqb_eq hs1] hok] hd] hbx] hst].
    subst F s1; move: hok => /= /andP [hoks /andP [hoka /andP [hokr _]]].
    have [hsr hsa hra] := dist3 _ _ _ hd.
    exists [:: SSet s0 (expr.op bopname.add ce (expr.var a)); SSet r0 (expr.op bopname.add (expr.var s0) b)].
    split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    move: (hb) => /=; rewrite hce.
    case ha: (map.get l a) => [va|] //=.
    rewrite get_put_eq (eval_agree m l); last by apply: not_smem_put; apply: (all_notin_smem _ _ _ hbx); rewrite smem_cons String.eqb_refl.
    case hbv: (eval_expr m l b) => [vb|] //= -[? ?]; subst m' l'.
    move: (hreads) => /= /andP [hra' hrbD].
    case: hrx => hl hW hF hAV.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd (Some ce) s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx := rb_neq AV 0 b cb rb r0 ho hokr (all_notin _ _ _ hbx (introT orP (or_intror (introT orP (or_introl (String.eqb_refl _)))))) hrbs.
    have [hw hcar] := addcarry2 va vb cin.
    have hb' : forall x, smem x (evars b) -> x <> s0 /\ x <> r0.
    { move=> x hx; have hn := allP hbx _ (smemP_in _ _ hx).
      by split => e; subst x; move: hn; rewrite /smem /= ?String.eqb_refl ?orbT. }
    set v1 := CW.add (b2w cin) va; set v2 := CW.add v1 vb.
    have hsets : forall x, smem x (flatten (map ssets [:: SSet s0 (expr.op bopname.add ce (expr.var a));
                      SSet r0 (expr.op bopname.add (expr.var s0) b)])) -> smem x ([:: r0] ++ [:: s0]).
    { by move=> x; rewrite /smem /=; case: (String.eqb x s0); case: (String.eqb x r0). }
    have hokall : all ok_name ([:: r0] ++ [:: s0]) by apply/andP; split => //; apply/andP.
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv r0 <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put (map.put l s0 v1) r0 v2) (ADD (LTU (V s0) (V a)) (LTU (V r0) b))
                 = Some (b2w (cres false (jw va) (jw vb) cin).1).
    { have e1 : String.eqb r0 s0 = false by apply/String.eqb_neq; apply: nesym.
      have e2 : String.eqb r0 a = false by apply/String.eqb_neq.
      have e3 : String.eqb s0 a = false by apply/String.eqb_neq.
      rewrite /= !get_put_dec' e1 e2 e3 !String.eqb_refl ha (leval_agree l); last first.
      { move=> x hx; have [hx1 hx2] := hb' x hx.
        by rewrite (get_put_neq _ r0 x _ (nesym hx2)) (get_put_neq _ s0 x _ (nesym hx1)). }
      by rewrite hlb /cres -hcar. }
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 _ false r0 a rb pcf cb [:: s0]
      va vb v2 cin (ADD (LTU (V s0) (V a)) (LTU (V r0) b))
      hb erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin (get_put_eq _ _ _) hw hfact.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
    move=> x; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hx].
    + by exists va.
    + by subst b; exists vb.
  Qed.


  Lemma rule_sc_ok AV F ss r : rule_sc name cfn AV F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_sc; case: ss => [|[s0 e1|??] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // a.
    case: rest => [|[r0 e2|??] rest] //.
    case: e2 => // o e2 ce; case: o => //; case: e2 => // s1.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    move: hc => /andP [/andP [/andP [/andP [/andP [/andP [/oeqbP hF /String.eqb_eq hs1] hok] hd] hsce] hbx] hst].
    subst F s1; move: hok => /= /andP [hoks /andP [hoka /andP [hokr _]]].
    have [hsr hsa hra] := dist3 _ _ _ hd.
    exists [:: SSet s0 (expr.op bopname.sub (expr.var a) b); SSet r0 (expr.op bopname.sub (expr.var s0) ce)].
    split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    have hb' : forall x, smem x (evars b) -> x <> s0 /\ x <> r0.
    { move=> x hx; have hn := allP hbx _ (smemP_in _ _ hx).
      by split => e; subst x; move: hn; rewrite /smem /= ?String.eqb_refl ?orbT. }
    move: (hb) => /=.
    case ha: (map.get l a) => [va|] //=.
    case hbv: (eval_expr m l b) => [vb|] //=.
    rewrite get_put_eq (eval_agree m l); last by apply: not_smem_put.
    rewrite hce /= => -[? ?]; subst m' l'.
    move: (hreads) => /= /andP [hra' hrbD].
    case: hrx => hl hW hF hAV.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd (Some ce) s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx := rb_neq AV 0 b cb rb r0 ho hokr (all_notin _ _ _ hbx (introT orP (or_intror (introT orP (or_introl (String.eqb_refl _)))))) hrbs.
    have [hw hcar] := subborrow2 va vb cin.
    set v1 := CW.sub va vb; set v2 := CW.sub v1 (b2w cin).
    have hsets : forall x, smem x (flatten (map ssets [:: SSet s0 (expr.op bopname.sub (expr.var a) b);
                      SSet r0 (expr.op bopname.sub (expr.var s0) ce)])) -> smem x ([:: r0] ++ [:: s0]).
    { by move=> x; rewrite /smem /=; case: (String.eqb x s0); case: (String.eqb x r0). }
    have hokall : all ok_name ([:: r0] ++ [:: s0]) by apply/andP; split => //; apply/andP.
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv r0 <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put (map.put l s0 v1) r0 v2) (ADD (LTU (V a) (V s0)) (LTU (V s0) (V r0)))
                 = Some (b2w (cres true (jw va) (jw vb) cin).1).
    { have e1 : String.eqb r0 s0 = false by apply/String.eqb_neq; apply: nesym.
      have e2 : String.eqb r0 a = false by apply/String.eqb_neq.
      have e3 : String.eqb s0 a = false by apply/String.eqb_neq.
      by rewrite /= !get_put_dec' e1 e2 e3 !String.eqb_refl ha /cres -hcar. }
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 _ true r0 a rb pcf cb [:: s0]
      va vb v2 cin (ADD (LTU (V a) (V s0)) (LTU (V s0) (V r0)))
      hb erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin (get_put_eq _ _ _) hw hfact.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
    move=> x; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hx].
    + by exists va.
    + by subst b; exists vb.
  Qed.


  Lemma rule_s0_ok AV F ss r : rule_s0 name cfn AV ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_s0; case: ss => [|[x e1|a1 v1] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // a.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    exists [:: SSet x (expr.op bopname.sub (expr.var a) b)]; split => //.
    move=> D Wd m l s m' l' hb [hl hW hF hAV] hm hreads.
    move: hc => /= /andP [/andP [/andP [hokx /andP [hoka _]] /neqP hxa] hbx].
    move: (hb) => /=; case ha: (map.get l a) => [va|] //; case hbv: (eval_expr m l b) => [vb|] // -[? ?].
    subst m' l'.
    move: (hreads) => /= /andP [hra hrbD].
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd F s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx := rb_neq AV 0 b cb rb x ho hokx hbx hrbs.
    have [hw hcar] := subborrow0 va vb.
    have hsets : forall y, smem y (flatten (map ssets [:: SSet x (expr.op bopname.sub (expr.var a) b)]))
                    -> smem y ([:: x] ++ [::]) by [].
    have hokall : all ok_name ([:: x] ++ [::]) by rewrite /= andbT.
    have hfact : leval (map.put l x (CW.sub va vb)) (LTU (V a) (V x)) = Some (b2w (cres true (jw va) (jw vb) false).1).
    { have e2 : String.eqb x a = false by apply/String.eqb_neq.
      by rewrite /= !get_put_dec' e2 !String.eqb_refl ha /cres -hcar. }
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd F AV l _ m m s vm1 _ true x a rb (Pbool false) cb [::]
      va vb (CW.sub va vb) false (LTU (V a) (V x))
      hb erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx erefl (get_put_eq _ _ _) hw hfact.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
    move=> y; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hy].
    + by exists va.
    + by subst b; exists vb.
  Qed.

  Lemma rule_ac1_ok AV F ss r : rule_ac1 name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_ac1; case: ss => [|[x e1|a1 v1] rest] //.
    case: e1 => // o ce e1; case: o => //; case: e1 => // a.
    case: ifP => // hc [<-].
    move: hc => /andP [/andP [/oeqbP hF /= /andP [hokx /andP [hoka _]]] /neqP hxa]; subst F.
    exists [:: SSet x (expr.op bopname.add ce (expr.var a))]; split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF hAV.
    move: (hb) => /=; rewrite hce; case ha: (map.get l a) => [va|] // -[? ?]; subst m' l'.
    move: (hreads) => /= /andP [hra _].
    pose vm1 := (evm s).[vv (tmp 0) <- Vword (wrepr U64 0)].
    have hr1 : run s [:: asg name (tmp 0) (cst 0)] = ok (with_vm s vm1) by rewrite run_cons run_asg_cst.
    have hfr1 : forall y, y <> vv (tmp 0) -> get vm1 y = get (evm s) y.
    { by move=> y hy; rewrite /vm1 Vm.setP_neq //; apply/eqP; apply: nesym. }
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrb : get vm1 (vv (tmp 0)) = Vword (jw (CW.of_Z 0)) by rewrite /vm1 gset_eq jw_of_Z.
    have hrbx : vv (tmp 0) != vv x by apply: tmp_okn.
    have [hw hcar] := addcarry1 va cin.
    have hsets : forall y, smem y (flatten (map ssets [:: SSet x (expr.op bopname.add ce (expr.var a))]))
                    -> smem y ([:: x] ++ [::]) by [].
    have hokall : all ok_name ([:: x] ++ [::]) by rewrite /= andbT.
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv x <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put l x (CW.add (b2w cin) va)) (LTU (V x) (V a))
                 = Some (b2w (cres false (jw va) (jw (CW.of_Z 0)) cin).1).
    { have e2 : String.eqb x a = false by apply/String.eqb_neq.
      by rewrite /= !get_put_dec' e2 !String.eqb_refl ha /cres jw_of_Z -hcar. }
    have hw' : jw (CW.add (b2w cin) va) = (cres false (jw va) (jw (CW.of_Z 0)) cin).2 by rewrite /cres jw_of_Z.
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 _ false x a (tmp 0) pcf _ [::]
      va (CW.of_Z 0) (CW.add (b2w cin) va) cin (LTU (V x) (V a))
      hb erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin (get_put_eq _ _ _) hw' hfact.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) [:: a] hl; apply => //.
    by move=> y; rewrite smem_cons smem_nil orbF => /String.eqb_eq ->; exists va.
  Qed.

  Lemma rule_sc1_ok AV F ss r : rule_sc1 name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_sc1; case: ss => [|[x e1|a1 v1] rest] //.
    case: e1 => // o e1 ce; case: o => //; case: e1 => // a.
    case: ifP => // hc [<-].
    move: hc => /andP [/andP [/oeqbP hF /= /andP [hokx /andP [hoka _]]] /neqP hxa]; subst F.
    exists [:: SSet x (expr.op bopname.sub (expr.var a) ce)]; split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF hAV.
    move: (hb) => /=; case ha: (map.get l a) => [va|] //; rewrite hce => -[? ?]; subst m' l'.
    move: (hreads) => /= /andP [hra _].
    pose vm1 := (evm s).[vv (tmp 0) <- Vword (wrepr U64 0)].
    have hr1 : run s [:: asg name (tmp 0) (cst 0)] = ok (with_vm s vm1) by rewrite run_cons run_asg_cst.
    have hfr1 : forall y, y <> vv (tmp 0) -> get vm1 y = get (evm s) y.
    { by move=> y hy; rewrite /vm1 Vm.setP_neq //; apply/eqP; apply: nesym. }
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrb : get vm1 (vv (tmp 0)) = Vword (jw (CW.of_Z 0)) by rewrite /vm1 gset_eq jw_of_Z.
    have hrbx : vv (tmp 0) != vv x by apply: tmp_okn.
    have [hw hcar] := subborrow1 va cin.
    have hsets : forall y, smem y (flatten (map ssets [:: SSet x (expr.op bopname.sub (expr.var a) ce)]))
                    -> smem y ([:: x] ++ [::]) by [].
    have hokall : all ok_name ([:: x] ++ [::]) by rewrite /= andbT.
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv x <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put l x (CW.sub va (b2w cin))) (LTU (V a) (V x))
                 = Some (b2w (cres true (jw va) (jw (CW.of_Z 0)) cin).1).
    { have e2 : String.eqb x a = false by apply/String.eqb_neq.
      by rewrite /= !get_put_dec' e2 !String.eqb_refl ha /cres jw_of_Z -hcar. }
    have hw' : jw (CW.sub va (b2w cin)) = (cres true (jw va) (jw (CW.of_Z 0)) cin).2 by rewrite /cres jw_of_Z.
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 _ true x a (tmp 0) pcf _ [::]
      va (CW.of_Z 0) (CW.sub va (b2w cin)) cin (LTU (V a) (V x))
      hb erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin (get_put_eq _ _ _) hw' hfact.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) [:: a] hl; apply => //.
    by move=> y; rewrite smem_cons smem_nil orbF => /String.eqb_eq ->; exists va.
  Qed.


  Lemma finish_carry0 D Wd F AV l l' m m' (s : estate) vm1 cons sub r a rb cin cb st
      (va vb v : w64) (c : bool) :
    brun m l cons = Some (m', l') -> m' = m ->
    (forall x, smem x (flatten (map ssets cons)) -> smem x ([:: r] ++ st)) ->
    all ok_name ([:: r] ++ st) ->
    RX D Wd F AV l (evm s) -> mem_rel m (emem s) ->
    run s cb = ok (with_vm s vm1) -> (forall y, y <> vv (tmp 0) -> get vm1 y = get (evm s) y) ->
    get vm1 (vv a) = Vword (jw va) -> get vm1 (vv rb) = Vword (jw vb) -> vv rb != vv r ->
    sem_pexpr true gd (with_vm s vm1.[vv r <- Vword (jw va)]) cin = ok (Vbool c) ->
    map.get l' r = Some v -> jw v = (cres sub (jw va) (jw vb) c).2 ->
    exists s', run s (cb ++ [:: asg name r (pv name a); carryop name cfn sub r rb cin]) = ok s' /\ [/\
        forall x v, map.get l' x = Some v -> ok_name x /\
          (~~ smem x (st ++ minus D [:: r]) -> get (evm s') (vv x) = Vword (jw v)),
        forall k, get (evm s') (vv (hname k)) = get (evm s) (vv (hname k)),
        (forall x, smem x [:: r] -> exists w : u64, get (evm s') (vv x) = Vword w) &
        mem_post m m' s s'].
  Proof.
    move=> hb hmm hset hok [hl hW hF hAV] hm hr1 hfr1 ha hrb hne hc hv hjv.
    pose vm3 := vm1.[vv r <- Vword (jw va)].[cfv <- Vbool (cres sub (jw va) (jw vb) c).1]
                   .[vv r <- Vword (cres sub (jw va) (jw vb) c).2].
    have hfr : vframe [:: r] (evm s) vm3.
    { apply: vframe_set; last by rewrite smem_cons String.eqb_refl.
      apply: vframe_cf; apply: vframe_set; last by rewrite smem_cons String.eqb_refl.
      exact: vframe_tmpf hfr1. }
    exists (with_vm s vm3); split.
    { by rewrite run_cat hr1 bind_ok (carry_run s vm1 sub r a rb cin (jw va) (jw vb) c). }
    subst m'; split.
    - apply: (rx_vars D [:: r] st l l' (evm s) vm3 m m cons hb hset hok hl) => //.
      move=> x w; rewrite smem_cons smem_nil orbF => /String.eqb_eq -> hx.
      by rewrite hv in hx; case: hx => <-; rewrite /vm3 gset_eq hjv.
    - by move=> k; apply: (vframe_h _ _ _ _ hfr); move: hok => /= /andP [-> _].
    - move=> x; rewrite smem_cons smem_nil orbF => /String.eqb_eq ->.
      by exists (cres sub (jw va) (jw vb) c).2; rewrite /vm3 gset_eq.
    - exact: mem_post_refl.
  Qed.

  Lemma jw_b2w_if b : jw (b2w b) = if b then wrepr U64 1 else wrepr U64 0.
  Proof. by rewrite jw_b2w; case: b. Qed.

  (** Appending [matcf co] to a rule's code: [co] stops being stale. *)
  Lemma matcf_ext D st st' ws co l' m m' (s s' : estate) b :
    ok_name co -> all ok_name ws -> map.get l' co = Some (b2w b) -> get (evm s') cfv = Vbool b ->
    (forall x, x <> co -> ~~ smem x (st' ++ minus D (ws ++ [:: co])) -> ~~ smem x (st ++ minus D ws)) ->
    (forall x v, map.get l' x = Some v -> ok_name x /\
       (~~ smem x (st ++ minus D ws) -> get (evm s') (vv x) = Vword (jw v))) ->
    (forall k, get (evm s') (vv (hname k)) = get (evm s) (vv (hname k))) ->
    (forall x, smem x ws -> exists w : u64, get (evm s') (vv x) = Vword w) ->
    mem_post m m' s s' ->
    exists s'', run s' (matcf name cfn co) = ok s'' /\ [/\
      forall x v, map.get l' x = Some v -> ok_name x /\
        (~~ smem x (st' ++ minus D (ws ++ [:: co])) -> get (evm s'') (vv x) = Vword (jw v)),
      get (evm s'') cfv = Vbool b,
      forall k, get (evm s'') (vv (hname k)) = get (evm s) (vv (hname k)),
      (forall x, smem x (ws ++ [:: co]) -> exists w : u64, get (evm s'') (vv x) = Vword w) &
      mem_post m m' s s''].
  Proof.
    move=> hco hwsok hlco hcf hst hvars hh hws [hm1 hm2 hm3 hm4].
    rewrite (run_matcf s' co b hco hcf).
    set vm'' := _.[vv co <- _]; exists (with_vm s' vm''); split => //; split.
    - move=> x v hx; have [hokx hv] := hvars x v hx; split => // hD.
      case: (String.eqb_spec x co) => [e | hne]; first subst x.
      + by rewrite /vm'' gset_eq; move: hx; rewrite hlco => -[<-]; rewrite jw_b2w_if.
      + rewrite /vm'' Vm.setP_neq; last by apply: vneq; apply: nesym.
        rewrite Vm.setP_neq; last by apply: tmp_okn.
        rewrite Vm.setP_neq; last by apply: vneq; apply: nesym.
        by apply: hv; apply: hst.
    - by rewrite /vm'' !gset_vv_cf.
    - move=> k; rewrite /vm'' Vm.setP_neq; last by apply: okn_h.
      rewrite Vm.setP_neq; last by rewrite eq_sym; apply: h_tmp.
      by rewrite Vm.setP_neq; [exact: hh | apply: okn_h].
    - move=> x; rewrite smem_cat => /orP [hx | ].
      + case: (String.eqb_spec x co) => [-> | hne]; first by rewrite /vm'' gset_eq; eexists.
        have [w hw] := hws x hx; exists w.
        rewrite /vm'' Vm.setP_neq; last by apply: vneq; apply: nesym.
        rewrite Vm.setP_neq; last by apply: tmp_okn; apply: (smem_all _ _ _ hx hwsok).
        by rewrite Vm.setP_neq //; apply: vneq; apply: nesym.
      + rewrite smem_cons smem_nil orbF => /String.eqb_eq ->; rewrite /vm'' gset_eq; by eexists.
    - by split.
  Qed.


  Ltac clean := repeat match goal with
    | h : is_true (_ && _) |- _ => move/andP: h => [? ?]
    | h : is_true (String.eqb _ _) |- _ => move/String.eqb_eq: h => ?; subst
    | h : is_true (eeqb _ _) |- _ => move/eeqbP: h => ?; subst
    | h : is_true (oeqb _ _) |- _ => move/oeqbP: h => ?; subst
    end.

  Ltac gets := repeat first [ rewrite get_put_eq | rewrite get_put_neq; last by congruence ].

  Lemma dist5 a b c d e0 : dist [:: a; b; c; d; e0] ->
    [/\ [/\ a <> b, a <> c, a <> d & a <> e0], [/\ b <> c, b <> d & b <> e0], [/\ c <> d & c <> e0] & d <> e0].
  Proof.
    move=> h; split; [split | split | split |] => e; subst; move: h;
      by rewrite /dist /= !inE !eqxx /= ?orbT ?andbF.
  Qed.

  Lemma notin5 x a b c d e : ~~ smem x [:: a; b; c; d; e] -> [/\ x <> a, x <> b, x <> c, x <> d & x <> e].
  Proof. by rewrite /smem /= !negb_or => /andP [/neqP ? /andP [/neqP ? /andP [/neqP ? /andP [/neqP ? /andP [/neqP ? _]]]]]. Qed.

  Lemma notin_all (xs l : list string) : all (fun y => ~~ smem y xs) l ->
    forall y x, smem y l -> smem x xs -> y <> x.
  Proof. by move=> h y x hy hx e; subst; have := all_notin_smem _ _ _ h hx; rewrite hy. Qed.

  Lemma smemP_in' x (l : list string) : x \in l -> smem x l.
  Proof. by elim: l => // y l ih; rewrite smem_cons inE => /orP [/eqP -> | /ih ->]; rewrite ?String.eqb_refl ?orbT. Qed.

  Lemma brun_set m l x e v ss : eval_expr m l e = Some v ->
    brun m l (SSet x e :: ss) = brun m (map.put l x v) ss.
  Proof. by move=> h; rewrite /= h. Qed.

  Lemma brun_set_none m l x e ss : eval_expr m l e = None -> brun m l (SSet x e :: ss) = None.
  Proof. by move=> h; rewrite /= h. Qed.

  Lemma all6 (p : string -> bool) a b c d e f : all p [:: a; b; c; d; e; f] ->
    [/\ p a, p b, p c, p d & p e /\ p f].
  Proof. by rewrite /= andbT => /and5P [? ? ? ? /andP [? ?]]. Qed.

  Lemma smem1 x y : smem x [:: y] = String.eqb x y.
  Proof. by rewrite smem_cons smem_nil orbF. Qed.

  Lemma stale_shift D st ws co x : x <> co ->
    ~~ smem x (st ++ minus D (ws ++ [:: co])) -> ~~ smem x ((st ++ [:: co]) ++ minus D ws).
  Proof.
    move=> hne; rewrite !smem_cat !smem_minus smem_cat smem1.
    have -> : String.eqb x co = false by apply/String.eqb_neq.
    by rewrite !orbF.
  Qed.

  Lemma rule_acm_ok AV F ss r : rule_acm name cfn AV F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_acm; case: ss => [|[s0 e1|??] rest] //.
    case: e1 => // o ce e1; case: o => //; case: e1 => // a.
    case: rest => [|[c1 e2|??] rest] //; case: e2 => // o e2 e2'; case: o => //; case: e2 => // s1; case: e2' => // a1.
    case: rest => [|[r0 e3|??] rest] //; case: e3 => // o e3 b; case: o => //; case: e3 => // s2.
    case: rest => [|[c2 e4|??] rest] //; case: e4 => // o e4 b1; case: o => //; case: e4 => // r1.
    case: rest => [|[co e5|??] rest] //; case: e5 => // o e5 e5'; case: o => //; case: e5 => // c1'; case: e5' => // c2'.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    clean.
    match goal with h : is_true (dist _) |- _ => have [[? ? ? ?] [? ? ?] [? ?] ?] := dist5 _ _ _ _ _ h end.
    match goal with h : is_true (~~ smem a _) |- _ => have [? ? ? ? ?] := notin5 _ _ _ _ _ _ h end.
    match goal with h : is_true (all okv _) |- _ => have [hoks hoka hokc1 hokr [hokc2 hokco]] := all6 _ _ _ _ _ _ _ h end.
    have hbx : forall x, smem x (evars b) -> [/\ x <> s0, x <> c1, x <> r0, x <> c2 & x <> co].
    { move=> x hx; match goal with h : is_true (all _ (evars b)) |- _ => have hh := all_notin_smem _ _ x h end.
      by apply: notin5; apply/negP => hin; move: (hh hin); rewrite hx. }
    pose cons := [:: SSet s0 (expr.op bopname.add ce (expr.var a)); SSet c1 (expr.op bopname.ltu (expr.var s0) (expr.var a));
      SSet r0 (expr.op bopname.add (expr.var s0) b); SSet c2 (expr.op bopname.ltu (expr.var r0) b);
      SSet co (expr.op bopname.add (expr.var c1) (expr.var c2))].
    exists cons; split; first by case: (stale_ok_var co rest).
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF hAV.
    have hreads0 : all (fun x => ~~ smem x D) (a :: opnd_vars b) by case: (stale_ok_var co rest) hreads.
    move: (hreads0) => /= /andP [hra hrbD].
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /cons brun_set_none //= hce ha.
    set v1 := CW.add (b2w cin) va; set k1 := ltw v1 va.
    have he1 : eval_expr m l (expr.op bopname.add ce (expr.var a)) = Some v1 by rewrite /= hce ha.
    have he2 : eval_expr m (map.put l s0 v1) (expr.op bopname.ltu (expr.var s0) (expr.var a)) = Some k1.
    { by rewrite /=; gets; rewrite ha. }
    have hbe : forall l'', (forall x, smem x (evars b) -> map.get l'' x = map.get l x) ->
      eval_expr m l'' b = eval_expr m l b by move=> l'' h; apply: eval_agree.
    case hbv: (eval_expr m l b) => [vb|]; last first.
    { move: hb; rewrite /cons (brun_set _ _ _ _ _ _ he1) (brun_set _ _ _ _ _ _ he2) brun_set_none //=.
      by gets; rewrite hbe ?hbv // => x /hbx [? ? ? ? ?]; gets. }
    set v2 := CW.add v1 vb; set k2 := ltw v2 vb.
    have he3 : eval_expr m (map.put (map.put l s0 v1) c1 k1) (expr.op bopname.add (expr.var s0) b) = Some v2.
    { by rewrite /=; gets; rewrite hbe ?hbv // => x /hbx [? ? ? ? ?]; gets. }
    have he4 : eval_expr m (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) (expr.op bopname.ltu (expr.var r0) b) = Some k2.
    { by rewrite /=; gets; rewrite hbe ?hbv // => x /hbx [? ? ? ? ?]; gets. }
    have he5 : eval_expr m (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2)
                 (expr.op bopname.add (expr.var c1) (expr.var c2)) = Some (CW.add k1 k2).
    { by rewrite /=; gets. }
    have hb2 : brun m l cons = Some (m, map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)).
    { by rewrite /cons (brun_set _ _ _ _ _ _ he1) (brun_set _ _ _ _ _ _ he2) (brun_set _ _ _ _ _ _ he3)
        (brun_set _ _ _ _ _ _ he4) (brun_set _ _ _ _ _ _ he5). }
    rewrite hb2 in hb; case: hb => ? ?; subst m' l'.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd (Some ce) s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx : vv rb != vv r0.
    { apply: (rb_neq AV 0 b cb rb r0 ho hokr) => //.
      by apply/allP => y /smemP_in' /hbx [? ? ? ? ?]; apply/negP => /String.eqb_eq. }
    have [hw hcar] := addcarry2 va vb cin.
    have hsets : forall x, smem x (flatten (map ssets cons)) -> smem x ([:: r0] ++ [:: s0; c1; c2; co]).
    { by move=> x; rewrite /smem /=; case: (String.eqb x s0); case: (String.eqb x c1); case: (String.eqb x r0);
        case: (String.eqb x c2); case: (String.eqb x co). }
    have hokall : all ok_name ([:: r0] ++ [:: s0; c1; c2; co]).
    { by rewrite /okv in hokr hoks hokc1 hokc2 hokco; rewrite /= hokr hoks hokc1 hokc2 hokco. }
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv r0 <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) (V co)
                 = Some (b2w (cres false (jw va) (jw vb) cin).1).
    { by rewrite /= get_put_eq /cres -hcar. }
    have hv2 : map.get (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) r0 = Some v2.
    { by gets. }
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 cons false r0 a rb pcf cb [:: s0; c1; c2; co]
      va vb v2 cin (V co) hb2 erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin hv2 hw hfact.
    have hreads' : forall x, smem x (a :: opnd_vars b) -> exists w : u64, get (evm s) (vv x) = Vword w.
    { have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
      move=> x; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hx]; first by exists va.
      by subst b; exists vb. }
    case: (stale_ok_var co rest).
    - by exists s'; split => //; split => //; split.
    - have [bco [hcfb hlco]] := h2.
      have hco : map.get (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) co
                 = Some (b2w bco) by move: hlco => /=.
      have hokr1 : all ok_name [:: r0] by rewrite /okv in hokr; rewrite /= hokr.
      have [s'' [hrun2 [g1 g2 g3 g4 g5]]] := matcf_ext D [:: s0; c1; c2; co] [:: s0; c1; c2] [:: r0] co _ m m s s' bco
        hokco hokr1 hco hcfb (fun x hx => stale_shift D [:: s0; c1; c2] [:: r0] co x hx) h1 h3 h4 h5.
      exists s''; split; first by rewrite run_cat hrun bind_ok hrun2.
      split => //; first by exists bco; split => //.
  Qed.


  Lemma notin_evars x e : ~~ smem x (evars e) -> forall y, smem y (evars e) -> y <> x.
  Proof. by move=> h y hy e'; subst; rewrite hy in h. Qed.

  Lemma rule_scm_ok AV F ss r : rule_scm name cfn AV F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_scm; case: ss => [|[s0 e1|??] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // a.
    case: rest => [|[c1 e2|??] rest] //; case: e2 => // o e2 e2'; case: o => //; case: e2 => // a1; case: e2' => // s1.
    case: rest => [|[r0 e3|??] rest] //; case: e3 => // o e3 ce; case: o => //; case: e3 => // s2.
    case: rest => [|[c2 e4|??] rest] //; case: e4 => // o e4 e4'; case: o => //; case: e4 => // s3; case: e4' => // r1.
    case: rest => [|[co e5|??] rest] //; case: e5 => // o e5 e5'; case: o => //; case: e5 => // c1'; case: e5' => // c2'.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    clean.
    match goal with h : is_true (dist _) |- _ => have [[? ? ? ?] [? ? ?] [? ?] ?] := dist5 _ _ _ _ _ h end.
    match goal with h : is_true (~~ smem a _) |- _ => have [? ? ? ? ?] := notin5 _ _ _ _ _ _ h end.
    match goal with h : is_true (all okv _) |- _ => have [hoks hoka hokc1 hokr [hokc2 hokco]] := all6 _ _ _ _ _ _ _ h end.
    have hbx : forall x, smem x (evars b) -> [/\ x <> s0, x <> c1, x <> r0, x <> c2 & x <> co].
    { move=> x hx; match goal with h : is_true (all _ (evars b)) |- _ => have hh := all_notin_smem _ _ x h end.
      by apply: notin5; apply/negP => hin; move: (hh hin); rewrite hx. }
    have hcex : forall x, smem x (evars ce) -> x <> s0 /\ x <> c1.
    { move=> x hx; split.
      - by match goal with h : is_true (~~ smem s0 (evars ce)) |- _ => exact: notin_evars h x hx end.
      - by match goal with h : is_true (~~ smem c1 (evars ce)) |- _ => exact: notin_evars h x hx end. }
    pose cons := [:: SSet s0 (expr.op bopname.sub (expr.var a) b); SSet c1 (expr.op bopname.ltu (expr.var a) (expr.var s0));
      SSet r0 (expr.op bopname.sub (expr.var s0) ce); SSet c2 (expr.op bopname.ltu (expr.var s0) (expr.var r0));
      SSet co (expr.op bopname.add (expr.var c1) (expr.var c2))].
    exists cons; split; first by case: (stale_ok_var co rest).
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF hAV.
    have hreads0 : all (fun x => ~~ smem x D) (a :: opnd_vars b) by case: (stale_ok_var co rest) hreads.
    move: (hreads0) => /= /andP [hra hrbD].
    have hbe : forall l'', (forall x, smem x (evars b) -> map.get l'' x = map.get l x) ->
      eval_expr m l'' b = eval_expr m l b by move=> l'' h; apply: eval_agree.
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /cons brun_set_none //= ha.
    case hbv: (eval_expr m l b) => [vb|]; last by move: hb; rewrite /cons brun_set_none //= ha hbv.
    set v1 := CW.sub va vb; set k1 := ltw va v1.
    have he1 : eval_expr m l (expr.op bopname.sub (expr.var a) b) = Some v1 by rewrite /= ha hbv.
    have he2 : eval_expr m (map.put l s0 v1) (expr.op bopname.ltu (expr.var a) (expr.var s0)) = Some k1.
    { by rewrite /=; gets; rewrite ha. }
    set v2 := CW.sub v1 (b2w cin); set k2 := ltw v1 v2.
    have he3 : eval_expr m (map.put (map.put l s0 v1) c1 k1) (expr.op bopname.sub (expr.var s0) ce) = Some v2.
    { rewrite /=; gets; rewrite (eval_agree m l _ ce) ?hce //.
      by move=> x /hcex [? ?]; gets. }
    have he4 : eval_expr m (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) (expr.op bopname.ltu (expr.var s0) (expr.var r0)) = Some k2.
    { by rewrite /=; gets. }
    have he5 : eval_expr m (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2)
                 (expr.op bopname.add (expr.var c1) (expr.var c2)) = Some (CW.add k1 k2).
    { by rewrite /=; gets. }
    have hb2 : brun m l cons = Some (m, map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)).
    { by rewrite /cons (brun_set _ _ _ _ _ _ he1) (brun_set _ _ _ _ _ _ he2) (brun_set _ _ _ _ _ _ he3)
        (brun_set _ _ _ _ _ _ he4) (brun_set _ _ _ _ _ _ he5). }
    rewrite hb2 in hb; case: hb => ? ?; subst m' l'.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd (Some ce) s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx : vv rb != vv r0.
    { apply: (rb_neq AV 0 b cb rb r0 ho hokr) => //.
      by apply/allP => y /smemP_in' /hbx [? ? ? ? ?]; apply/negP => /String.eqb_eq. }
    have [hw hcar] := subborrow2 va vb cin.
    have hsets : forall x, smem x (flatten (map ssets cons)) -> smem x ([:: r0] ++ [:: s0; c1; c2; co]).
    { by move=> x; rewrite /smem /=; case: (String.eqb x s0); case: (String.eqb x c1); case: (String.eqb x r0);
        case: (String.eqb x c2); case: (String.eqb x co). }
    have hokall : all ok_name ([:: r0] ++ [:: s0; c1; c2; co]).
    { by rewrite /okv in hokr hoks hokc1 hokc2 hokco; rewrite /= hokr hoks hokc1 hokc2 hokco. }
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv r0 <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have hfact : leval (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) (V co)
                 = Some (b2w (cres true (jw va) (jw vb) cin).1).
    { by rewrite /= get_put_eq /cres -hcar. }
    have hv2 : map.get (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) r0 = Some v2.
    { by gets. }
    have [s' [hrun [h1 h2 h3 h4 h5]]] := finish_carry D Wd (Some ce) AV l _ m m s vm1 cons true r0 a rb pcf cb [:: s0; c1; c2; co]
      va vb v2 cin (V co) hb2 erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin hv2 hw hfact.
    have hreads' : forall x, smem x (a :: opnd_vars b) -> exists w : u64, get (evm s) (vv x) = Vword w.
    { have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
      move=> x; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hx]; first by exists va.
      by subst b; exists vb. }
    case: (stale_ok_var co rest).
    - by exists s'; split => //; split => //; split.
    - have [bco [hcfb hlco]] := h2.
      have hco : map.get (map.put (map.put (map.put (map.put (map.put l s0 v1) c1 k1) r0 v2) c2 k2) co (CW.add k1 k2)) co
                 = Some (b2w bco) by move: hlco => /=.
      have hokr1 : all ok_name [:: r0] by rewrite /okv in hokr; rewrite /= hokr.
      have [s'' [hrun2 [g1 g2 g3 g4 g5]]] := matcf_ext D [:: s0; c1; c2; co] [:: s0; c1; c2] [:: r0] co _ m m s s' bco
        hokco hokr1 hco hcfb (fun x hx => stale_shift D [:: s0; c1; c2] [:: r0] co x hx) h1 h3 h4 h5.
      exists s''; split; first by rewrite run_cat hrun bind_ok hrun2.
      split => //; first by exists bco; split => //.
  Qed.


  Lemma rule_acx_ok AV F ss r : rule_acx name cfn AV F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_acx; case: ss => [|[x e1|??] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // o ce e1; case: o => //; case: e1 => // a.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    move: hc => /andP [/andP [/andP [/oeqbP hF /= /andP [hokx /andP [hoka _]]] /neqP hxa] hbx]; subst F.
    pose cons := [:: SSet x (expr.op bopname.add (expr.op bopname.add ce (expr.var a)) b)].
    exists cons; split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF hAV.
    move: (hreads) => /= /andP [hra hrbD].
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /cons brun_set_none //= hce ha.
    case hbv: (eval_expr m l b) => [vb|]; last by move: hb; rewrite /cons brun_set_none //= hce ha hbv.
    set v := CW.add (CW.add (b2w cin) va) vb.
    have he1 : eval_expr m l (expr.op bopname.add (expr.op bopname.add ce (expr.var a)) b) = Some v by rewrite /= hce ha hbv.
    have hb2 : brun m l cons = Some (m, map.put l x v) by rewrite /cons (brun_set _ _ _ _ _ _ he1).
    rewrite hb2 in hb; case: hb => ? ?; subst m' l'.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 0 b cb rb D Wd (Some ce) s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrbx := rb_neq AV 0 b cb rb x ho hokx hbx hrbs.
    have [hw _] := addcarry2 va vb cin.
    have hsets : forall y, smem y (flatten (map ssets cons)) -> smem y ([:: x] ++ [::]) by [].
    have hokall : all ok_name ([:: x] ++ [::]) by rewrite /= andbT.
    have hcin : sem_pexpr true gd (with_vm s vm1.[vv x <- Vword (jw va)]) pcf = ok (Vbool cin).
    { by apply: pcf_eval; rewrite gset_vv_cf hfr1. }
    have [s' [hrun [h1 h3 h4 h5]]] := finish_carry0 D Wd (Some ce) AV l _ m m s vm1 cons false x a rb pcf cb [::]
      va vb v cin hb2 erefl hsets hokall (And4 hl hW hF hAV) hm hr1 hfr1 hva hrb hrbx hcin (get_put_eq _ _ _) hw.
    exists s'; split => //; split => //; split => //.
    have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
    move=> y; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hy]; first by exists va.
    by subst b; exists vb.
  Qed.

  Lemma jw_wumul (a b : w64) :
    jw (CW.mul a b) = (wumul (jw a) (jw b)).2 /\ jw (CW.mulhuu a b) = (wumul (jw a) (jw b)).1.
  Proof.
    split; last by rewrite jw_mulhuu.
    by rewrite jw_mul /wumul /= /jw -wrepr_mul !wunsigned_jw.
  Qed.


  Lemma rule_mulx_ok AV F ss r : rule_mulx name AV ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_mulx; case: ss => [|[x e1|??] rest] //.
    case: e1 => // o e1 b; case: o => //; case: e1 => // a.
    case: rest => [|[y e2|??] rest] //; case: e2 => // o e2 b'; case: o => //; case: e2 => // a'.
    case: ifP => // hc; case ho: opnd => [[cb rb]|] // [<-].
    move: hc => /andP [/andP [/andP [/andP [/String.eqb_eq ? /eeqbP ?] hok] /neqP hxy] hxab]; subst a' b'.
    move: hok => /= /andP [hokx /andP [hoky /andP [hoka _]]].
    rewrite /okv in hokx hoky hoka.
    move: hxab; rewrite smem_cons negb_or => /andP [/neqP hxa hxb].
    have hbx : forall z, smem z (evars b) -> z <> x by move=> z hz e; subst; rewrite hz in hxb.
    pose cons := [:: SSet x (expr.op bopname.mul (expr.var a) b); SSet y (expr.op bopname.mulhuu (expr.var a) b)].
    exists cons; split => //.
    move=> D Wd m l s m' l' hb [hl hW hF hAV] hm hreads.
    move: (hreads) => /= /andP [hra hrbD].
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /cons brun_set_none //= ha.
    case hbv: (eval_expr m l b) => [vb|]; last by move: hb; rewrite /cons brun_set_none //= ha hbv.
    have he1 : eval_expr m l (expr.op bopname.mul (expr.var a) b) = Some (CW.mul va vb) by rewrite /= ha hbv.
    have he2 : eval_expr m (map.put l x (CW.mul va vb)) (expr.op bopname.mulhuu (expr.var a) b) = Some (CW.mulhuu va vb).
    { rewrite /= get_put_neq; last exact: hxa.
      by rewrite ha (eval_agree m l) ?hbv // => z hz; rewrite get_put_neq //; apply: nesym; apply: hbx. }
    have hb2 : brun m l cons = Some (m, map.put (map.put l x (CW.mul va vb)) y (CW.mulhuu va vb)).
    { by rewrite /cons (brun_set _ _ _ _ _ _ he1) (brun_set _ _ _ _ _ _ he2). }
    rewrite hb2 in hb; case: hb => ? ?; subst m' l'.
    have [vm1 [hr1 hrb hlb hfr1 hrbs]] := opnd_sim AV 1 b cb rb D Wd F s m l vb ho (And4 hl hW hF hAV) hbv hrbD.
    have hva : get vm1 (vv a) = Vword (jw va).
    { rewrite hfr1; last by apply/eqP; apply: okn_tmp.
      by have [_ ->] := hl _ _ ha. }
    have hrb0 : vv rb != vv (tmp 0).
    { case: hrbs => [-> | [[j ->] | [hokrb _]]].
      - by apply: vneq => /tmp_inj.
      - exact: h_tmp.
      - exact: okn_tmp. }
    have [hjx hjy] := jw_wumul va vb.
    set u := wumul (jw va) (jw vb).
    pose vm3 := vm1.[vv (tmp 0) <- Vword (jw va)].[vv x <- Vword u.2].[vv y <- Vword u.1].
    have hrun : run s (cb ++ [:: asg name (tmp 0) (pv name a); mulx name x y (tmp 0) rb]) = ok (with_vm s vm3).
    { rewrite run_cat hr1 bind_ok run_cons (run_asg_var name gd _ _ _ (jw va)) // bind_ok run_cons.
      rewrite (run_mulx name gd _ x y (tmp 0) rb (jw va) (jw vb)) //.
      - by rewrite gset_eq.
      - by rewrite Vm.setP_neq // eq_sym. }
    have hfr : vframe [:: x; y] (evm s) vm3.
    { apply: vframe_set; last by rewrite smem_cons smem_cons String.eqb_refl orbT.
      apply: vframe_set; last by rewrite smem_cons String.eqb_refl.
      apply: vframe_tmp; exact: vframe_tmpf hfr1. }
    have hokall : all ok_name ([:: x; y] ++ [::]) by rewrite /= hokx hoky.
    exists (with_vm s vm3); split => //; split.
    - apply: (rx_vars D [:: x; y] [::] l _ (evm s) vm3 m m cons hb2 _ hokall hl _ hfr).
      + by move=> z; rewrite /smem /=; case: (String.eqb z x); case: (String.eqb z y).
      + move=> z w; rewrite smem_cons smem1 => /orP [/String.eqb_eq -> | /String.eqb_eq ->] hz.
        * move: hz; rewrite get_put_neq; last exact: (nesym hxy).
          rewrite get_put_eq => -[<-].
          by rewrite /vm3 Vm.setP_neq; [rewrite gset_eq hjx | apply: vneq; apply: nesym].
        * by move: hz; rewrite get_put_eq => -[<-]; rewrite /vm3 gset_eq hjy.
    - by [].
    - by move=> k; apply: (vframe_h _ _ _ _ hfr); rewrite /= hokx hoky.
    - split.
      + have := reads_def D l (evm s) (a :: opnd_vars b) hl; apply => //.
        move=> z; rewrite smem_cons => /orP [/String.eqb_eq -> | /smem_opnd hz]; first by exists va.
        by subst b; exists vb.
      + move=> z; rewrite orbF => /orP [/String.eqb_eq -> | /String.eqb_eq ->].
        * by rewrite /vm3 Vm.setP_neq; [rewrite gset_eq; eexists | apply: vneq; apply: nesym].
        * by rewrite /vm3 gset_eq; eexists.
    - exact: mem_post_refl.
  Qed.


  Lemma vframe_refl ws vm : vframe ws vm vm. Proof. by []. Qed.

  Lemma mem_post_id m (s : estate) : mem_rel m (emem s) -> mem_post m m s s.
  Proof. by move=> h; split. Qed.

  Lemma rule_name_ok AV F ss r : rule_name name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_name; case: ss => [|[c ce|??] rest] //.
    case: ifP => // /andP [/oeqbP hF hokc]; subst F; rewrite /okv in hokc.
    have hcore : forall D Wd m l (s : estate) m' l', brun m l [:: SSet c ce] = Some (m', l') ->
      RX D Wd (Some ce) AV l (evm s) -> mem_rel m (emem s) ->
      exists b, [/\ m' = m, map.get l' c = Some (b2w b), get (evm s) cfv = Vbool b &
        forall x v, map.get l' x = Some v -> ok_name x /\
          (~~ smem x ([:: c] ++ minus D [::]) -> get (evm s) (vv x) = Vword (jw v))].
    { move=> D Wd m l s m' l' hb hrx hm.
      have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
      case: hrx => hl hW hF' hAV.
      move: (hb); rewrite (brun_set _ _ _ _ _ _ hce) => -[? ?]; subst m' l'.
      exists cin; split => //; first exact: get_put_eq.
      apply: (rx_vars D [::] [:: c] l _ (evm s) (evm s) m m _ hb) => //; try by rewrite /= hokc. }
    case hsv: (stale_ok_var c rest) => -[<-].
    - exists [:: SSet c ce]; split => //.
      move=> D Wd m l s m' l' hb hrx hm _.
      have [b [? hlc hcf hvars]] := hcore D Wd m l s m' l' hb hrx hm; subst m'.
      exists s; split => //; split => //; try (by exists b; split => //=; rewrite hlc);
        try (by split); try (exact: mem_post_id hm).
    - exists [:: SSet c ce]; split => //.
      move=> D Wd m l s m' l' hb hrx hm _.
      have [b [? hlc hcf hvars]] := hcore D Wd m l s m' l' hb hrx hm; subst m'.
      have [s'' [hrun [g1 g2 g3 g4 g5]]] := matcf_ext D [:: c] [::] [::] c l' m m s s b hokc isT hlc hcf
        (fun x hx => stale_shift D [::] [::] c x hx) hvars (fun k => erefl) (fun x (hx : smem x [::]) => ltac:(by [])) (mem_post_id m s hm).
      exists s''; split => //; split => //; try (by exists b; split => //=; rewrite hlc); try (by split).
  Qed.


  Lemma rule_mask_ok AV F ss r : rule_mask name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_mask; case: ss => [|[x e1|??] rest] //.
    case: e1 => // o e1 e1'; case: o => //; case: e1 => // o1 e1; case: o1 => //; case: e1 => // z; case: z => // p; case: p => //.
    case: e1' => // o ce z0; case: o => //; case: z0 => // z0; case: z0 => //.
    case: ifP => // /andP [/oeqbP hF hokx] [<-]; subst F; rewrite /okv in hokx.
    pose e := expr.op bopname.add (expr.op1 op1.opp (expr.literal 1)) (expr.op bopname.eq ce (expr.literal 0)).
    exists [:: SSet x e]; split => //.
    move=> D Wd m l s m' l' hb hrx hm _.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF' hAV.
    have he : eval_expr m l e = Some (CW.opp (b2w cin)) by rewrite /e /= hce -mask_b2w.
    move: (hb); rewrite (brun_set _ _ _ _ _ _ he) => -[? ?]; subst m' l'.
    pose vm' := (evm s).[vv x <- Vword (wrepr U64 0)].[vv x <- Vword (wsubcarry (wrepr U64 0) (wrepr U64 0) cin).2].
    have hrun : run s [:: asg name x (cst 0); sbbself name cfn x] = ok (with_vm s vm').
    { rewrite run_cons run_asg_cst bind_ok run_cons (run_sbbself _ x (wrepr U64 0) cin) //.
      - by rewrite gset_eq.
      - by rewrite gset_vv_cf. }
    have hfr : vframe [:: x] (evm s) vm'.
    { by apply: vframe_set; [apply: vframe_set; [apply: vframe_refl |] |]; rewrite smem1 String.eqb_refl. }
    exists (with_vm s vm'); split => //; split.
    - apply: (rx_vars D [:: x] [::] l _ (evm s) vm' m m _ hb) => //; try by rewrite /= hokx.
      move=> y w; rewrite smem1 => /String.eqb_eq ->; rewrite get_put_eq => -[<-].
      by rewrite /vm' gset_eq jw_mask.
    - by [].
    - by move=> k; apply: (vframe_h _ _ _ _ hfr); rewrite /= hokx.
    - split => // y; rewrite smem1 => /String.eqb_eq ->; rewrite /vm' gset_eq; by eexists.
    - exact: mem_post_refl.
  Qed.

  Lemma rule_sel_ok AV F ss r : rule_sel name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_sel; case: ss => [|[m0 e1|??] rest] //.
    case: e1 => // o e1 e1'; case: o => //; case: e1 => // o1 e1; case: o1 => //; case: e1 => // z; case: z => // p; case: p => //.
    case: e1' => // o ce z0; case: o => //; case: z0 => // z0; case: z0 => //.
    case: rest => [|[n0 e2|??] rest] //; case: e2 => // o e2 e2'; case: o => //; case: e2 => // m1; case: e2' => // k.
    case: rest => [|[r0 e3|??] rest] //; case: e3 => // o e3 e3'; case: o => //.
    case: e3 => // o e3 e3''; case: o => //; case: e3 => // a; case: e3'' => // m2.
    case: e3' => // o e4 e4'; case: o => //; case: e4 => // b; case: e4' => // n1.
    case: ifP => // hc [<-].
    clean.
    match goal with h : is_true (Z.eqb _ _) |- _ => move/Z.eqb_eq: h => ? end; subst k.
    match goal with h : is_true (dist _) |- _ => move: h; rewrite /dist /= !inE !negb_or andbT => /andP [/andP [/eqP hmn /eqP hmr] /eqP hnr] end.
    match goal with h : is_true (~~ smem a _) |- _ => move: h; rewrite /smem /= !negb_or => /andP [/neqP ham /andP [/neqP han /andP [/neqP har _]]] end.
    match goal with h : is_true (~~ smem b _) |- _ => move: h; rewrite /smem /= !negb_or => /andP [/neqP hbm /andP [/neqP hbn _]] end.
    match goal with h : is_true (all okv _) |- _ => move: h; rewrite /= /okv => /and5P [hokm hokn hokr hoka /andP [hokb _]] end.
    have hce3 : forall y, smem y (evars ce) -> [/\ y <> m0, y <> n0 & y <> r0].
    { move=> y hy; match goal with h : is_true (all _ (evars ce)) |- _ => have hh := all_notin_smem _ _ y h end.
      by split => e; subst y; move: (hh ltac:(by rewrite /smem /= String.eqb_refl ?orbT)); rewrite hy. }
    pose cons := [:: SSet m0 (expr.op bopname.add (expr.op1 op1.opp (expr.literal 1)) (expr.op bopname.eq ce (expr.literal 0)));
      SSet n0 (expr.op bopname.xor (expr.var m0) (expr.literal (2 ^ 64 - 1)));
      SSet r0 (expr.op bopname.or (expr.op bopname.and (expr.var a) (expr.var m0)) (expr.op bopname.and (expr.var b) (expr.var n0)))].
    exists cons; split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF' hAV.
    move: (hreads) => /= /andP [hra /andP [hrb _]].
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /cons /= hce; gets; rewrite ha.
    case hbb: (map.get l b) => [vb|]; last by move: hb; rewrite /cons /= hce; gets; rewrite ha hbb.
    pose vm0 := @CW.add 64 W (@CW.opp 64 W (@CW.of_Z 64 W 1))
      (if @CW.eqb 64 W (b2w cin) (@CW.of_Z 64 W 0) then @CW.of_Z 64 W 1 else @CW.of_Z 64 W 0).
    pose vn := @CW.xor 64 W vm0 (@CW.of_Z 64 W (2 ^ 64 - 1)).
    have he1 : eval_expr m l (expr.op bopname.add (expr.op1 op1.opp (expr.literal 1)) (expr.op bopname.eq ce (expr.literal 0))) = Some vm0.
    { by rewrite /= hce. }
    have he2 : eval_expr m (map.put l m0 vm0) (expr.op bopname.xor (expr.var m0) (expr.literal (2 ^ 64 - 1))) = Some vn.
    { by rewrite /= get_put_eq. }
    have he3 : eval_expr m (map.put (map.put l m0 vm0) n0 vn)
      (expr.op bopname.or (expr.op bopname.and (expr.var a) (expr.var m0)) (expr.op bopname.and (expr.var b) (expr.var n0)))
      = Some (if cin then va else vb).
    { rewrite /=; gets; rewrite ha hbb; congr Some; exact: select_b2w. }
    have hb2 : brun m l cons = Some (m, map.put (map.put (map.put l m0 vm0) n0 vn) r0 (if cin then va else vb)).
    { by rewrite /cons (brun_set _ _ _ _ _ _ he1) (brun_set _ _ _ _ _ _ he2) (brun_set _ _ _ _ _ _ he3). }
    rewrite hb2 in hb; case: hb => ? ?; subst m' l'.
    have [_ hva] := hl _ _ ha; have [_ hvb] := hl _ _ hbb.
    pose vm' := (evm s).[vv r0 <- Vword (jw vb)].[vv r0 <- Vword (if cin then jw va else jw vb)].
    have hrun : run s [:: asg name r0 (pv name b); asg name r0 (Pif (aword U64) pcf (pv name a) (pv name r0))] = ok (with_vm s vm').
    { rewrite run_cons (run_asg_var name gd _ _ _ (jw vb)) ?hvb // bind_ok run_cons.
      rewrite (run_pif_cf _ r0 a r0 (jw va) (jw vb) cin) //.
      - by rewrite gset_neq ?hva //; apply: nesym.
      - by rewrite gset_eq.
      - by rewrite gset_vv_cf. }
    have hfr : vframe [:: r0] (evm s) vm'.
    { by apply: vframe_set; [apply: vframe_set; [apply: vframe_refl |] |]; rewrite smem1 String.eqb_refl. }
    exists (with_vm s vm'); split => //; split.
    - apply: (rx_vars D [:: r0] [:: m0; n0] l _ (evm s) vm' m m cons hb2) => //.
      + by move=> y; rewrite /smem /=; case: (String.eqb y m0); case: (String.eqb y n0); case: (String.eqb y r0).
      + by rewrite /= hokr hokm hokn.
      + move=> y w; rewrite smem1 => /String.eqb_eq ->; rewrite get_put_eq => -[<-].
        by rewrite /vm' gset_eq; case: (cin).
    - exists cin; split; first by rewrite /vm' !gset_vv_cf.
      rewrite (leval_agree l) //; move=> y hy; have [? ? ?] := hce3 y hy; by gets.
    - by move=> k; apply: (vframe_h _ _ _ _ hfr); rewrite /= hokr.
    - split.
      + move=> y; rewrite ?orbF => /orP [/String.eqb_eq -> | /String.eqb_eq ->].
        * by have [_ ->] := hl _ _ ha; [eexists |].
        * by have [_ ->] := hl _ _ hbb; [eexists |].
      + by move=> y; rewrite ?orbF => /String.eqb_eq ->; rewrite /vm' gset_eq; eexists.
    - exact: mem_post_refl.
  Qed.


  Lemma rule_sf_ok AV F ss r : rule_sf name cfn F ss = Some r -> rspec AV F ss r.
  Proof.
    rewrite /rule_sf; case: ss => [|[x e1|??] rest] //.
    case: e1 => // o e1 e1'; case: o => //; case: e1 => // a; case: e1' => // o e2 ce; case: o => //; case: e2 => // a'.
    case: ifP => // /andP [/andP [/oeqbP hF /String.eqb_eq ?] hok] [<-]; subst F a'.
    move: hok; rewrite /= /okv andbT => /andP [hokx hoka].
    pose e := expr.op bopname.ltu (expr.var a) (expr.op bopname.sub (expr.var a) ce).
    exists [:: SSet x e]; split => //.
    move=> D Wd m l s m' l' hb hrx hm hreads.
    have [cin [hcf [hce hlce]]] := rx_fact D Wd ce AV l (evm s) m hrx.
    case: hrx => hl hW hF' hAV.
    move: (hreads) => /= /andP [hra _].
    case ha: (map.get l a) => [va|]; last by move: hb; rewrite /= ha.
    set c' := (wsubcarry (jw va) (wrepr U64 0) cin).1.
    have he : eval_expr m l e = Some (b2w c') by rewrite /e /= ha hce -subborrow_ltw.
    move: (hb); rewrite (brun_set _ _ _ _ _ _ he) => -[? ?]; subst m' l'.
    have [_ hva] := hl _ _ ha; have hva' := hva hra.
    pose vm1 := (evm s).[vv (tmp 0) <- Vword (wrepr U64 0)].[vv (tmp 2) <- Vword (jw va)]
                  .[cfv <- Vbool c'].[vv (tmp 2) <- Vword (wsubcarry (jw va) (wrepr U64 0) cin).2].
    have hrun1 : run s [:: asg name (tmp 0) (cst 0); asg name (tmp 2) (pv name a); carryop name cfn true (tmp 2) (tmp 0) pcf]
                 = ok (with_vm s vm1).
    { rewrite run_cons run_asg_cst bind_ok run_cons (run_asg_var name gd _ _ _ (jw va)); last first.
      { by rewrite gset_neq //; apply: ok_name_neq_tmp. }
      rewrite bind_ok run_cons (run_carryop _ true (tmp 2) (tmp 0) pcf (jw va) (wrepr U64 0) cin) //.
      - by rewrite gset_eq.
      - by rewrite gset_neq ?gset_eq // => /tmp_inj.
      - by apply: pcf_eval; rewrite !gset_vv_cf. }
    have hfr : vframe [::] (evm s) vm1.
    { by apply: vframe_tmp; apply: vframe_cf; apply: vframe_tmp; apply: vframe_tmp; apply: vframe_refl. }
    have hvars := rx_vars D [::] [:: x] l _ (evm s) vm1 m m _ hb ltac:(by []) ltac:(by rewrite /= hokx) hl ltac:(by []) hfr.
    have hcf1 : get vm1 cfv = Vbool c' by rewrite /vm1 gset_vv_cf gset_cf_eq.
    have [s'' [hrun2 [g1 g2 g3 g4 g5]]] := matcf_ext D [:: x] [::] [::] x _ m m s (with_vm s vm1) c' hokx isT
      (get_put_eq _ _ _) hcf1 (fun y hy => stale_shift D [::] [::] x y hy) hvars
      (fun k => vframe_h _ _ _ _ hfr isT) (fun y (hy : smem y [::]) => ltac:(by [])) (mem_post_refl m s vm1 hm).
    have hrun : run s ([:: asg name (tmp 0) (cst 0); asg name (tmp 2) (pv name a); carryop name cfn true (tmp 2) (tmp 0) pcf]
                       ++ matcf name cfn x) = ok s'' by rewrite run_cat hrun1 bind_ok hrun2.
    exists s''; split; first exact: hrun.
    split => //.
    - by exists c'; split => //=; rewrite get_put_eq.
    - split => //; have := reads_def D l (evm s) [:: a] hl; apply => //.
      by move=> y; rewrite smem1 => /String.eqb_eq ->; exists va.
  Qed.


  (** ** The plain rule: [Comp.ccmd] on the locals without the stale variables *)
  Fixpoint noite (e : expr) : bool :=
    match e with
    | expr.ite _ _ _ | expr.inlinetable _ _ _ => false
    | expr.load _ a | expr.op1 _ a => noite a
    | expr.op _ a b => noite a && noite b
    | _ => true
    end.

  Lemma cexpr_noite e : forall n c r n', cexpr name n e = Some (c, r, n') -> noite e.
  Proof.
    elim: e => [z | x | sz a iha | sz t a iha | o a iha | o a iha b ihb | c iha a ihb b ihc] n c' r n' //=.
    - case: sz => //; case hf: (addr_fast a) => [[y k]|].
      + by move: hf; rewrite /addr_fast; case: a {iha} => // -[] // [] // y' [] // k'.
      + by case h: (cexpr name n a) => [[[ca ra] n1]|] // _; apply: iha h.
    - case: o => //; by case h: (cexpr name n a) => [[[ca ra] n1]|] // _; apply: iha h.
    - case ha: (cexpr name n a) => [[[ca ra] n1]|] //; case hb: (cexpr name n1 b) => [[[cb rb] n2]|] // _.
      by rewrite (iha _ _ _ _ ha) (ihb _ _ _ _ hb).
  Qed.

  Lemma eval_evars_in m l e v : noite e -> eval_expr m l e = Some v ->
    forall x, List.In x (evars e) -> exists w, map.get l x = Some w.
  Proof.
    elim: e v => [z | y | sz a iha | sz t a iha | o a iha | o a iha b ihb | c ihc a iha b ihb] v //= hn.
    - by move=> h x [<- | []]; exists v.
    - by case h: (eval_expr m l a) => [va|] // _; apply: iha h.
    - by case h: (eval_expr m l a) => [va|] // _; apply: iha h.
    - move: hn => /andP [hna hnb].
      case ha: (eval_expr m l a) => [va|] //; case hb: (eval_expr m l b) => [vb|] // _ x.
      rewrite List.in_app_iff => -[hx | hx]; [exact: iha _ hna ha x hx | exact: ihb _ hnb hb x hx].
  Qed.

  Lemma eval_evars m l e v : noite e -> eval_expr m l e = Some v ->
    forall x, smem x (evars e) -> exists w, map.get l x = Some w.
  Proof. by move=> hn hv x /smemP; apply: eval_evars_in hn hv x. Qed.

  Fixpoint removes (l : locals) (D : list string) : locals :=
    match D with [::] => l | y :: D => removes (map.remove l y) D end.

  Lemma get_removes l D z : map.get (removes l D) z = if smem z D then None else map.get l z.
  Proof.
    elim: D l => [|y D ih] l; first by [].
    rewrite [removes _ (_ :: _)]/= ih smem_cons.
    rewrite (@coqutil.Map.Properties.map.get_remove_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec).
    rewrite String.eqb_sym; case: (String.eqb z y) => //=; by case: smem.
  Qed.

  Lemma RL_removes D l vm :
    (forall x v, map.get l x = Some v -> ok_name x /\ (~~ smem x D -> get vm (vv x) = Vword (jw v))) ->
    RL name (removes l D) vm.
  Proof.
    move=> hl x v; rewrite get_removes; case hx: (smem x D) => // h.
    have [hok hv] := hl _ _ h; split => //; apply: hv; by rewrite hx.
  Qed.

  Lemma eval_removes m l D e : all (fun x => ~~ smem x D) (evars e) ->
    eval_expr m (removes l D) e = eval_expr m l e.
  Proof.
    move=> h; apply: eval_agree => x hx; rewrite get_removes.
    by have := smem_all _ _ _ hx h => /negbTE ->.
  Qed.

  Definition pspec (AV : avail) (F : option expr) (ss : list stmt) (r : res) : Prop :=
    exists cons, ss = cons ++ r_rest r /\
    forall D Wd m l (s : estate) m' l',
      brun m l cons = Some (m', l') -> RX D Wd F AV l (evm s) -> mem_rel m (emem s) ->
      all (fun x => ~~ smem x D) (r_reads r) ->
      exists s', run s (r_code r) = ok s' /\ [/\
        forall x v, map.get l' x = Some v -> ok_name x /\
          (~~ smem x (r_stale r ++ minus D (r_writes r)) -> get (evm s') (vv x) = Vword (jw v)),
        (if r_fact r is Some ce then exists b, get (evm s') cfv = Vbool b /\ leval l' ce = Some (b2w b) else True),
        (forall x, smem x (r_reads r) -> exists w : u64, get (evm s) (vv x) = Vword w) /\
        (forall x, smem x (r_writes r) -> exists w : u64, get (evm s') (vv x) = Vword w) &
        mem_post m m' s s'].

  Lemma rule_plain_ok AV F ss r : rule_plain name ss = Some r -> pspec AV F ss r.
  Proof.
    rewrite /rule_plain; case: ss => [|[x e|a v] rest] //.
    - case hc: (ccmd name (cmd.set x e)) => [c|] // [<-].
      have hne : noite e.
      { move: hc => /=; case: ifP => // _; case he: (cexpr name 0 e) => [[[ce r0] n']|] // _.
        exact: cexpr_noite he. }
      exists [:: SSet x e]; split => //.
      move=> D Wd m l s m' l' hb [hl hW hF hAV] hm hreads.
      case hv: (eval_expr m l e) => [v|]; last by move: hb; rewrite /= hv.
      move: (hb); rewrite (brun_set _ _ _ _ _ _ hv) => -[? ?]; subst m' l'.
      have hv0 : eval_expr m (removes l D) e = Some v by rewrite eval_removes.
      pose post : @bedrock2.Semantics.trace 64 BW W Mem -> mem -> locals -> Prop :=
        fun t' m' l'' => t' = nil /\ m' = m /\ l'' = map.put (removes l D) x v.
      have hex : exec map.empty (cmd.set x e) nil m (removes l D) post by econstructor; [exact: hv0 | ].
      have [s' [hrun [m2 [l2 [[_ [? ?]] hRL hm2 hscs [hdom hfr]]]]]] :=
        ccmd_correct name name_inj gd map.empty _ _ hc _ _ _ _ hex s (RL_removes D l (evm s) hl) hm.
      subst m2 l2.
      exists s'; split => //; split.
      + move=> z w; rewrite get_put_dec'; case hxz: (String.eqb x z).
        * move/String.eqb_eq: hxz => <- [<-].
          have [hok hvx] := hRL x v (get_put_eq _ _ _); split => // _; exact: hvx.
        * move=> hz; have [hok _] := hl _ _ hz; split => // hD.
          have hzD : ~~ smem z D.
          { have hD' : ~~ smem z ([::] ++ minus D [:: x]) := hD.
            move: hD'; rewrite smem_cat smem_minus negb_or negb_and negbK smem1 => /andP [_].
            by rewrite String.eqb_sym hxz orbF. }
          have := hRL z w; rewrite get_put_dec' hxz get_removes (negbTE hzD) => /(_ hz) [_ ->] //.
      + by [].
      + split.
        * have := reads_def D l (evm s) (evars e) hl; apply => //.
          exact: eval_evars hne hv.
        * move=> z hz; have hz' : smem z [:: x] := hz; move: hz'; rewrite smem1 => /String.eqb_eq ->.
          by have [_ ->] := hRL x v (get_put_eq _ _ _); eexists.
      + by split.
    - case hc: (ccmd name (cmd.store access_size.word a v)) => [c|] // [<-].
      have hne : noite a && noite v.
      { move: hc => /=; case he: (cexpr name 0 v) => [[[cv rv] n1]|] //.
        rewrite (cexpr_noite _ _ _ _ _ he) andbT.
        case hf: (addr_fast a) => [[y k]|].
        - by move=> _; move: hf; rewrite /addr_fast; case: (a) => // -[] // [] // y' [] // k'.
        - by case ha: (cexpr name n1 a) => [[[ca ra] n2]|] // _; exact: cexpr_noite ha. }
      move: hne => /andP [hna hnv].
      exists [:: SStore a v]; split => //.
      move=> D Wd m l s m' l' hb [hl hW hF hAV] hm hreads.
      move: (hreads) => /=; rewrite all_cat => /andP [hra hrv].
      case ha: (eval_expr m l a) => [va|]; last by move: hb; rewrite /= ha.
      case hv: (eval_expr m l v) => [vv'|]; last by move: hb; rewrite /= ha hv.
      case hst: (bedrock2.Memory.store access_size.word m va vv') => [m1|]; last by move: hb; rewrite /= ha hv hst.
      move: (hb); rewrite /= ha hv hst => -[? ?]; subst m' l'.
      have ha0 : eval_expr m (removes l D) a = Some va by rewrite eval_removes.
      have hv0 : eval_expr m (removes l D) v = Some vv' by rewrite eval_removes.
      pose post : @bedrock2.Semantics.trace 64 BW W Mem -> mem -> locals -> Prop :=
        fun t' m' l'' => t' = nil /\ m' = m1 /\ l'' = removes l D.
      have hex : exec map.empty (cmd.store access_size.word a v) nil m (removes l D) post.
      { by econstructor; [exact: ha0 | exact: hv0 | exact: hst |]. }
      have [s' [hrun [m2 [l2 [[_ [? ?]] hRL hm2 hscs [hdom hfr]]]]]] :=
        ccmd_correct name name_inj gd map.empty _ _ hc _ _ _ _ hex s (RL_removes D l (evm s) hl) hm.
      subst m2 l2.
      exists s'; split => //; split.
      + move=> z w hz; have [hok _] := hl _ _ hz; split => // hD.
        have hzD : ~~ smem z D.
        { have hD' : ~~ smem z ([::] ++ minus D [::]) := hD.
          by move: hD'; rewrite smem_cat smem_minus /= andbT. }
        have := hRL z w; rewrite get_removes (negbTE hzD) => /(_ hz) [_ ->] //.
      + by [].
      + split => //.
        have := reads_def D l (evm s) (evars a ++ evars v) hl; apply => //.
        move=> z; rewrite smem_cat => /orP [hz | hz]; [exact: eval_evars hna ha z hz | exact: eval_evars hnv hv z hz].
      + by split.
  Qed.


  (** ** One step of the translation *)
  Lemma rspec_pspec AV F ss r : rspec AV F ss r -> pspec AV F ss r.
  Proof.
    move=> [cons [hss h]]; exists cons; split => // D Wd m l s m' l' hb hrx hm hr.
    by have [s' [hrun [h1 h2 h3 h4 h5]]] := h D Wd m l s m' l' hb hrx hm hr; exists s'; split.
  Qed.

  Lemma rule_plain_av ss r : rule_plain name ss = Some r -> r_av r = false.
  Proof.
    rewrite /rule_plain; case: ss => [|[x e|a v] rest] //.
    - by case: ccmd => // c [<-].
    - by case: ccmd => // c [<-].
  Qed.

  Lemma step_ok AV F ss r : step name cfn AV F ss = Some r ->
    rspec AV F ss r \/ (r_av r = false /\ pspec AV F ss r).
  Proof.
    rewrite /step /first_some /=.
    case h1: rule_acm => [r1|]; first by move=> [<-]; left; exact: rule_acm_ok h1.
    case h2: rule_scm => [r2|]; first by move=> [<-]; left; exact: rule_scm_ok h2.
    case h3: rule_ac => [r3|]; first by move=> [<-]; left; exact: rule_ac_ok h3.
    case h4: rule_sc => [r4|]; first by move=> [<-]; left; exact: rule_sc_ok h4.
    case h5: rule_acx => [r5|]; first by move=> [<-]; left; exact: rule_acx_ok h5.
    case h6: rule_mulx => [r6|]; first by move=> [<-]; left; exact: rule_mulx_ok h6.
    case h7: rule_name => [r7|]; first by move=> [<-]; left; exact: rule_name_ok h7.
    case h8: rule_sel => [r8|]; first by move=> [<-]; left; exact: rule_sel_ok h8.
    case h9: rule_mask => [r9|]; first by move=> [<-]; left; exact: rule_mask_ok h9.
    case h10: rule_sf => [r10|]; first by move=> [<-]; left; exact: rule_sf_ok h10.
    case h11: rule_ac1 => [r11|]; first by move=> [<-]; left; exact: rule_ac1_ok h11.
    case h12: rule_sc1 => [r12|]; first by move=> [<-]; left; exact: rule_sc1_ok h12.
    case h13: rule_a0 => [r13|]; first by move=> [<-]; left; exact: rule_a0_ok h13.
    case h14: rule_s0 => [r14|]; first by move=> [<-]; left; exact: rule_s0_ok h14.
    case h15: rule_plain => [r15|] // [<-]; right; split; [exact: rule_plain_av h15 | exact: rule_plain_ok h15].
  Qed.

  Lemma mem_post_trans m1 m2 m3 (s1 s2 s3 : estate) :
    mem_post m1 m2 s1 s2 -> mem_post m2 m3 s2 s3 -> mem_post m1 m3 s1 s3.
  Proof.
    move=> [h1 h2 h3 h4] [g1 g2 g3 g4]; split => //.
    - by rewrite g2.
    - by move=> k; rewrite g3 h3.
    - move=> p hp; rewrite g4; first exact: h4.
      by move=> a' ha'; rewrite -/(map.get m2 a' = None) h3; apply: hp.
  Qed.


  (** ** Hoisting *)
  Definition AVfresh (AV : avail) (hc : nat) : Prop :=
    forall h e, List.In (h, e) AV -> exists k, h = hname k /\ (k < hc)%coq_nat.

  Lemma hoistable_spec e y k : hoistable e = Some (y, k) ->
    e = expr.op bopname.and (expr.var y) (expr.literal k) /\ ok_name y.
  Proof.
    rewrite /hoistable; case: e => // -[] // [] // y' [] // k'.
    by case: ifP => // hok [<- <-].
  Qed.

  Lemma vv_h_neq j k : j <> k -> vv (hname j) != vv (hname k).
  Proof. by move=> h; apply: vneq => /hname_inj. Qed.

  Lemma hoist_ok Wd D es : forall AV hc c AV' hc' rs F l (s : estate),
    hoist name Wd D AV hc es = (c, AV', hc', rs) ->
    RX D Wd F AV l (evm s) -> AVfresh AV hc ->
    exists vm', [/\ run s c = ok (with_vm s vm'), RX D Wd F AV' l vm', AVfresh AV' hc',
      (forall x, smem x rs -> ok_name x /\ exists w : u64, get (evm s) (vv x) = Vword w) &
      forall x, ok_name x -> get vm' (vv x) = get (evm s) (vv x)].
  Proof.
    elim: es => [|e es ih] AV hc c AV' hc' rs F l s /=.
    { move=> [<- <- <- <-] hrx hf; exists (evm s); split => //; first by rewrite with_vm_id. }
    case hh: (hoistable e) => [[y k]|]; last exact: ih.
    case: ifP => [hc0 | _]; last exact: ih.
    case hrec: (hoist name Wd D ((hname hc, e) :: AV) hc.+1 es) => [[[c1 AV1] hc1] rs1] [<- <- <- <-].
    move=> [hl hW hF hAV] hf.
    have [? hoky] := hoistable_spec e y k hh; subst e.
    move: hc0 => /andP [/andP [hyW hyD] hfind].
    have [vy hy] := hW y hyW.
    have [_ hvy] := hl _ _ hy; have hvy' := hvy hyD.
    set h := hname hc.
    pose vm1 := (evm s).[vv h <- Vword (jw vy)].[vv (tmp 0) <- Vword (wrepr U64 k)]
                  .[vv h <- Vword (wand (jw vy) (wrepr U64 k))].
    have hrun1 : run s (hcode name h y k) = ok (with_vm s vm1).
    { rewrite /hcode run_cons (run_asg_var name gd _ _ _ (jw vy)) // bind_ok run_cons run_asg_cst bind_ok run_cons.
      rewrite (run_asg_op2 name gd _ WAnd h (tmp 0) (jw vy) (wrepr U64 k)) //.
      - by rewrite Vm.setP_neq ?gset_eq //; apply: tmp_h.
      - by rewrite gset_eq. }
    have hfr1 : forall x, ok_name x -> get vm1 (vv x) = get (evm s) (vv x).
    { move=> x hx; rewrite /vm1 Vm.setP_neq; last by apply: h_okn.
      rewrite Vm.setP_neq; last by apply: tmp_okn.
      by rewrite Vm.setP_neq //; apply: h_okn. }
    have hrx1 : RX D Wd F ((h, expr.op bopname.and (expr.var y) (expr.literal k)) :: AV) l vm1.
    { split => //.
      - move=> x v hx; have [hok hv] := hl _ _ hx; split => // hD; rewrite hfr1 //; exact: hv.
      - by case: F hF {hrec} => // ce [b [hb hce]]; exists b; split => //; rewrite /vm1 !gset_vv_cf.
      - move=> h' e' [[<- <-] | hin].
        + split; first by exists hc.
          exists (CW.and vy (CW.of_Z k)); split; first by rewrite /= hy.
          by rewrite /vm1 gset_eq jw_and jw_of_Z.
        + have [hh' [v [hle hv]]] := hAV _ _ hin; split => //; exists v; split => //.
          have [j [hj' hj]] := hf _ _ hin; subst h'.
          rewrite /vm1 Vm.setP_neq; last by apply: vv_h_neq; lia.
          rewrite Vm.setP_neq; last by apply: tmp_h.
          by rewrite Vm.setP_neq; [exact: hv | apply: vv_h_neq; lia]. }
    have hf1 : AVfresh ((h, expr.op bopname.and (expr.var y) (expr.literal k)) :: AV) hc.+1.
    { move=> h' e' [[<- _] | hin]; first by exists hc; split => //; lia.
      have [j [-> hj]] := hf _ _ hin; exists j; split => //; lia. }
    have [vm2 [hrun2 hrx2 hf2 hrs2 hfr2]] := ih _ _ _ _ _ _ F l (with_vm s vm1) hrec hrx1 hf1.
    exists vm2; split => //.
    - have hr : run s (hcode name h y k ++ c1) = ok (with_vm s vm2) by rewrite run_cat hrun1 bind_ok hrun2.
      exact: hr.
    - move=> x; rewrite smem_cons => /orP [/String.eqb_eq -> | hx]; first by split => //; exists (jw vy).
      have [hokx [w hw]] := hrs2 x hx; split => //; exists w; by rewrite -hw /= hfr1.
    - by move=> x hx; rewrite hfr2 //= hfr1.
  Qed.


  (** ** The whole translation *)
  Variable spillp : string -> bool.

  Lemma run_wrap (s s' : estate) reads writes c :
    (forall x, smem x reads -> exists w : u64, get (evm s) (vv x) = Vword w) ->
    run s c = ok s' ->
    (forall x, smem x writes -> exists w : u64, get (evm s') (vv x) = Vword w) ->
    run s (wrap name spillp reads writes c) = ok s'.
  Proof.
    move=> hr hc hw; rewrite /wrap run_cat run_spills; last by move=> x /smemP; apply: hr.
    rewrite bind_ok run_cat hc bind_ok run_spills //.
    by move=> x /smemP; apply: hw.
  Qed.

  Lemma In_filter {A} (p : pred A) x (l : list A) : List.In x [seq y <- l | p y] -> List.In x l /\ p x.
  Proof.
    elim: l => //= y l ih; case: ifP => hp /=.
    - by move=> [<- | /ih [h1 h2]]; split => //; [left | right].
    - by move=> /ih [h1 h2]; split => //; right.
  Qed.

  Lemma no_cyc (b c : seq stmt) y : c <> y :: b ++ c.
  Proof.
    move/(congr1 size) => /= /eqP; rewrite size_cat -addSn -{1}[size c]add0n eqn_add2r //.
  Qed.

  Lemma cat_inj_r (a b c : list stmt) : a ++ c = b ++ c -> a = b.
  Proof.
    elim: a b => [|x a ih] [|y b] //=.
    - by move/no_cyc.
    - by move/esym/no_cyc.
    - by move=> [-> /ih ->].
  Qed.

  Lemma take_cons_rest (a b : list stmt) : take (size (a ++ b) - size b) (a ++ b) = a.
  Proof. by rewrite size_cat addnK take_size_cat. Qed.

  Theorem xchunks_ok fuel : forall F D AV Wd hc ss cs m l (s : estate) m' l',
    xchunks name cfn fuel F D AV Wd hc ss = Some cs ->
    brun m l ss = Some (m', l') -> RX D Wd F AV l (evm s) -> AVfresh AV hc -> mem_rel m (emem s) ->
    exists s', run s (flatten [seq wrap name spillp ch.1.1 ch.1.2 ch.2 | ch <- cs]) = ok s' /\ mem_post m m' s s'.
  Proof.
    elim: fuel => [|fuel ih] F D AV Wd hc ss cs m l s m' l'.
    { case: ss => [|st ss] //= [<-] [? ?] _ _ hm; subst m' l'; exists s; split => //; exact: mem_post_id. }
    case: ss => [|st ss'].
    { move=> /= [<-] [? ?] _ _ hm; subst m' l'; exists s; split => //; exact: mem_post_id. }
    rewrite [xchunks _ _ _ _ _ _ _ _ _]/=.
    case hh: (if F is None then hoist name Wd D AV hc (hcands (st :: ss')) else ([::], AV, hc, [::])) => [[[hcd AV1] hc1] hrs].
    case hs: (step name cfn AV1 F (st :: ss')) => [r|] //.
    case: ifP => // hreads.
    set cons := take _ _.
    case hx: xchunks => [cs'|] // [<-] hb hrx hf hm.
    (* hoisting *)
    have [vm1 [hrun1 hrx1 hf1 hrs1 hfr1]] : exists vm1, [/\ run s hcd = ok (with_vm s vm1), RX D Wd F AV1 l vm1,
        AVfresh AV1 hc1, (forall x, smem x hrs -> exists w : u64, get (evm s) (vv x) = Vword w) &
        forall x, ok_name x -> get vm1 (vv x) = get (evm s) (vv x)].
    { case: F hrx hh hs => [ce|] hrx hh hs.
      - case: hh => <- <- <- <-; exists (evm s); split => //; by rewrite with_vm_id.
      - have [vm1 [? ? ? hr ?]] := hoist_ok Wd D _ AV hc hcd AV1 hc1 hrs None l s hh hrx hf.
        exists vm1; split => // z hz; by have [_ ?] := hr z hz. }
    have hst := step_ok AV1 F (st :: ss') r hs.
    have hpsp : pspec AV1 F (st :: ss') r by case: hst => [h | [_ h]] //; exact: rspec_pspec.
    case: (hpsp) => cons0 [hss hcore].
    have hcons : cons = cons0 by have := take_cons_rest cons0 (r_rest r); rewrite -hss.
    move: (hb); rewrite hss brun_app; case hb1: (brun m l cons0) => [[m1 l1]|] // hb2.
    have hm1 : mem_rel m (emem (with_vm s vm1)) by [].
    have [s2 [hrun2 [g1 g2 g3 g5]]] := hcore D Wd m l (with_vm s vm1) m1 l1 hb1 hrx1 hm1 hreads.
    case: g3 => g3r g3w.
    pose AV2 := if r_av r then [seq p <- AV1 | all (fun x => ~~ smem x (flatten (map ssets cons))) (evars p.2)] else [::].
    have hrx2 : RX (r_stale r ++ minus D (r_writes r)) (flatten (map ssets cons) ++ Wd) (r_fact r) AV2 l1 (evm s2).
    { case: (hrx1) => hl1 hW1 hF1 hAV1; split => //.
      - move=> x; rewrite smem_cat hcons => /orP [hx1 | hx1]; first exact: brun_sets hb1 x hx1.
        have [v hv] := hW1 x hx1; exact: brun_def hb1 x v hv.
      - rewrite /AV2; case hav: (r_av r) => // h e hin0; have [hin hall] := In_filter _ _ _ hin0.
        case: hst => [[cons1 [hss1 hcore1]] | [hav' _]]; last by rewrite hav in hav'.
        have hcc : cons1 = cons0 by apply: (cat_inj_r _ _ (r_rest r)); rewrite -hss1; exact: hss.
        subst cons1.
        have [s2' [hrun2' [_ _ hhol _ _]]] := hcore1 D Wd m l (with_vm s vm1) m1 l1 hb1 hrx1 hm1 hreads.
        have es2 : s2' = s2 by move: hrun2'; rewrite hrun2 => -[].
        subst s2'.
        have [hish [v [hle hv]]] := hAV1 _ _ hin.
        split => //; exists v; split.
        + rewrite (leval_agree l) // => x hx2; apply: (brun_keep m l cons0 m1 l1 hb1).
          by have := smem_all _ _ _ hx2 hall; rewrite hcons.
        + by case: (hish) => k hk; subst h; rewrite hhol; exact: hv. }
    have hf2 : AVfresh AV2 hc1.
    { rewrite /AV2; case: (r_av r) => // h e hin0; have [hin _] := In_filter _ _ _ hin0; exact: hf1 _ _ hin. }
    have [s3 [hrun3 hmp3]] := ih _ _ _ _ _ _ _ m1 l1 s2 m' l' hx hb2 hrx2 hf2 (match g5 with And4 h _ _ _ => h end).
    exists s3; split.
    - have hr : run s (wrap name spillp hrs [::] hcd ++ (wrap name spillp (r_reads r) (r_writes r) (r_code r)
                  ++ flatten [seq wrap name spillp ch.1.1 ch.1.2 ch.2 | ch <- cs'])) = ok s3.
      { rewrite run_cat (run_wrap s (with_vm s vm1) hrs [::] hcd hrs1 hrun1) // bind_ok.
        by rewrite run_cat (run_wrap _ s2 _ _ _ g3r hrun2 g3w) bind_ok hrun3. }
      exact: hr.
    - apply: (mem_post_trans _ m _ _ (with_vm s vm1)); first exact: mem_post_refl.
      exact: mem_post_trans g5 hmp3.
  Qed.


  (** The simulation theorem of the optimising translation: when bedrock2 runs [c] from
      [(m, l)] to [post], the translated Jasmin code runs from any related state to a state
      whose memory is related to a final bedrock2 memory satisfying [post]; no Jasmin byte
      outside the bedrock2 domain changes. *)
  Theorem xcmd_correct (fenv : @map.rep _ _ bedrock2.Semantics.env) c ps jc :
    xcmd name cfn spillp ps c = Some jc ->
    forall t m l post, exec fenv c t m l post ->
    forall s, RL name l (evm s) -> (forall p, List.In p ps -> exists v, map.get l p = Some v) ->
    mem_rel m (emem s) ->
    exists s', run s jc = ok s' /\ exists m' l', post t m' l' /\ mem_post m m' s s'.
  Proof.
    rewrite /xcmd /xchunks_of; case hf: (flat c) => [ss|] //; case hxc: xchunks => [cs|] // [<-].
    move=> t m l post hex s hRL hps hm.
    have [m' [l' [hb hpost]]] := exec_flat fenv c ss hf t m l post hex.
    have hrx : RX [::] ps None [::] l (evm s).
    { split => //.
      - by move=> x v hx; have [hok hv] := hRL x v hx; split => // _; exact: hv.
      - by move=> x /smemP; exact: hps. }
    have [s' [hrun hmp]] := xchunks_ok _ _ _ _ _ _ _ _ m l s m' l' hxc hb hrx (fun h e (hin : List.In _ [::]) => match hin with end) hm.
    by exists s'; split => //; exists m', l'.
  Qed.

End S.
