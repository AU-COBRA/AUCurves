(** * The bedrock2 -> Jasmin translation of straight-line code, and its simulation theorem. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String Ascii.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.
Import bedrock2.Syntax.

(** ** Names *)
Fixpoint ts (n : nat) : string := match n with O => EmptyString | S n => String "t"%char (ts n) end.
Definition tmp (n : nat) : string := String "$"%char (ts n).

Definition ok_name (x : string) : bool :=
  match x with String c _ => negb (Ascii.eqb c "$"%char) | EmptyString => true end.

Lemma ts_inj n m : ts n = ts m -> n = m.
Proof.
  elim: n m => [|n ih] [|m] //= h; try discriminate.
  by case: h => /ih ->.
Qed.

Lemma tmp_inj {n m} : tmp n = tmp m -> n = m.
Proof. by move=> [] /ts_inj. Qed.

Lemma ok_name_tmp {x n} : ok_name x -> x <> tmp n.
Proof. by move=> h e; subst x. Qed.

(** ** The translation *)
Section C.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance withsubword.
  Variable name : string -> Ident.ident.

  Local Notation vv := (vv name).
  Local Notation pv := (pv name).
  Local Notation asg := (asg name).

  Definition small_off (k : Z) : bool := (0 <=? k) && (k <? 2 ^ 31).

  Definition wop_of (o : bopname) : option wop :=
    match o with
    | bopname.add => Some WAdd | bopname.sub => Some WSub | bopname.mul => Some WMul
    | bopname.and => Some WAnd | bopname.or => Some WOr | bopname.xor => Some WXor
    | _ => None
    end.

  Definition addr_fast (a : expr) : option (string * Z) :=
    match a with
    | expr.op bopname.add (expr.var b) (expr.literal k) =>
        if ok_name b && small_off k then Some (b, k) else None
    | _ => None
    end.

  (** [cexpr n e]: code computing [e], the variable holding the result, and the next free
      temporary.  It writes temporaries [tmp k], [n <= k < n'] only. *)
  Fixpoint cexpr (n : nat) (e : expr) : option (jcmd * string * nat) :=
    match e with
    | expr.var x => if ok_name x then Some ([::], x, n) else None
    | expr.literal v => Some ([:: asg (tmp n) (cst v)], tmp n, S n)
    | expr.load access_size.word a =>
        match addr_fast a with
        | Some (b, k) => Some ([:: asg (tmp n) (Pload Unaligned U64 (addr name b k))], tmp n, S n)
        | None =>
            match cexpr n a with
            | Some (ca, ra, n1) =>
                Some (ca ++ [:: asg (tmp n1) (Pload Unaligned U64 (pv ra))], tmp n1, S n1)
            | None => None
            end
        end
    | expr.op1 op1.opp a =>
        match cexpr n a with
        | Some (ca, ra, n1) =>
            Some (ca ++ [:: asg (tmp n1) (cst 0);
                           asg (tmp n1) (Papp2 (wop_sop2 WSub) (pv (tmp n1)) (pv ra))],
                  tmp n1, S n1)
        | None => None
        end
    | expr.op o a b =>
        match cexpr n a with
        | Some (ca, ra, n1) =>
          match cexpr n1 b with
          | Some (cb, rb, n2) =>
            let t := tmp n2 in
            match wop_of o with
            | Some w =>
                Some (ca ++ cb ++ [:: asg t (pv ra); asg t (Papp2 (wop_sop2 w) (pv t) (pv rb))],
                      t, S n2)
            | None =>
              match o with
              | bopname.ltu =>
                Some (ca ++ cb ++ [:: asg t (cst 0); asg (tmp (S n2)) (cst 1);
                       asg t (Pif (aword U64) (Papp2 (wcmp_sop2 CLtu) (pv ra) (pv rb))
                                  (pv (tmp (S n2))) (pv t))], t, S (S n2))
              | bopname.eq =>
                Some (ca ++ cb ++ [:: asg t (cst 0); asg (tmp (S n2)) (cst 1);
                       asg t (Pif (aword U64) (Papp2 (wcmp_sop2 CEq) (pv ra) (pv rb))
                                  (pv (tmp (S n2))) (pv t))], t, S (S n2))
              | bopname.mulhuu =>
                Some (ca ++ cb ++ [:: asg (tmp (S (S n2))) (pv ra);
                                      mulx name (tmp (S n2)) t (tmp (S (S n2))) rb],
                      t, S (S (S n2)))
              | _ => None
              end
            end
          | None => None
          end
        | None => None
        end
    | _ => None
    end.

  Fixpoint ccmd (c : cmd) : option jcmd :=
    match c with
    | cmd.skip => Some [::]
    | cmd.unset _ => Some [::]
    | cmd.seq a b =>
        match ccmd a, ccmd b with Some ca, Some cb => Some (ca ++ cb) | _, _ => None end
    | cmd.set x e =>
        if ok_name x then
          match cexpr 0 e with Some (ce, r, _) => Some (ce ++ [:: asg x (pv r)]) | None => None end
        else None
    | cmd.store access_size.word a v =>
        match cexpr 0 v with
        | Some (cv, rv, n1) =>
            match addr_fast a with
            | Some (b, k) => Some (cv ++ [:: store name b k rv])
            | None =>
                match cexpr n1 a with
                | Some (ca, ra, _) => Some (cv ++ ca ++ [:: storev name ra rv])
                | None => None
                end
            end
        | None => None
        end
    | _ => None
    end.

  (** ** Spill hints
      [spillp x]: keep the source variable [x] in a stack slot between statements: unspill
      it before each statement that reads it, spill it after each statement that writes it
      (the parameters on entry).  Any choice is correct (spills are no-ops in the source
      semantics); it only decides the register pressure seen by the register allocator. *)
  Variable spillp : string -> bool.

  Fixpoint vars_e (e : expr) : list string :=
    match e with
    | expr.var x => [:: x]
    | expr.load _ a | expr.op1 _ a => vars_e a
    | expr.op _ a b => vars_e a ++ vars_e b
    | expr.inlinetable _ _ a => vars_e a
    | expr.ite _ _ _ => [::]  (* not translated *)
    | expr.literal _ => [::]
    end.

  Fixpoint spills (o : pseudo_operator.spill_op) (xs : list string) : jcmd :=
    match xs with
    | [::] => [::]
    | x :: xs => if spillp x then spill1 name o x :: spills o xs else spills o xs
    end.

  Fixpoint ccmd_sp (c : cmd) : option jcmd :=
    match c with
    | cmd.seq a b =>
        match ccmd_sp a, ccmd_sp b with Some ca, Some cb => Some (ca ++ cb) | _, _ => None end
    | cmd.set x e =>
        match ccmd (cmd.set x e) with
        | Some ce => Some (spills pseudo_operator.Unspill (vars_e e) ++ ce ++ spills pseudo_operator.Spill [:: x])
        | None => None
        end
    | cmd.store sz a v =>
        match ccmd (cmd.store sz a v) with
        | Some cs => Some (spills pseudo_operator.Unspill (vars_e a ++ vars_e v) ++ cs)
        | None => None
        end
    | _ => ccmd c
    end.

  Lemma ccmd_sp_some c : isSome (ccmd c) -> isSome (ccmd_sp c).
  Proof.
    elim: c => // [x e | sz a v | c1 ih1 c2 ih2]; cbn [ccmd_sp].
    - by case: (ccmd (cmd.set x e)).
    - by case: (ccmd (cmd.store sz a v)).
    - cbn [ccmd]; case: (ccmd c1) ih1 => // ca /(_ isT); case: (ccmd_sp c1) => // ca' _.
      by case: (ccmd c2) ih2 => // cb /(_ isT); case: (ccmd_sp c2).
  Qed.
End C.
