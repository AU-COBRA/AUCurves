(** * Carry chains, MULX pairs and spill hints: the optimising bedrock2 -> Jasmin translation.

    The bedrock2 bodies of fiat-crypto's leaves compute carries as words: [s = c + a],
    [c1 = s <u a], [r = s + b], [c2 = r <u b], [co = c1 + c2] (addcarryx), and the same with
    subtraction (subborrowx).  [xtr] translates such windows to Jasmin's [Oaddcarry] /
    [Osubcarry] with the carry in a boolean variable [cfv] (the x86 carry flag after
    register allocation), pairs [x = a * b; y = mulhuu a b] into one [MULX], and translates
    every other statement as [Comp.ccmd] does.

    State of the translation: a fact [F] (a bedrock2 expression whose value is the carry
    held by [cfv]) and a list [D] of stale source variables (intermediates of the windows,
    which the Jasmin code never computes).  A window makes a variable stale only when the
    rest of the body reads it at most inside the new fact; a statement whose Jasmin code would
    read a stale variable makes the whole translation fail, and the leaf then falls back to
    [Comp.ccmd_sp] ([leaf_code2]).  Shapes the rules do not recognise are translated by
    [Comp.ccmd] one statement at a time. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String Ascii.
Require bedrock2.Syntax.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.
Import bedrock2.Syntax.

(** ** Straight-line statements *)
Inductive stmt := SSet (x : string) (e : expr) | SStore (a v : expr).

Fixpoint flat (c : cmd) : option (list stmt) :=
  match c with
  | cmd.skip => Some [::]
  | cmd.set x e => Some [:: SSet x e]
  | cmd.store access_size.word a v => Some [:: SStore a v]
  | cmd.seq a b =>
      match flat a, flat b with Some sa, Some sb => Some (sa ++ sb) | _, _ => None end
  | _ => None
  end.

(** ** Syntactic equality of expressions *)
Definition bop_eqb (a b : bopname) : bool :=
  match a, b with
  | bopname.add, bopname.add | bopname.sub, bopname.sub | bopname.mul, bopname.mul
  | bopname.mulhuu, bopname.mulhuu | bopname.divu, bopname.divu | bopname.remu, bopname.remu
  | bopname.and, bopname.and | bopname.or, bopname.or | bopname.xor, bopname.xor
  | bopname.sru, bopname.sru | bopname.slu, bopname.slu | bopname.srs, bopname.srs
  | bopname.lts, bopname.lts | bopname.ltu, bopname.ltu | bopname.eq, bopname.eq => true
  | _, _ => false
  end.

Lemma bop_eqbP a b : bop_eqb a b -> a = b.
Proof. by case: a; case: b. Qed.

(** Only the fragment the facts use is compared; anything else is unequal. *)
Fixpoint eeqb (a b : expr) : bool :=
  match a, b with
  | expr.literal x, expr.literal y => Z.eqb x y
  | expr.var x, expr.var y => String.eqb x y
  | expr.op o a1 a2, expr.op o' b1 b2 => bop_eqb o o' && eeqb a1 b1 && eeqb a2 b2
  | expr.op1 op1.opp a1, expr.op1 op1.opp b1 => eeqb a1 b1
  | _, _ => false
  end.

Lemma eeqbP a b : eeqb a b -> a = b.
Proof.
  elim: a b => [x | x | sz a iha | sz t a iha | o1 a iha | o a1 ih1 a2 ih2 | c ihc a1 ih1 a2 ih2]
    [y | y | sz' b | sz' t' b | o1' b | o' b1 b2 | c' b1 b2] //=.
  all: try (by move=> /Z.eqb_eq ->).
  all: try (by move=> /String.eqb_eq ->).
  all: try (by case: o1 => //; case: o1' => // /iha ->).
  all: try (by case: o1).
  move=> h; have [h12 h3] := andb_prop _ _ h; have [h1 h2] := andb_prop _ _ h12.
  by rewrite (bop_eqbP _ _ h1) (ih1 _ h2) (ih2 _ h3).
Qed.

Definition oeqb (F : option expr) (e : expr) : bool :=
  if F is Some ce then eeqb ce e else false.

(** Variables read, skipping the subterms equal to [ce]. *)
Fixpoint vars_ex (ce : expr) (e : expr) : list string :=
  if eeqb ce e then [::] else
  match e with
  | expr.var x => [:: x]
  | expr.load _ a | expr.op1 _ a | expr.inlinetable _ _ a => vars_ex ce a
  | expr.op _ a b => vars_ex ce a ++ vars_ex ce b
  | expr.ite c a b => vars_ex ce c ++ vars_ex ce a ++ vars_ex ce b
  | expr.literal _ => [::]
  end.

Fixpoint evars (e : expr) : list string :=
  match e with
  | expr.var x => [:: x]
  | expr.load _ a | expr.op1 _ a | expr.inlinetable _ _ a => evars a
  | expr.op _ a b => evars a ++ evars b
  | expr.ite c a b => evars c ++ evars a ++ evars b
  | expr.literal _ => [::]
  end.

Definition svars_ex (ce : expr) (s : stmt) : list string :=
  match s with
  | SSet _ e => vars_ex ce e
  | SStore a v => vars_ex ce a ++ vars_ex ce v
  end.

Definition svars (s : stmt) : list string :=
  match s with
  | SSet _ e => evars e
  | SStore a v => evars a ++ evars v
  end.

Definition smem (x : string) (l : list string) : bool := has (String.eqb x) l.

(** [x] may become stale before [rest] when [rest] reads it only inside [ce]. *)
Definition stale_ok (x : string) (ce : expr) (rest : list stmt) : bool :=
  all (fun s => ~~ smem x (svars_ex ce s)) rest.

(** A carry variable may become stale when only the next statement reads it. *)
Definition stale_ok_var (x : string) (rest : list stmt) : bool :=
  match rest with
  | [::] => true
  | _ :: rest' => all (fun s => ~~ smem x (svars s)) rest'
  end.

(** ** Jasmin instructions with the carry variable *)
Section C.
  Context {atoI : arch_toIdent}.
  #[local] Existing Instance x86_extra.
  Variable name : string -> Ident.ident.
  (** The identifier of the boolean carry variable (supplied by the driver). *)
  Variable cfn : Ident.ident.

  Local Notation vv := (vv name).
  Local Notation pv := (pv name).
  Local Notation lv := (lv name).
  Local Notation asg := (asg name).

  Definition cfv : var := {| vtype := abool; vname := cfn |}.
  Definition cfi : var_i := {| v_var := cfv; v_info := dummy_var_info |}.
  Definition pcf : pexpr := Plvar cfi.

  (** [(cfv, r) := r +/- b +/- cin]: [ADD]/[ADC]/[SUB]/[SBB] after lowering. *)
  Definition carryop (sub : bool) (r b : string) (cin : pexpr) : instr :=
    I (Copn [:: Lvar cfi; lv r] AT_none
         (if sub then sopn_subcarry U64 else sopn_addcarry U64) [:: pv r; pv b; cin]).

  (** [r := r - r - cfv] with the carry-out dropped ([SBB r, r]). *)
  Definition sbbself (r : string) : instr :=
    I (Copn [:: Lnone dummy_var_info abool; lv r] AT_none (sopn_subcarry U64) [:: pv r; pv r; pcf]).

  (** [x := cfv ? 1 : 0] without touching the flags ([MOV]s and [CMOV]). *)
  Definition matcf (x : string) : jcmd :=
    [:: asg x (cst 0); asg (tmp 1) (cst 1);
        asg x (Pif (aword U64) pcf (pv (tmp 1)) (pv x))].

  (** An operand: a variable, or a literal loaded into a temporary. *)
  (** Available expressions: [(h, e)] when the Jasmin variable [h] (a holder, see [hname])
      holds the value of the load-free expression [e]. *)
  Definition avail := list (string * expr).

  Fixpoint av_find (AV : avail) (e : expr) : option string :=
    match AV with
    | [::] => None
    | (h, e') :: AV => if eeqb e' e then Some h else av_find AV e
    end.

  Definition opnd (AV : avail) (k : nat) (e : expr) : option (jcmd * string) :=
    match e with
    | expr.var y => if ok_name y then Some ([::], y) else None
    | expr.literal z => Some ([:: asg (tmp k) (cst z)], tmp k)
    | _ => if av_find AV e is Some h then Some ([::], h) else None
    end.

  Definition opnd_vars (e : expr) : list string :=
    match e with expr.var y => [:: y] | _ => [::] end.

  (** ** Spill hints (any choice is correct) *)
  Variable spillp : string -> bool.

  Definition wrap (reads writes : list string) (c : jcmd) : jcmd :=
    spills name spillp pseudo_operator.Unspill reads ++ c ++ spills name spillp pseudo_operator.Spill writes.

  (** ** The rules
      A rule consumes some statements and returns: the code, the new fact, the variables it
      makes stale, the variables its code reads and those it writes. *)
  Record res := mkres' { r_code : jcmd; r_fact : option expr; r_stale : list string;
                         r_reads : list string; r_writes : list string; r_rest : list stmt;
                         r_av : bool (* keeps the available expressions *) }.
  Definition mkres c f st rd wr rest := mkres' c f st rd wr rest true.

  Definition okv (x : string) : bool := ok_name x.
  Definition dist (xs : list string) : bool := uniq [seq (x : string) | x <- xs].

  Definition V := expr.var.
  Definition LTU a b := expr.op bopname.ltu a b.
  Definition ADD a b := expr.op bopname.add a b.
  Definition SUB a b := expr.op bopname.sub a b.

  (** Window rules.  [F] is the current fact. *)
  Definition rule_acm (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet s (expr.op bopname.add ce (expr.var a)) ::
      SSet c1 (expr.op bopname.ltu (expr.var s1) (expr.var a1)) ::
      SSet r (expr.op bopname.add (expr.var s2) b) ::
      SSet c2 (expr.op bopname.ltu (expr.var r1) b1) ::
      SSet co (expr.op bopname.add (expr.var c1') (expr.var c2')) :: rest =>
      if oeqb F ce && String.eqb s1 s && String.eqb a1 a && String.eqb s2 s && eeqb b1 b
         && String.eqb r1 r && String.eqb c1' c1 && String.eqb c2' c2
         && all okv [:: s; a; c1; r; c2; co] && dist [:: s; c1; r; c2; co]
         && ~~ smem s (evars ce) && ~~ smem a [:: s; c1; r; c2; co]
         && all (fun y => ~~ smem y [:: s; c1; r; c2; co]) (evars b)
         && stale_ok s (expr.literal 0) rest && stale_ok c1 (expr.literal 0) rest
         && stale_ok c2 (expr.literal 0) rest
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               let c := cb ++ [:: asg r (pv a); carryop false r rb pcf] in
               Some (if stale_ok_var co rest
                     then mkres c (Some (V co)) [:: s; c1; c2; co] (a :: opnd_vars b) [:: r] rest
                     else mkres (c ++ matcf co) (Some (V co)) [:: s; c1; c2] (a :: opnd_vars b) [:: r; co] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  Definition rule_scm (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet s (expr.op bopname.sub (expr.var a) b) ::
      SSet c1 (expr.op bopname.ltu (expr.var a1) (expr.var s1)) ::
      SSet r (expr.op bopname.sub (expr.var s2) ce) ::
      SSet c2 (expr.op bopname.ltu (expr.var s3) (expr.var r1)) ::
      SSet co (expr.op bopname.add (expr.var c1') (expr.var c2')) :: rest =>
      if oeqb F ce && String.eqb s1 s && String.eqb a1 a && String.eqb s2 s && String.eqb s3 s
         && String.eqb r1 r && String.eqb c1' c1 && String.eqb c2' c2
         && all okv [:: s; a; c1; r; c2; co] && dist [:: s; c1; r; c2; co]
         && ~~ smem s (evars ce) && ~~ smem c1 (evars ce) && ~~ smem a [:: s; c1; r; c2; co]
         && all (fun y => ~~ smem y [:: s; c1; r; c2; co]) (evars b)
         && stale_ok s (expr.literal 0) rest && stale_ok c1 (expr.literal 0) rest
         && stale_ok c2 (expr.literal 0) rest
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               let c := cb ++ [:: asg r (pv a); carryop true r rb pcf] in
               Some (if stale_ok_var co rest
                     then mkres c (Some (V co)) [:: s; c1; c2; co] (a :: opnd_vars b) [:: r] rest
                     else mkres (c ++ matcf co) (Some (V co)) [:: s; c1; c2] (a :: opnd_vars b) [:: r; co] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** [s = ce + a; r = s + b]: fact [s <u a + r <u b]. *)
  Definition rule_ac (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet s (expr.op bopname.add ce (expr.var a)) ::
      SSet r (expr.op bopname.add (expr.var s1) b) :: rest =>
      let nf := ADD (LTU (V s) (V a)) (LTU (V r) b) in
      if oeqb F ce && String.eqb s1 s && all okv [:: s; a; r] && dist [:: s; r; a]
         && all (fun y => ~~ smem y [:: s; r]) (evars b)
         && stale_ok s nf rest
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg r (pv a); carryop false r rb pcf])
                       (Some nf) [:: s] (a :: opnd_vars b) [:: r] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** [s = a - b; r = s - ce]: fact [a <u s + s <u r]. *)
  Definition rule_sc (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet s (expr.op bopname.sub (expr.var a) b) ::
      SSet r (expr.op bopname.sub (expr.var s1) ce) :: rest =>
      let nf := ADD (LTU (V a) (V s)) (LTU (V s) (V r)) in
      if oeqb F ce && String.eqb s1 s && all okv [:: s; a; r] && dist [:: s; r; a]
         && ~~ smem s (evars ce)
         && all (fun y => ~~ smem y [:: s; r]) (evars b)
         && stale_ok s nf rest
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg r (pv a); carryop true r rb pcf])
                       (Some nf) [:: s] (a :: opnd_vars b) [:: r] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** [x = a * b; y = mulhuu a b]: one MULX ([b] a variable or a literal). *)
  Definition rule_mulx (AV : avail) (ss : list stmt) : option res :=
    match ss with
    | SSet x (expr.op bopname.mul (expr.var a) b) ::
      SSet y (expr.op bopname.mulhuu (expr.var a') b') :: rest =>
      if String.eqb a' a && eeqb b' b && all okv [:: x; y; a] && ~~ String.eqb x y
         && ~~ smem x (a :: evars b)
      then match opnd AV 1 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg (tmp 0) (pv a); mulx name x y (tmp 0) rb]) None [::]
                       (a :: opnd_vars b) [:: x; y] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** fiat's select [m = -1 + (ce == 0); n = m ^ (2^64-1); r = (a & m) | (b & n)], that is
      [r = ce ? a : b], as [r := b; r := cfv ? a : r] ([CMOV]); the fact stays. *)
  Definition rule_sel (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet m (expr.op bopname.add (expr.op1 op1.opp (expr.literal 1))
               (expr.op bopname.eq ce (expr.literal 0))) ::
      SSet n (expr.op bopname.xor (expr.var m1) (expr.literal k)) ::
      SSet r (expr.op bopname.or (expr.op bopname.and (expr.var a) (expr.var m2))
                                 (expr.op bopname.and (expr.var b) (expr.var n1))) :: rest =>
      if oeqb F ce && String.eqb m1 m && String.eqb m2 m && String.eqb n1 n
         && Z.eqb k (2 ^ 64 - 1) && all okv [:: m; n; r; a; b] && dist [:: m; n; r]
         && ~~ smem a [:: m; n; r] && ~~ smem b [:: m; n]
         && all (fun y => ~~ smem y [:: m; n; r]) (evars ce)
         && stale_ok m (expr.literal 0) rest && stale_ok n (expr.literal 0) rest
      then Some (mkres [:: asg r (pv b); asg r (Pif (aword U64) pcf (pv a) (pv r))] F [:: m; n]
                       [:: a; b] [:: r] rest)
      else None
    | _ => None
    end.

  (** [r = a + b] / [r = a - b] with the carry kept. *)
  Definition rule_a0 (AV : avail) (ss : list stmt) : option res :=
    match ss with
    | SSet r (expr.op bopname.add (expr.var a) b) :: rest =>
      if all okv [:: r; a] && ~~ String.eqb r a && all (fun y => ~~ String.eqb y r) (evars b)
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg r (pv a); carryop false r rb (Pbool false)])
                       (Some (LTU (V r) (V a))) [::] (a :: opnd_vars b) [:: r] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  Definition rule_s0 (AV : avail) (ss : list stmt) : option res :=
    match ss with
    | SSet r (expr.op bopname.sub (expr.var a) b) :: rest =>
      if all okv [:: r; a] && ~~ String.eqb r a && all (fun y => ~~ String.eqb y r) (evars b)
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg r (pv a); carryop true r rb (Pbool false)])
                       (Some (LTU (V a) (V r))) [::] (a :: opnd_vars b) [:: r] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** [r = ce + a] / [r = a - ce] (end of a chain). *)
  Definition rule_ac1 (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet r (expr.op bopname.add ce (expr.var a)) :: rest =>
      if oeqb F ce && all okv [:: r; a] && ~~ String.eqb r a
      then Some (mkres [:: asg (tmp 0) (cst 0); asg r (pv a); carryop false r (tmp 0) pcf]
                       (Some (LTU (V r) (V a))) [::] [:: a] [:: r] rest)
      else None
    | _ => None
    end.

  Definition rule_sc1 (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet r (expr.op bopname.sub (expr.var a) ce) :: rest =>
      if oeqb F ce && all okv [:: r; a] && ~~ String.eqb r a
      then Some (mkres [:: asg (tmp 0) (cst 0); asg r (pv a); carryop true r (tmp 0) pcf]
                       (Some (LTU (V a) (V r))) [::] [:: a] [:: r] rest)
      else None
    | _ => None
    end.

  (** [r = (ce + a) + b] (last limb, carry-out dropped). *)
  Definition rule_acx (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet r (expr.op bopname.add (expr.op bopname.add ce (expr.var a)) b) :: rest =>
      if oeqb F ce && all okv [:: r; a] && ~~ String.eqb r a
         && all (fun y => ~~ String.eqb y r) (evars b)
      then match opnd AV 0 b with
           | Some (cb, rb) =>
               Some (mkres (cb ++ [:: asg r (pv a); carryop false r rb pcf])
                       None [::] (a :: opnd_vars b) [:: r] rest)
           | None => None
           end
      else None
    | _ => None
    end.

  (** [c = ce]: name the carry (stale [c]) or materialise it. *)
  Definition rule_name (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet c ce :: rest =>
      if oeqb F ce && okv c then
        if stale_ok_var c rest then Some (mkres [::] (Some (V c)) [:: c] [::] [::] rest)
        else Some (mkres (matcf c) (Some (V c)) [::] [::] [:: c] rest)
      else None
    | _ => None
    end.

  (** [x = -1 + (ce == 0)] = [- ce]: [SBB x, x]. *)
  Definition rule_mask (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet x (expr.op bopname.add (expr.op1 op1.opp (expr.literal 1))
               (expr.op bopname.eq ce (expr.literal 0))) :: rest =>
      if oeqb F ce && okv x
      then Some (mkres [:: asg x (cst 0); sbbself x] None [::] [::] [:: x] rest)
      else None
    | _ => None
    end.

  (** [x = a <u (a - ce)] (the borrow of [a - ce]). *)
  Definition rule_sf (F : option expr) (ss : list stmt) : option res :=
    match ss with
    | SSet x (expr.op bopname.ltu (expr.var a) (expr.op bopname.sub (expr.var a') ce)) :: rest =>
      if oeqb F ce && String.eqb a' a && all okv [:: x; a]
      then Some (mkres ([:: asg (tmp 0) (cst 0); asg (tmp 2) (pv a); carryop true (tmp 2) (tmp 0) pcf]
                        ++ matcf x)
                       (Some (V x)) [::] [:: a] [:: x] rest)
      else None
    | _ => None
    end.

  (** Any other statement, as [Comp.ccmd]. *)
  Definition rule_plain (ss : list stmt) : option res :=
    match ss with
    | SSet x e :: rest =>
        match ccmd name (cmd.set x e) with
        | Some c => Some (mkres' c None [::] (evars e) [:: x] rest false)
        | None => None
        end
    | SStore a v :: rest =>
        match ccmd name (cmd.store access_size.word a v) with
        | Some c => Some (mkres' c None [::] (evars a ++ evars v) [::] rest false)
        | None => None
        end
    | [::] => None
    end.

  Definition first_some (rs : list (option res)) : option res :=
    foldr (fun r acc => if r is Some _ then r else acc) None rs.

  Definition step (AV : avail) (F : option expr) (ss : list stmt) : option res :=
    first_some [:: rule_acm AV F ss; rule_scm AV F ss; rule_ac AV F ss; rule_sc AV F ss;
                   rule_acx AV F ss; rule_mulx AV ss;
                   rule_name F ss; rule_sel F ss; rule_mask F ss; rule_sf F ss; rule_ac1 F ss; rule_sc1 F ss;
                   rule_a0 AV ss; rule_s0 AV ss; rule_plain ss].

  Definition minus (D xs : list string) : list string := [seq x <- D | ~~ smem x xs].

  (** ** Hoisting masked operands into available expressions
      When no carry is live, the operands [y & k] of the additions in the next statements are
      computed into holders ([hname]), so that the windows can use them as operands. *)
  Definition hname (k : nat) : string := String "$" (String "a" (ts k)).

  Definition hcands (ss : list stmt) : list expr :=
    flatten [seq match st with
                 | SSet _ (expr.op bopname.add (expr.var _) e) => [:: e]
                 | SSet _ (expr.op bopname.add (expr.op bopname.add _ (expr.var _)) e) => [:: e]
                 | _ => [::]
                 end | st <- take 12 ss].

  Definition hoistable (e : expr) : option (string * Z) :=
    match e with
    | expr.op bopname.and (expr.var y) (expr.literal k) => if ok_name y then Some (y, k) else None
    | _ => None
    end.

  Definition hcode (h y : string) (k : Z) : jcmd :=
    [:: asg h (pv y); asg (tmp 0) (cst k); asg h (Papp2 (wop_sop2 WAnd) (pv h) (pv (tmp 0)))].

  Fixpoint hoist (W D : list string) (AV : avail) (hc : nat) (es : list expr)
      : jcmd * avail * nat * list string :=
    match es with
    | [::] => ([::], AV, hc, [::])
    | e :: es =>
        match hoistable e with
        | Some (y, k) =>
            if smem y W && ~~ smem y D && (if av_find AV e is None then true else false) then
              let '(c, AV', hc', rs) := hoist W D ((hname hc, e) :: AV) hc.+1 es in
              (hcode (hname hc) y k ++ c, AV', hc', y :: rs)
            else hoist W D AV hc es
        | None => hoist W D AV hc es
        end
    end.

  Definition ssets (st : stmt) : list string :=
    match st with SSet x _ => [:: x] | SStore _ _ => [::] end.

  (** A chunk: the variables its code reads and writes (for the spill hints) and its code. *)
  Definition chunk := (list string * list string * jcmd)%type.

  Fixpoint xchunks (fuel : nat) (F : option expr) (D : list string) (AV : avail)
      (W : list string) (hc : nat) (ss : list stmt) : option (list chunk) :=
    match ss with
    | [::] => Some [::]
    | _ =>
      match fuel with
      | O => None
      | S fuel =>
        let '(hcd, AV1, hc1, hrs) :=
          if F is None then hoist W D AV hc (hcands ss) else ([::], AV, hc, [::]) in
        match step AV1 F ss with
        | Some r =>
            if all (fun x => ~~ smem x D) (r_reads r) then
              let cons := take (size ss - size (r_rest r)) ss in
              let defs := flatten (map ssets cons) in
              let AV2 := if r_av r then [seq p <- AV1 | all (fun x => ~~ smem x defs) (evars p.2)] else [::] in
              let W2 := defs ++ W in
              match xchunks fuel (r_fact r) (r_stale r ++ minus D (r_writes r)) AV2 W2 hc1 (r_rest r) with
              | Some cs => Some ((hrs, [::], hcd) :: (r_reads r, r_writes r, r_code r) :: cs)
              | None => None
              end
            else None
        | None => None
        end
      end
    end.

  Definition xchunks_of (ps : list string) (c : cmd) : option (list chunk) :=
    match flat c with
    | Some ss => xchunks (size ss) None [::] [::] ps 0 ss
    | None => None
    end.

  Definition xcmd (ps : list string) (c : cmd) : option jcmd :=
    match xchunks_of ps c with
    | Some cs => Some (flatten [seq wrap ch.1.1 ch.1.2 ch.2 | ch <- cs])
    | None => None
    end.
End C.

(** ** The statement groups of the translation (for the spill choice; not used in proofs) *)
Section G.
  Context {atoI : arch_toIdent}.
  #[local] Existing Instance x86_extra.
  Variable name : string -> Ident.ident.
  Variable cfn : Ident.ident.
  Definition cmd_groups (ps : list string) (c : cmd) : list (list string * list string) :=
    match xchunks_of name cfn ps c with
    | Some cs => [seq ch.1 | ch <- cs]
    | None => [::]
    end.
End G.
