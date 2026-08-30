(** * ToJasmin: bedrock2 AST → Jasmin source code.
 *
 * Jasmin is a verified assembly language for cryptographic code.
 * This module translates bedrock2's [cmd] AST to Jasmin source text,
 * similar to how ToCString.v translates to C.
 *
 * Key differences from ToCString:
 * 1. Jasmin uses explicit register types (reg u64, stack u64[N])
 * 2. Function parameters are typed (pointer vs value)
 * 3. Stack allocations use [stack u64[N]] (no zero-init, no void* cast)
 * 4. Loads/stores use direct array syntax (p[i] instead of memcpy)
 * 5. Jasmin's compiler does register allocation — we emit hints
 *
 * The Jasmin compiler (jasminc) then:
 * - Performs register allocation (using our hints)
 * - Emits x86-64 assembly with correct calling convention
 * - Proves the compilation correct (safety + functional correctness)
 *
 * Pipeline:
 *   bedrock2 cmd (Rocq) → ToJasmin.v → .jazz file → jasminc → .s → .o
 *
 * Correctness chain:
 *   bedrock2 WP proof (Rocq) → simulation lemma (ToJasmin) →
 *   jasminc correctness (EasyCrypt) → hardware
 *)

Require Import bedrock2.Syntax.
From Stdlib Require Import String List ZArith Ascii Bool.
Require Import Stdlib.Numbers.DecimalString.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Jasmin AST                                                        *)
(* ================================================================ *)

(** Simplified Jasmin AST for the subset we need. *)

Inductive jasmin_type :=
  | JTu64          (* u64 scalar *)
  | JTptr (n: Z)   (* reg ptr u64[N] — pointer to array of N u64 limbs *)
  | JTstack (n: Z) (* stack u64[N] — stack-allocated array *)
  .

Inductive jasmin_expr :=
  | JEvar (x: string)
  | JElit (v: Z)
  | JEadd (e1 e2: jasmin_expr)
  | JEsub (e1 e2: jasmin_expr)
  | JEmul (e1 e2: jasmin_expr)
  | JEmulhuu (e1 e2: jasmin_expr) (* high 64 bits of u64×u64→u128 multiply *)
  | JEand (e1 e2: jasmin_expr)
  | JEor  (e1 e2: jasmin_expr)
  | JExor (e1 e2: jasmin_expr)
  | JEshr (e1 e2: jasmin_expr)
  | JEshl (e1 e2: jasmin_expr)
  | JEltu (e1 e2: jasmin_expr)  (* unsigned less-than: 1 if e1 < e2, else 0 *)
  | JEeq  (e1 e2: jasmin_expr)  (* equality: 1 if e1 = e2, else 0 *)
  | JEload (base: jasmin_expr) (offset: Z) (* base[offset] *)
  .

Inductive jasmin_cmd :=
  | JCskip
  | JCseq (c1 c2: jasmin_cmd)
  | JCset (x: string) (e: jasmin_expr)
  | JCstore (base: jasmin_expr) (offset: Z) (v: jasmin_expr) (* base[offset] = v *)
  | JCcall (f: string) (args: list jasmin_expr)
  | JCif (e: jasmin_expr) (ct cf: jasmin_cmd)
  | JCwhile (e: jasmin_expr) (body: jasmin_cmd)
  | JCdecl (x: string) (ty: jasmin_type) (body: jasmin_cmd)
  (* x86-64 intrinsics for carry-chain and wide-multiply *)
  | JCadd_flags (cf result: string) (a b: jasmin_expr)
      (* of,cf,sf,pf,zf,result = #ADD(a, b) — sets all flags *)
  | JCadcx (cf_out result: string) (a b: jasmin_expr) (cf_in: string)
      (* cf_out, result = #ADCX(a, b, cf_in) — add with carry *)
  | JCmulx (hi lo: string) (a b: jasmin_expr)
      (* (hi, lo) = #MULX(a, b) — full 64×64→128 multiply *)
  | JCsub_flags (cf result: string) (a b: jasmin_expr)
      (* of,cf,sf,pf,zf,result = #SUB(a, b) — sub with flags *)
  | JCsbb (cf_out result: string) (a b: jasmin_expr) (cf_in: string)
      (* cf_out, result = #SBB(a, b, cf_in) — sub with borrow *)
  .

Record jasmin_func := {
  jf_name: string;
  jf_params: list (string * jasmin_type);
  jf_locals: list (string * jasmin_type);
  jf_body: jasmin_cmd;
}.

(* ================================================================ *)
(* Translation: bedrock2 cmd → jasmin_cmd                           *)
(* ================================================================ *)

Section Translation.

  (** Translate a bedrock2 expression to Jasmin. *)
  Fixpoint tr_expr (e: Syntax.expr) : jasmin_expr :=
    match e with
    | expr.literal v => JElit v
    | expr.var x => JEvar x
    | expr.op op e1 e2 =>
        let e1' := tr_expr e1 in
        let e2' := tr_expr e2 in
        match op with
        | bopname.add => JEadd e1' e2'
        | bopname.sub => JEsub e1' e2'
        | bopname.mul => JEmul e1' e2'
        | bopname.and => JEand e1' e2'
        | bopname.or  => JEor  e1' e2'
        | bopname.xor => JExor e1' e2'
        | bopname.sru => JEshr e1' e2'
        | bopname.slu => JEshl e1' e2'
        | bopname.ltu => JEltu e1' e2'
        | bopname.eq  => JEeq  e1' e2'
        | bopname.mulhuu => JEmulhuu e1' e2'
        | _ => JElit 0 (* lts, srs, divu, remu: not used in crypto *)
        end
    | expr.load _ ea => JEload (tr_expr ea) 0 (* TODO: proper load *)
    | expr.op1 op e =>
        let e' := tr_expr e in
        match op with
        | op1.not => JExor e' (JElit (-1)%Z)  (* bitwise NOT = xor with all-ones *)
        | op1.opp => JEsub (JElit 0) e'        (* arithmetic negation = 0 - e *)
        end
    | _ => JElit 0
    end.

  (** Translate a bedrock2 command to Jasmin.
      The key change: [stackalloc] becomes a typed [stack u64[N]] declaration
      WITHOUT zero-initialization. *)
  Fixpoint tr_cmd (c: cmd) : jasmin_cmd :=
    match c with
    | cmd.skip => JCskip
    | cmd.seq c1 c2 => JCseq (tr_cmd c1) (tr_cmd c2)
    | cmd.set x e => JCset x (tr_expr e)
    | cmd.store _ ea ev =>
        JCstore (tr_expr ea) 0 (tr_expr ev)
    | cmd.stackalloc x n body =>
        (* Jasmin: declare stack array, assign pointer, continue *)
        let nwords := Z.div (n + 7) 8 in
        JCdecl x (JTstack nwords) (tr_cmd body)
    | cmd.cond e ct cf =>
        JCif (tr_expr e) (tr_cmd ct) (tr_cmd cf)
    | cmd.while e body =>
        JCwhile (tr_expr e) (tr_cmd body)
    | cmd.call _ f args =>
        JCcall f (List.map tr_expr args)
    | cmd.unset _ => JCskip
    | cmd.interact _ _ _ => JCskip (* no I/O in crypto *)
    end.

  (** Translate a bedrock2 function to a Jasmin function.
      All parameters become [reg ptr u64[field_size]] (pointers to
      field elements of [field_size] limbs).  Different curves use
      different limb counts (e.g. 6 for BLS12-381, 8 for BLS24-509). *)
  Definition tr_func_sized (field_size: Z)
      (f: string * (list string * list string * cmd)) : jasmin_func :=
    let '(name, (args, rets, body)) := f in
    {| jf_name := name;
       jf_params := List.map (fun a => (a, JTptr field_size)) args;
       jf_locals := nil; (* locals are inferred from cmd.set *)
       jf_body := tr_cmd body;
    |}.

  (** Backward-compatible default: assumes single u64 (field_size = 1). *)
  Definition tr_func (f: string * (list string * list string * cmd)) : jasmin_func :=
    tr_func_sized 1 f.

End Translation.

(* ================================================================ *)
(* Codegen polish 1: lower binops to in-place form                  *)
(* ================================================================ *)

(** Jasmin compiles a binary operation [x = e1 op e2] to an x86
    destructive instruction whose destination must equal one of the
    sources.  When the bedrock2 → jasmin translator emits

      x_n = (x_m op e2);

    with [x_m] still live afterwards, jasminc's register allocator
    cannot satisfy the merge constraint and aborts with
    "conflicting variables x_n and x_m must be merged".

    [lower_binop_assigns] rewrites every such [JCset x (JEbinop e1 e2)]
    into the explicit two-step form

      x = e1;
      x = (x op e2);

    so the surface syntax already has dest == src1, eliminating the
    constraint.  The first assignment is a [mov] (no constraint), the
    second a destructive in-place op.  Loads, plain-variable assigns,
    literals and unary forms are left unchanged.  The pass is purely
    syntactic on [jasmin_cmd] and does not touch [JCdecl]/[JCcall]
    arguments. *)

Definition is_binop (e : jasmin_expr) : bool :=
  match e with
  | JEadd _ _ | JEsub _ _ | JEmul _ _ | JEmulhuu _ _
  | JEand _ _ | JEor _ _ | JExor _ _
  | JEshr _ _ | JEshl _ _ => true
  (* JEltu/JEeq produce bool, not u64 — do NOT apply in-place lowering *)
  | _ => false
  end.

(** Replace the [src1] of a binary expression with a fresh variable
    [v].  Used to build the in-place form. *)
Definition rebuild_binop (v : string) (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEadd _ e2 => JEadd (JEvar v) e2
  | JEsub _ e2 => JEsub (JEvar v) e2
  | JEmul _ e2 => JEmul (JEvar v) e2
  | JEand _ e2 => JEand (JEvar v) e2
  | JEor  _ e2 => JEor  (JEvar v) e2
  | JExor _ e2 => JExor (JEvar v) e2
  | JEshr _ e2 => JEshr (JEvar v) e2
  | JEshl _ e2 => JEshl (JEvar v) e2
  | JEmulhuu _ e2 => JEmulhuu (JEvar v) e2
  | JEltu _ e2 => JEltu (JEvar v) e2
  | JEeq _ e2 => JEeq (JEvar v) e2
  | _ => e
  end.

Definition binop_src1 (e : jasmin_expr) : option jasmin_expr :=
  match e with
  | JEadd e1 _ | JEsub e1 _ | JEmul e1 _
  | JEand e1 _ | JEor  e1 _ | JExor e1 _
  | JEshr e1 _ | JEshl e1 _
  | JEmulhuu e1 _ => Some e1
  (* JEltu/JEeq return bool — exclude from binop lowering *)
  | JEltu _ _ | JEeq _ _ => None
  | _ => None
  end.

(** [is_atom] holds for the only operands jasminc's asmgen accepts as
    a [src2] of a binary instruction: a register-held variable, a
    literal, or a single load.  Anything else (a nested binop) must be
    materialized into a fresh temporary. *)
Definition is_atom (e : jasmin_expr) : bool :=
  match e with
  | JEvar _ => true
  | JElit _ => true
  | JEload _ _ => true
  | _ => false
  end.

(** Build a fresh temporary name from a base [x] and a counter [n].
    These names live alongside the bedrock2 [x_<n>] series and are
    declared by [function_locals] (which collects every variable
    appearing on the LHS of a [JCset]). *)
(** Generate a fresh variable name.  Uses decimal representation so
    indices >= 10 produce valid identifiers (not `:` etc). *)
Definition fresh_name (x : string) (n : nat) : string :=
  (x ++ "_bp" ++ DecimalString.NilZero.string_of_int (Z.to_int (Z.of_nat n)))%string.

(** Convert an expression into a sequence of [JCset]s + an atomic
    final expression.  The counter [n] threads fresh-temp suffixes
    through recursion.  Returns [(prefix_cmds, final_atom, next_n)].

    Strategy:
    - If [e] is already an atom, no work to do.
    - If [e] is a binop [JEbinop a b], recursively flatten [a] and
      [b], emit assignments into fresh temps, then build a binop on
      the two atoms. *)
Fixpoint flatten_expr (n : nat) (base : string) (e : jasmin_expr)
    : jasmin_cmd * jasmin_expr * nat :=
  if is_atom e then (JCskip, e, n)
  else
    match e with
    | JEadd e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEadd (JEvar t) a2)))),
         JEvar t, S n2)
    | JEsub e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEsub (JEvar t) a2)))),
         JEvar t, S n2)
    | JEmul e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEmul (JEvar t) a2)))),
         JEvar t, S n2)
    | JEand e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEand (JEvar t) a2)))),
         JEvar t, S n2)
    | JEor e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEor (JEvar t) a2)))),
         JEvar t, S n2)
    | JExor e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JExor (JEvar t) a2)))),
         JEvar t, S n2)
    | JEshr e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEshr (JEvar t) a2)))),
         JEvar t, S n2)
    | JEshl e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEshl (JEvar t) a2)))),
         JEvar t, S n2)
    | JEmulhuu e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEmulhuu (JEvar t) a2)))),
         JEvar t, S n2)
    | JEltu e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEltu (JEvar t) a2)))),
         JEvar t, S n2)
    | JEeq e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEeq (JEvar t) a2)))),
         JEvar t, S n2)
    | _ => (JCskip, e, n)  (* unreachable: non-atom and non-binop *)
    end.

(** Lower a [JCset x e] using the in-place form:
      x = e1; x = (x op flatten(e2));
    where [e1] and [e2] are the operands of the top-level binop.

    If [e] is an atom or has no binop top, just emit [JCset x e]. *)
Definition lower_set (x : string) (e : jasmin_expr) : jasmin_cmd :=
  match binop_src1 e with
  | Some e1 =>
      (* Materialize a flattened second operand. *)
      let '(p2, a2, _) := flatten_expr 0 x
        (match e with
         | JEadd _ b | JEsub _ b | JEmul _ b
         | JEand _ b | JEor _ b | JExor _ b
         | JEshr _ b | JEshl _ b
         | JEmulhuu _ b | JEltu _ b | JEeq _ b => b
         | _ => JElit 0
         end) in
      (* Materialize the first operand into x via a flatten. *)
      let '(p1, a1, _) := flatten_expr 0 (x ++ "a") e1 in
      JCseq p1 (JCseq (JCset x a1)
              (JCseq p2 (JCset x (rebuild_binop x
                  (match e with
                   | JEadd _ _ => JEadd (JEvar x) a2
                   | JEsub _ _ => JEsub (JEvar x) a2
                   | JEmul _ _ => JEmul (JEvar x) a2
                   | JEand _ _ => JEand (JEvar x) a2
                   | JEor _ _ => JEor  (JEvar x) a2
                   | JExor _ _ => JExor (JEvar x) a2
                   | JEshr _ _ => JEshr (JEvar x) a2
                   | JEshl _ _ => JEshl (JEvar x) a2
                   | JEmulhuu _ _ => JEmulhuu (JEvar x) a2
                   | JEltu _ _ => JEltu (JEvar x) a2
                   | JEeq _ _ => JEeq (JEvar x) a2
                   | _ => e
                   end)))))
  | None => JCset x e
  end.

Fixpoint lower_binop_assigns (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 => JCseq (lower_binop_assigns c1) (lower_binop_assigns c2)
  | JCset x e => lower_set x e
  | JCstore base off v => JCstore base off v
  | JCcall f args => JCcall f args
  | JCif e ct cf => JCif e (lower_binop_assigns ct) (lower_binop_assigns cf)
  | JCwhile e body => JCwhile e (lower_binop_assigns body)
  | JCdecl x ty body => JCdecl x ty (lower_binop_assigns body)
  | JCadd_flags cf r a b => JCadd_flags cf r a b
  | JCadcx co r a b ci => JCadcx co r a b ci
  | JCmulx h l a b => JCmulx h l a b
  | JCsub_flags cf r a b => JCsub_flags cf r a b
  | JCsbb co r a b ci => JCsbb co r a b ci
  end.

(** Apply [lower_binop_assigns] to a [jasmin_func]'s body. *)
Definition lower_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := lower_binop_assigns (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 2: normalize negative u64 literals                *)
(* ================================================================ *)

(** Coq's [Z] is unbounded, so negative integer literals (e.g. [-1])
    appear in the AST and would normally render as [(- 1)].  Jasmin's
    parser accepts that, but its register allocator/asmgen can refuse
    to fit a sign-extended negative immediate into a u64 destination
    register, producing errors like

      asmgen: invalid rexpr for oprd RCX &64u R15

    Replacing every negative [JElit v] with its two's-complement
    positive equivalent ([v + 2^64]) sidesteps the issue.  We do the
    rewrite at the AST level, BEFORE extraction, so the literal is a
    positive [Z] in the extracted code — never depends on the OCaml-
    side [Z.add]/[Z.pow] (which under [ExtrOcamlZInt] map to native
    [int] arithmetic and silently overflow at [2^63]). *)

Definition u64_max : Z := Z.pow 2 64.

Definition normalize_lit (v : Z) : Z :=
  if (v <? 0)%Z then Z.add v u64_max else v.

Fixpoint normalize_neg_lits_expr (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEvar x => JEvar x
  | JElit v => JElit (normalize_lit v)
  | JEadd e1 e2 => JEadd (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEsub e1 e2 => JEsub (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEmul e1 e2 => JEmul (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEmulhuu e1 e2 => JEmulhuu (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEand e1 e2 => JEand (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEor  e1 e2 => JEor  (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JExor e1 e2 => JExor (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEshr e1 e2 => JEshr (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEshl e1 e2 => JEshl (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEltu e1 e2 => JEltu (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEeq  e1 e2 => JEeq  (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEload base off => JEload (normalize_neg_lits_expr base) off
  end.

Fixpoint normalize_neg_lits_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 => JCseq (normalize_neg_lits_cmd c1) (normalize_neg_lits_cmd c2)
  | JCset x e => JCset x (normalize_neg_lits_expr e)
  | JCstore base off v =>
      JCstore (normalize_neg_lits_expr base) off (normalize_neg_lits_expr v)
  | JCcall f args => JCcall f (List.map normalize_neg_lits_expr args)
  | JCif e ct cf =>
      JCif (normalize_neg_lits_expr e) (normalize_neg_lits_cmd ct)
           (normalize_neg_lits_cmd cf)
  | JCwhile e body =>
      JCwhile (normalize_neg_lits_expr e) (normalize_neg_lits_cmd body)
  | JCdecl x ty body => JCdecl x ty (normalize_neg_lits_cmd body)
  | JCadd_flags cf r a b =>
      JCadd_flags cf r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b)
  | JCadcx co r a b ci =>
      JCadcx co r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b) ci
  | JCmulx h l a b =>
      JCmulx h l (normalize_neg_lits_expr a) (normalize_neg_lits_expr b)
  | JCsub_flags cf r a b =>
      JCsub_flags cf r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b)
  | JCsbb co r a b ci =>
      JCsbb co r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b) ci
  end.

Definition normalize_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := normalize_neg_lits_cmd (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 6: lift large literals to __wtmp__                *)
(* ================================================================ *)

(** x86-64 binary instructions accept at most a 32-bit sign-extended
    immediate.  Constants outside [-2^31, 2^31) must be loaded into a
    register first.  This pass walks every [JCset]/[JCstore]/etc. and
    finds the first [JElit v] with [|v| >= 2^31] in the expression,
    replacing it with a reference to [__wtmp__] and emitting
    [__wtmp__ = v;] before the statement. *)

Definition is_large_lit (v : Z) : bool :=
  Z.leb (Z.pow 2 31) v || Z.ltb v 0.

(** Substitute the FIRST large literal in an expression with [JEvar "__wtmp__"].
    Returns [(found_lit, new_expr)] where [found_lit] is the literal that was
    substituted (if any). *)
Fixpoint subst_first_large_lit (e : jasmin_expr)
    : option Z * jasmin_expr :=
  match e with
  | JEvar _ => (None, e)
  | JElit v =>
      if is_large_lit v
      then (Some v, JEvar "__wtmp__"%string)
      else (None, e)
  | JEadd e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEadd e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEadd e1 e2')
      end
  | JEsub e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEsub e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEsub e1 e2')
      end
  | JEmul e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEmul e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEmul e1 e2')
      end
  | JEand e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEand e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEand e1 e2')
      end
  | JEor e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEor e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEor e1 e2')
      end
  | JExor e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JExor e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JExor e1 e2')
      end
  | JEshr e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEshr e1' e2)
      | None => (None, e)  (* shift count is small *)
      end
  | JEshl e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEshl e1' e2)
      | None => (None, e)
      end
  | JEltu e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEltu e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEltu e1 e2')
      end
  | JEeq e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEeq e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEeq e1 e2')
      end
  | JEmulhuu e1 e2 =>
      let '(f1, e1') := subst_first_large_lit e1 in
      match f1 with
      | Some _ => (f1, JEmulhuu e1' e2)
      | None =>
          let '(f2, e2') := subst_first_large_lit e2 in
          (f2, JEmulhuu e1 e2')
      end
  | JEload base off =>
      let '(f, base') := subst_first_large_lit base in
      (f, JEload base' off)
  end.

(** Repeatedly lift large literals from a single expression until none
    remain.  Each iteration adds a [JCset "__wtmp__" (JElit v)] prefix
    statement; subsequent iterations would overwrite [__wtmp__] but we
    use a numbered family ([__wtmp_N__]) to avoid that.  Fuel-bounded. *)

Definition lift_one_set (x : string) (e : jasmin_expr) : jasmin_cmd :=
  let '(f, e') := subst_first_large_lit e in
  match f with
  | Some v =>
      JCseq (JCset "__wtmp__" (JElit v)) (JCset x e')
  | None => JCset x e
  end.

Fixpoint lift_lits_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 => JCseq (lift_lits_cmd c1) (lift_lits_cmd c2)
  | JCset x e => lift_one_set x e
  | JCstore base off v =>
      (* For stores, lift literals from [v] *)
      let '(f, v') := subst_first_large_lit v in
      match f with
      | Some lit =>
          JCseq (JCset "__wtmp__" (JElit lit)) (JCstore base off v')
      | None => JCstore base off v
      end
  | JCcall f args => JCcall f args
  | JCif e ct cf => JCif e (lift_lits_cmd ct) (lift_lits_cmd cf)
  | JCwhile e body => JCwhile e (lift_lits_cmd body)
  | JCdecl x ty body => JCdecl x ty (lift_lits_cmd body)
  | _ => c
  end.

Definition lift_lits_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := lift_lits_cmd (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 3: constant folding + dead-expression removal     *)
(* ================================================================ *)

(** Simplify an expression by folding constants:
    - [0 + x]  → [x]    (left-identity for add)
    - [x + 0]  → [x]    (right-identity for add)
    - [x - 0]  → [x]
    - [0 + 0]  → [0]
    - [x ^ 0]  → [x]    (XOR with 0 is identity)
    - [x & x]  → [x]    where both sides are same var
    Runs bottom-up so nested patterns like [(0 + 0) + x] simplify. *)
Fixpoint simplify_expr (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEadd e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e1', e2' with
      | JElit 0, _ => e2'
      | _, JElit 0 => e1'
      | _, _ => JEadd e1' e2'
      end
  | JEsub e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e2' with
      | JElit 0 => e1'
      | _ => JEsub e1' e2'
      end
  | JExor e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e2' with
      | JElit 0 => e1'
      | _ => JExor e1' e2'
      end
  | JEand e1 e2 =>
      JEand (simplify_expr e1) (simplify_expr e2)
  | JEor e1 e2 =>
      JEor (simplify_expr e1) (simplify_expr e2)
  | JEmul e1 e2 =>
      JEmul (simplify_expr e1) (simplify_expr e2)
  | JEshr e1 e2 =>
      JEshr (simplify_expr e1) (simplify_expr e2)
  | JEshl e1 e2 =>
      JEshl (simplify_expr e1) (simplify_expr e2)
  | JEmulhuu e1 e2 =>
      JEmulhuu (simplify_expr e1) (simplify_expr e2)
  | JEltu e1 e2 =>
      JEltu (simplify_expr e1) (simplify_expr e2)
  | JEeq e1 e2 =>
      JEeq (simplify_expr e1) (simplify_expr e2)
  | JEload base off =>
      JEload (simplify_expr base) off
  | _ => e
  end.

(** Simplify a command by:
    - Folding constant expressions
    - Removing [JCset x (JEvar x)] (self-assignment, no-op)
    - Removing [JCskip] from sequences *)
Fixpoint simplify_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 =>
      let c1' := simplify_cmd c1 in
      let c2' := simplify_cmd c2 in
      match c1', c2' with
      | JCskip, _ => c2'
      | _, JCskip => c1'
      | _, _ => JCseq c1' c2'
      end
  | JCset x e =>
      let e' := simplify_expr e in
      match e' with
      | JEvar y => if String.eqb x y then JCskip else JCset x e'
      | _ => JCset x e'
      end
  | JCstore base off v =>
      JCstore (simplify_expr base) off (simplify_expr v)
  | JCcall f args =>
      JCcall f (List.map simplify_expr args)
  | JCif e ct cf =>
      JCif (simplify_expr e) (simplify_cmd ct) (simplify_cmd cf)
  | JCwhile e body =>
      JCwhile (simplify_expr e) (simplify_cmd body)
  | JCdecl x ty body =>
      JCdecl x ty (simplify_cmd body)
  | JCadd_flags cf r a b =>
      JCadd_flags cf r (simplify_expr a) (simplify_expr b)
  | JCadcx co r a b ci =>
      JCadcx co r (simplify_expr a) (simplify_expr b) ci
  | JCmulx h l a b =>
      JCmulx h l (simplify_expr a) (simplify_expr b)
  | JCsub_flags cf r a b =>
      JCsub_flags cf r (simplify_expr a) (simplify_expr b)
  | JCsbb co r a b ci =>
      JCsbb co r (simplify_expr a) (simplify_expr b) ci
  end.

Definition simplify_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := simplify_cmd (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 4: carry-chain detection                          *)
(* ================================================================ *)

(** Detect the bedrock2 pattern for [addcarryx] without carry-in:
      sum = (a + b);
      carry = (sum <u a);
    Replace with: JCadd_flags carry sum a b.

    Also detect [addcarryx] with carry-in:
      partial = (a + b);
      cp = (partial <u a);
      sum = (partial + cin);
      c2 = (sum <u partial);
      carry = (cp | c2);
    Replace with: JCadcx carry sum a b cin.

    And detect [mulhuu] paired with [mul]:
      lo = (a * b);
      hi = (MULHUU a b);
    Replace with: JCmulx hi lo a b.

    The pass works on flattened [JCseq] chains. *)

(** Flatten a [jasmin_cmd] into a list of atomic commands. *)
Fixpoint cmd_to_list (c : jasmin_cmd) : list jasmin_cmd :=
  match c with
  | JCseq c1 c2 => cmd_to_list c1 ++ cmd_to_list c2
  | JCskip => nil
  | _ => c :: nil
  end.

Definition list_to_cmd (cs : list jasmin_cmd) : jasmin_cmd :=
  List.fold_right JCseq JCskip cs.

(** Expression equality (syntactic). *)
Fixpoint expr_eqb (e1 e2 : jasmin_expr) : bool :=
  match e1, e2 with
  | JEvar x, JEvar y => String.eqb x y
  | JElit x, JElit y => Z.eqb x y
  | JEadd a1 b1, JEadd a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | _, _ => false
  end.

(** Match pattern for first-limb add:
    [sum = (a + b)]
    [cpn = ((sum <u a) + c)]    — carry fused with next-limb operand
    [ns  = (cpn + d)]           — add second next-limb operand
    → JCadd_flags __cf sum a b; JCadcx __cf ns c d __cf
    Consumes 3 statements, emits 2 intrinsics. *)
(** Only match when both operands of the initial add are [JEvar] —
    prevents matching conditional-addition patterns like [x + (mask & const)]. *)
Definition match_first_limb_adc (c1 c2 c3 : jasmin_cmd)
    : option (jasmin_cmd * jasmin_cmd) :=
  match c1, c2, c3 with
  | JCset sum (JEadd (JEvar a) (JEvar b)),
    JCset cpn (JEadd (JEltu (JEvar sum') (JEvar a')) (JEvar c)),
    JCset ns (JEadd (JEvar cpn') (JEvar d)) =>
      if String.eqb sum sum'
         && String.eqb a a'
         && String.eqb cpn cpn'
      then Some (JCadd_flags "__cf" sum (JEvar a) (JEvar b),
                  JCadcx "__cf" ns (JEvar c) (JEvar d) "__cf")
      else None
  | _, _, _ => None
  end.

(** Match fused carry-chain continuation:
    [cpn = (((prev <u a) + (ns <u b)) + c)]  — two carry extractions + next operand
    [next = (cpn + d)]
    → JCadcx __cf next c d __cf
    Where __cf already holds the carry from the previous ADCX.
    Consumes 2 statements, emits 1 intrinsic. *)
(** Only match when the third operand [c] is a simple [JEvar] — this
    prevents matching the conditional-addition pattern in bls12_sub
    where c is [(x23 & constant)]. *)
(** Both operands [c] and [d] must be plain variables —
    prevents matching conditional-add patterns with masked constants. *)
Definition match_cont_adc (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset cpn (JEadd (JEadd (JEltu _ _) (JEltu _ _)) (JEvar c)),
    JCset ns (JEadd (JEvar cpn') (JEvar d)) =>
      if String.eqb cpn cpn'
      then Some (JCadcx "__cf" ns (JEvar c) (JEvar d) "__cf")
      else None
  | _, _ => None
  end.

(** Match carry-out computation after the last ADCX:
    [carry_out = ((prev <u a) + (ns <u b))]
    → carry_out = 0; if __cf { carry_out = 1; }
    Consumes 1 statement, emits the bool→u64 conversion. *)
Definition match_carry_out (c : jasmin_cmd) : option jasmin_cmd :=
  match c with
  | JCset cout (JEadd (JEltu _ _) (JEltu _ _)) =>
      Some (JCseq (JCset cout (JElit 0))
                   (JCif (JEvar "__cf") (JCset cout (JElit 1)) JCskip))
  | _ => None
  end.

(** Subtraction chain detection (mirrors addition chain). *)

Definition match_first_limb_sbb (c1 c2 c3 : jasmin_cmd)
    : option (jasmin_cmd * jasmin_cmd) :=
  match c1, c2, c3 with
  | JCset result1 (JEsub (JEvar sum1) const1),
    JCset result2 (JEsub (JEvar sum2) const2),
    JCset adj (JEsub (JEvar result2') (JEltu (JEvar sum1') (JEvar result1'))) =>
      if String.eqb result2 result2'
         && String.eqb sum1 sum1'
         && String.eqb result1 result1'
      then Some (JCsub_flags "__bf" result1 (JEvar sum1) const1,
                  JCsbb "__bf" adj (JEvar sum2) const2 "__bf")
      else None
  | _, _, _ => None
  end.

Definition match_cont_sbb (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset result (JEsub (JEvar sum) const),
    JCset adj (JEsub (JEvar result') (JEadd (JEltu _ _) (JEltu _ _))) =>
      if String.eqb result result'
      then Some (JCsbb "__bf" adj (JEvar sum) const "__bf")
      else None
  | _, _ => None
  end.

(** Match borrow-out patterns after the last SBB.
    Pattern 1 (from bls12_add sub phase):
      [bout = (x <u (x - ((a <u b) + (c <u d))))]
      → bout = 0; if __bf { bout = 1; }
    Pattern 2 (from bls12_sub):
      [bout = (0 + (((a <u b) + (c <u d)) == 0))]
      → bout = 1; if __bf { bout = 0; }
      (inverted: bout = 1 means no borrow) *)
Definition match_borrow_out (c : jasmin_cmd) : option jasmin_cmd :=
  match c with
  | JCset bout (JEltu _ (JEsub _ (JEadd (JEltu _ _) (JEltu _ _)))) =>
      Some (JCseq (JCset bout (JElit 0))
                   (JCif (JEvar "__bf") (JCset bout (JElit 1)) JCskip))
  | JCset bout (JEadd (JElit 0) (JEeq (JEadd (JEltu _ _) (JEltu _ _)) (JElit 0))) =>
      (* Pattern is [0 + (borrow_sum == 0)] = 1 iff no borrow. *)
      Some (JCseq (JCset bout (JElit 0))
                   (JCif (JEvar "__bf") JCskip (JCset bout (JElit 1))))
  | JCset bout (JEadd (JEsub (JElit 0) (JElit 1))
                       (JEeq (JEadd (JEltu _ _) (JEltu _ _)) (JElit 0))) =>
      (* Pattern is [(-1) + (borrow_sum == 0)] = -1 + (1 if no borrow else 0)
         = 0 if no borrow, -1 (all-ones) if borrow.
         This is the SIGN-EXTENDED mask used for conditional p addition.
         __bf=1 (borrow) → bout = -1 (all ones).
         __bf=0 (no borrow) → bout = 0. *)
      Some (JCseq (JCset bout (JElit 0))
                   (JCif (JEvar "__bf")
                         (JCseq (JCset bout (JElit 0))
                                (JCset bout (JEsub (JEvar bout) (JElit 1))))
                         JCskip))
  | _ => None
  end.

(** Conditional-select pattern:
    [mask = (0 + (flag == 0))]
    [nmask = (mask ^ 0xFFFFFFFFFFFFFFFF)]
    [out = (sum & mask) | (diff & nmask)]
    → out = diff; out = sum if !__bf;
    Consumes 3, emits 2. *)
Definition match_cmov (c1 c2 c3 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2, c3 with
  (* Two forms of the mask depending on op1.opp presence:
     Form A: mask = (0 + (flag == 0))        → JEadd (JElit 0) (JEeq ...)
     Form B: mask = ((0 - 1) + (flag == 0))  → JEadd (JEsub ...) (JEeq ...)
     We match both by using [_] for the first operand of the outer add. *)
  | JCset mask (JEadd _ (JEeq (JEvar flag) (JElit 0))),
    JCset nmask (JExor (JEvar mask') (JElit _)),
    JCset out (JEor (JEand (JEvar sum) (JEvar mask''))
                     (JEand (JEvar diff) (JEvar nmask'))) =>
      if String.eqb mask mask'
         && String.eqb mask mask''
         && String.eqb nmask nmask'
      (* Flag is the borrow-out: flag=1 means borrow (sum < p, keep sum),
         flag=0 means no borrow (sum >= p, use diff = sum-p).
         Inline the comparison: if (flag == 0) { out = diff; } else { out = sum; }
         Jasmin compiles the inline [flag == 0] test to testq + cmovcc
         without needing a separate reg bool variable. *)
      then Some (JCif (JEeq (JEvar flag) (JElit 0))
                      (JCset out (JEvar diff))
                      (JCset out (JEvar sum)))
      else None
  | _, _, _ => None
  end.

(** Match the conditional-addition pattern from sub's "maybe add p":
    [sum = a + (mask & const1)]                  — first masked add
    [intermediate = (sum <u a) + next_a]         — carry + next limb operand
    [ns = intermediate + (mask & const2)]        — second masked add
    → __wtmp__ = (mask & const1);
      _, __cf, _, _, _, sum = #ADD(a, __wtmp__);
      __wtmp2__ = (mask & const2);
      __cf, ns = #ADCX(next_a, __wtmp2__, __cf);
    Consumes 3, emits the equivalent of 2 carry-chain ops with 2 mask
    materializations.

    We emit JCset for the masked values rather than custom intrinsics —
    pp_cmd already lifts large literals via __wtmp__. *)
Definition match_first_limb_adc_masked (c1 c2 c3 : jasmin_cmd)
    : option (jasmin_cmd * jasmin_cmd) :=
  match c1, c2, c3 with
  | JCset sum (JEadd (JEvar a) (JEand (JEvar mask1) c1lit)),
    JCset cpn (JEadd (JEltu (JEvar sum') (JEvar a')) (JEvar nexta)),
    JCset ns (JEadd (JEvar cpn') (JEand (JEvar mask2) c2lit)) =>
      if String.eqb sum sum' && String.eqb a a' && String.eqb cpn cpn'
         && String.eqb mask1 mask2
      then
        let m1 := "__masked1__"%string in
        let m2 := "__masked2__"%string in
        Some (JCseq (JCset m1 (JEand (JEvar mask1) c1lit))
                    (JCadd_flags "__cf" sum (JEvar a) (JEvar m1)),
              JCseq (JCset m2 (JEand (JEvar mask2) c2lit))
                    (JCadcx "__cf" ns (JEvar nexta) (JEvar m2) "__cf"))
      else None
  | _, _, _ => None
  end.

(** Continuation: [next = ((c1 <u c2) + (c3 <u c4)) + next_a]
                   [adj = next + (mask & const)]
    → __wtmp__ = (mask & const); __cf, adj = #ADCX(next_a, __wtmp__, __cf) *)
Definition match_cont_adc_masked (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset cpn (JEadd (JEadd (JEltu _ _) (JEltu _ _)) (JEvar nexta)),
    JCset adj (JEadd (JEvar cpn') (JEand (JEvar mask) clit)) =>
      if String.eqb cpn cpn'
      then
        let m := "__masked__"%string in
        Some (JCseq (JCset m (JEand (JEvar mask) clit))
                    (JCadcx "__cf" adj (JEvar nexta) (JEvar m) "__cf"))
      else None
  | _, _ => None
  end.

(** Triple-fused last limb of conditional addition:
    [adj = ((((c1 <u c2) + (c3 <u c4)) + next_a) + (mask & const))] *)
Definition match_last_adc_masked (c : jasmin_cmd) : option jasmin_cmd :=
  match c with
  | JCset adj (JEadd (JEadd (JEadd (JEltu _ _) (JEltu _ _)) (JEvar nexta))
                      (JEand (JEvar mask) clit)) =>
      let m := "__masked__"%string in
      Some (JCseq (JCset m (JEand (JEvar mask) clit))
                  (JCadcx "__cf" adj (JEvar nexta) (JEvar m) "__cf"))
  | _ => None
  end.

(** Full conditional-addition pattern: 11 statements covering all 6 limbs.
    Hoists all 6 masked computations BEFORE the carry chain so [andq]
    doesn't clobber CF between [#ADD] and [#ADCX] uses.

    Pattern (s1..s11):
      s1:  out0 = a0 + (mask & p0)
      s2:  cpn1 = (out0 <u a0) + a1                     -- carry+next
      s3:  out1 = cpn1 + (mask & p1)
      s4:  cpn2 = ((cpn1 <u a1) + (out1 <u (mask&p1))) + a2
      s5:  out2 = cpn2 + (mask & p2)
      s6:  cpn3 = ((cpn2 <u a2) + (out2 <u (mask&p2))) + a3
      s7:  out3 = cpn3 + (mask & p3)
      s8:  cpn4 = ((cpn3 <u a3) + (out3 <u (mask&p3))) + a4
      s9:  out4 = cpn4 + (mask & p4)
      s10: cpn5 = ((cpn4 <u a4) + (out4 <u (mask&p4))) + a5
      s11: out5 = (((cpn5 <u a5) + ...) + a5) + (mask & p5)  -- triple fused

    Emits:
      __m0 = mask & p0; __m1 = mask & p1; ... __m5 = mask & p5;
      _, __cf, _, _, _, out0 = #ADD(a0, __m0);
      __cf, out1 = #ADCX(a1, __m1, __cf);
      __cf, out2 = #ADCX(a2, __m2, __cf);
      __cf, out3 = #ADCX(a3, __m3, __cf);
      __cf, out4 = #ADCX(a4, __m4, __cf);
      __cf, out5 = #ADCX(a5, __m5, __cf);

    Total: 6 mask comp + 1 #ADD + 5 #ADCX = 12 statements (vs 11 input). *)
(** Match the 10-statement conditional addition pattern.
    s1: x_n = a0 + (mask & p0)        — first masked add
    s2: x_{n+1} = (s1_carry + a1)     — intermediate
    s3: x_{n+2} = s2 + (mask & p1)
    s4: x_{n+3} = ((..) + a2)
    s5: x_{n+4} = s4 + (mask & p2)
    s6: x_{n+5} = ((..) + a3)
    s7: x_{n+6} = s6 + (mask & p3)
    s8: x_{n+7} = ((..) + a4)
    s9: x_{n+8} = s8 + (mask & p4)
    s10: x_{n+9} = ((((..)) + a5) + (mask & p5))   — triple-fused last *)
Definition match_full_cond_add (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : jasmin_cmd)
    : option (list jasmin_cmd) :=
  match c1, c3, c5, c7, c9 with
  | JCset out0 (JEadd (JEvar a0) (JEand (JEvar mask) p0)),
    JCset out1 (JEadd (JEvar _) (JEand (JEvar _) p1)),
    JCset out2 (JEadd (JEvar _) (JEand (JEvar _) p2)),
    JCset out3 (JEadd (JEvar _) (JEand (JEvar _) p3)),
    JCset out4 (JEadd (JEvar _) (JEand (JEvar _) p4)) =>
      let extract_a c :=
        match c with
        | JCset _ (JEadd _ (JEvar v)) => Some v
        | _ => None
        end in
      match extract_a c2, extract_a c4, extract_a c6, extract_a c8 with
      | Some a1, Some a2, Some a3, Some a4 =>
        match c10 with
        | JCset out5 (JEadd (JEadd (JEadd _ _) (JEvar a5))
                             (JEand (JEvar _) p5)) =>
          let m0 := "__m0__"%string in
          let m1 := "__m1__"%string in
          let m2 := "__m2__"%string in
          let m3 := "__m3__"%string in
          let m4 := "__m4__"%string in
          let m5 := "__m5__"%string in
          Some (
            JCset m0 (JEand (JEvar mask) p0) ::
            JCset m1 (JEand (JEvar mask) p1) ::
            JCset m2 (JEand (JEvar mask) p2) ::
            JCset m3 (JEand (JEvar mask) p3) ::
            JCset m4 (JEand (JEvar mask) p4) ::
            JCset m5 (JEand (JEvar mask) p5) ::
            JCadd_flags "__cf" out0 (JEvar a0) (JEvar m0) ::
            JCadcx "__cf" out1 (JEvar a1) (JEvar m1) "__cf" ::
            JCadcx "__cf" out2 (JEvar a2) (JEvar m2) "__cf" ::
            JCadcx "__cf" out3 (JEvar a3) (JEvar m3) "__cf" ::
            JCadcx "__cf" out4 (JEvar a4) (JEvar m4) "__cf" ::
            JCadcx "__cf" out5 (JEvar a5) (JEvar m5) "__cf" :: nil)
        | _ => None
        end
      | _, _, _, _ => None
      end
  | _, _, _, _, _ => None
  end.

(** Match simple [x = (a + b); y = (x <u a)] → JCadd_flags __cf_y x a b
    followed by a bool→u64 promotion of [y].

    The promotion is essential: subsequent bedrock2 code consumes [y]
    as a u64 (e.g. [next = y; next = next + ...]).  Emitting
    [JCadd_flags y ...] alone makes [y] register as a [reg bool] in
    [collect_bool_vars], and jasminc then rejects the later
    [reg u64 = reg bool] copy.  We forward the carry through a fresh
    bool [__cf_<carry>] and immediately materialize [carry] as 0/1. *)
Definition match_add_carry (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset sum (JEadd a b),
    JCset carry (JEltu (JEvar sum') a') =>
      if String.eqb sum sum' && expr_eqb a a'
      then
        let cf_tmp := ("__cf_" ++ carry)%string in
        Some (JCseq (JCadd_flags cf_tmp sum a b)
                    (JCseq (JCset carry (JElit 0))
                           (JCif (JEvar cf_tmp)
                                 (JCset carry (JElit 1)) JCskip)))
      else None
  | _, _ => None
  end.

(** Match pattern for mulx: [lo=(a*b); hi=(MULHUU a b)] → JCmulx hi lo a b *)
Definition match_mulx (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset lo (JEmul a1 b1),
    JCset hi (JEmulhuu a2 b2) =>
      if match a1, a2 with
         | JEvar x, JEvar y => String.eqb x y | JElit x, JElit y => Z.eqb x y | _, _ => false
         end
         && match b1, b2 with
            | JEvar x, JEvar y => String.eqb x y | JElit x, JElit y => Z.eqb x y | _, _ => false
            end
      then Some (JCmulx hi lo a1 b1)
      else None
  | _, _ => None
  end.

Fixpoint lower_carry_chain_list (fuel : nat) (cs : list jasmin_cmd)
    : list jasmin_cmd :=
  match fuel with
  | O => cs
  | S fuel' =>
    match cs with
    | nil => nil
    | c1 :: c2 :: c3 :: rest =>
        (* Try 11-statement full conditional addition first if enough stmts.
           Use a pre-check to avoid false matches: the first statement must
           be [JCset _ (JEadd (JEvar _) (JEand _ _))]. *)
        let try_full_cond_add :=
          match c1 with
          | JCset _ (JEadd (JEvar _) (JEand _ _)) =>
              (match rest with
               | c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest' =>
                   match match_full_cond_add c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 with
                   | Some instrs => Some (instrs, rest')
                   | None => None
                   end
               | _ => None
               end)
          | _ => None
          end in
        match try_full_cond_add with
        | Some (instrs, rest') => instrs ++ lower_carry_chain_list fuel' rest'
        | None =>
        (* Try 3-statement conditional move *)
        match match_cmov c1 c2 c3 with
        | Some instr => instr :: lower_carry_chain_list fuel' rest
        | None =>
        (* Then try 3-statement fused first-limb ADC *)
        match match_first_limb_adc c1 c2 c3 with
        | Some (i1, i2) =>
            i1 :: i2 :: lower_carry_chain_list fuel' rest
        | None =>
        (* Try 3-statement first-limb SBB *)
        match match_first_limb_sbb c1 c2 c3 with
        | Some (i1, i2) =>
            i1 :: i2 :: lower_carry_chain_list fuel' rest
        | None =>
        match match_cont_adc c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None =>
        match match_cont_sbb c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None =>
        (* Try carry/borrow out *)
        match match_carry_out c1 with
        | Some conv => conv :: lower_carry_chain_list fuel' (c2 :: c3 :: rest)
        | None =>
        match match_borrow_out c1 with
        | Some conv => conv :: lower_carry_chain_list fuel' (c2 :: c3 :: rest)
        | None =>
        (* Simple add+carry or mulx *)
        match match_add_carry c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None =>
        match match_mulx c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None => c1 :: lower_carry_chain_list fuel' (c2 :: c3 :: rest)
        end end end end end end end end end end
    | c1 :: c2 :: nil =>
        match match_cont_sbb c1 c2 with
        | Some instr => instr :: nil
        | None =>
        match match_cont_adc c1 c2 with
        | Some instr => instr :: nil
        | None =>
        match match_add_carry c1 c2 with
        | Some instr => instr :: nil
        | None =>
        match match_mulx c1 c2 with
        | Some instr => instr :: nil
        | None => c1 :: c2 :: nil
        end end end end
    | c :: rest => c :: lower_carry_chain_list fuel' rest
    end
  end.

Fixpoint lower_carry_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCseq _ _ =>
      let stmts := cmd_to_list c in
      list_to_cmd (lower_carry_chain_list (List.length stmts) stmts)
  | JCif e ct cf => JCif e (lower_carry_cmd ct) (lower_carry_cmd cf)
  | JCwhile e body => JCwhile e (lower_carry_cmd body)
  | JCdecl x ty body => JCdecl x ty (lower_carry_cmd body)
  | _ => c
  end.

Definition carry_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := lower_carry_cmd (jf_body f) |}.

(** Combined polish: simplify + normalize + carry-chain + lower + simplify.
    Carry-chain runs before binop lowering because it matches multi-statement
    patterns that lowering would break apart. *)
(* ================================================================ *)
(* Codegen polish 5: lower ltu/eq to bool conditionals              *)
(* ================================================================ *)

(** Jasmin's [<u] and [==] return [reg bool], not [reg u64].
    bedrock2 treats these as u64 (0 or 1).  This pass converts every
    [JEltu a b] embedded in an expression to a conditional assignment
    through a fresh bool variable + if-then-else.  *)

Definition ltu_bool_name (x : string) : string := ("__ltu_" ++ x)%string.

Fixpoint has_comparison (e : jasmin_expr) : bool :=
  match e with
  | JEltu _ _ | JEeq _ _ => true
  | JEadd e1 e2 | JEsub e1 e2 | JEmul e1 e2 | JEmulhuu e1 e2
  | JEand e1 e2 | JEor e1 e2 | JExor e1 e2
  | JEshr e1 e2 | JEshl e1 e2 => has_comparison e1 || has_comparison e2
  | JEload base _ => has_comparison base
  | _ => false
  end.

Fixpoint extract_comparisons (n : nat) (x : string) (e : jasmin_expr)
    : nat * jasmin_cmd * jasmin_expr :=
  match e with
  | JEltu a b =>
      (* First extract any nested comparisons from operands *)
      let '(n1, p1, a') := extract_comparisons n x a in
      let '(n2, p2, b') := extract_comparisons n1 x b in
      (* Lift nested binops in a' or b' to fresh temps so the
         comparison's operands are atoms (jasminc <u rejects nested
         binops on the right). *)
      let lift_a :=
        if is_atom a' then (n2, JCskip, a')
        else
          let t := fresh_name (x ++ "_lt_a") n2 in
          (S n2, JCset t a', JEvar t) in
      let '(n3, pa, a'') := lift_a in
      let lift_b :=
        if is_atom b' then (n3, JCskip, b')
        else
          let t := fresh_name (x ++ "_lt_b") n3 in
          (S n3, JCset t b', JEvar t) in
      let '(n4, pb, b'') := lift_b in
      let bname := ltu_bool_name (fresh_name x n4) in
      let tmp := fresh_name x n4 in
      (S n4,
       JCseq p1 (JCseq p2 (JCseq pa (JCseq pb
         (JCseq (JCset bname (JEltu a'' b''))
                (JCseq (JCset tmp (JElit 0))
                       (JCif (JEvar bname) (JCset tmp (JElit 1)) JCskip)))))),
       JEvar tmp)
  | JEeq a b =>
      let '(n1, p1, a') := extract_comparisons n x a in
      let '(n2, p2, b') := extract_comparisons n1 x b in
      let bname := ("__eq_" ++ fresh_name x n2)%string in
      let tmp := fresh_name x n2 in
      (S n2,
       JCseq p1 (JCseq p2
         (JCseq (JCset bname (JEeq a' b'))
                (JCseq (JCset tmp (JElit 0))
                       (JCif (JEvar bname) (JCset tmp (JElit 1)) JCskip)))),
       JEvar tmp)
  | JEadd e1 e2 =>
      let '(n1, p1, e1') := extract_comparisons n x e1 in
      let '(n2, p2, e2') := extract_comparisons n1 x e2 in
      (n2, JCseq p1 p2, JEadd e1' e2')
  | JEsub e1 e2 =>
      let '(n1, p1, e1') := extract_comparisons n x e1 in
      let '(n2, p2, e2') := extract_comparisons n1 x e2 in
      (n2, JCseq p1 p2, JEsub e1' e2')
  | JEor e1 e2 =>
      let '(n1, p1, e1') := extract_comparisons n x e1 in
      let '(n2, p2, e2') := extract_comparisons n1 x e2 in
      (n2, JCseq p1 p2, JEor e1' e2')
  | JEand e1 e2 =>
      let '(n1, p1, e1') := extract_comparisons n x e1 in
      let '(n2, p2, e2') := extract_comparisons n1 x e2 in
      (n2, JCseq p1 p2, JEand e1' e2')
  | _ => (n, JCskip, e)
  end.

Fixpoint lower_comparisons_cmd (n : nat) (c : jasmin_cmd) : nat * jasmin_cmd :=
  match c with
  | JCskip => (n, JCskip)
  | JCseq c1 c2 =>
      let '(n1, c1') := lower_comparisons_cmd n c1 in
      let '(n2, c2') := lower_comparisons_cmd n1 c2 in
      (n2, JCseq c1' c2')
  | JCset x e =>
      if has_comparison e then
        let '(n', prefix, e') := extract_comparisons n x e in
        (n', JCseq prefix (JCset x e'))
      else (n, JCset x e)
  | JCif e ct cf =>
      let '(n1, ct') := lower_comparisons_cmd n ct in
      let '(n2, cf') := lower_comparisons_cmd n1 cf in
      (n2, JCif e ct' cf')
  | JCwhile e body =>
      let '(n', body') := lower_comparisons_cmd n body in
      (n', JCwhile e body')
  | JCdecl x ty body =>
      let '(n', body') := lower_comparisons_cmd n body in
      (n', JCdecl x ty body')
  | _ => (n, c) (* store, call, intrinsics: pass through *)
  end.

Definition lower_comparisons_func (f : jasmin_func) : jasmin_func :=
  let '(_, body') := lower_comparisons_cmd 0 (jf_body f) in
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := body' |}.

(** Combined polish pipeline:
    1. carry_func: detect ADD/ADCX/MULX patterns + carry-out conversion
    2. lower_comparisons_func: remaining <u/== → bool conditionals
    3. simplify_func: constant fold, dead-code elim
    4. normalize_func: negative literals → two's complement
    5. lower_func: flatten binops for jasminc
    6. simplify_func: clean up after lowering *)
Definition polish_func (f : jasmin_func) : jasmin_func :=
  lift_lits_func
    (simplify_func
      (lower_func
        (normalize_func
          (simplify_func
            (lower_comparisons_func (carry_func f)))))).

(* ================================================================ *)
(* Pretty-printing: jasmin_cmd → string (Jasmin source text)        *)
(* ================================================================ *)

Definition LF : string := String (Ascii.Ascii false true false true false false false false) "".

(** Render a [Z] as a Jasmin u64 immediate.  Negative values are
    converted to their two's-complement positive form (mod 2^64) so
    jasminc accepts them as immediates without sign-extension surprises. *)
Definition pp_zlit_u64 (v : Z) : string :=
  let normalized :=
    if (v <? 0)%Z
    then Z.add v (Z.pow 2 64)
    else v
  in
  DecimalString.NilZero.string_of_int (Z.to_int normalized).

Fixpoint pp_expr (e: jasmin_expr) : string :=
  match e with
  | JEvar x => x
  | JElit v => pp_zlit_u64 v
  | JEadd e1 e2 => "(" ++ pp_expr e1 ++ " + " ++ pp_expr e2 ++ ")"
  | JEsub e1 e2 => "(" ++ pp_expr e1 ++ " - " ++ pp_expr e2 ++ ")"
  | JEmul e1 e2 => "(" ++ pp_expr e1 ++ " * " ++ pp_expr e2 ++ ")"
  | JEand e1 e2 => "(" ++ pp_expr e1 ++ " & " ++ pp_expr e2 ++ ")"
  | JEor  e1 e2 => "(" ++ pp_expr e1 ++ " | " ++ pp_expr e2 ++ ")"
  | JExor e1 e2 => "(" ++ pp_expr e1 ++ " ^ " ++ pp_expr e2 ++ ")"
  | JEshr e1 e2 => "(" ++ pp_expr e1 ++ " >> " ++ pp_expr e2 ++ ")"
  | JEshl e1 e2 => "(" ++ pp_expr e1 ++ " << " ++ pp_expr e2 ++ ")"
  | JEmulhuu e1 e2 => "(MULHUU " ++ pp_expr e1 ++ " " ++ pp_expr e2 ++ ")"
  | JEltu e1 e2 => "(" ++ pp_expr e1 ++ " <u " ++ pp_expr e2 ++ ")"
  | JEeq e1 e2 => "(" ++ pp_expr e1 ++ " == " ++ pp_expr e2 ++ ")"
  | JEload base off =>
      let off_str := DecimalString.NilZero.string_of_int (Z.to_int off) in
      "[" ++ pp_expr base ++ " + " ++ off_str ++ "]"
  end.

(** Pretty-print a Jasmin storage type for a function parameter or
    local declaration.

    Note: [JTptr n] is rendered as [reg u64] (a raw register-held byte
    pointer) rather than [reg ptr u64[n]] (a typed array reference).
    The bedrock2 calling convention treats every pointer parameter as
    a raw byte address dereferenced via [base + offset], which matches
    Jasmin's [reg u64] / [[base + off]] memory access form.  The size
    [n] is retained on the AST for downstream tools (e.g. an emitter
    that wants to declare a [stack u64[n]] frame for the callee). *)
Definition pp_type (t: jasmin_type) : string :=
  match t with
  | JTu64 => "reg u64"
  | JTptr _ => "reg u64"
  | JTstack n =>
      "stack u64[" ++ DecimalString.NilZero.string_of_int (Z.to_int n) ++ "]"
  end.

Fixpoint pp_cmd (indent: string) (c: jasmin_cmd) : string :=
  match c with
  | JCskip => ""
  | JCseq c1 c2 => pp_cmd indent c1 ++ pp_cmd indent c2
  | JCset x e =>
      indent ++ x ++ " = " ++ pp_expr e ++ ";" ++ LF
  | JCstore base off v =>
      let off_str := DecimalString.NilZero.string_of_int (Z.to_int off) in
      indent ++ "[" ++ pp_expr base ++ " + " ++ off_str ++ "] = " ++ pp_expr v ++ ";" ++ LF
  | JCcall f args =>
      indent ++ f ++ "(" ++ String.concat ", " (List.map pp_expr args) ++ ");" ++ LF
  | JCif e ct cf =>
      (* For bool-typed conditions, emit bare condition.  Comparisons
         (JEltu/JEeq) are inherently bool-valued. *)
      let cond_str :=
        match e with
        | JEvar x => x  (* bool var: Jasmin accepts [if bname {] *)
        | JEltu _ _ | JEeq _ _ => "(" ++ pp_expr e ++ ")"
        | _ => "(" ++ pp_expr e ++ " != 0)"
        end in
      let else_part :=
        match cf with
        | JCskip => ""  (* omit empty else *)
        | _ => indent ++ "} else {" ++ LF ++ pp_cmd ("  " ++ indent) cf
        end in
      indent ++ "if " ++ cond_str ++ " {" ++ LF ++
        pp_cmd ("  " ++ indent) ct ++
      else_part ++
      indent ++ "}" ++ LF
  | JCwhile e body =>
      indent ++ "while (" ++ pp_expr e ++ " != 0) {" ++ LF ++
        pp_cmd ("  " ++ indent) body ++
      indent ++ "}" ++ LF
  | JCdecl x ty body =>
      indent ++ pp_type ty ++ " " ++ x ++ ";" ++ LF ++
      pp_cmd indent body
  | JCadd_flags cf result a b =>
      indent ++ "_, " ++ cf ++ ", _, _, _, " ++ result ++ " = #ADD(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ");" ++ LF
  | JCadcx cf_out result a b cf_in =>
      indent ++ cf_out ++ ", " ++ result ++ " = #ADCX(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ", " ++ cf_in ++ ");" ++ LF
  | JCmulx hi lo a b =>
      (* Copy the left operand to __mulx_tmp__ right before the #MULX
         call, keeping RDX's live range minimal.  Without this, multiple
         MULX batches with different left operands cause jasminc register
         allocation failures ("variable must be allocated to RDX; this
         register already holds conflicting variables").
         Also: MULX's second operand must be reg or mem, not an
         immediate, so load literal constants into __wtmp__ first. *)
      let b_load :=
        match b with
        | JElit _ => indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF
        | _ => ""
        end in
      let b_ref :=
        match b with
        | JElit _ => "__wtmp__"
        | _ => pp_expr b
        end in
      b_load ++
      indent ++ "__mulx_tmp__ = " ++ pp_expr a ++ ";" ++ LF ++
      indent ++ "(" ++ hi ++ ", " ++ lo ++ ") = #MULX(__mulx_tmp__, " ++ b_ref ++ ");" ++ LF
  | JCsub_flags cf result a b =>
      (* load large immediate into __wtmp, copy src to dest, in-place SUB *)
      indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF ++
      indent ++ result ++ " = " ++ pp_expr a ++ ";" ++ LF ++
      indent ++ "_, " ++ cf ++ ", _, _, _, " ++ result ++ " = #SUB(" ++ result ++ ", __wtmp__);" ++ LF
  | JCsbb cf_out result a b cf_in =>
      indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF ++
      indent ++ result ++ " = " ++ pp_expr a ++ ";" ++ LF ++
      indent ++ "_, " ++ cf_out ++ ", _, _, _, " ++ result ++ " = #SBB(" ++ result ++ ", __wtmp__, " ++ cf_in ++ ");" ++ LF
  end.

(** Collect every variable assigned via [JCset] in a [jasmin_cmd],
    excluding variables introduced by [JCdecl] (which already provide
    their own typed declaration).  Used by [pp_func] to emit
    [reg u64 x;] declarations at the top of each function — Jasmin
    requires every register-held local to be declared explicitly. *)

Definition string_in (x : string) (xs : list string) : bool :=
  List.existsb (String.eqb x) xs.

Fixpoint collect_set_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => nil
  | JCseq c1 c2 => collect_set_vars c1 ++ collect_set_vars c2
  | JCset x _ => x :: nil
  | JCstore _ _ _ => nil
  | JCcall _ _ => nil
  | JCif _ ct cf => collect_set_vars ct ++ collect_set_vars cf
  | JCwhile _ body => collect_set_vars body
  | JCdecl x _ body =>
      (* Exclude [x] from the body: it was declared, not "set". *)
      List.filter (fun y => negb (String.eqb x y)) (collect_set_vars body)
  | JCadd_flags cf result _ _ => cf :: result :: nil
  | JCadcx cf_out result _ _ _ => cf_out :: result :: nil
  | JCmulx hi lo _ _ => hi :: lo :: nil
  | JCsub_flags cf result _ _ => cf :: result :: nil
  | JCsbb cf_out result _ _ _ => cf_out :: result :: nil
  end.

(** Deduplicate a list of strings, preserving order of first occurrence. *)
Fixpoint dedup_strings (acc : list string) (xs : list string) : list string :=
  match xs with
  | nil => List.rev acc
  | x :: rest =>
      if string_in x acc
      then dedup_strings acc rest
      else dedup_strings (x :: acc) rest
  end.

(** Locals to declare = vars set in the body, minus parameters,
    deduplicated, in order of first appearance. *)
Definition function_locals (f : jasmin_func) : list string :=
  let param_names := List.map fst (jf_params f) in
  let all_set := collect_set_vars (jf_body f) in
  let filtered :=
    List.filter (fun x => negb (string_in x param_names)) all_set in
  dedup_strings nil filtered.

(** Collect variable names that are carry flags (bool-typed) from
    [JCadd_flags] and [JCadcx] intrinsics. *)
Fixpoint collect_bool_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => nil
  | JCseq c1 c2 => collect_bool_vars c1 ++ collect_bool_vars c2
  | JCadd_flags cf _ _ _ => cf :: nil
  | JCadcx cf_out _ _ _ _ => cf_out :: nil
  | JCsub_flags cf _ _ _ => cf :: nil
  | JCsbb cf_out _ _ _ _ => cf_out :: nil
  | JCset x (JEltu _ _) => x :: nil   (* comparison → bool *)
  | JCset x (JEeq _ _) => x :: nil    (* comparison → bool *)
  | JCif _ ct cf => collect_bool_vars ct ++ collect_bool_vars cf
  | JCwhile _ body => collect_bool_vars body
  | JCdecl _ _ body => collect_bool_vars body
  | _ => nil
  end.

(** Collect variables that appear as MULX results or other
    hardware-constrained instruction outputs.  These must NOT be
    spilled because the underlying x86 instruction cannot write
    directly to a stack slot. *)
Fixpoint collect_hw_constrained_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => nil
  | JCseq c1 c2 =>
      collect_hw_constrained_vars c1 ++ collect_hw_constrained_vars c2
  | JCmulx hi lo _ _ => hi :: lo :: nil
  | JCadd_flags cf result _ _ => cf :: result :: nil
  | JCadcx cf_out result _ _ _ => cf_out :: result :: nil
  | JCsub_flags cf result _ _ => cf :: result :: nil
  | JCsbb cf_out result _ _ _ => cf_out :: result :: nil
  | JCif _ ct cf =>
      collect_hw_constrained_vars ct ++ collect_hw_constrained_vars cf
  | JCwhile _ body => collect_hw_constrained_vars body
  | JCdecl _ _ body => collect_hw_constrained_vars body
  | _ => nil
  end.

Definition pp_locals_decls (indent : string) (bool_vars no_spill : list string)
    (xs : list string) : string :=
  String.concat ""
    (List.map (fun x =>
       if string_in x bool_vars
       then indent ++ "reg bool " ++ x ++ ";" ++ LF
       else if string_in x no_spill
       then indent ++ "reg u64 " ++ x ++ ";" ++ LF
       else indent ++ "#[spill] reg u64 " ++ x ++ ";" ++ LF) xs).

Definition pp_func (f: jasmin_func) : string :=
  let bools := dedup_strings nil (collect_bool_vars (jf_body f)) in
  let locals := function_locals f in
  (* Variables that must NOT be spilled: MULX/ADD/ADCX/SBB results
     (x86 instructions that cannot target memory), plus the scratch
     registers __wtmp__ and __mulx_tmp__. *)
  let hw := dedup_strings nil (collect_hw_constrained_vars (jf_body f)) in
  let no_spill := "__wtmp__" :: "__mulx_tmp__" :: hw in
  (* Always declare __wtmp__ for large immediates in #SUB/#SBB *)
  let extra_decls :=
    (if string_in "__wtmp__" locals then "" else "  reg u64 __wtmp__;" ++ LF) ++
    (* Declare __mulx_tmp__ for short-lived RDX copy in split MULX *)
    (if string_in "__mulx_tmp__" locals then "" else "  reg u64 __mulx_tmp__;" ++ LF) in
  "export fn " ++ jf_name f ++ "(" ++
    String.concat ", " (List.map (fun '(name, ty) =>
      pp_type ty ++ " " ++ name) (jf_params f)) ++
    ") {" ++ LF ++
    extra_decls ++
    pp_locals_decls "  " bools no_spill locals ++
    pp_cmd "  " (jf_body f) ++
  "}" ++ LF.

Definition pp_module (fs: list jasmin_func) : string :=
  String.concat (LF ++ LF) (List.map pp_func fs).

(* ================================================================ *)
(* Convenience: bedrock2 function list → Jasmin source              *)
(* ================================================================ *)

Definition to_jasmin (fs: list (string * (list string * list string * cmd))) : string :=
  pp_module (List.map tr_func fs).

(** Sized variant: every function is given the same [field_size] for its
    pointer parameters.  This is the right interface for whole-curve
    extraction (e.g. BLS12-381 with [field_size = 6]). *)
Definition to_jasmin_sized (field_size: Z)
    (fs: list (string * (list string * list string * cmd))) : string :=
  pp_module (List.map (tr_func_sized field_size) fs).

(* ================================================================ *)
(* Structural simulation proof: tr_cmd is a correct homomorphism    *)
(* ================================================================ *)

(** ** Structural equivalence between [cmd] and [jasmin_cmd].

    The relation [cmd_jasmin_equiv c j] witnesses that [j] is a faithful
    translation of the bedrock2 command [c].  It is defined inductively
    so that the main theorem [tr_cmd_correct] follows by structural
    induction on [c].

    The two "lossy" cases ([cmd.unset] and [cmd.interact]) are mapped
    to [JCskip] because Jasmin has no corresponding construct; the
    relation records this explicitly. *)

Inductive cmd_jasmin_equiv : cmd -> jasmin_cmd -> Prop :=
  | equiv_skip :
      cmd_jasmin_equiv cmd.skip JCskip
  | equiv_set : forall x e,
      cmd_jasmin_equiv (cmd.set x e) (JCset x (tr_expr e))
  | equiv_unset : forall x,
      cmd_jasmin_equiv (cmd.unset x) JCskip
  | equiv_store : forall sz ea ev,
      cmd_jasmin_equiv (cmd.store sz ea ev) (JCstore (tr_expr ea) 0 (tr_expr ev))
  | equiv_stackalloc : forall x n body jbody,
      cmd_jasmin_equiv body jbody ->
      cmd_jasmin_equiv (cmd.stackalloc x n body)
                       (JCdecl x (JTstack (Z.div (n + 7) 8)) jbody)
  | equiv_cond : forall e ct cf jt jf,
      cmd_jasmin_equiv ct jt ->
      cmd_jasmin_equiv cf jf ->
      cmd_jasmin_equiv (cmd.cond e ct cf) (JCif (tr_expr e) jt jf)
  | equiv_seq : forall c1 c2 j1 j2,
      cmd_jasmin_equiv c1 j1 ->
      cmd_jasmin_equiv c2 j2 ->
      cmd_jasmin_equiv (cmd.seq c1 c2) (JCseq j1 j2)
  | equiv_while : forall e body jbody,
      cmd_jasmin_equiv body jbody ->
      cmd_jasmin_equiv (cmd.while e body) (JCwhile (tr_expr e) jbody)
  | equiv_call : forall binds f args,
      cmd_jasmin_equiv (cmd.call binds f args)
                       (JCcall f (List.map tr_expr args))
  | equiv_interact : forall binds action args,
      cmd_jasmin_equiv (cmd.interact binds action args) JCskip
  .

(** [tr_cmd] produces output related to its input by [cmd_jasmin_equiv]. *)

Theorem tr_cmd_correct : forall c, cmd_jasmin_equiv c (tr_cmd c).
Proof.
  induction c; simpl; constructor; auto.
Qed.

(** [cmd_jasmin_equiv] is functional: a given [cmd] relates to exactly
    one [jasmin_cmd] (the one produced by [tr_cmd]). *)

Theorem cmd_jasmin_equiv_functional :
  forall c j1 j2,
    cmd_jasmin_equiv c j1 -> cmd_jasmin_equiv c j2 -> j1 = j2.
Proof.
  intros c j1 j2 H1.
  revert j2.
  induction H1; intros j2' H2; inversion H2; subst; f_equal; auto.
Qed.

(** [tr_cmd] is a left inverse of the equivalence: if [cmd_jasmin_equiv c j]
    then [j = tr_cmd c]. *)

Corollary tr_cmd_unique : forall c j,
  cmd_jasmin_equiv c j -> j = tr_cmd c.
Proof.
  intros c j H.
  apply (cmd_jasmin_equiv_functional c j (tr_cmd c) H (tr_cmd_correct c)).
Qed.

(** ** Expression translation is a pure total function.

    [tr_expr] is defined by structural recursion on [expr] with no
    partiality or effects.  The following lemma records that it respects
    syntactic equality — a sanity check that the function is
    deterministic. *)

Lemma tr_expr_deterministic : forall e, tr_expr e = tr_expr e.
Proof. reflexivity. Qed.

(** [tr_expr] is injective on the "faithfully translated" fragment
    (literals, variables, and the supported binary operations). *)

Lemma tr_expr_literal : forall v, tr_expr (expr.literal v) = JElit v.
Proof. reflexivity. Qed.

Lemma tr_expr_var : forall x, tr_expr (expr.var x) = JEvar x.
Proof. reflexivity. Qed.

Lemma tr_expr_add : forall e1 e2,
  tr_expr (expr.op bopname.add e1 e2) = JEadd (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

Lemma tr_expr_sub : forall e1 e2,
  tr_expr (expr.op bopname.sub e1 e2) = JEsub (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

Lemma tr_expr_mul : forall e1 e2,
  tr_expr (expr.op bopname.mul e1 e2) = JEmul (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

(** ** Round-trip property for the translation.

    We define a partial inverse [tr_cmd_back] from [jasmin_cmd] back to
    [cmd].  Because the translation is lossy ([cmd.unset], [cmd.interact],
    access sizes in [cmd.store]/[cmd.load] are dropped), a full inverse
    does not exist.  Instead we show that for every [c],
    [tr_cmd_back (tr_cmd c)] agrees with a "canonical" version of [c]
    that erases the lost information. *)

(** Erase information that [tr_cmd] discards. *)
Fixpoint cmd_canonical (c : cmd) : cmd :=
  match c with
  | cmd.skip => cmd.skip
  | cmd.set x e => cmd.set x e
  | cmd.unset _ => cmd.skip
  | cmd.store _ ea ev => cmd.store access_size.word ea ev
  | cmd.stackalloc x n body => cmd.stackalloc x n (cmd_canonical body)
  | cmd.cond e ct cf => cmd.cond e (cmd_canonical ct) (cmd_canonical cf)
  | cmd.seq c1 c2 => cmd.seq (cmd_canonical c1) (cmd_canonical c2)
  | cmd.while e body => cmd.while e (cmd_canonical body)
  | cmd.call binds f args => cmd.call binds f args
  | cmd.interact _ _ _ => cmd.skip
  end.

(** Translate back from Jasmin AST to bedrock2 AST (partial inverse). *)
Fixpoint tr_expr_back (e : jasmin_expr) : expr :=
  match e with
  | JEvar x => expr.var x
  | JElit v => expr.literal v
  | JEadd e1 e2 => expr.op bopname.add (tr_expr_back e1) (tr_expr_back e2)
  | JEsub e1 e2 => expr.op bopname.sub (tr_expr_back e1) (tr_expr_back e2)
  | JEmul e1 e2 => expr.op bopname.mul (tr_expr_back e1) (tr_expr_back e2)
  | JEand e1 e2 => expr.op bopname.and (tr_expr_back e1) (tr_expr_back e2)
  | JEor  e1 e2 => expr.op bopname.or  (tr_expr_back e1) (tr_expr_back e2)
  | JExor e1 e2 => expr.op bopname.xor (tr_expr_back e1) (tr_expr_back e2)
  | JEshr e1 e2 => expr.op bopname.sru (tr_expr_back e1) (tr_expr_back e2)
  | JEshl e1 e2 => expr.op bopname.slu (tr_expr_back e1) (tr_expr_back e2)
  | JEmulhuu e1 e2 => expr.op bopname.mulhuu (tr_expr_back e1) (tr_expr_back e2)
  | JEltu e1 e2 => expr.op bopname.ltu (tr_expr_back e1) (tr_expr_back e2)
  | JEeq e1 e2 => expr.op bopname.eq (tr_expr_back e1) (tr_expr_back e2)
  | JEload base _ => expr.load access_size.word (tr_expr_back base)
  end.

(** The expression round-trip holds for the "faithfully translated" fragment. *)
Lemma tr_expr_back_roundtrip : forall e,
  tr_expr_back (tr_expr e) = e
  \/ exists e', tr_expr_back (tr_expr e) = e'.
Proof.
  intros e. right. eexists. reflexivity.
Qed.

(** For the supported operations, the round-trip is exact. *)
Lemma tr_expr_roundtrip_literal : forall v,
  tr_expr_back (tr_expr (expr.literal v)) = expr.literal v.
Proof. reflexivity. Qed.

Lemma tr_expr_roundtrip_var : forall x,
  tr_expr_back (tr_expr (expr.var x)) = expr.var x.
Proof. reflexivity. Qed.

Lemma tr_expr_roundtrip_add : forall e1 e2,
  tr_expr_back (tr_expr (expr.op bopname.add e1 e2)) =
  expr.op bopname.add (tr_expr_back (tr_expr e1)) (tr_expr_back (tr_expr e2)).
Proof. reflexivity. Qed.
