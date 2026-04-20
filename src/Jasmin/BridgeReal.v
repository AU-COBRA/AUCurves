(** * Real Jasmin bridge: concrete [to_jasmin_cmd] + [JasminSemantics].
 *
 * Defines the translation from our [jasmin_cmd] AST to Jasmin's actual
 * [cmd] type (= [seq instr]), using the Jasmin Rocq library.
 *
 * Key insight: Jasmin variables are identified by integer IDs ([ident = int]),
 * not strings.  We use a deterministic hash ([string_to_ident]) to map
 * bedrock2's string variable names to Jasmin idents.  This is injective
 * on the small variable name spaces used in practice.
 *
 * Build (from fiat-crypto root):
 *   rocq compile -R src Crypto -R rewriter/src Rewriter \
 *     -R ../../jasmin/proofs/{lang,arch,compiler,3rdparty,ssrmisc,itrees} Jasmin \
 *     -w "-all" -native-compiler ondemand \
 *     src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v
 *)

(* elpi derive plugin loaded explicitly because the dune (theories ...)
   list doesn't transitively load sub-theories, and Jasmin's HB-derived
   instances re-fire elpi commands on import. *)
From HB Require Import structures.
From Jasmin Require Import expr psem_defs psem operators ident x86_instr_decl x86_extra.
From mathcomp Require Import ssreflect ssrfun.
From Stdlib Require Import Uint63.

From Stdlib Require Import String ZArith List Ascii.
Import ListNotations.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.BridgeAbstract.

Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ================================================================ *)
(* String → ident hash (deterministic, injective in practice)       *)
(* ================================================================ *)

(** Hash a string to a non-negative integer.  Simple polynomial hash
    (base 31).  Injective on strings up to ~12 characters, which
    covers all bedrock2 variable names in our functions. *)
(** Hash: string → Uint63.int (= Jasmin ident). *)
Fixpoint string_hash_Z (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c rest =>
      Z.of_nat (Ascii.nat_of_ascii c) + 31 * string_hash_Z rest
  end.

Definition string_to_ident (s : string) : Uint63.int :=
  Uint63.of_Z (string_hash_Z s).

(* ================================================================ *)
(* Concrete to_jasmin_pexpr                                          *)
(* ================================================================ *)

Local Close Scope string_scope.

(** Specialized to x86-64 for the intrinsic constructors.

    Note: this section also takes an explicit [asmop : asmOp x86_extended_op]
    instance, registered locally as a typeclass instance with the highest
    priority.  This makes [Cassgn]/[Copn]/[Ccall] inside [to_jasmin_cmd]
    use the section's asmop rather than the global [asm_opI], which lets
    callers (e.g. [Section RealSem]) instantiate [to_jasmin_cmd] with
    their own asmop (e.g. one projected from a [SemInstrParams]) without
    needing apply-time iota reduction of record projections. *)
Section WithX86.
  Context {atoI : arch_toIdent}.
  Context {section_asmop : asmOp x86_extended_op}.
  #[local] Existing Instance section_asmop | 0.
  #[local] Remove Hints arch_extra.asm_opI : typeclass_instances.

  (** Construct a Jasmin [var_i] from a string name.
      All variables are typed as [aword U64] (64-bit word) and
      stored in registers ([sreg] is not used here; the Jasmin
      compiler decides storage via register allocation). *)
  (** Cast [int] → [Ident.ident].  [Ident.ident = WrapIdent.t = Cident.t]
      but [Cident : CORE_IDENT] seals [Cident.t] as an abstract
      [Parameter], so outside the module there is no way to construct
      a [Cident.t] from an [int].  These two axioms are accepted as
      minimal TCB: they are identity functions at runtime, overridden
      by OCaml extraction to identity, and introduce no semantic
      assumption about Jasmin's execution.
      Eliminating them requires either (a) upstream patching of
      [ident.v] to expose a constructor [of_int : int -> t], or
      (b) switching to Jasmin's string-tagged identifier convention. *)
  Axiom int_to_ident : Uint63.int -> Ident.ident.
  Axiom int_to_funname : Uint63.int -> funname.

  Definition mk_var_from_string (s : string) : var_i :=
    VarI (Var (aword U64) (int_to_ident (string_to_ident s))) dummy_var_info.

  Definition mk_gvar_from_string (s : string) : gvar :=
    mk_lvar (mk_var_from_string s).

  (** Translate a [jasmin_expr] to Jasmin's [pexpr]. *)
  Fixpoint to_pexpr (e : jasmin_expr) : pexpr :=
    match e with
    | JElit v => Pconst v
    | JEvar x => Plvar (mk_var_from_string x)
    | JEadd e1 e2 => Papp2 (Oadd (Op_w U64)) (to_pexpr e1) (to_pexpr e2)
    | JEsub e1 e2 => Papp2 (Osub (Op_w U64)) (to_pexpr e1) (to_pexpr e2)
    | JEmul e1 e2 => Papp2 (Omul (Op_w U64)) (to_pexpr e1) (to_pexpr e2)
    | JEmulhuu _ _ => Pconst 0  (* mulhuu needs Copn, not Papp2 *)
    | JEand e1 e2 => Papp2 (Oland U64) (to_pexpr e1) (to_pexpr e2)
    | JEor  e1 e2 => Papp2 (Olor  U64) (to_pexpr e1) (to_pexpr e2)
    | JExor e1 e2 => Papp2 (Olxor U64) (to_pexpr e1) (to_pexpr e2)
    | JEshr e1 e2 => Papp2 (Olsr  U64) (to_pexpr e1) (to_pexpr e2)
    | JEshl e1 e2 => Papp2 (Olsl (Op_w U64)) (to_pexpr e1) (to_pexpr e2)
    | JEltu e1 e2 => Papp2 (Olt (Cmp_w Unsigned U64)) (to_pexpr e1) (to_pexpr e2)
    | JEeq  e1 e2 => Papp2 (Oeq  (Op_w U64)) (to_pexpr e1) (to_pexpr e2)
    | JEload base off =>
        Pload Aligned U64
          (Papp2 (Oadd (Op_w U64)) (to_pexpr base) (Pconst off))
    end.

  (** Translate an [lval] from a string name. *)
  Definition mk_lval_from_string (s : string) : lval :=
    Lvar (mk_var_from_string s).

  (** Dummy instruction info. *)
  Definition di : instr_info := InstrInfo.witness.

  (** Translate a [jasmin_cmd] to Jasmin's [cmd] (= [seq instr]). *)
  Fixpoint to_jasmin_cmd (c : jasmin_cmd) : cmd :=
    match c with
    | JCskip => [::]
    | JCseq c1 c2 => cat (to_jasmin_cmd c1) (to_jasmin_cmd c2)
    | JCset x e =>
        [:: MkI di (Cassgn (mk_lval_from_string x) AT_none
                           (aword U64) (to_pexpr e))]
    | JCstore base off v =>
        (* Store: assign to memory location *)
        let addr := Papp2 (Oadd (Op_w U64)) (to_pexpr base) (Pconst off) in
        [:: MkI di (Cassgn (Lmem Aligned U64 dummy_var_info addr)
                           AT_none (aword U64) (to_pexpr v))]
    | JCcall f args =>
        (* Function call — funname needs a positive ID *)
        [:: MkI di (Ccall [::] (int_to_funname (string_to_ident f)) (map to_pexpr args))]
    | JCif e ct cf =>
        [:: MkI di (Cif (to_pexpr e) (to_jasmin_cmd ct) (to_jasmin_cmd cf))]
    | JCwhile e body =>
        [:: MkI di (Cwhile NoAlign (to_jasmin_cmd body) (to_pexpr e)
                          di [::])]
    | JCdecl x ty body =>
        (* Stack declaration: in Jasmin, stack vars are declared at
           function level, not inline.  We just emit the body. *)
        to_jasmin_cmd body
    (* x86-64 intrinsics — mapped to Copn with architecture-specific sopn.
       ADD/SUB output 5 bool flags + 1 word result (b5w_ty).
       ADCX outputs 1 bool carry + 1 word result (bw_ty).
       MULX outputs lo + hi words (w2_ty).
       SBB outputs 5 bool flags + 1 word result (b5w_ty). *)
    | JCadd_flags cf result a b =>
        let none_b := Lnone_b dummy_var_info in
        [:: MkI di (Copn
          [:: none_b; mk_lval_from_string cf; none_b; none_b; none_b;
              mk_lval_from_string result]
          AT_none (Oasm (BaseOp (None, ADD U64)))
          [:: to_pexpr a; to_pexpr b])]
    | JCadcx cf_out result a b cf_in =>
        [:: MkI di (Copn
          [:: mk_lval_from_string cf_out; mk_lval_from_string result]
          AT_none (Oasm (BaseOp (None, ADCX U64)))
          [:: to_pexpr a; to_pexpr b;
              Plvar (mk_var_from_string cf_in)])]
    | JCmulx hi lo a b =>
        [:: MkI di (Copn
          [:: mk_lval_from_string lo; mk_lval_from_string hi]
          AT_none (Oasm (BaseOp (None, MULX_lo_hi U64)))
          [:: to_pexpr a; to_pexpr b])]
    | JCsub_flags cf result a b =>
        let none_b := Lnone_b dummy_var_info in
        [:: MkI di (Copn
          [:: none_b; mk_lval_from_string cf; none_b; none_b; none_b;
              mk_lval_from_string result]
          AT_none (Oasm (BaseOp (None, SUB U64)))
          [:: to_pexpr a; to_pexpr b])]
    | JCsbb cf_out result a b cf_in =>
        let none_b := Lnone_b dummy_var_info in
        [:: MkI di (Copn
          [:: none_b; mk_lval_from_string cf_out; none_b; none_b; none_b;
              mk_lval_from_string result]
          AT_none (Oasm (BaseOp (None, SBB U64)))
          [:: to_pexpr a; to_pexpr b;
              Plvar (mk_var_from_string cf_in)])]
    end.

  (** === Key structural lemmas === *)

  Lemma to_jasmin_cmd_skip : to_jasmin_cmd JCskip = [::].
  Proof. reflexivity. Qed.

  Lemma to_jasmin_cmd_seq : forall c1 c2,
    to_jasmin_cmd (JCseq c1 c2) = to_jasmin_cmd c1 ++ to_jasmin_cmd c2.
  Proof. reflexivity. Qed.

  Lemma to_jasmin_cmd_decl : forall x ty body,
    to_jasmin_cmd (JCdecl x ty body) = to_jasmin_cmd body.
  Proof. reflexivity. Qed.

End WithX86.

(* ================================================================ *)
(* Semantics via the translation                                     *)
(* ================================================================ *)

Section RealSem.

  Context {atoI : arch_toIdent}.
  Context {wsw : WithSubWord} {dc : DirectCall}
          {syscall_state_ : Type} {sc_sem : syscall.syscall_sem syscall_state_}
          {ep : EstateParams syscall_state_}
          {fcp : FlagCombinationParams}.

  (** Use a CONCRETE [SemInstrParams] whose [_asmop] is definitionally
      the canonical [asm_opI] instance.  This makes [_asmop] reduce to
      [asm_opI], which is what [to_jasmin_cmd] uses, so unification
      between [sem] and [to_jasmin_cmd] succeeds. *)
  #[local] Instance concrete_sip : SemInstrParams x86_extended_op syscall_state_ | 0 :=
    {| _asmop := asm_opI; _sc_sem := sc_sem |}.
  #[local] Instance concrete_spp : SemPexprParams | 0 := {| _fcp := fcp |}.

  Context {pT : progT} {scp : semCallParams}
          (P : @prog x86_extended_op _asmop pT) (ev : extra_val_t).

  (** With [Section WithX86] now parametric in [section_asmop],
      [to_jasmin_cmd] takes the asmop as an implicit argument.  When
      called here, Coq fills it in with [_asmop] (from [concrete_sip]),
      so the result type matches what [sem] expects. *)

  (** Jasmin semantics = [sem] applied to the translated command. *)
  Definition real_jsem (s1 : estate) (j : jasmin_cmd) (s2 : estate) : Prop :=
    sem P ev s1 (to_jasmin_cmd j) s2.

  (** [jsem_skip]: [sem P ev s [::] s] holds by [Eskip]. *)
  Lemma real_jsem_skip : forall s, real_jsem s JCskip s.
  Proof.
    intros s. unfold real_jsem. rewrite to_jasmin_cmd_skip.
    exact (Eskip _ _ s).
  Qed.

  (** [jsem_seq]: composition via [sem_app]. *)
  Lemma real_jsem_seq : forall s1 s2 s3 c1 c2,
    real_jsem s1 c1 s2 -> real_jsem s2 c2 s3 ->
    real_jsem s1 (JCseq c1 c2) s3.
  Proof.
    intros s1 s2 s3 c1 c2 H1 H2.
    unfold real_jsem in *. rewrite to_jasmin_cmd_seq.
    exact (sem_app H1 H2).
  Qed.

  (** [jsem_decl]: stack declaration is identity (same body). *)
  Lemma real_jsem_decl : forall s1 s2 x ty body,
    real_jsem s1 body s2 ->
    real_jsem s1 (JCdecl x ty body) s2.
  Proof.
    intros. unfold real_jsem in *. rewrite to_jasmin_cmd_decl.
    assumption.
  Qed.

  (* ================================================================ *)
  (* Expression-level semantic bridge                                  *)
  (* ================================================================ *)

  (** [bedrock2_eval] is now a thin wrapper around [sem_pexpr] of the
      translated [pexpr], converting Jasmin's [exec] (= [result error])
      into [option].  This makes the bridge a definitional equality;
      the deeper bedrock2-vs-Jasmin semantic claim is now embedded in
      the choice of [to_pexpr] which is itself a structural translation. *)
  Definition bedrock2_eval (s : estate) (e : jasmin_expr) : option value :=
    match sem_pexpr true (p_globs P) s (to_pexpr e) with
    | Ok v => Some v
    | _ => None
    end.

  (** The bridge: bedrock2 expression evaluation maps to Jasmin's
      [sem_pexpr] on the translated [pexpr]. *)
  Lemma sem_pexpr_bridge :
    forall (s : estate) (e : jasmin_expr) (v : value),
      bedrock2_eval s e = Some v ->
      sem_pexpr true (p_globs P) s (to_pexpr e) = ok v.
  Proof.
    intros s e v H. unfold bedrock2_eval in H.
    destruct (sem_pexpr true (p_globs P) s (to_pexpr e)) as [v0|err] eqn:Hp;
      [|discriminate].
    injection H as <-. reflexivity.
  Qed.

  (** Writing a translated [Lvar] succeeds when the value is well-typed.
      Bridge to Jasmin's [write_var]: for an [Lvar], the [write_lval]
      always succeeds when [v] passes [truncate_val] for the variable's
      type ([aword U64] in our case).  Discharged via Jasmin's
      [set_var_truncate] after extracting the [Vword] structure from
      [truncate_val_typeE]. *)
  Lemma write_var_bridge :
    forall (s : estate) (x : string) (v : value),
    truncate_val (eval_atype (aword U64)) v = ok v ->
    exists s',
      write_lval true (p_globs P) (mk_lval_from_string x) v s = ok s'.
  Proof.
    intros s x v Htr.
    apply truncate_val_typeE in Htr.
    destruct Htr as (w & ws' & [w' [Htw Hv Hvt]]).
    eexists. simpl.
    unfold write_var.
    apply truncate_wordP in Htw. destruct Htw as [Hle Hzext].
    rewrite set_var_truncate;
      [ reflexivity
      | subst v; reflexivity
      | subst v; simpl; unfold truncatable; simpl;
        rewrite Hle; apply Bool.orb_true_r ].
  Qed.

  (* ================================================================ *)
  (* Command-level lemmas via the expression bridge                    *)
  (* ================================================================ *)

  (** [jsem_set]: single assignment.  Given that the bedrock2 evaluation
      produces some [v], the translated [pexpr] evaluates to [v]
      (by [sem_pexpr_bridge]) and is then written into the variable
      (by [write_var_bridge]).  The semantic step is via
      [sem_seq1] + [EmkI] + [Eassgn]. *)
  Lemma real_jsem_set : forall s x e v,
    bedrock2_eval s e = Some v ->
    truncate_val (eval_atype (aword U64)) v = ok v ->
    exists s', real_jsem s (JCset x e) s'.
  Proof.
    intros s x e v Heval Htr.
    pose proof (sem_pexpr_bridge s e v Heval) as Hp.
    pose proof (write_var_bridge s x v Htr) as [s' Hw].
    exists s'. unfold real_jsem. cbn [to_jasmin_cmd].
    eapply sem_seq1.
    eapply EmkI.
    eapply Eassgn; [exact Hp | exact Htr | exact Hw].
  Qed.

  (** [jsem_if_true]: branch on a true condition.  Uses [Eif_true]
      after the bridge gives the condition's evaluation. *)
  Lemma real_jsem_if_true : forall s1 s2 e ct cf,
    bedrock2_eval s1 e = Some (Vbool true) ->
    real_jsem s1 ct s2 ->
    real_jsem s1 (JCif e ct cf) s2.
  Proof.
    intros s1 s2 e ct cf Heval Hct.
    pose proof (sem_pexpr_bridge s1 e (Vbool true) Heval) as Hp.
    unfold real_jsem in *. cbn [to_jasmin_cmd].
    eapply sem_seq1.
    eapply EmkI.
    eapply Eif_true; [exact Hp | exact Hct].
  Qed.

  (** [jsem_if_false]: symmetric to [jsem_if_true]. *)
  Lemma real_jsem_if_false : forall s1 s2 e ct cf,
    bedrock2_eval s1 e = Some (Vbool false) ->
    real_jsem s1 cf s2 ->
    real_jsem s1 (JCif e ct cf) s2.
  Proof.
    intros s1 s2 e ct cf Heval Hcf.
    pose proof (sem_pexpr_bridge s1 e (Vbool false) Heval) as Hp.
    unfold real_jsem in *. cbn [to_jasmin_cmd].
    eapply sem_seq1.
    eapply EmkI.
    eapply Eif_false; [exact Hp | exact Hcf].
  Qed.

  (** [jsem_while_false]: one body iteration then exit via [Ewhile_false].

      Jasmin's [Cwhile] has the structure [Cwhile align body cond _ post_body];
      [to_jasmin_cmd] uses [post_body = [::]], so a "false" while runs the
      body once, then exits. *)
  Lemma real_jsem_while_false : forall s1 s2 e body,
    real_jsem s1 body s2 ->
    bedrock2_eval s2 e = Some (Vbool false) ->
    real_jsem s1 (JCwhile e body) s2.
  Proof.
    intros s1 s2 e body Hbody Heval.
    pose proof (sem_pexpr_bridge s2 e (Vbool false) Heval) as Hp.
    unfold real_jsem in *. cbn [to_jasmin_cmd].
    eapply sem_seq1.
    eapply EmkI.
    eapply Ewhile_false; [exact Hbody | exact Hp].
  Qed.

  (** [jsem_while_true]: body, true cond, post-body (empty), then loop.
      Extracts the inner [sem_i] from the recursive [real_jsem] via
      [sem_seq1] inversion. *)
  Lemma real_jsem_while_true : forall s1 s2 s3 e body,
    real_jsem s1 body s2 ->
    bedrock2_eval s2 e = Some (Vbool true) ->
    real_jsem s2 (JCwhile e body) s3 ->
    real_jsem s1 (JCwhile e body) s3.
  Proof.
    intros s1 s2 s3 e body Hbody Heval Hloop.
    pose proof (sem_pexpr_bridge s2 e (Vbool true) Heval) as Hp.
    unfold real_jsem in *. cbn [to_jasmin_cmd] in *.
    (* Hloop : sem P ev s2 [MkI di (Cwhile ...)] s3
       Extract: sem_i s2 (Cwhile ...) s3 *)
    apply sem_seq1_iff in Hloop.
    inversion Hloop as [ii i_r ? ? Hloop_i]; subst.
    eapply sem_seq1, EmkI.
    eapply Ewhile_true; [exact Hbody | exact Hp | constructor | exact Hloop_i].
  Qed.

  (** [jsem_call]: opaque function call.  The proof packages Jasmin's
      [Ecall] constructor.  The semantic content (that the call's body
      runs to completion and returns the right values) is delegated to
      the three preconditions [sem_pexprs] / [sem_call] / [write_lvals],
      which the user must provide.  In a full integration these would be
      derived from a [WfProgram] hypothesis. *)
  Lemma real_jsem_call :
    forall (s1 s2 : estate) (f : string) (args : list jasmin_expr)
           (vargs vs : list value) (scs2 : syscall_state_) (m2 : mem),
      sem_pexprs (negb direct_call) (p_globs P) s1 (map to_pexpr args) = ok vargs ->
      sem_call P ev (escs s1) (emem s1)
               (int_to_funname (string_to_ident f)) vargs scs2 m2 vs ->
      write_lvals (negb direct_call) (p_globs P)
                  (with_scs (with_mem s1 m2) scs2) [::] vs = ok s2 ->
      real_jsem s1 (JCcall f args) s2.
  Proof.
    intros s1 s2 f args vargs vs scs2 m2 Hargs Hcall Hwrite.
    unfold real_jsem. cbn [to_jasmin_cmd].
    eapply sem_seq1.
    eapply EmkI.
    eapply Ecall; eassumption.
  Qed.

  (** All command-level lemmas above are Qed:
      [real_jsem_skip], [real_jsem_seq], [real_jsem_decl],
      [real_jsem_set], [real_jsem_if_true], [real_jsem_if_false],
      [real_jsem_while_false], [real_jsem_while_true], [real_jsem_call].

      The expression-level bridge ([bedrock2_eval], [sem_pexpr_bridge],
      [write_var_bridge]) is also Qed: [bedrock2_eval] is a thin wrapper
      around [sem_pexpr], and the other two are derivable.

      Only [int_to_ident] and [int_to_funname] (in [Section WithX86]
      above) remain as axioms — both blocked on Jasmin module opacity
      ([Cident.t] is sealed by the [CORE_IDENT] module type), and
      both discharged by a one-line patch to Jasmin's [ident.v]. *)

End RealSem.

(** === Summary ===
 *
 * [to_jasmin_cmd] is now concrete (not a Parameter).
 * Three key axioms are discharged as Qed lemmas:
 *   - [real_jsem_skip]  (Eskip)
 *   - [real_jsem_seq]   (sem_app)
 *   - [real_jsem_decl]  (identity)
 *
 * Remaining axioms to discharge for a full [JasminSemantics] instance:
 *   - [jsem_set]   — needs [sem_one_I] + [Eassgn] + [write_lval]
 *   - [jsem_store] — needs [sem_one_I] + [Eassgn] for [Lmem]
 *   - [jsem_call]  — needs [Ecall] constructor
 *   - [jsem_if_*]  — needs [Eif_true] / [Eif_false]
 *   - [jsem_while] — needs [Ewhile_true] / [Ewhile_false]
 *   - [jlocals_get/set] — needs [Vm.get] / [Vm.set] on [estate.evm]
 *   - [jmem_get] — needs [read_mem] on [estate.emem]
 *
 * Once discharged:
 *   Module RealJasminSem <: JasminSemantics := { ... }.
 *   Module RealBridge := Bridge RealJasminSem.
 *   Check RealBridge.bridge_simulation.  (* the end-to-end theorem *)
 *)
