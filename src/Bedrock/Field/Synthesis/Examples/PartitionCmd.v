(** * PartitionCmd: verified partitioning pass for jasmin_cmd.
 *
 * Transforms a flat [jasmin_cmd] (right-associated chain of [JCseq])
 * into a sequence of smaller blocks, each wrapped in [JCdecl] scopes
 * for its local variables.  This bounds register pressure within each
 * block, enabling jasminc's register allocator to succeed on large
 * Montgomery multiplication bodies.
 *
 * The correctness proof rests on two semantic properties:
 *   1. [JCseq] is associative in [jeval] (sequential composition).
 *   2. [JCdecl] is transparent in [jeval] (scoping is a no-op
 *      in our variable-store semantics).
 *
 * Pipeline position:
 *   bedrock2 cmd -> tr_cmd (Qed) -> jasmin_cmd
 *     -> partition_cmd (this file, Qed) -> jasmin_cmd
 *     -> polish_func -> to_jasmin_cmd (Qed) -> Jasmin cmd
 *
 * Self-contained: inlines the jasmin AST and semantics definitions
 * to avoid requiring pre-compiled .vo dependencies.
 *)

From Stdlib Require Import ZArith String Bool List Lia.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ================================================================ *)
(* Jasmin AST (inlined from ToJasmin.v)                             *)
(* ================================================================ *)

Inductive jasmin_type :=
  | JTu64
  | JTptr (n: Z)
  | JTstack (n: Z)
  .

Inductive jasmin_expr :=
  | JEvar (x: string)
  | JElit (v: Z)
  | JEadd (e1 e2: jasmin_expr)
  | JEsub (e1 e2: jasmin_expr)
  | JEmul (e1 e2: jasmin_expr)
  | JEmulhuu (e1 e2: jasmin_expr)
  | JEand (e1 e2: jasmin_expr)
  | JEor  (e1 e2: jasmin_expr)
  | JExor (e1 e2: jasmin_expr)
  | JEshr (e1 e2: jasmin_expr)
  | JEshl (e1 e2: jasmin_expr)
  | JEltu (e1 e2: jasmin_expr)
  | JEeq  (e1 e2: jasmin_expr)
  | JEload (base: jasmin_expr) (offset: Z)
  .

Inductive jasmin_cmd :=
  | JCskip
  | JCseq (c1 c2: jasmin_cmd)
  | JCset (x: string) (e: jasmin_expr)
  | JCstore (base: jasmin_expr) (offset: Z) (v: jasmin_expr)
  | JCcall (f: string) (args: list jasmin_expr)
  | JCif (e: jasmin_expr) (ct cf: jasmin_cmd)
  | JCwhile (e: jasmin_expr) (body: jasmin_cmd)
  | JCdecl (x: string) (ty: jasmin_type) (body: jasmin_cmd)
  | JCadd_flags (cf result: string) (a b: jasmin_expr)
  | JCadcx (cf_out result: string) (a b: jasmin_expr) (cf_in: string)
  | JCmulx (hi lo: string) (a b: jasmin_expr)
  | JCsub_flags (cf result: string) (a b: jasmin_expr)
  | JCsbb (cf_out result: string) (a b: jasmin_expr) (cf_in: string)
  .

Record jasmin_func := {
  jf_name: string;
  jf_params: list (string * jasmin_type);
  jf_locals: list (string * jasmin_type);
  jf_body: jasmin_cmd;
}.

(* ================================================================ *)
(* Section 1: Flattening JCseq chains to lists                      *)
(* ================================================================ *)

Fixpoint flatten_seq (c : jasmin_cmd) : list jasmin_cmd :=
  match c with
  | JCseq c1 c2 => flatten_seq c1 ++ flatten_seq c2
  | _ => [c]
  end.

Fixpoint unflatten (cs : list jasmin_cmd) : jasmin_cmd :=
  match cs with
  | [] => JCskip
  | [c] => c
  | c :: rest => JCseq c (unflatten rest)
  end.

(* ================================================================ *)
(* Section 2: Collecting assigned variables                         *)
(* ================================================================ *)

Fixpoint assigned_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => []
  | JCseq c1 c2 => assigned_vars c1 ++ assigned_vars c2
  | JCset x _ => [x]
  | JCstore _ _ _ => []
  | JCcall _ _ => []
  | JCif _ ct cf => assigned_vars ct ++ assigned_vars cf
  | JCwhile _ body => assigned_vars body
  | JCdecl _ _ body => assigned_vars body
  | JCadd_flags cf r _ _ => [cf; r]
  | JCadcx co r _ _ _ => [co; r]
  | JCmulx h l _ _ => [h; l]
  | JCsub_flags cf r _ _ => [cf; r]
  | JCsbb co r _ _ _ => [co; r]
  end.

Fixpoint string_mem (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else string_mem x ys
  end.

Fixpoint dedup (xs : list string) : list string :=
  match xs with
  | [] => []
  | x :: rest =>
      if string_mem x rest then dedup rest else x :: dedup rest
  end.

Fixpoint wrap_decls (vars : list string) (body : jasmin_cmd) : jasmin_cmd :=
  match vars with
  | [] => body
  | x :: rest => JCdecl x JTu64 (wrap_decls rest body)
  end.

(* ================================================================ *)
(* Section 3: The partition_cmd function                            *)
(* ================================================================ *)

(** Split a list into chunks of size [n].  Uses [fuel] to guarantee
    termination (fuel = length of the input list). *)
Fixpoint chunk_list_aux {A : Type} (n : nat) (fuel : nat) (xs : list A)
    : list (list A) :=
  match fuel with
  | O => match xs with [] => [] | _ => [xs] end
  | S fuel' =>
      match xs with
      | [] => []
      | _ =>
          match n with
          | O => [xs]
          | S _ => firstn n xs :: chunk_list_aux n fuel' (skipn n xs)
          end
      end
  end.

Definition chunk_list {A : Type} (n : nat) (xs : list A) : list (list A) :=
  chunk_list_aux n (length xs) xs.

Definition build_block (stmts : list jasmin_cmd) : jasmin_cmd :=
  let body := unflatten stmts in
  let vars := dedup (assigned_vars body) in
  wrap_decls vars body.

Definition partition_cmd (n : nat) (c : jasmin_cmd) : jasmin_cmd :=
  let stmts := flatten_seq c in
  let chunks := chunk_list n stmts in
  let blocks := List.map build_block chunks in
  unflatten blocks.

(* ================================================================ *)
(* Section 4: Abstract semantics and correctness proof              *)
(* ================================================================ *)

Section WithWord.

  Variable word : Type.
  Variable word_of_Z : Z -> word.
  Variable word_add : word -> word -> word.
  Variable word_sub : word -> word -> word.
  Variable word_mul : word -> word -> word.
  Variable word_and : word -> word -> word.
  Variable word_or  : word -> word -> word.
  Variable word_xor : word -> word -> word.
  Variable word_sru : word -> word -> word.
  Variable word_slu : word -> word -> word.
  Variable word_ltu : word -> word -> bool.
  Variable word_eqb : word -> word -> bool.

  Definition env := string -> word.

  Definition update (e : env) (x : string) (w : word) : env :=
    fun y => if String.eqb y x then w else e y.

  Fixpoint eval_jexpr (ev : env) (e : jasmin_expr) : option word :=
    match e with
    | JElit v => Some (word_of_Z v)
    | JEvar x => Some (ev x)
    | JEadd e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_add v1 v2)
        | _, _ => None
        end
    | JEsub e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_sub v1 v2)
        | _, _ => None
        end
    | JEmul e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_mul v1 v2)
        | _, _ => None
        end
    | JEand e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_and v1 v2)
        | _, _ => None
        end
    | JEor e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_or v1 v2)
        | _, _ => None
        end
    | JExor e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_xor v1 v2)
        | _, _ => None
        end
    | JEshr e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_sru v1 v2)
        | _, _ => None
        end
    | JEshl e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 => Some (word_slu v1 v2)
        | _, _ => None
        end
    | JEltu e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 =>
            Some (if word_ltu v1 v2 then word_of_Z 1 else word_of_Z 0)
        | _, _ => None
        end
    | JEeq e1 e2 =>
        match eval_jexpr ev e1, eval_jexpr ev e2 with
        | Some v1, Some v2 =>
            Some (if word_eqb v1 v2 then word_of_Z 1 else word_of_Z 0)
        | _, _ => None
        end
    | JEmulhuu _ _ => None
    | JEload _ _ => None
    end.

  Inductive jeval : env -> jasmin_cmd -> env -> Prop :=
  | jeval_skip : forall e, jeval e JCskip e
  | jeval_seq : forall e1 e2 e3 c1 c2,
      jeval e1 c1 e2 -> jeval e2 c2 e3 ->
      jeval e1 (JCseq c1 c2) e3
  | jeval_set : forall e x ex w,
      eval_jexpr e ex = Some w ->
      jeval e (JCset x ex) (update e x w)
  | jeval_decl : forall e x ty body e',
      jeval e body e' ->
      jeval e (JCdecl x ty body) e'
  | jeval_if_true : forall e econd ct cf w e',
      eval_jexpr e econd = Some w ->
      w <> word_of_Z 0 ->
      jeval e ct e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_if_false : forall e econd ct cf e',
      eval_jexpr e econd = Some (word_of_Z 0) ->
      jeval e cf e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_while_false : forall e econd body,
      eval_jexpr e econd = Some (word_of_Z 0) ->
      jeval e (JCwhile econd body) e
  | jeval_while_true : forall e e' e'' econd body w,
      eval_jexpr e econd = Some w ->
      w <> word_of_Z 0 ->
      jeval e body e' ->
      jeval e' (JCwhile econd body) e'' ->
      jeval e (JCwhile econd body) e''
  | jeval_store : forall e base off v vbase vv,
      eval_jexpr e base = Some vbase ->
      eval_jexpr e v = Some vv ->
      jeval e (JCstore base off v) e
  | jeval_call : forall e f args,
      jeval e (JCcall f args) e
  | jeval_add_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadd_flags cf r a b)
        (update (update e cf (word_of_Z 0)) r (word_add va vb))
  | jeval_adcx : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadcx co r a b ci)
        (update (update e co (word_of_Z 0)) r (word_add va vb))
  | jeval_mulx : forall e h l a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCmulx h l a b)
        (update (update e h (word_of_Z 0)) l (word_mul va vb))
  | jeval_sub_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsub_flags cf r a b)
        (update (update e cf (word_of_Z 0)) r (word_sub va vb))
  | jeval_sbb : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsbb co r a b ci)
        (update (update e co (word_of_Z 0)) r (word_sub va vb))
  .

  (* -------------------------------------------------------------- *)
  (* Key lemma 1: wrap_decls is transparent                         *)
  (* -------------------------------------------------------------- *)

  Lemma wrap_decls_correct :
    forall vars body e e',
      jeval e body e' ->
      jeval e (wrap_decls vars body) e'.
  Proof.
    induction vars as [|x rest IH]; intros; simpl.
    - assumption.
    - apply jeval_decl. apply IH. assumption.
  Qed.

  Lemma wrap_decls_complete :
    forall vars body e e',
      jeval e (wrap_decls vars body) e' ->
      jeval e body e'.
  Proof.
    induction vars as [|x rest IH]; intros; simpl in *.
    - assumption.
    - inversion H; subst. eapply IH. eassumption.
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 2: list-based sequential semantics                   *)
  (* -------------------------------------------------------------- *)

  Inductive jeval_list : env -> list jasmin_cmd -> env -> Prop :=
  | jeval_list_nil : forall e, jeval_list e [] e
  | jeval_list_cons : forall e1 e2 e3 c cs,
      jeval e1 c e2 -> jeval_list e2 cs e3 ->
      jeval_list e1 (c :: cs) e3.

  Lemma jeval_list_app :
    forall cs1 cs2 e1 e2 e3,
      jeval_list e1 cs1 e2 ->
      jeval_list e2 cs2 e3 ->
      jeval_list e1 (cs1 ++ cs2) e3.
  Proof.
    induction cs1 as [|c cs1 IH]; intros; simpl.
    - inversion H; subst. assumption.
    - inversion H; subst.
      econstructor; [eassumption | eapply IH; eassumption].
  Qed.

  Lemma jeval_list_app_inv :
    forall cs1 cs2 e1 e3,
      jeval_list e1 (cs1 ++ cs2) e3 ->
      exists e2, jeval_list e1 cs1 e2 /\ jeval_list e2 cs2 e3.
  Proof.
    induction cs1 as [|c cs1 IH]; intros; simpl in *.
    - exists e1. split; [constructor | assumption].
    - inversion H; subst.
      destruct (IH _ _ _ H5) as [e2' [? ?]].
      exists e2'. split; [econstructor; eassumption | assumption].
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 3: unflatten <-> jeval_list                          *)
  (* -------------------------------------------------------------- *)

  Lemma unflatten_jeval :
    forall cs e e',
      jeval_list e cs e' ->
      jeval e (unflatten cs) e'.
  Proof.
    induction cs as [|c cs IH]; intros.
    - inversion H; subst. constructor.
    - inversion H; subst.
      destruct cs as [|c2 cs'].
      + inversion H5; subst. assumption.
      + simpl. econstructor; [eassumption | apply IH; assumption].
  Qed.

  Lemma jeval_unflatten_inv :
    forall cs e e',
      jeval e (unflatten cs) e' ->
      jeval_list e cs e'.
  Proof.
    induction cs as [|c cs IH]; intros; simpl in *.
    - inversion H; subst. constructor.
    - destruct cs as [|c2 cs'].
      + econstructor; [eassumption | constructor].
      + simpl in H. inversion H; subst.
        econstructor; [eassumption | apply IH; assumption].
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 4: flatten_seq <-> jeval                             *)
  (* -------------------------------------------------------------- *)

  Lemma flatten_seq_correct :
    forall c e e',
      jeval e c e' ->
      jeval_list e (flatten_seq c) e'.
  Proof.
    induction c; intros; simpl;
      try (econstructor; [eassumption | constructor]).
    (* JCseq *)
    inversion H; subst.
    eapply jeval_list_app; [eapply IHc1 | eapply IHc2]; eassumption.
  Qed.

  Lemma flatten_seq_complete :
    forall c e e',
      jeval_list e (flatten_seq c) e' ->
      jeval e c e'.
  Proof.
    induction c; intros; simpl in *;
      try (inversion H; subst; inversion H5; subst; assumption).
    (* JCseq *)
    apply jeval_list_app_inv in H.
    destruct H as [e2 [? ?]].
    econstructor; [eapply IHc1 | eapply IHc2]; eassumption.
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 5: build_block preserves jeval                       *)
  (* -------------------------------------------------------------- *)

  Lemma build_block_correct :
    forall stmts e e',
      jeval_list e stmts e' ->
      jeval e (build_block stmts) e'.
  Proof.
    intros. unfold build_block.
    apply wrap_decls_correct.
    apply unflatten_jeval.
    assumption.
  Qed.

  Lemma build_block_complete :
    forall stmts e e',
      jeval e (build_block stmts) e' ->
      jeval_list e stmts e'.
  Proof.
    intros. unfold build_block in H.
    apply jeval_unflatten_inv.
    apply wrap_decls_complete in H.
    assumption.
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 6: chunk_list_aux preserves jeval_list               *)
  (* -------------------------------------------------------------- *)

  (** Helper: skipn on a nonempty list with positive n reduces length *)
  Lemma skipn_length_lt :
    forall {A : Type} (n : nat) (x : A) (xs : list A),
      (n > 0)%nat -> (length (skipn n (x :: xs)) < S (length xs))%nat.
  Proof.
    intros. rewrite skipn_length. simpl. destruct n; lia.
  Qed.

  (** We prove the chunk lemma on chunk_list_aux directly, using
      well-founded induction on fuel. *)
  Lemma jeval_list_chunk_aux :
    forall fuel n stmts e e',
      (n > 0)%nat ->
      (length stmts <= fuel)%nat ->
      jeval_list e stmts e' ->
      jeval_list e (List.concat (chunk_list_aux n fuel stmts)) e'.
  Proof.
    induction fuel as [|fuel' IH]; intros.
    - destruct stmts; simpl.
      + inversion H1; subst. constructor.
      + simpl in H0. lia.
    - destruct stmts as [|s rest].
      + simpl. inversion H1; subst. constructor.
      + simpl. destruct n as [|n']; [lia|]. simpl.
        inversion H1; subst.
        econstructor; [eassumption|].
        rewrite <- (firstn_skipn n' rest) in H7.
        apply jeval_list_app_inv in H7.
        destruct H7 as [emid [Hfst Hskp]].
        eapply jeval_list_app; [exact Hfst|].
        apply IH; [lia | | exact Hskp].
        rewrite skipn_length. simpl in H0. lia.
  Qed.

  Lemma chunk_aux_jeval_list :
    forall fuel n stmts e e',
      (n > 0)%nat ->
      (length stmts <= fuel)%nat ->
      jeval_list e (List.concat (chunk_list_aux n fuel stmts)) e' ->
      jeval_list e stmts e'.
  Proof.
    induction fuel as [|fuel' IH]; intros.
    - destruct stmts; simpl in *.
      + inversion H1; subst. constructor.
      + lia.
    - destruct stmts as [|s rest].
      + simpl in H1. inversion H1; subst. constructor.
      + simpl in H1. destruct n as [|n']; [lia|]. simpl in H1.
        inversion H1; subst.
        econstructor; [eassumption|].
        rewrite <- (firstn_skipn n' rest).
        apply jeval_list_app_inv in H7.
        destruct H7 as [emid [Hfst Hskp]].
        eapply jeval_list_app; [exact Hfst|].
        apply (IH (S n')); [lia | | exact Hskp].
        rewrite skipn_length. simpl in H0. lia.
  Qed.

  Lemma jeval_list_chunks :
    forall n stmts e e',
      (n > 0)%nat ->
      jeval_list e stmts e' ->
      jeval_list e (List.concat (chunk_list n stmts)) e'.
  Proof.
    intros. unfold chunk_list.
    eapply jeval_list_chunk_aux; eauto.
  Qed.

  Lemma chunks_jeval_list :
    forall n stmts e e',
      (n > 0)%nat ->
      jeval_list e (List.concat (chunk_list n stmts)) e' ->
      jeval_list e stmts e'.
  Proof.
    intros. unfold chunk_list in H0.
    eapply chunk_aux_jeval_list; eauto.
  Qed.

  (* -------------------------------------------------------------- *)
  (* Key lemma 7: map build_block preserves jeval_list              *)
  (* -------------------------------------------------------------- *)

  Lemma jeval_list_map_build_block :
    forall chunks e e',
      jeval_list e (List.concat chunks) e' ->
      jeval_list e (List.map build_block chunks) e'.
  Proof.
    induction chunks as [|chunk rest IH]; intros; simpl in *.
    - inversion H; subst. constructor.
    - apply jeval_list_app_inv in H.
      destruct H as [emid [? ?]].
      econstructor.
      + apply build_block_correct. eassumption.
      + apply IH. assumption.
  Qed.

  Lemma jeval_list_map_build_block_inv :
    forall chunks e e',
      jeval_list e (List.map build_block chunks) e' ->
      jeval_list e (List.concat chunks) e'.
  Proof.
    induction chunks as [|chunk rest IH]; intros; simpl in *.
    - inversion H; subst. constructor.
    - inversion H; subst.
      apply build_block_complete in H3.
      eapply jeval_list_app.
      + eassumption.
      + apply IH. assumption.
  Qed.

  (* ================================================================ *)
  (* Main theorems                                                     *)
  (* ================================================================ *)

  Theorem partition_cmd_correct :
    forall n c e e',
      (n > 0)%nat ->
      jeval e c e' ->
      jeval e (partition_cmd n c) e'.
  Proof.
    intros n c e e' Hn Heval.
    unfold partition_cmd.
    apply unflatten_jeval.
    apply jeval_list_map_build_block.
    apply jeval_list_chunks; [exact Hn|].
    apply flatten_seq_correct.
    exact Heval.
  Qed.

  Theorem partition_cmd_complete :
    forall n c e e',
      (n > 0)%nat ->
      jeval e (partition_cmd n c) e' ->
      jeval e c e'.
  Proof.
    intros n c e e' Hn Heval.
    unfold partition_cmd in Heval.
    apply jeval_unflatten_inv in Heval.
    apply jeval_list_map_build_block_inv in Heval.
    apply chunks_jeval_list in Heval; [|exact Hn].
    apply flatten_seq_complete.
    exact Heval.
  Qed.

  Corollary partition_cmd_equiv :
    forall n c e e',
      (n > 0)%nat ->
      (jeval e c e' <-> jeval e (partition_cmd n c) e').
  Proof.
    intros. split.
    - apply partition_cmd_correct. assumption.
    - apply partition_cmd_complete. assumption.
  Qed.

  (* ================================================================ *)
  (* Lifted to jasmin_func                                            *)
  (* ================================================================ *)

  Definition partition_func (n : nat) (f : jasmin_func) : jasmin_func :=
    {| jf_name := jf_name f;
       jf_params := jf_params f;
       jf_locals := jf_locals f;
       jf_body := partition_cmd n (jf_body f) |}.

End WithWord.

(* ================================================================ *)
(* Summary                                                           *)
(* ================================================================ *)

(** This file provides:
 *
 * 1. [partition_cmd n c]: splits a [jasmin_cmd] into blocks of at
 *    most [n] statements, each wrapped in [JCdecl] scopes.
 *
 * 2. [partition_cmd_correct] (Qed): if [jeval e c e'], then
 *    [jeval e (partition_cmd n c) e'].
 *
 * 3. [partition_cmd_complete] (Qed): the converse -- partitioning
 *    does not introduce new behaviors.
 *
 * 4. [partition_cmd_equiv] (Qed): the biconditional.
 *
 * 5. [partition_func]: lifts the pass to [jasmin_func].
 *
 * The proofs rest on:
 *   - [JCdecl] transparency: [jeval_decl] says [JCdecl] just runs
 *     the body, so [wrap_decls] is semantically invisible.
 *   - [JCseq] associativity: restructuring the sequential spine
 *     (flattening then unflattening) preserves the execution trace.
 *   - List chunking: [chunk_list n xs] partitions a list such that
 *     [concat (chunk_list n xs)] has the same jeval_list semantics
 *     as [xs] (proved by induction on fuel with length bound).
 *)
