(** * AdcChain: fiat's carry and borrow windows as [#ADCX] / [#SBB] chains.

    fiat-crypto's bedrock2 Montgomery multiply spells every
    [addcarryx(c, a, b)] as five assignments,

      [s = c + a; c1 = s <u a; r = s + b; c2 = r <u b; co = c1 + c2],

    and every [subborrowx(c, a, B)] of the final conditional subtraction
    as [t = a - B; b1 = a <u t; r = t - c; b2 = t <u r; bo = b1 + b2].
    [carry_func] matches neither, and [lower_comparisons] turns each
    comparison into a data-dependent branch.  [adc_func] rewrites each
    such window into one [#ADCX] / [#SBB] when the carry-in [c] is known
    to be 0 or 1 and the intermediates are not read afterwards (also the
    first limb [t = a - B; b1 = a <u t] into [#SUB] and the last limb
    [r = a - c; bo = a <u r] into [#SBB]).  The carry-out stays in a
    boolean (the CPU carry flag, after jasminc's allocation) and is
    consumed by the next window directly; it is copied into its [u64]
    variable only when something else reads it, by the branch-free
    [co = 0; _, co = #ADCX(co, co, cf)].

    Correctness ([adc_cmd_correct]) is stated against [run], a
    semantics of the straight-line fragment with memory in which
    [#ADD]/[#ADCX]/[#SUB]/[#SBB] compute their real carries and borrows
    (the [jeval] of [PolishProofs.v] gives them a placeholder carry of
    0, so it cannot express this pass): whenever the original command
    runs, the rewritten one runs to the same final memory.  The leaves
    return through memory only, so that is their whole observable
    behaviour.

    New variable names all start with ["__adc"]; [adc_cmd] leaves a
    body that already mentions such a name unchanged. *)

Require Import Bedrock.Jasmin.Core.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
From Stdlib Require Import String List ZArith Bool Lia.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* Names                                                             *)
(* ================================================================ *)

Fixpoint vars_of (e : jasmin_expr) : list string :=
  match e with
  | JEvar x => [x]
  | JElit _ => []
  | JEadd a b | JEsub a b | JEmul a b | JEmulhuu a b | JEand a b
  | JEor a b | JExor a b | JEshr a b | JEshl a b | JEltu a b | JEeq a b =>
      vars_of a ++ vars_of b
  | JEload b _ => vars_of b
  end.

(** Every variable a command reads or writes. *)
Fixpoint names (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => []
  | JCseq a b => names a ++ names b
  | JCset y e => y :: vars_of e
  | JCstore b _ v => vars_of b ++ vars_of v
  | JCcall _ args => flat_map vars_of args
  | JCif e a b => vars_of e ++ names a ++ names b
  | JCwhile e b => vars_of e ++ names b
  | JCdecl y _ b => y :: names b
  | JCadd_flags cf r a b | JCsub_flags cf r a b => cf :: r :: vars_of a ++ vars_of b
  | JCadcx co r a b ci | JCsbb co r a b ci => co :: r :: ci :: vars_of a ++ vars_of b
  | JCmulx h l a b => h :: l :: vars_of a ++ vars_of b
  end.

Definition mentions (x : string) (k : jasmin_cmd) : bool := existsb (String.eqb x) (names k).

Lemma mentions_In : forall x k, mentions x k = true <-> In x (names k).
Proof.
  intros. unfold mentions. rewrite existsb_exists. split.
  - intros [y [H E]]. apply String.eqb_eq in E. subst. exact H.
  - intros H. exists x. split; [exact H | apply String.eqb_refl].
Qed.

Definition helper (x : string) : bool := String.prefix "__adc" x.

Definition fl_of (co : string) : string := String.append "__adc_cf_" co.
Definition fi_of (co : string) : string := String.append "__adc_ci_" co.
Definition ti_of (co : string) : string := String.append "__adc_t_" co.
Definition mi_of (x : string) : string := String.append "__adc_m_" x.

Lemma helper_fl : forall s, helper (fl_of s) = true. Proof. reflexivity. Qed.
Lemma helper_fi : forall s, helper (fi_of s) = true. Proof. reflexivity. Qed.
Lemma helper_ti : forall s, helper (ti_of s) = true. Proof. reflexivity. Qed.
Lemma helper_mi : forall s, helper (mi_of s) = true. Proof. reflexivity. Qed.

Lemma helper_neq : forall x y, helper x = true -> helper y = false -> x <> y.
Proof. intros x y Hx Hy ->. congruence. Qed.

Lemma length_append : forall p s,
  String.length (String.append p s) = String.length p + String.length s.
Proof. induction p; intros; cbn; [reflexivity | rewrite IHp; reflexivity]. Qed.

Lemma append_neq_self : forall p s, p <> "" -> String.append p s <> s.
Proof.
  intros p s Hp E. apply (f_equal String.length) in E.
  rewrite length_append in E. destruct p; [congruence|]. cbn in E. lia.
Qed.

(* ================================================================ *)
(* The pass                                                           *)
(* ================================================================ *)

(** Commands that compile to moves only, so a carry flag survives
    them.  Not needed for correctness: it only keeps the boolean that
    holds a pending carry allocatable to the flag by jasminc. *)
Definition flag_neutral (c : jasmin_cmd) : bool :=
  match c with
  | JCset _ (JEvar _) | JCset _ (JElit _) | JCset _ (JEload _ _) => true
  | JCstore _ _ (JEvar _) | JCstore _ _ (JElit _) => true
  | JCmulx _ _ _ _ => true
  | _ => false
  end.

(** Copy the carry held in [fl] into [x], without a branch. *)
Definition materialize (x fl : string) : list jasmin_cmd :=
  [JCset x (JElit 0); JCadcx (mi_of x) x (JEvar x) (JEvar x) fl].

Definition flush (p : option (string * string)) : list jasmin_cmd :=
  match p with Some (x, fl) => materialize x fl | None => [] end.

Definition pend_hit (p : option (string * string)) (k : jasmin_cmd) : bool :=
  match p with Some (x, fl) => mentions x k || mentions fl k | None => false end.

(** Variables known to hold 0 or 1 after [k]. *)
Definition bits_after (bits : list string) (k : jasmin_cmd) : list string :=
  filter (fun v => negb (mentions v k)) bits ++
  (match k with JCset x (JEltu _ _) => [x] | _ => [] end).

(** [carry_func]'s first add of a chain:
    [_, fl, .., s = #ADD(a, b); x = 0; if fl { x = 1; }]. *)
Definition match_first_add (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * string * jasmin_expr * jasmin_expr * string * list jasmin_cmd) :=
  match k1, rest1 with
  | JCadd_flags fl s a b,
    JCset x (JElit z0) :: JCif (JEvar fl') (JCset x' (JElit z1)) JCskip :: rest =>
      if String.eqb fl fl' && String.eqb x x' && negb (String.eqb x fl)
         && Z.eqb z0 0 && Z.eqb z1 1
      then Some (fl, s, a, b, x, rest) else None
  | _, _ => None
  end.

Definition notin (x : string) (l : list string) : bool := negb (existsb (String.eqb x) l).

(** The window's five results are distinct and distinct from its
    three inputs, and the carry-in is distinct from the addends. *)
Definition window_names_ok (c a b s c1 r c2 co : string) : bool :=
  notin s [c1; r; c2; co] && notin c1 [r; c2; co] && notin r [c2; co] && notin c2 [co] &&
  forallb (fun o => notin o [c; a; b]) [s; c1; r; c2; co] &&
  notin c [a; b].

Definition match_window (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * string * string * string * string * string * string * string
              * list jasmin_cmd) :=
  match k1, rest1 with
  | JCset s (JEadd (JEvar c) (JEvar a)),
    JCset c1 (JEltu (JEvar s') (JEvar a')) ::
    JCset r (JEadd (JEvar s'') (JEvar b)) ::
    JCset c2 (JEltu (JEvar r') (JEvar b')) ::
    JCset co (JEadd (JEvar c1') (JEvar c2')) :: rest =>
      if String.eqb s s' && String.eqb s s'' && String.eqb a a' && String.eqb b b'
         && String.eqb r r' && String.eqb c1 c1' && String.eqb c2 c2'
         && window_names_ok c a b s c1 r c2 co
      then Some (c, a, b, s, c1, r, c2, co, rest) else None
  | _, _ => None
  end.

(** fiat's [subborrowx(c, a, B)]:
    [t = a - B; b1 = a <u t; r = t - c; b2 = t <u r; bo = b1 + b2]. *)
Definition simple_arg (e : jasmin_expr) : option (list string) :=
  match e with JEvar y => Some [y] | JElit _ => Some [] | _ => None end.

Definition match_sbb_window (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * string * jasmin_expr * string * string * string * string * string
              * list jasmin_cmd) :=
  match k1, rest1 with
  | JCset t (JEsub (JEvar a) bB),
    JCset b1 (JEltu (JEvar a1) (JEvar t1)) ::
    JCset r (JEsub (JEvar t2) (JEvar c)) ::
    JCset b2 (JEltu (JEvar t3) (JEvar r1)) ::
    JCset bo (JEadd (JEvar b1a) (JEvar b2a)) :: rest =>
      match simple_arg bB with
      | Some bv =>
          if String.eqb a a1 && String.eqb t t1 && String.eqb t t2 && String.eqb t t3
             && String.eqb r r1 && String.eqb b1 b1a && String.eqb b2 b2a
             && window_names_ok c a (match bv with [y] => y | _ => a end) t b1 r b2 bo
          then Some (c, a, bB, t, b1, r, b2, bo, rest) else None
      | None => None
      end
  | _, _ => None
  end.

(** First limb: [t = a - B; b1 = a <u t]. *)
Definition match_sub_first (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * jasmin_expr * string * string * list jasmin_cmd) :=
  match k1, rest1 with
  | JCset t (JEsub (JEvar a) bB), JCset b1 (JEltu (JEvar a1) (JEvar t1)) :: rest =>
      match simple_arg bB with
      | Some bv =>
          if String.eqb a a1 && String.eqb t t1 && notin t [a; b1] && notin b1 (a :: bv)
             && notin t bv
          then Some (a, bB, t, b1, rest) else None
      | None => None
      end
  | _, _ => None
  end.

(** Last limb with [B = 0]: [r = a - c; bo = a <u r]. *)
Definition match_sbb_tail (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * string * string * string * list jasmin_cmd) :=
  match k1, rest1 with
  | JCset r (JEsub (JEvar a) (JEvar c)), JCset bo (JEltu (JEvar a1) (JEvar r1)) :: rest =>
      if String.eqb a a1 && String.eqb r r1 && notin r [a; c; bo] && notin bo [a; c]
         && notin c [a]
      then Some (c, a, r, bo, rest) else None
  | _, _ => None
  end.

Fixpoint adc_list (fuel : nat) (bits : list string) (pending : option (string * string))
    (cs : list jasmin_cmd) {struct fuel} : list jasmin_cmd :=
  match fuel with
  | O => flush pending ++ cs
  | S fuel' =>
    match cs with
    | [] => flush pending
    | k1 :: rest1 =>
      let step (_ : unit) :=
        if flag_neutral k1 && negb (pend_hit pending k1)
        then k1 :: adc_list fuel' (bits_after bits k1) pending rest1
        else flush pending ++ k1 :: adc_list fuel' (bits_after bits k1) None rest1 in
      match match_first_add k1 rest1 with
      | Some (fl, s, a, b, x, rest) =>
          flush pending ++
          JCadd_flags fl s a b :: adc_list fuel' (x :: bits_after bits k1) (Some (x, fl)) rest
      | None =>
      match match_window k1 rest1 with
      | Some (c, a, b, s, c1, r, c2, co, rest) =>
          if existsb (String.eqb c) bits
             && negb (existsb (fun k => mentions s k || mentions c1 k || mentions c2 k) rest)
          then
            let bits' := co :: filter (fun v => notin v [s; c1; r; c2; co]) bits in
            let fresh (_ : unit) :=
              flush pending ++
              JCadd_flags (fi_of co) (ti_of co) (JEvar c) (JElit (-1)) ::
              JCadcx (fl_of co) r (JEvar a) (JEvar b) (fi_of co) ::
              adc_list fuel' bits' (Some (co, fl_of co)) rest in
            match pending with
            | Some (x, fl) =>
                if String.eqb x c && negb (existsb (mentions c) rest)
                then JCadcx (fl_of co) r (JEvar a) (JEvar b) fl ::
                     adc_list fuel' bits' (Some (co, fl_of co)) rest
                else fresh tt
            | None => fresh tt
            end
          else step tt
      | None =>
      match match_sbb_window k1 rest1 with
      | Some (c, a, bB, t, b1, r, b2, bo, rest) =>
          if existsb (String.eqb c) bits
             && negb (existsb (fun k => mentions t k || mentions b1 k || mentions b2 k) rest)
          then
            let bits' := bo :: filter (fun v => notin v [t; b1; r; b2; bo]) bits in
            let fresh (_ : unit) :=
              flush pending ++
              JCadd_flags (fi_of bo) (ti_of bo) (JEvar c) (JElit (-1)) ::
              JCsbb (fl_of bo) r (JEvar a) bB (fi_of bo) ::
              adc_list fuel' bits' (Some (bo, fl_of bo)) rest in
            match pending with
            | Some (x, fl) =>
                if String.eqb x c && negb (existsb (mentions c) rest)
                then JCsbb (fl_of bo) r (JEvar a) bB fl ::
                     adc_list fuel' bits' (Some (bo, fl_of bo)) rest
                else fresh tt
            | None => fresh tt
            end
          else step tt
      | None =>
      match match_sub_first k1 rest1 with
      | Some (a, bB, t, b1, rest) =>
          flush pending ++
          JCsub_flags (fl_of b1) t (JEvar a) bB ::
          adc_list fuel' (b1 :: filter (fun v => notin v [t; b1]) bits) (Some (b1, fl_of b1)) rest
      | None =>
      match match_sbb_tail k1 rest1 with
      | Some (c, a, r, bo, rest) =>
          match pending with
          | Some (x, fl) =>
              if String.eqb x c && negb (existsb (mentions c) rest)
              then JCsbb (fl_of bo) r (JEvar a) (JElit 0) fl ::
                   adc_list fuel' (bo :: filter (fun v => notin v [r; bo]) bits)
                            (Some (bo, fl_of bo)) rest
              else step tt
          | None => step tt
          end
      | None => step tt
      end end end
      end end
    end
  end.

Definition no_helpers (cs : list jasmin_cmd) : bool :=
  forallb (fun k => negb (existsb helper (names k))) cs.

Definition adc_cmd (c : jasmin_cmd) : jasmin_cmd :=
  let cs := cmd_to_list c in
  if no_helpers cs then list_to_cmd (adc_list (S (length cs)) [] None cs) else c.

Definition adc_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f; jf_params := jf_params f; jf_locals := jf_locals f;
     jf_body := adc_cmd (jf_body f) |}.

(** [polish_func] with [adc_func] after the MULX pairing. *)
Definition polish_func_adc (f : jasmin_func) : jasmin_func :=
  lift_lits_func
    (simplify_func
      (lower_func
        (normalize_func
          (simplify_func
            (lower_comparisons_func
              (adc_func (lower_mulx_pairs_func (carry_func f)))))))).

(* ================================================================ *)
(* Semantics of the straight-line fragment, with real carries        *)
(* ================================================================ *)

Section Sem.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width} {word_ok : word.ok word}.

  Definition env := string -> word.
  Definition mem := word -> word.

  Definition upd (e : env) (x : string) (v : word) : env :=
    fun y => if String.eqb y x then v else e y.
  Definition mupd (m : mem) (a v : word) : mem :=
    fun b => if word.eqb b a then v else m b.

  Definition w0 : word := word.of_Z 0.
  Definition w1 : word := word.of_Z 1.
  Definition b2w (b : bool) : word := if b then w1 else w0.

  Fixpoint ev (e : env) (m : mem) (x : jasmin_expr) : word :=
    match x with
    | JEvar y => e y
    | JElit v => word.of_Z v
    | JEadd a b => word.add (ev e m a) (ev e m b)
    | JEsub a b => word.sub (ev e m a) (ev e m b)
    | JEmul a b => word.mul (ev e m a) (ev e m b)
    | JEmulhuu a b => word.mulhuu (ev e m a) (ev e m b)
    | JEand a b => word.and (ev e m a) (ev e m b)
    | JEor a b => word.or (ev e m a) (ev e m b)
    | JExor a b => word.xor (ev e m a) (ev e m b)
    | JEshr a b => word.sru (ev e m a) (ev e m b)
    | JEshl a b => word.slu (ev e m a) (ev e m b)
    | JEltu a b => b2w (word.ltu (ev e m a) (ev e m b))
    | JEeq a b => b2w (word.eqb (ev e m a) (ev e m b))
    | JEload b off => m (word.add (ev e m b) (word.of_Z off))
    end.

  (** A Jasmin boolean held as a word: true iff nonzero. *)
  Definition bit (w : word) : word := b2w (negb (word.eqb w w0)).

  (** Carry out of [a + b + c] and borrow out of [a - b - c]. *)
  Definition carry (a b c : word) : word :=
    b2w (Z.leb (2 ^ width) (word.unsigned a + word.unsigned b + word.unsigned c))%Z.
  Definition borrow (a b c : word) : word :=
    b2w (Z.ltb (word.unsigned a - word.unsigned b - word.unsigned c) 0)%Z.

  (** [#ADD], [#ADCX], [#SUB], [#SBB], [#MULX] as [pp_cmd] prints them;
      [while] and calls are outside the fragment. *)
  Fixpoint run (e : env) (m : mem) (c : jasmin_cmd) : option (env * mem) :=
    match c with
    | JCskip => Some (e, m)
    | JCseq a b => match run e m a with Some (e', m') => run e' m' b | None => None end
    | JCset x v => Some (upd e x (ev e m v), m)
    | JCstore b off v => Some (e, mupd m (word.add (ev e m b) (word.of_Z off)) (ev e m v))
    | JCif x t f => if word.eqb (ev e m x) w0 then run e m f else run e m t
    | JCdecl _ _ b => run e m b
    | JCwhile _ _ | JCcall _ _ => None
    | JCadd_flags cf r a b =>
        let va := ev e m a in let vb := ev e m b in
        Some (upd (upd e cf (carry va vb w0)) r (word.add va vb), m)
    | JCadcx co r a b ci =>
        let va := ev e m a in let vb := ev e m b in let vc := bit (e ci) in
        Some (upd (upd e co (carry va vb vc)) r (word.add (word.add va vb) vc), m)
    | JCmulx h l a b =>
        let va := ev e m a in let vb := ev e m b in
        Some (upd (upd e h (word.mulhuu va vb)) l (word.mul va vb), m)
    | JCsub_flags cf r a b =>
        let va := ev e m a in let vb := ev e m b in
        Some (upd (upd e cf (borrow va vb w0)) r (word.sub va vb), m)
    | JCsbb co r a b ci =>
        let va := ev e m a in let vb := ev e m b in let vc := bit (e ci) in
        Some (upd (upd e co (borrow va vb vc)) r (word.sub (word.sub va vb) vc), m)
    end.

  Fixpoint run_list (e : env) (m : mem) (cs : list jasmin_cmd) : option (env * mem) :=
    match cs with
    | [] => Some (e, m)
    | k :: r => match run e m k with Some (e', m') => run_list e' m' r | None => None end
    end.

  Lemma run_list_app : forall a b e m,
    run_list e m (a ++ b) =
      match run_list e m a with Some (e', m') => run_list e' m' b | None => None end.
  Proof.
    induction a as [|k a IH]; intros; cbn; [reflexivity|].
    destruct (run e m k) as [[e' m']|]; [apply IH | reflexivity].
  Qed.

  Lemma run_cmd_to_list : forall c e m, run e m c = run_list e m (cmd_to_list c).
  Proof.
    induction c; intros; cbn; try reflexivity.
    - rewrite run_list_app, IHc1. destruct (run_list e m _) as [[e' m']|]; [apply IHc2|reflexivity].
    - match goal with |- ?a = match ?a with _ => _ end => destruct a as [[? ?]|]; reflexivity end.
    - match goal with |- ?a = match ?a with _ => _ end => destruct a as [[? ?]|]; reflexivity end.
  Qed.

  Lemma run_list_to_cmd : forall cs e m, run e m (list_to_cmd cs) = run_list e m cs.
  Proof.
    induction cs as [|k cs IH]; intros; cbn; [reflexivity|].
    destruct (run e m k) as [[e' m']|]; [apply IH | reflexivity].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Frame: a command only depends on, and only changes, its names     *)
  (* ---------------------------------------------------------------- *)

  Lemma ev_ext : forall x e1 e2 m,
    (forall y, In y (vars_of x) -> e1 y = e2 y) -> ev e1 m x = ev e2 m x.
  Proof.
    induction x; intros e1 e2 m H; cbn in *;
      try (rewrite (IHx1 e1 e2 m), (IHx2 e1 e2 m) by (intros; apply H; apply in_or_app; auto));
      try reflexivity.
    - apply H; auto.
    - rewrite (IHx e1 e2 m) by auto. reflexivity.
  Qed.

  Lemma upd_eq : forall e x v, upd e x v x = v.
  Proof. intros. unfold upd. rewrite String.eqb_refl. reflexivity. Qed.
  Lemma upd_ne : forall e x v y, y <> x -> upd e x v y = e y.
  Proof. intros. unfold upd. destruct (String.eqb_spec y x); congruence. Qed.

  Definition agree_on (l : list string) (e1 e2 : env) : Prop := forall x, In x l -> e1 x = e2 x.

  Ltac frame_simple :=
    match goal with
    | Hrun : Some _ = Some (_, _), Hag : agree_on _ ?e1 ?e2 |- _ =>
        injection Hrun as <- <-; eexists; split; [reflexivity|];
        repeat match goal with
          | |- context [ev e1 ?m ?x] =>
              rewrite (ev_ext x e1 e2 m) by (intros; apply Hag; cbn; rewrite ?in_app_iff; tauto)
          end;
        try (match goal with
             | |- context [bit (e1 ?ci)] => rewrite (Hag ci) by (cbn; tauto)
             end);
        let y := fresh "y" in
        let Hy := fresh "Hy" in
        intros y; unfold upd;
        repeat match goal with
          | |- context [String.eqb y ?z] => destruct (String.eqb_spec y z)
          end;
        subst; split; intros Hy;
        first [ reflexivity | apply Hag; exact Hy | split; reflexivity
              | exfalso; apply Hy; cbn; rewrite ?in_app_iff; tauto ]
    end.

  Lemma frame : forall k e1 e2 m e1' m',
    run e1 m k = Some (e1', m') -> agree_on (names k) e1 e2 ->
    exists e2', run e2 m k = Some (e2', m') /\
      forall x, (In x (names k) -> e1' x = e2' x) /\
                (~ In x (names k) -> e1' x = e1 x /\ e2' x = e2 x).
  Proof.
    induction k; intros e1 e2 m e1' m' Hrun Hag; cbn [run names] in *;
      try discriminate; try frame_simple.
    - (* seq *)
      destruct (run e1 m k1) as [[ea ma]|] eqn:H1; [|discriminate].
      destruct (IHk1 e1 e2 m ea ma H1) as [eb [H1' Hb]].
      { intros y Hy; apply Hag; apply in_or_app; auto. }
      destruct (IHk2 ea eb ma e1' m' Hrun) as [ec [H2' Hc]].
      { intros y Hy. destruct (in_dec String.string_dec y (names k1)) as [Hin|Hnin].
        - apply Hb; exact Hin.
        - destruct (proj2 (Hb y) Hnin) as [-> ->]. apply Hag. apply in_or_app; auto. }
      exists ec. rewrite H1'. split; [exact H2'|].
      intros x. split.
      + intros Hx. destruct (in_dec String.string_dec x (names k2)) as [Hin|Hnin].
        * apply Hc; exact Hin.
        * destruct (proj2 (Hc x) Hnin) as [-> ->].
          apply in_app_or in Hx as [Hx|Hx]; [apply Hb; exact Hx | contradiction].
      + intros Hx. assert (~ In x (names k1)) by (intro; apply Hx; apply in_or_app; auto).
        assert (~ In x (names k2)) by (intro; apply Hx; apply in_or_app; auto).
        destruct (proj2 (Hc x) ltac:(assumption)) as [-> ->].
        apply (proj2 (Hb x)); assumption.
    - (* store *)
      injection Hrun as <- <-. eexists. split.
      + rewrite (ev_ext base e1 e2 m), (ev_ext v e1 e2 m)
          by (intros; apply Hag; apply in_or_app; auto). reflexivity.
      + intros x. split; [intros Hx; apply Hag; exact Hx | auto].
    - (* if *)
      rewrite (ev_ext e e1 e2 m) in Hrun by (intros; apply Hag; apply in_or_app; auto).
      destruct (word.eqb (ev e2 m e) w0).
      + destruct (IHk2 e1 e2 m e1' m' Hrun) as [ec [H Hc]].
        { intros y Hy; apply Hag; apply in_or_app; right; apply in_or_app; auto. }
        exists ec. split; [exact H|]. intros x. split.
        * intros Hx. destruct (in_dec String.string_dec x (names k2)) as [Hin|Hnin];
            [apply Hc; exact Hin|].
          destruct (proj2 (Hc x) Hnin) as [-> ->]. apply Hag; exact Hx.
        * intros Hx. apply (proj2 (Hc x)). intro; apply Hx.
          apply in_or_app; right; apply in_or_app; auto.
      + destruct (IHk1 e1 e2 m e1' m' Hrun) as [ec [H Hc]].
        { intros y Hy; apply Hag; apply in_or_app; right; apply in_or_app; auto. }
        exists ec. split; [exact H|]. intros x. split.
        * intros Hx. destruct (in_dec String.string_dec x (names k1)) as [Hin|Hnin];
            [apply Hc; exact Hin|].
          destruct (proj2 (Hc x) Hnin) as [-> ->]. apply Hag; exact Hx.
        * intros Hx. apply (proj2 (Hc x)). intro; apply Hx.
          apply in_or_app; right; apply in_or_app; auto.
    - (* decl *)
      destruct (IHk e1 e2 m e1' m' Hrun) as [ec [H Hc]].
      { intros y Hy; apply Hag; right; auto. }
      exists ec. split; [exact H|]. intros y. split.
      + intros Hy. destruct (in_dec String.string_dec y (names k)) as [Hin|Hnin];
          [apply Hc; exact Hin|].
        destruct (proj2 (Hc y) Hnin) as [-> ->]. apply Hag; exact Hy.
      + intros Hy. apply (proj2 (Hc y)). intro; apply Hy; right; auto.
  Qed.

  Lemma frame_list : forall cs e1 e2 m e1' m',
    run_list e1 m cs = Some (e1', m') -> agree_on (flat_map names cs) e1 e2 ->
    exists e2', run_list e2 m cs = Some (e2', m').
  Proof.
    induction cs as [|k cs IH]; intros e1 e2 m e1' m' Hrun Hag; cbn in *.
    - injection Hrun as <- <-. eexists; reflexivity.
    - destruct (run e1 m k) as [[ea ma]|] eqn:Hk; [|discriminate].
      destruct (frame k e1 e2 m ea ma Hk) as [eb [Hk' Hb]].
      { intros y Hy; apply Hag; apply in_or_app; auto. }
      rewrite Hk'. apply (IH ea eb ma e1' m' Hrun).
      intros y Hy. destruct (in_dec String.string_dec y (names k)) as [Hin|Hnin].
      + apply Hb; exact Hin.
      + destruct (proj2 (Hb y) Hnin) as [-> ->]. apply Hag. apply in_or_app; auto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Carry arithmetic                                                  *)
  (* ---------------------------------------------------------------- *)

  Local Open Scope Z_scope.

  Add Ring wring : (@Properties.word.ring_theory width word word_ok).

  Definition is_bit (w : word) : Prop := w = w0 \/ w = w1.

  Lemma M_ge4 : 4 <= 2 ^ width.
  Proof.
    destruct (@width_cases width BW) as [-> | ->]; cbv; congruence.
  Qed.

  Lemma u_w0 : word.unsigned w0 = 0.
  Proof. apply Properties.word.unsigned_of_Z_0. Qed.
  Lemma u_w1 : word.unsigned w1 = 1.
  Proof. apply Properties.word.unsigned_of_Z_1. Qed.

  Lemma w0_ne_w1 : w0 <> w1.
  Proof. intro E. pose proof u_w0 as H0. rewrite E, u_w1 in H0. discriminate. Qed.

  Lemma b2w_bit : forall b, is_bit (b2w b).
  Proof. destruct b; [right|left]; reflexivity. Qed.

  Lemma carry_bit : forall a b c, is_bit (carry a b c).
  Proof. intros. apply b2w_bit. Qed.

  Lemma bit_id : forall w, is_bit w -> bit w = w.
  Proof.
    intros w [-> | ->]; unfold bit.
    - rewrite Properties.word.eqb_eq by reflexivity. reflexivity.
    - rewrite Properties.word.eqb_ne by (intro E; apply w0_ne_w1; symmetry; exact E).
      reflexivity.
  Qed.

  Lemma bit_bit : forall w, is_bit (bit w).
  Proof. intros. apply b2w_bit. Qed.

  Lemma mod_wrap1 : forall z M, 0 < M -> M <= z < 2 * M -> z mod M = z - M.
  Proof.
    intros z M HM Hz. replace z with ((z - M) + 1 * M) at 1 by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  (** [x + y <u y] is the carry out of [x + y]. *)
  Lemma ltu_add : forall x y : word,
    word.ltu (word.add x y) y = Z.leb (2 ^ width) (word.unsigned x + word.unsigned y).
  Proof.
    intros x y. rewrite word.unsigned_ltu, word.unsigned_add. unfold word.wrap.
    pose proof (Properties.word.unsigned_range x). pose proof (Properties.word.unsigned_range y).
    pose proof M_ge4.
    destruct (Z.leb_spec (2 ^ width) (word.unsigned x + word.unsigned y)).
    - rewrite mod_wrap1 by lia. apply Z.ltb_lt. lia.
    - rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
  Qed.

  (** fiat's window computes the sum and carry of [a + b + c]. *)
  Lemma window_sum : forall c a b : word,
    word.add (word.add c a) b = word.add (word.add a b) c.
  Proof. intros. ring. Qed.

  Lemma window_carry : forall c a b : word, is_bit c ->
    word.add (b2w (word.ltu (word.add c a) a)) (b2w (word.ltu (word.add (word.add c a) b) b))
    = carry a b c.
  Proof.
    intros c a b Hc. rewrite !ltu_add. unfold carry.
    pose proof (Properties.word.unsigned_range a). pose proof (Properties.word.unsigned_range b).
    pose proof M_ge4.
    rewrite word.unsigned_add. unfold word.wrap.
    destruct Hc as [-> | ->]; rewrite ?u_w0, ?u_w1.
    - rewrite Z.add_0_l, Z.add_0_r, (Z.mod_small (word.unsigned a)) by lia.
      repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end;
        cbn [b2w]; unfold w0, w1;
        rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
        first [reflexivity | exfalso; lia].
    - destruct (Z.leb_spec (2 ^ width) (1 + word.unsigned a)).
      + rewrite (mod_wrap1 (1 + word.unsigned a)) by lia.
        repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end;
          cbn [b2w]; unfold w0, w1;
          rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
          first [reflexivity | exfalso; lia].
      + rewrite (Z.mod_small (1 + word.unsigned a)) by lia.
        repeat match goal with |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y) end;
          cbn [b2w]; unfold w0, w1;
          rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
          first [reflexivity | exfalso; lia].
  Qed.

  (** [_, cf, .. = #ADD(c, -1)] sets [cf] to [c] when [c] is 0 or 1. *)
  Lemma add_m1_flag : forall c : word, is_bit c -> bit (carry c (word.of_Z (-1)) w0) = c.
  Proof.
    intros c Hc. rewrite bit_id by apply carry_bit. unfold carry.
    rewrite word.unsigned_of_Z. unfold word.wrap. pose proof M_ge4.
    replace (-1) with ((2 ^ width - 1) + (-1) * 2 ^ width) by ring.
    rewrite Z_mod_plus_full, Z.mod_small by lia. rewrite u_w0.
    destruct Hc as [-> | ->]; rewrite ?u_w0, ?u_w1.
    - destruct (Z.leb_spec (2 ^ width) (0 + (2 ^ width - 1) + 0)); [lia|reflexivity].
    - destruct (Z.leb_spec (2 ^ width) (1 + (2 ^ width - 1) + 0)); [reflexivity|lia].
  Qed.

  Lemma add_bit_l : forall x c : word, is_bit c -> word.add x (bit c) = word.add x c.
  Proof. intros. rewrite bit_id by assumption. reflexivity. Qed.

  Lemma mod_wrap_neg : forall z M, 0 < M -> - M <= z < 0 -> z mod M = z + M.
  Proof.
    intros z M HM Hz. replace z with ((z + M) + (-1) * M) at 1 by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  (** [x <u x - y] is the borrow out of [x - y]. *)
  Lemma ltu_sub : forall x y : word,
    word.ltu x (word.sub x y) = Z.ltb (word.unsigned x) (word.unsigned y).
  Proof.
    intros x y. rewrite word.unsigned_ltu, word.unsigned_sub. unfold word.wrap.
    pose proof (Properties.word.unsigned_range x). pose proof (Properties.word.unsigned_range y).
    destruct (Z.ltb_spec (word.unsigned x) (word.unsigned y)).
    - rewrite mod_wrap_neg by lia. apply Z.ltb_lt. lia.
    - rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
  Qed.

  Lemma sub_first_borrow : forall a b : word,
    b2w (word.ltu a (word.sub a b)) = borrow a b w0.
  Proof.
    intros. rewrite ltu_sub. unfold borrow. rewrite u_w0.
    destruct (Z.ltb_spec (word.unsigned a) (word.unsigned b));
      destruct (Z.ltb_spec (word.unsigned a - word.unsigned b - 0) 0); first [reflexivity | lia].
  Qed.

  Lemma sbb_window_borrow : forall c a b : word, is_bit c ->
    word.add (b2w (word.ltu a (word.sub a b)))
             (b2w (word.ltu (word.sub a b) (word.sub (word.sub a b) c)))
    = borrow a b c.
  Proof.
    intros c a b Hc. rewrite !ltu_sub. unfold borrow.
    pose proof (Properties.word.unsigned_range a). pose proof (Properties.word.unsigned_range b).
    pose proof M_ge4.
    rewrite word.unsigned_sub. unfold word.wrap.
    destruct Hc as [-> | ->]; rewrite ?u_w0, ?u_w1.
    - destruct (Z.ltb_spec ((word.unsigned a - word.unsigned b) mod 2 ^ width) 0).
      + pose proof (Z.mod_pos_bound (word.unsigned a - word.unsigned b) (2 ^ width)). lia.
      + repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end;
          cbn [b2w]; unfold w0, w1;
          rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
          first [reflexivity | exfalso; lia].
    - destruct (Z.ltb_spec (word.unsigned a) (word.unsigned b)).
      + rewrite (mod_wrap_neg (word.unsigned a - word.unsigned b)) by lia.
        repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end;
          cbn [b2w]; unfold w0, w1;
          rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
          first [reflexivity | exfalso; lia].
      + rewrite (Z.mod_small (word.unsigned a - word.unsigned b)) by lia.
        repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end;
          cbn [b2w]; unfold w0, w1;
          rewrite ?Properties.word.add_0_l, ?Properties.word.add_0_r;
          first [reflexivity | exfalso; lia].
  Qed.

  Lemma sbb_tail_borrow : forall a c : word,
    b2w (word.ltu a (word.sub a c)) = borrow a (word.of_Z 0) c.
  Proof.
    intros. rewrite ltu_sub. unfold borrow. rewrite Properties.word.unsigned_of_Z_0.
    destruct (Z.ltb_spec (word.unsigned a) (word.unsigned c));
      destruct (Z.ltb_spec (word.unsigned a - 0 - word.unsigned c) 0); first [reflexivity | lia].
  Qed.

  Lemma borrow_bit : forall a b c, is_bit (borrow a b c).
  Proof. intros. apply b2w_bit. Qed.

  Local Close Scope Z_scope.

  (* ---------------------------------------------------------------- *)
  (* The matchers                                                      *)
  (* ---------------------------------------------------------------- *)

  Ltac bool_hyps :=
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
    | H : negb _ = true |- _ => apply negb_true_iff in H
    end.

  Lemma match_first_add_spec : forall k1 rest1 fl s a b x rest,
    match_first_add k1 rest1 = Some (fl, s, a, b, x, rest) ->
    k1 = JCadd_flags fl s a b /\
    rest1 = JCset x (JElit 0) :: JCif (JEvar fl) (JCset x (JElit 1)) JCskip :: rest /\
    x <> fl.
  Proof.
    intros k1 rest1 fl s a b x rest H. unfold match_first_add in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end.
    injection H as <- <- <- <- <- <-. bool_hyps.
    split; [reflexivity|]. split; [reflexivity|].
    apply String.eqb_neq; assumption.
  Qed.

  Lemma notin_spec : forall x l, notin x l = true -> ~ In x l.
  Proof.
    intros x l H Hin. unfold notin in H. apply negb_true_iff in H.
    assert (existsb (String.eqb x) l = true) as E.
    { apply existsb_exists. exists x. split; [exact Hin | apply String.eqb_refl]. }
    congruence.
  Qed.

  Lemma match_window_spec : forall k1 rest1 c a b s c1 r c2 co rest,
    match_window k1 rest1 = Some (c, a, b, s, c1, r, c2, co, rest) ->
    k1 :: rest1 =
      JCset s (JEadd (JEvar c) (JEvar a)) :: JCset c1 (JEltu (JEvar s) (JEvar a)) ::
      JCset r (JEadd (JEvar s) (JEvar b)) :: JCset c2 (JEltu (JEvar r) (JEvar b)) ::
      JCset co (JEadd (JEvar c1) (JEvar c2)) :: rest /\
    window_names_ok c a b s c1 r c2 co = true.
  Proof.
    intros k1 rest1 c a b s c1 r c2 co rest H. unfold match_window in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end.
    injection H as <- <- <- <- <- <- <- <- <-.
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    end.
    repeat match goal with
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    end.
    split; [reflexivity | assumption].
  Qed.

  Definition window_facts (c a b s c1 r c2 co : string) : Prop :=
    ~ In s [c1; r; c2; co] /\ ~ In c1 [r; c2; co] /\ ~ In r [c2; co] /\ ~ In c2 [co] /\
    ~ In s [c; a; b] /\ ~ In c1 [c; a; b] /\ ~ In r [c; a; b] /\ ~ In c2 [c; a; b] /\
    ~ In co [c; a; b] /\ ~ In c [a; b].

  Lemma window_names_ok_facts : forall c a b s c1 r c2 co,
    window_names_ok c a b s c1 r c2 co = true -> window_facts c a b s c1 r c2 co.
  Proof.
    intros. unfold window_names_ok in H. cbn [forallb] in H.
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    end.
    repeat match goal with H : notin _ _ = true |- _ => apply notin_spec in H end.
    unfold window_facts; tauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Running the pieces                                                *)
  (* ---------------------------------------------------------------- *)

  Lemma if_bit : forall w : word, (if word.eqb w w0 then w0 else w1) = bit w.
  Proof. intros. unfold bit. destruct (word.eqb w w0); reflexivity. Qed.

  Ltac simpl_upd :=
    repeat match goal with
    | |- context [upd ?e ?x ?v ?x] => rewrite (upd_eq e x v)
    | |- context [upd ?e ?x ?v ?y] => rewrite (upd_ne e x v y) by (intro; subst; tauto)
    end.

  Lemma window_run : forall c a b s c1 r c2 co rest e1 m e1' m',
    window_facts c a b s c1 r c2 co -> is_bit (e1 c) ->
    run_list e1 m
      (JCset s (JEadd (JEvar c) (JEvar a)) :: JCset c1 (JEltu (JEvar s) (JEvar a)) ::
       JCset r (JEadd (JEvar s) (JEvar b)) :: JCset c2 (JEltu (JEvar r) (JEvar b)) ::
       JCset co (JEadd (JEvar c1) (JEvar c2)) :: rest) = Some (e1', m') ->
    exists e1w, run_list e1w m rest = Some (e1', m') /\
      e1w r = word.add (word.add (e1 a) (e1 b)) (e1 c) /\
      e1w co = carry (e1 a) (e1 b) (e1 c) /\
      (forall y, ~ In y [s; c1; r; c2; co] -> e1w y = e1 y).
  Proof.
    intros c a b s c1 r c2 co rest e1 m e1' m' F Hc H.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    cbn [run_list run ev] in H. eexists. split; [exact H|].
    cbn [In] in *.
    simpl_upd.
    split; [|split].
    - apply window_sum.
    - apply window_carry. exact Hc.
    - intros y Hy. simpl_upd. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The simulation                                                    *)
  (* ---------------------------------------------------------------- *)

  Definition pvar (p : option (string * string)) : option string := option_map fst p.

  Definition INV (bits : list string) (p : option (string * string)) (cs : list jasmin_cmd)
      (e1 e2 : env) : Prop :=
    (forall x, In x (flat_map names cs) -> pvar p <> Some x -> e1 x = e2 x) /\
    (forall v, In v bits -> is_bit (e1 v)) /\
    match p with
    | Some (x, fl) => is_bit (e1 x) /\ bit (e2 fl) = e1 x /\ x <> fl
    | None => True
    end.

  Definition NH (cs : list jasmin_cmd) : Prop :=
    forall x, In x (flat_map names cs) -> helper x = false.

  Lemma NH_tail : forall k cs, NH (k :: cs) -> NH cs.
  Proof. intros k cs H x Hx. apply H. cbn. apply in_or_app; auto. Qed.

  Lemma NH_app : forall a b, NH (a ++ b) -> NH b.
  Proof. intros a b H x Hx. apply H. rewrite flat_map_app. apply in_or_app; auto. Qed.

  Lemma helper_not_name : forall cs y h, NH cs -> In y (flat_map names cs) -> helper h = true ->
    y <> h.
  Proof. intros cs y h Hnh Hy Hh ->. rewrite (Hnh h Hy) in Hh. discriminate. Qed.

  Lemma flush_ok : forall p bits cs e1 e2 m,
    INV bits p cs e1 e2 -> NH cs ->
    exists e2', run_list e2 m (flush p) = Some (e2', m) /\ INV bits None cs e1 e2'.
  Proof.
    intros p bits cs e1 e2 m [HA [HB HC]] Hnh. destruct p as [[x fl]|].
    - destruct HC as [Hx [Hfl Hne]].
      cbn [flush materialize run_list run ev]. eexists. split; [reflexivity|].
      split; [|split; [exact HB | exact I]].
      intros y Hy _. destruct (String.eqb_spec y x) as [->|Hyx].
      + rewrite upd_eq. rewrite (upd_eq e2 x (word.of_Z 0)).
        rewrite (upd_ne e2 x (word.of_Z 0) fl) by (intro E; apply Hne; symmetry; exact E).
        rewrite !Properties.word.add_0_l. exact (eq_sym Hfl).
      + rewrite upd_ne by exact Hyx.
        rewrite upd_ne by exact (helper_not_name cs y (mi_of x) Hnh Hy (helper_mi x)).
        rewrite upd_ne by exact Hyx. apply HA; [exact Hy | cbn; congruence].
    - cbn. eexists. split; [reflexivity|]. split; [exact HA | split; [exact HB | exact I]].
  Qed.

  Lemma not_mentioned_rest : forall v (rest : list jasmin_cmd),
    existsb (mentions v) rest = false -> ~ In v (flat_map names rest).
  Proof.
    intros v rest H Hin. apply in_flat_map in Hin as [k [Hk Hv]].
    assert (existsb (mentions v) rest = true).
    { apply existsb_exists. exists k. split; [exact Hk|]. apply mentions_In. exact Hv. }
    congruence.
  Qed.

  Lemma window_dead : forall s c1 c2 rest,
    existsb (fun k => mentions s k || mentions c1 k || mentions c2 k) rest = false ->
    ~ In s (flat_map names rest) /\ ~ In c1 (flat_map names rest) /\ ~ In c2 (flat_map names rest).
  Proof.
    intros s c1 c2 rest H.
    assert (forall k, In k rest -> mentions s k = false /\ mentions c1 k = false /\ mentions c2 k = false)
      as Hk.
    { intros k Hin. destruct (mentions s k) eqn:E1, (mentions c1 k) eqn:E2, (mentions c2 k) eqn:E3;
        try (split; [|split]; reflexivity);
        exfalso; assert (existsb (fun k => mentions s k || mentions c1 k || mentions c2 k) rest = true)
          by (apply existsb_exists; exists k; split; [exact Hin | rewrite E1, E2, E3; reflexivity]);
        congruence. }
    split; [|split]; intro Hin; apply in_flat_map in Hin as [k [Hin Hv]];
      apply mentions_In in Hv; destruct (Hk k Hin) as (? & ? & ?); congruence.
  Qed.

  Lemma fm_tail : forall y k l, In y (flat_map names l) -> In y (flat_map names (k :: l)).
  Proof. intros. cbn [flat_map]. apply in_or_app. right. exact H. Qed.
  Lemma fm_head : forall y k l, In y (names k) -> In y (flat_map names (k :: l)).
  Proof. intros. cbn [flat_map]. apply in_or_app. left. exact H. Qed.

  Definition SIM (fuel : nat) : Prop :=
    forall bits p cs e1 e2 m e1' m',
      INV bits p cs e1 e2 -> NH cs -> run_list e1 m cs = Some (e1', m') ->
      exists e2', run_list e2 m (adc_list fuel bits p cs) = Some (e2', m').

  Lemma plain_step : forall bits p k1 rest1 e1 e2 m e1a ma,
    INV bits p (k1 :: rest1) e1 e2 -> pend_hit p k1 = false ->
    run e1 m k1 = Some (e1a, ma) ->
    exists e2a, run e2 m k1 = Some (e2a, ma) /\ INV (bits_after bits k1) p rest1 e1a e2a.
  Proof.
    intros bits p k1 rest1 e1 e2 m e1a ma [HA [HB HC]] Hp Hk.
    assert (Hnot : forall x fl, p = Some (x, fl) -> ~ In x (names k1) /\ ~ In fl (names k1)).
    { intros x fl ->. cbn in Hp. apply orb_false_iff in Hp as [H1 H2].
      split; intro Hin; apply mentions_In in Hin; congruence. }
    destruct (frame k1 e1 e2 m e1a ma Hk) as [e2a [Hk' Hfr]].
    { intros y Hy. apply HA; [cbn; apply in_or_app; auto|].
      destruct p as [[x fl]|]; cbn; [|congruence].
      intros E; injection E as ->. apply (proj1 (Hnot y fl eq_refl)); exact Hy. }
    exists e2a. split; [exact Hk'|].
    split; [|split].
    - intros y Hy Hpv. destruct (in_dec String.string_dec y (names k1)) as [Hin|Hnin].
      + apply Hfr; exact Hin.
      + destruct (proj2 (Hfr y) Hnin) as [-> ->].
        apply HA; [cbn; apply in_or_app; auto | exact Hpv].
    - intros v Hv. unfold bits_after in Hv. apply in_app_or in Hv as [Hv|Hv].
      + apply filter_In in Hv as [Hv Hm]. apply negb_true_iff in Hm.
        assert (~ In v (names k1)) as Hn by (intro Hin; apply mentions_In in Hin; congruence).
        destruct (proj2 (Hfr v) Hn) as [-> _]. apply HB; exact Hv.
      + destruct k1; cbn in Hv; try contradiction. destruct e; cbn in Hv; try contradiction.
        destruct Hv as [<-|[]]. cbn in Hk. injection Hk as <- <-. rewrite upd_eq. apply b2w_bit.
    - destruct p as [[x fl]|]; [|exact I].
      destruct HC as [Hx [Hfl Hne]]. destruct (Hnot x fl eq_refl) as [Hx1 Hfl1].
      destruct (proj2 (Hfr x) Hx1) as [-> _]. destruct (proj2 (Hfr fl) Hfl1) as [_ ->].
      split; [exact Hx | split; [exact Hfl | exact Hne]].
  Qed.

  Lemma step_case : forall fuel, SIM fuel ->
    forall bits p k1 rest1 e1 e2 m e1' m',
    INV bits p (k1 :: rest1) e1 e2 -> NH (k1 :: rest1) ->
    run_list e1 m (k1 :: rest1) = Some (e1', m') ->
    exists e2', run_list e2 m
      (if flag_neutral k1 && negb (pend_hit p k1)
       then k1 :: adc_list fuel (bits_after bits k1) p rest1
       else flush p ++ k1 :: adc_list fuel (bits_after bits k1) None rest1) = Some (e2', m').
  Proof.
    intros fuel IH bits p k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun.
    cbn [run_list] in Hrun. destruct (run e1 m k1) as [[e1a ma]|] eqn:Hk; [|discriminate].
    destruct (flag_neutral k1 && negb (pend_hit p k1)) eqn:E.
    - apply andb_true_iff in E as [_ E]. apply negb_true_iff in E.
      destruct (plain_step bits p k1 rest1 e1 e2 m e1a ma Hinv E Hk) as [e2a [Hk' Hinv']].
      cbn [run_list]. rewrite Hk'. exact (IH _ _ _ e1a e2a ma e1' m' Hinv' (NH_tail _ _ Hnh) Hrun).
    - destruct (flush_ok p bits (k1 :: rest1) e1 e2 m Hinv Hnh) as [e2b [Hf Hinvb]].
      rewrite run_list_app, Hf.
      destruct (plain_step bits None k1 rest1 e1 e2b m e1a ma Hinvb eq_refl Hk) as [e2a [Hk' Hinv']].
      cbn [run_list]. rewrite Hk'. exact (IH _ _ _ e1a e2a ma e1' m' Hinv' (NH_tail _ _ Hnh) Hrun).
  Qed.

  Lemma first_add_case : forall fuel, SIM fuel ->
    forall bits p fl s a b x rest e1 e2 m e1' m',
    let cs := JCadd_flags fl s a b :: JCset x (JElit 0) ::
              JCif (JEvar fl) (JCset x (JElit 1)) JCskip :: rest in
    x <> fl -> INV bits p cs e1 e2 -> NH cs -> run_list e1 m cs = Some (e1', m') ->
    exists e2', run_list e2 m
      (flush p ++ JCadd_flags fl s a b ::
       adc_list fuel (x :: bits_after bits (JCadd_flags fl s a b)) (Some (x, fl)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits p fl s a b x rest e1 e2 m e1' m' cs Hxfl Hinv Hnh Hrun.
    destruct (flush_ok p bits cs e1 e2 m Hinv Hnh) as [e2b [Hf Hinvb]].
    rewrite run_list_app, Hf.
    unfold cs in Hrun. cbn [run_list] in Hrun.
    destruct (run e1 m (JCadd_flags fl s a b)) as [[e1a ma]|] eqn:Hk; [|discriminate].
    destruct (plain_step bits None (JCadd_flags fl s a b) _ e1 e2b m e1a ma Hinvb eq_refl Hk)
      as [e2a [Hk' [HA [HB _]]]].
    cbn [run_list]. rewrite Hk'.
    assert (ma = m) by (cbn in Hk; injection Hk; auto). subst ma.
    cbn [run ev] in Hrun.
    rewrite (upd_ne e1a x (word.of_Z 0) fl) in Hrun by (intro E; apply Hxfl; symmetry; exact E).
    assert (Hfl : e1a fl = e2a fl).
    { apply HA; [apply fm_tail, fm_head; cbn; tauto | cbn; congruence]. }
    assert (Hag : forall y, In y (flat_map names rest) -> y <> x -> e1a y = e2a y).
    { intros y Hy Hyx. apply HA; [apply fm_tail, fm_tail; exact Hy | cbn; congruence]. }
    assert (HNH : NH rest) by (do 3 apply NH_tail in Hnh; exact Hnh).
    destruct (word.eqb (e1a fl) w0) eqn:Ew.
    - eapply (IH _ _ _ _ e2a m e1' m' _ HNH Hrun). Unshelve.
      split; [|split].
      + intros y Hy Hpv. assert (y <> x) by (intro; subst; cbn in Hpv; congruence).
        rewrite upd_ne by assumption. apply Hag; assumption.
      + intros v [<-|Hv]; [rewrite upd_eq; left; reflexivity|].
        destruct (String.eqb_spec v x) as [->|Hvx]; [rewrite upd_eq; left; reflexivity|].
        rewrite upd_ne by exact Hvx. apply HB. exact Hv.
      + rewrite upd_eq. split; [left; reflexivity|]. split; [|exact Hxfl].
        rewrite <- Hfl. unfold bit. rewrite Ew. reflexivity.
    - eapply (IH _ _ _ _ e2a m e1' m' _ HNH Hrun). Unshelve.
      split; [|split].
      + intros y Hy Hpv. assert (y <> x) by (intro; subst; cbn in Hpv; congruence).
        rewrite !upd_ne by assumption. apply Hag; assumption.
      + intros v [<-|Hv]; [rewrite upd_eq; right; reflexivity|].
        destruct (String.eqb_spec v x) as [->|Hvx]; [rewrite upd_eq; right; reflexivity|].
        rewrite !upd_ne by exact Hvx. apply HB. exact Hv.
      + rewrite upd_eq. split; [right; reflexivity|]. split; [|exact Hxfl].
        rewrite <- Hfl. unfold bit. rewrite Ew. reflexivity.
  Qed.

  Definition window_cmds (c a b s c1 r c2 co : string) (rest : list jasmin_cmd) :=
    JCset s (JEadd (JEvar c) (JEvar a)) :: JCset c1 (JEltu (JEvar s) (JEvar a)) ::
    JCset r (JEadd (JEvar s) (JEvar b)) :: JCset c2 (JEltu (JEvar r) (JEvar b)) ::
    JCset co (JEadd (JEvar c1) (JEvar c2)) :: rest.

  Lemma window_in : forall c a b s c1 r c2 co rest y,
    In y [c; a; b] -> In y (flat_map names (window_cmds c a b s c1 r c2 co rest)).
  Proof.
    intros. unfold window_cmds. cbn [In] in H.
    destruct H as [<-|[<-|[<-|[]]]].
    - apply fm_head. cbn. tauto.
    - apply fm_head. cbn. tauto.
    - apply fm_tail, fm_tail, fm_head. cbn. tauto.
  Qed.

  Lemma window_in_rest : forall c a b s c1 r c2 co rest y,
    In y (flat_map names rest) -> In y (flat_map names (window_cmds c a b s c1 r c2 co rest)).
  Proof. intros. unfold window_cmds. do 5 apply fm_tail. exact H. Qed.

  Lemma fl_of_neq : forall co, co <> fl_of co.
  Proof. intros co E. apply (append_neq_self "__adc_cf_" co); [discriminate | symmetry; exact E]. Qed.

  Lemma fi_ti_neq : forall co, fi_of co <> ti_of co.
  Proof. intros co E. apply (f_equal (String.get 6)) in E. cbn in E. discriminate. Qed.

  Lemma window_consume_case : forall fuel, SIM fuel ->
    forall bits fl c a b s c1 r c2 co rest e1 e2 m e1' m',
    window_facts c a b s c1 r c2 co -> In c bits ->
    ~ In s (flat_map names rest) -> ~ In c1 (flat_map names rest) ->
    ~ In c2 (flat_map names rest) -> ~ In c (flat_map names rest) ->
    INV bits (Some (c, fl)) (window_cmds c a b s c1 r c2 co rest) e1 e2 ->
    NH (window_cmds c a b s c1 r c2 co rest) ->
    run_list e1 m (window_cmds c a b s c1 r c2 co rest) = Some (e1', m') ->
    exists e2', run_list e2 m
      (JCadcx (fl_of co) r (JEvar a) (JEvar b) fl ::
       adc_list fuel (co :: filter (fun v => notin v [s; c1; r; c2; co]) bits)
                (Some (co, fl_of co)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits fl c a b s c1 r c2 co rest e1 e2 m e1' m' Fw Hcb Hs Hc1 Hc2 Hc
      Hinv Hnh Hrun.
    destruct Hinv as [HA [HB [Hcbit [Hfl Hcfl]]]].
    destruct (window_run c a b s c1 r c2 co rest e1 m e1' m' Fw (HB c Hcb) Hrun)
      as [e1w [Hrw [Hr [Hco Hoth]]]].
    pose proof Fw as Fw'. destruct Fw' as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    cbn [In] in *.
    assert (Ha : e1 a = e2 a).
    { apply HA; [apply window_in; cbn; tauto | cbn; intro E; injection E as E; subst; tauto]. }
    assert (Hb : e1 b = e2 b).
    { apply HA; [apply window_in; cbn; tauto | cbn; intro E; injection E as E; subst; tauto]. }
    assert (Hrn : helper r = false) by (apply Hnh; apply fm_tail, fm_tail, fm_head; cbn; tauto).
    cbn [run_list run ev].
    rewrite <- Ha, <- Hb, Hfl.
    assert (HNH : NH rest) by (unfold window_cmds in Hnh; do 5 apply NH_tail in Hnh; exact Hnh).
    eapply (IH _ _ _ e1w _ m e1' m' _ HNH Hrw). Unshelve.
    split; [|split].
    - intros y Hy Hpv.
      assert (y <> co) by (intro; subst; cbn in Hpv; congruence).
      assert (y <> fl_of co) by exact (helper_not_name rest y (fl_of co) HNH Hy (helper_fl co)).
      destruct (String.eqb_spec y r) as [->|Hyr].
      + rewrite upd_eq. exact Hr.
      + rewrite !upd_ne by assumption.
        assert (y <> s) by (intro; subst; contradiction).
        assert (y <> c1) by (intro; subst; contradiction).
        assert (y <> c2) by (intro; subst; contradiction).
        assert (y <> c) by (intro; subst; contradiction).
        rewrite Hoth by (cbn; intuition).
        apply HA; [apply window_in_rest; exact Hy | cbn; congruence].
    - intros v [<-|Hv].
      + rewrite Hco. apply carry_bit.
      + apply filter_In in Hv as [Hv Hn]. apply notin_spec in Hn.
        rewrite Hoth by exact Hn. apply HB; exact Hv.
    - rewrite Hco. split; [apply carry_bit|]. split; [|apply fl_of_neq].
      rewrite upd_ne by exact (helper_neq _ _ (helper_fl co) Hrn).
      rewrite upd_eq. apply bit_id. apply carry_bit.
  Qed.

  Lemma window_fresh_case : forall fuel, SIM fuel ->
    forall bits p c a b s c1 r c2 co rest e1 e2 m e1' m',
    window_facts c a b s c1 r c2 co -> In c bits ->
    ~ In s (flat_map names rest) -> ~ In c1 (flat_map names rest) ->
    ~ In c2 (flat_map names rest) ->
    INV bits p (window_cmds c a b s c1 r c2 co rest) e1 e2 ->
    NH (window_cmds c a b s c1 r c2 co rest) ->
    run_list e1 m (window_cmds c a b s c1 r c2 co rest) = Some (e1', m') ->
    exists e2', run_list e2 m
      (flush p ++
       JCadd_flags (fi_of co) (ti_of co) (JEvar c) (JElit (-1)) ::
       JCadcx (fl_of co) r (JEvar a) (JEvar b) (fi_of co) ::
       adc_list fuel (co :: filter (fun v => notin v [s; c1; r; c2; co]) bits)
                (Some (co, fl_of co)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits p c a b s c1 r c2 co rest e1 e2 m e1' m' Fw Hcb Hs Hc1 Hc2
      Hinv Hnh Hrun.
    destruct (flush_ok p bits _ e1 e2 m Hinv Hnh) as [e2b [Hf [HA [HB _]]]].
    rewrite run_list_app, Hf.
    destruct (window_run c a b s c1 r c2 co rest e1 m e1' m' Fw (HB c Hcb) Hrun)
      as [e1w [Hrw [Hr [Hco Hoth]]]].
    pose proof Fw as Fw'. destruct Fw' as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    cbn [In] in *.
    assert (Hin3 : forall y, In y [c; a; b] -> e1 y = e2b y /\ helper y = false).
    { intros y Hy. split; [apply HA; [apply window_in; exact Hy | cbn; congruence] |].
      apply Hnh. apply window_in. exact Hy. }
    destruct (Hin3 a ltac:(cbn; tauto)) as [Ha Han].
    destruct (Hin3 b ltac:(cbn; tauto)) as [Hb Hbn].
    destruct (Hin3 c ltac:(cbn; tauto)) as [Hc Hcn].
    assert (Hrn : helper r = false) by (apply Hnh; apply fm_tail, fm_tail, fm_head; cbn; tauto).
    cbn [run_list run ev].
    rewrite (upd_ne _ (ti_of co) _ a) by exact (not_eq_sym (helper_neq _ _ (helper_ti co) Han)).
    rewrite (upd_ne _ (fi_of co) _ a) by exact (not_eq_sym (helper_neq _ _ (helper_fi co) Han)).
    rewrite (upd_ne _ (ti_of co) _ b) by exact (not_eq_sym (helper_neq _ _ (helper_ti co) Hbn)).
    rewrite (upd_ne _ (fi_of co) _ b) by exact (not_eq_sym (helper_neq _ _ (helper_fi co) Hbn)).
    rewrite (upd_ne _ (ti_of co) _ (fi_of co)) by apply fi_ti_neq.
    rewrite upd_eq.
    rewrite <- Ha, <- Hb, <- Hc.
    rewrite (add_m1_flag (e1 c) (HB c Hcb)).
    assert (HNH : NH rest) by (unfold window_cmds in Hnh; do 5 apply NH_tail in Hnh; exact Hnh).
    eapply (IH _ _ _ e1w _ m e1' m' _ HNH Hrw). Unshelve.
    split; [|split].
    - intros y Hy Hpv.
      assert (y <> co) by (intro; subst; cbn in Hpv; congruence).
      destruct (String.eqb_spec y r) as [->|Hyr].
      + rewrite upd_eq. exact Hr.
      + rewrite upd_ne by assumption.
        rewrite upd_ne by exact (helper_not_name rest y (fl_of co) HNH Hy (helper_fl co)).
        rewrite upd_ne by exact (helper_not_name rest y (ti_of co) HNH Hy (helper_ti co)).
        rewrite upd_ne by exact (helper_not_name rest y (fi_of co) HNH Hy (helper_fi co)).
        assert (y <> s) by (intro; subst; contradiction).
        assert (y <> c1) by (intro; subst; contradiction).
        assert (y <> c2) by (intro; subst; contradiction).
        rewrite Hoth by (cbn; intuition).
        apply HA; [apply window_in_rest; exact Hy | cbn; congruence].
    - intros v [<-|Hv].
      + rewrite Hco. apply carry_bit.
      + apply filter_In in Hv as [Hv Hn]. apply notin_spec in Hn.
        rewrite Hoth by exact Hn. apply HB; exact Hv.
    - rewrite Hco. split; [apply carry_bit|]. split; [|apply fl_of_neq].
      rewrite upd_ne by exact (helper_neq _ _ (helper_fl co) Hrn).
      rewrite upd_eq. apply bit_id. apply carry_bit.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Borrow windows                                                    *)
  (* ---------------------------------------------------------------- *)

  Lemma simple_arg_spec : forall e bv, simple_arg e = Some bv ->
    vars_of e = bv /\ ((exists y, e = JEvar y /\ bv = [y]) \/ (exists z, e = JElit z /\ bv = [])).
  Proof.
    intros e bv H. destruct e; cbn in H; try discriminate; injection H as <-; split; auto.
    - left; eauto.
    - right; eauto.
  Qed.

  Definition bname_of (a : string) (bv : list string) : string :=
    match bv with [y] => y | _ => a end.

  Lemma match_sbb_window_spec : forall k1 rest1 c a bB t b1 r b2 bo rest,
    match_sbb_window k1 rest1 = Some (c, a, bB, t, b1, r, b2, bo, rest) ->
    exists bv, simple_arg bB = Some bv /\
    k1 :: rest1 =
      JCset t (JEsub (JEvar a) bB) :: JCset b1 (JEltu (JEvar a) (JEvar t)) ::
      JCset r (JEsub (JEvar t) (JEvar c)) :: JCset b2 (JEltu (JEvar t) (JEvar r)) ::
      JCset bo (JEadd (JEvar b1) (JEvar b2)) :: rest /\
    window_names_ok c a (bname_of a bv) t b1 r b2 bo = true.
  Proof.
    intros k1 rest1 c a bB t b1 r b2 bo rest H. unfold match_sbb_window in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end;
    injection H as <- <- <- <- <- <- <- <- <-;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    end;
    repeat match goal with
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    end;
    eexists; (split; [eassumption|]); split; [reflexivity | assumption].
  Qed.

  Lemma match_sub_first_spec : forall k1 rest1 a bB t b1 rest,
    match_sub_first k1 rest1 = Some (a, bB, t, b1, rest) ->
    exists bv, simple_arg bB = Some bv /\
    k1 :: rest1 = JCset t (JEsub (JEvar a) bB) :: JCset b1 (JEltu (JEvar a) (JEvar t)) :: rest /\
    ~ In t [a; b1] /\ ~ In t bv.
  Proof.
    intros k1 rest1 a bB t b1 rest H. unfold match_sub_first in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end;
    injection H as <- <- <- <- <-;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    end;
    repeat match goal with
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    end;
    repeat match goal with H : notin _ _ = true |- _ => apply notin_spec in H end;
    eexists; (split; [eassumption|]); split; [reflexivity | split; assumption].
  Qed.

  Lemma match_sbb_tail_spec : forall k1 rest1 c a r bo rest,
    match_sbb_tail k1 rest1 = Some (c, a, r, bo, rest) ->
    k1 :: rest1 = JCset r (JEsub (JEvar a) (JEvar c)) :: JCset bo (JEltu (JEvar a) (JEvar r)) :: rest /\
    ~ In r [a; c; bo] /\ ~ In bo [a; c] /\ ~ In c [a].
  Proof.
    intros k1 rest1 c a r bo rest H. unfold match_sbb_tail in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end;
    injection H as <- <- <- <- <-;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    end;
    repeat match goal with
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    end;
    repeat match goal with H : notin _ _ = true |- _ => apply notin_spec in H end;
    split; [reflexivity | tauto].
  Qed.

  Definition sbb_cmds (c a : string) (bB : jasmin_expr) (t b1 r b2 bo : string)
      (rest : list jasmin_cmd) :=
    JCset t (JEsub (JEvar a) bB) :: JCset b1 (JEltu (JEvar a) (JEvar t)) ::
    JCset r (JEsub (JEvar t) (JEvar c)) :: JCset b2 (JEltu (JEvar t) (JEvar r)) ::
    JCset bo (JEadd (JEvar b1) (JEvar b2)) :: rest.

  Lemma sbb_run : forall c a bB t b1 r b2 bo rest e1 m e1' m' bn,
    window_facts c a bn t b1 r b2 bo -> is_bit (e1 c) ->
    run_list e1 m (sbb_cmds c a bB t b1 r b2 bo rest) = Some (e1', m') ->
    exists e1w, run_list e1w m rest = Some (e1', m') /\
      e1w r = word.sub (word.sub (e1 a) (ev e1 m bB)) (e1 c) /\
      e1w bo = borrow (e1 a) (ev e1 m bB) (e1 c) /\
      (forall y, ~ In y [t; b1; r; b2; bo] -> e1w y = e1 y).
  Proof.
    intros c a bB t b1 r b2 bo rest e1 m e1' m' bn F Hc H.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    unfold sbb_cmds in H. cbn [run_list run ev] in H. eexists. split; [exact H|].
    cbn [In] in *.
    simpl_upd.
    split; [|split].
    - reflexivity.
    - apply sbb_window_borrow. exact Hc.
    - intros y Hy. simpl_upd. reflexivity.
  Qed.

  Lemma sbb_in : forall c a bB t b1 r b2 bo rest y,
    In y (a :: c :: vars_of bB) -> In y (flat_map names (sbb_cmds c a bB t b1 r b2 bo rest)).
  Proof.
    intros. unfold sbb_cmds. cbn [In] in H.
    destruct H as [<-|[<-|H]].
    - apply fm_head. cbn. tauto.
    - apply fm_tail, fm_tail, fm_head. cbn. tauto.
    - apply fm_head. cbn. right. right. exact H.
  Qed.

  Lemma sbb_in_rest : forall c a bB t b1 r b2 bo rest y,
    In y (flat_map names rest) -> In y (flat_map names (sbb_cmds c a bB t b1 r b2 bo rest)).
  Proof. intros. unfold sbb_cmds. do 5 apply fm_tail. exact H. Qed.

  Lemma sbb_case : forall fuel, SIM fuel ->
    forall bits p c a bB bv t b1 r b2 bo rest e1 e2 m e1' m' (consume : bool),
    simple_arg bB = Some bv ->
    window_facts c a (bname_of a bv) t b1 r b2 bo -> In c bits ->
    ~ In t (flat_map names rest) -> ~ In b1 (flat_map names rest) ->
    ~ In b2 (flat_map names rest) ->
    INV bits p (sbb_cmds c a bB t b1 r b2 bo rest) e1 e2 ->
    NH (sbb_cmds c a bB t b1 r b2 bo rest) ->
    run_list e1 m (sbb_cmds c a bB t b1 r b2 bo rest) = Some (e1', m') ->
    (consume = true -> exists fl, p = Some (c, fl) /\ ~ In c (flat_map names rest)) ->
    exists e2', run_list e2 m
      (if consume then
         match p with
         | Some (_, fl) => JCsbb (fl_of bo) r (JEvar a) bB fl ::
             adc_list fuel (bo :: filter (fun v => notin v [t; b1; r; b2; bo]) bits)
                      (Some (bo, fl_of bo)) rest
         | None => []
         end
       else
         flush p ++
         JCadd_flags (fi_of bo) (ti_of bo) (JEvar c) (JElit (-1)) ::
         JCsbb (fl_of bo) r (JEvar a) bB (fi_of bo) ::
         adc_list fuel (bo :: filter (fun v => notin v [t; b1; r; b2; bo]) bits)
                  (Some (bo, fl_of bo)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits p c a bB bv t b1 r b2 bo rest e1 e2 m e1' m' consume Hsa Fw Hcb
      Ht Hb1 Hb2 Hinv Hnh Hrun Hcons.
    pose proof Hinv as [HA [HB HC]].
    destruct (sbb_run c a bB t b1 r b2 bo rest e1 m e1' m' (bname_of a bv) Fw (HB c Hcb) Hrun)
      as [e1w [Hrw [Hr [Hbo Hoth]]]].
    pose proof Fw as Fw'. destruct Fw' as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    apply simple_arg_spec in Hsa as [Hvb Hshape].
    assert (Hbv : forall y, In y (vars_of bB) -> y <> c /\ ~ In y [t; b1; r; b2; bo]).
    { intros y Hy. rewrite Hvb in Hy.
      destruct Hshape as [[y' [-> ->]] | [z [-> ->]]]; [|contradiction].
      destruct Hy as [<-|[]]. cbn [bname_of In] in *. split; [intro; subst; tauto|].
      intros [E|[E|[E|[E|[E|[]]]]]]; subst; tauto. }
    assert (Hrn : helper r = false) by (apply Hnh; apply fm_tail, fm_tail, fm_head; cbn; tauto).
    assert (HNH : NH rest) by (unfold sbb_cmds in Hnh; do 5 apply NH_tail in Hnh; exact Hnh).
    assert (Hfin : forall e2w,
      e2w r = word.sub (word.sub (e1 a) (ev e1 m bB)) (e1 c) ->
      bit (e2w (fl_of bo)) = borrow (e1 a) (ev e1 m bB) (e1 c) ->
      (forall y, In y (flat_map names rest) -> y <> bo -> y <> r -> e1 y = e2w y) ->
      exists e2', run_list e2w m
        (adc_list fuel (bo :: filter (fun v => notin v [t; b1; r; b2; bo]) bits)
                  (Some (bo, fl_of bo)) rest) = Some (e2', m')).
    { intros e2w Hr2 Hfl2 Hag.
      eapply (IH _ _ _ e1w e2w m e1' m' _ HNH Hrw). Unshelve.
      split; [|split].
      - intros y Hy Hpv.
        assert (y <> bo) by (intro; subst; cbn in Hpv; congruence).
        destruct (String.eqb_spec y r) as [->|Hyr]; [rewrite Hr, Hr2; reflexivity|].
        assert (y <> t) by (intro; subst; contradiction).
        assert (y <> b1) by (intro; subst; contradiction).
        assert (y <> b2) by (intro; subst; contradiction).
        rewrite Hoth by (cbn; intuition). apply Hag; assumption.
      - intros v [<-|Hv].
        + rewrite Hbo. apply borrow_bit.
        + apply filter_In in Hv as [Hv Hn]. apply notin_spec in Hn.
          rewrite Hoth by exact Hn. apply HB; exact Hv.
      - rewrite Hbo. split; [apply borrow_bit|]. split; [|apply fl_of_neq].
        rewrite Hfl2. reflexivity. }
    destruct consume.
    - destruct (Hcons eq_refl) as [fl [-> Hcr]].
      destruct HC as [_ [Hfl _]].
      assert (Ha : e1 a = e2 a).
      { apply HA; [apply sbb_in; cbn; tauto |].
        cbn; intro E; injection E as E. apply F10. cbn. left. congruence. }
      assert (HbB : ev e1 m bB = ev e2 m bB).
      { apply ev_ext. intros y Hy. apply HA.
        - apply sbb_in. right. right. exact Hy.
        - cbn. intro E; injection E as E; subst. apply (proj1 (Hbv y Hy)). reflexivity. }
      cbn [run_list run ev]. rewrite <- Ha, <- HbB, Hfl.
      apply Hfin.
      + rewrite upd_eq. reflexivity.
      + rewrite upd_ne by exact (helper_neq _ _ (helper_fl bo) Hrn).
        rewrite upd_eq. apply bit_id. apply borrow_bit.
      + intros y Hy Hybo Hyr.
        rewrite upd_ne by exact Hyr.
        rewrite upd_ne by exact (helper_not_name rest y (fl_of bo) HNH Hy (helper_fl bo)).
        assert (y <> c) by (intro; subst; contradiction).
        apply HA; [apply sbb_in_rest; exact Hy | cbn; congruence].
    - destruct (flush_ok p bits _ e1 e2 m Hinv Hnh) as [e2b [Hf [HA' _]]].
      rewrite run_list_app, Hf.
      assert (Hag3 : forall y, In y (a :: c :: vars_of bB) -> e1 y = e2b y /\ helper y = false).
      { intros y Hy. split; [apply HA'; [apply sbb_in; exact Hy | cbn; congruence] |].
        apply Hnh. apply sbb_in. exact Hy. }
      destruct (Hag3 a ltac:(cbn; tauto)) as [Ha Han].
      destruct (Hag3 c ltac:(cbn; tauto)) as [Hc Hcn].
      cbn [run_list run ev].
      rewrite (upd_ne _ (ti_of bo) _ a) by exact (not_eq_sym (helper_neq _ _ (helper_ti bo) Han)).
      rewrite (upd_ne _ (fi_of bo) _ a) by exact (not_eq_sym (helper_neq _ _ (helper_fi bo) Han)).
      rewrite (upd_ne _ (ti_of bo) _ (fi_of bo)) by apply fi_ti_neq.
      rewrite upd_eq.
      assert (HbB : ev e1 m bB = ev (upd (upd e2b (fi_of bo)
                                   (carry (e2b c) (word.of_Z (-1)) w0)) (ti_of bo)
                                   (word.add (e2b c) (word.of_Z (-1)))) m bB).
      { apply ev_ext. intros y Hy.
        destruct (Hag3 y ltac:(cbn; tauto)) as [Hy1 Hy2].
        rewrite upd_ne by exact (not_eq_sym (helper_neq _ _ (helper_ti bo) Hy2)).
        rewrite upd_ne by exact (not_eq_sym (helper_neq _ _ (helper_fi bo) Hy2)).
        exact Hy1. }
      rewrite <- HbB, <- Ha, <- Hc.
      rewrite (add_m1_flag (e1 c) (HB c Hcb)).
      apply Hfin.
      + rewrite upd_eq. reflexivity.
      + rewrite upd_ne by exact (helper_neq _ _ (helper_fl bo) Hrn).
        rewrite upd_eq. apply bit_id. apply borrow_bit.
      + intros y Hy Hybo Hyr.
        rewrite upd_ne by exact Hyr.
        rewrite upd_ne by exact (helper_not_name rest y (fl_of bo) HNH Hy (helper_fl bo)).
        rewrite upd_ne by exact (helper_not_name rest y (ti_of bo) HNH Hy (helper_ti bo)).
        rewrite upd_ne by exact (helper_not_name rest y (fi_of bo) HNH Hy (helper_fi bo)).
        apply HA'; [apply sbb_in_rest; exact Hy | cbn; congruence].
  Qed.

  Lemma sub_first_case : forall fuel, SIM fuel ->
    forall bits p a bB bv t b1 rest e1 e2 m e1' m',
    simple_arg bB = Some bv -> ~ In t [a; b1] -> ~ In t bv ->
    let cs := JCset t (JEsub (JEvar a) bB) :: JCset b1 (JEltu (JEvar a) (JEvar t)) :: rest in
    INV bits p cs e1 e2 -> NH cs -> run_list e1 m cs = Some (e1', m') ->
    exists e2', run_list e2 m
      (flush p ++ JCsub_flags (fl_of b1) t (JEvar a) bB ::
       adc_list fuel (b1 :: filter (fun v => notin v [t; b1]) bits) (Some (b1, fl_of b1)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits p a bB bv t b1 rest e1 e2 m e1' m' Hsa Ht Htb cs Hinv Hnh Hrun.
    destruct (flush_ok p bits cs e1 e2 m Hinv Hnh) as [e2b [Hf [HA [HB _]]]].
    rewrite run_list_app, Hf.
    apply simple_arg_spec in Hsa as [Hvb _].
    cbn [In] in Ht.
    unfold cs in Hrun. cbn [run_list run ev] in Hrun.
    rewrite (upd_eq e1 t) in Hrun. rewrite (upd_ne e1 t _ a) in Hrun by (intro; subst; tauto).
    assert (Hn : forall y, In y (flat_map names cs) -> helper y = false) by exact Hnh.
    assert (Ha : e1 a = e2b a) by (apply HA; [apply fm_head; cbn; tauto | cbn; congruence]).
    assert (HbB : ev e1 m bB = ev e2b m bB).
    { apply ev_ext. intros y Hy. apply HA; [apply fm_head; cbn; right; right; exact Hy | cbn; congruence]. }
    assert (Htn : helper t = false) by (apply Hnh; apply fm_head; cbn; tauto).
    assert (HNH : NH rest) by (do 2 apply NH_tail in Hnh; exact Hnh).
    cbn [run_list run ev]. rewrite <- Ha, <- HbB.
    eapply (IH _ _ _ _ _ m e1' m' _ HNH Hrun). Unshelve.
    split; [|split].
    - intros y Hy Hpv. assert (y <> b1) by (intro; subst; cbn in Hpv; congruence).
      rewrite (upd_ne _ b1 _ y) by assumption.
      destruct (String.eqb_spec y t) as [->|Hyt]; [rewrite !upd_eq; reflexivity|].
      rewrite !upd_ne by first [exact Hyt | exact (helper_not_name rest y (fl_of b1) HNH Hy (helper_fl b1))].
      apply HA; [apply fm_tail, fm_tail; exact Hy | cbn; congruence].
    - intros v [<-|Hv].
      + rewrite upd_eq. apply b2w_bit.
      + apply filter_In in Hv as [Hv Hnn]. apply notin_spec in Hnn. cbn [In] in Hnn.
        rewrite !upd_ne by (intro; subst; tauto). apply HB; exact Hv.
    - rewrite upd_eq. split; [apply b2w_bit|]. split; [|apply fl_of_neq].
      rewrite upd_ne by exact (helper_neq _ _ (helper_fl b1) Htn).
      rewrite upd_eq. rewrite sub_first_borrow. apply bit_id. apply borrow_bit.
  Qed.

  Lemma sbb_tail_case : forall fuel, SIM fuel ->
    forall bits fl c a r bo rest e1 e2 m e1' m',
    ~ In r [a; c; bo] -> ~ In bo [a; c] -> ~ In c [a] -> ~ In c (flat_map names rest) ->
    let cs := JCset r (JEsub (JEvar a) (JEvar c)) :: JCset bo (JEltu (JEvar a) (JEvar r)) :: rest in
    INV bits (Some (c, fl)) cs e1 e2 -> NH cs -> run_list e1 m cs = Some (e1', m') ->
    exists e2', run_list e2 m
      (JCsbb (fl_of bo) r (JEvar a) (JElit 0) fl ::
       adc_list fuel (bo :: filter (fun v => notin v [r; bo]) bits) (Some (bo, fl_of bo)) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH bits fl c a r bo rest e1 e2 m e1' m' Hr Hbo Hca Hcr cs Hinv Hnh Hrun.
    destruct Hinv as [HA [HB [Hcbit [Hfl Hcfl]]]].
    cbn [In] in Hr, Hbo, Hca.
    unfold cs in Hrun. cbn [run_list run ev] in Hrun.
    rewrite (upd_eq e1 r) in Hrun. rewrite (upd_ne e1 r _ a) in Hrun by (intro; subst; tauto).
    assert (Ha : e1 a = e2 a).
    { apply HA; [apply fm_head; cbn; tauto | cbn; intro E; injection E as E; subst; tauto]. }
    assert (Hrn : helper r = false) by (apply Hnh; apply fm_head; cbn; tauto).
    assert (HNH : NH rest) by (do 2 apply NH_tail in Hnh; exact Hnh).
    cbn [run_list run ev]. rewrite <- Ha, Hfl.
    rewrite Properties.word.sub_0_r.
    eapply (IH _ _ _ _ _ m e1' m' _ HNH Hrun). Unshelve.
    split; [|split].
    - intros y Hy Hpv. assert (y <> bo) by (intro; subst; cbn in Hpv; congruence).
      rewrite (upd_ne _ bo _ y) by assumption.
      destruct (String.eqb_spec y r) as [->|Hyr]; [rewrite !upd_eq; reflexivity|].
      rewrite !upd_ne by first [exact Hyr | exact (helper_not_name rest y (fl_of bo) HNH Hy (helper_fl bo))].
      assert (y <> c) by (intro; subst; contradiction).
      apply HA; [apply fm_tail, fm_tail; exact Hy | cbn; congruence].
    - intros v [<-|Hv].
      + rewrite upd_eq. apply b2w_bit.
      + apply filter_In in Hv as [Hv Hnn]. apply notin_spec in Hnn. cbn [In] in Hnn.
        rewrite !upd_ne by (intro; subst; tauto). apply HB; exact Hv.
    - rewrite upd_eq. split; [apply b2w_bit|]. split; [|apply fl_of_neq].
      rewrite upd_ne by exact (helper_neq _ _ (helper_fl bo) Hrn).
      rewrite upd_eq. rewrite sbb_tail_borrow. apply bit_id. apply borrow_bit.
  Qed.

  Lemma adc_list_ok : forall fuel, SIM fuel.
  Proof.
    induction fuel as [|fuel IH]; intros bits p cs e1 e2 m e1' m' Hinv Hnh Hrun.
    - cbn [adc_list]. destruct (flush_ok p bits cs e1 e2 m Hinv Hnh) as [e2b [Hf [HA _]]].
      rewrite run_list_app, Hf. eapply frame_list; [exact Hrun|].
      intros y Hy. apply HA; [exact Hy | cbn; congruence].
    - destruct cs as [|k1 rest1].
      + cbn [run_list] in Hrun. injection Hrun as <- <-. cbn [adc_list].
        destruct (flush_ok p bits [] e1 e2 m Hinv Hnh) as [e2b [Hf _]].
        rewrite Hf. eexists; reflexivity.
      + cbn [adc_list]. cbv beta zeta.
        destruct (match_first_add k1 rest1) as [[[[[[fl s] a] b] x] rest]|] eqn:F.
        * pose proof (match_first_add_spec _ _ _ _ _ _ _ _ F) as (-> & -> & Hxfl).
          exact (first_add_case fuel IH bits p fl s a b x rest e1 e2 m e1' m' Hxfl Hinv Hnh Hrun).
        * destruct (match_window k1 rest1) as [[[[[[[[[c a] b] s] c1] r] c2] co] rest]|] eqn:W.
          -- pose proof (match_window_spec _ _ _ _ _ _ _ _ _ _ _ W) as [Wcs Wok].
             apply window_names_ok_facts in Wok.
             destruct (existsb (String.eqb c) bits &&
                       negb (existsb (fun k => mentions s k || mentions c1 k || mentions c2 k) rest))
               eqn:C.
             ++ apply andb_true_iff in C as [C1 C2]. apply negb_true_iff in C2.
                assert (Hcb : In c bits).
                { apply existsb_exists in C1 as [v [Hv E]]. apply String.eqb_eq in E.
                  subst. exact Hv. }
                destruct (window_dead s c1 c2 rest C2) as (Hs & Hc1 & Hc2).
                rewrite Wcs in Hinv, Hnh, Hrun.
                destruct p as [[x fl]|].
                ** destruct (String.eqb x c && negb (existsb (mentions c) rest)) eqn:D.
                   --- apply andb_true_iff in D as [D1 D2]. apply String.eqb_eq in D1. subst x.
                       apply negb_true_iff in D2. apply not_mentioned_rest in D2.
                       exact (window_consume_case fuel IH bits fl c a b s c1 r c2 co rest
                                e1 e2 m e1' m' Wok Hcb Hs Hc1 Hc2 D2 Hinv Hnh Hrun).
                   --- exact (window_fresh_case fuel IH bits (Some (x, fl)) c a b s c1 r c2 co rest
                                e1 e2 m e1' m' Wok Hcb Hs Hc1 Hc2 Hinv Hnh Hrun).
                ** exact (window_fresh_case fuel IH bits None c a b s c1 r c2 co rest
                            e1 e2 m e1' m' Wok Hcb Hs Hc1 Hc2 Hinv Hnh Hrun).
             ++ exact (step_case fuel IH bits p k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun).
          -- destruct (match_sbb_window k1 rest1)
               as [[[[[[[[[c a] bB] t] b1] r] b2] bo] rest]|] eqn:SW.
             ++ destruct (match_sbb_window_spec _ _ _ _ _ _ _ _ _ _ _ SW) as [bv [Hsa [Wcs Wok]]].
                apply window_names_ok_facts in Wok.
                destruct (existsb (String.eqb c) bits &&
                          negb (existsb (fun k => mentions t k || mentions b1 k || mentions b2 k) rest))
                  eqn:C.
                ** apply andb_true_iff in C as [C1 C2]. apply negb_true_iff in C2.
                   assert (Hcb : In c bits).
                   { apply existsb_exists in C1 as [v [Hv E]]. apply String.eqb_eq in E.
                     subst. exact Hv. }
                   destruct (window_dead t b1 b2 rest C2) as (Ht & Hb1 & Hb2).
                   rewrite Wcs in Hinv, Hnh, Hrun.
                   destruct p as [[x fl]|].
                   --- destruct (String.eqb x c && negb (existsb (mentions c) rest)) eqn:D.
                       +++ apply andb_true_iff in D as [D1 D2]. apply String.eqb_eq in D1. subst x.
                           apply negb_true_iff in D2. apply not_mentioned_rest in D2.
                           exact (sbb_case fuel IH bits (Some (c, fl)) c a bB bv t b1 r b2 bo rest
                                    e1 e2 m e1' m' true Hsa Wok Hcb Ht Hb1 Hb2 Hinv Hnh Hrun
                                    (fun _ => ex_intro _ fl (conj eq_refl D2))).
                       +++ exact (sbb_case fuel IH bits (Some (x, fl)) c a bB bv t b1 r b2 bo rest
                                    e1 e2 m e1' m' false Hsa Wok Hcb Ht Hb1 Hb2 Hinv Hnh Hrun
                                    (fun H => ltac:(discriminate H))).
                   --- exact (sbb_case fuel IH bits None c a bB bv t b1 r b2 bo rest
                                e1 e2 m e1' m' false Hsa Wok Hcb Ht Hb1 Hb2 Hinv Hnh Hrun
                                (fun H => ltac:(discriminate H))).
                ** exact (step_case fuel IH bits p k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun).
             ++ destruct (match_sub_first k1 rest1) as [[[[[a bB] t] b1] rest]|] eqn:SF.
                ** destruct (match_sub_first_spec _ _ _ _ _ _ _ SF) as [bv [Hsa [Wcs [Ht Htb]]]].
                   rewrite Wcs in Hinv, Hnh, Hrun.
                   exact (sub_first_case fuel IH bits p a bB bv t b1 rest e1 e2 m e1' m'
                            Hsa Ht Htb Hinv Hnh Hrun).
                ** destruct (match_sbb_tail k1 rest1) as [[[[[c a] r] bo] rest]|] eqn:ST.
                   --- destruct (match_sbb_tail_spec _ _ _ _ _ _ _ ST) as [Wcs [Hr [Hbo Hca]]].
                       destruct p as [[x fl]|].
                       +++ destruct (String.eqb x c && negb (existsb (mentions c) rest)) eqn:D.
                           *** apply andb_true_iff in D as [D1 D2]. apply String.eqb_eq in D1.
                               subst x. apply negb_true_iff in D2. apply not_mentioned_rest in D2.
                               rewrite Wcs in Hinv, Hnh, Hrun.
                               exact (sbb_tail_case fuel IH bits fl c a r bo rest e1 e2 m e1' m'
                                        Hr Hbo Hca D2 Hinv Hnh Hrun).
                           *** exact (step_case fuel IH bits _ k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun).
                       +++ exact (step_case fuel IH bits _ k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun).
                   --- exact (step_case fuel IH bits p k1 rest1 e1 e2 m e1' m' Hinv Hnh Hrun).
  Qed.

  (** Main theorem: whenever the original command runs, the rewritten
      one runs to the same final memory. *)
  Theorem adc_cmd_correct : forall c e m e' m',
    run e m c = Some (e', m') -> exists e'', run e m (adc_cmd c) = Some (e'', m').
  Proof.
    intros c e m e' m' H. unfold adc_cmd. cbv zeta.
    destruct (no_helpers (cmd_to_list c)) eqn:Hn.
    - rewrite run_list_to_cmd. rewrite run_cmd_to_list in H.
      refine (adc_list_ok (S (length (cmd_to_list c))) [] None (cmd_to_list c) e e m e' m'
                _ _ H).
      + split; [intros; reflexivity | split; [intros v [] | exact I]].
      + intros x Hx. unfold no_helpers in Hn. rewrite forallb_forall in Hn.
        apply in_flat_map in Hx as [k [Hk Hx]]. specialize (Hn k Hk). apply negb_true_iff in Hn.
        destruct (helper x) eqn:Hh; [|reflexivity]. exfalso.
        assert (existsb helper (names k) = true) by (apply existsb_exists; exists x; auto).
        congruence.
    - exists e'. exact H.
  Qed.

  Theorem adc_func_correct : forall f e m e' m',
    run e m (jf_body f) = Some (e', m') ->
    exists e'', run e m (jf_body (adc_func f)) = Some (e'', m').
  Proof. intros. eapply adc_cmd_correct. eassumption. Qed.

  Lemma adc_func_signature : forall f,
    jf_name (adc_func f) = jf_name f /\ jf_params (adc_func f) = jf_params f /\
    jf_locals (adc_func f) = jf_locals f.
  Proof. intros; repeat split. Qed.

End Sem.
