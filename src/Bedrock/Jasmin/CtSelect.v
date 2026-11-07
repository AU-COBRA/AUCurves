(** * CtSelect: the Fp leaves' remaining branches as flag and mask arithmetic.

    After [AdcChain.polish_func_adc], fiat-crypto's Fp leaves (add, sub,
    mul, square, select_znz) still hold three kinds of [if], and
    [Core.pp_cmd] prints each as a Jasmin [if], which jasminc compiles to a
    conditional jump on secret data:

      - [x = 0; if fl { x = 1; }]: a carry, a borrow or a comparison copied
        into a word ([carry_func], [lower_comparisons]);
      - [x = 0; if fl { x = 0; x = x - 1; }]: the borrow mask of fiat's
        subtraction (all ones on a borrow);
      - [if (v == 0) { x = a; } else { x = b; }]: fiat's [cmovznz], one per
        limb, selecting [t] or [t - p] after the final subtraction of add,
        mul and square, and the selection of [select_znz].

    [ct_func] rewrites them without a branch:

      - [x = 0; __ct_c, x = #ADCX(x, x, fl)]       ([x = bit fl], as
        [AdcChain.materialize]);
      - [x = 0; __ct_c, x = #SBB(x, x, fl)]        ([x = 0 - 0 - bit fl]);
      - the mask [__ct_m = (v == 0) ? -1 : 0], computed as
        [_, __ct_f, __ct_t = #SUB(v, 1)] (the borrow of [v - 1] is [v == 0])
        and [__ct_m = #SBB(__ct_t, __ct_t, __ct_f)], once for a run of
        selects on the same [v], and per select
        [x = b ^ ((a ^ b) & __ct_m)] in five two-address steps.

    Correctness ([ct_cmd_correct]) is stated, as for [AdcChain.adc_cmd_correct],
    against [AdcChain.run], the semantics of the straight-line fragment in which
    [#ADCX]/[#SUB]/[#SBB] compute their real carries and borrows: whenever the
    original command runs, the rewritten one runs to the same final memory (the
    leaves return through memory only).  New variable names all start with
    ["__ct"]; [ct_cmd] leaves a body that already mentions such a name unchanged.
    The rewrite is a [jasmin_cmd] to [jasmin_cmd] pass, so the printers and their
    lemmas ([SpillLiveness.pp_module_live_erases], ...) apply to its output as
    they stand, and [AdcChain] is not changed.  [has_branch] tests the result
    syntactically; the extraction files check it on the leaves by computation. *)

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.AdcChain.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
From Stdlib Require Import String List ZArith Bool Lia.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* Names                                                             *)
(* ================================================================ *)

Definition ct_helper (x : string) : bool := String.prefix "__ct" x.

Definition ct_t : string := "__ct_t".
Definition ct_m : string := "__ct_m".
Definition ct_f : string := "__ct_f".
Definition ct_c : string := "__ct_c".

(* ================================================================ *)
(* The pass                                                           *)
(* ================================================================ *)

(** [x = 0; if fl { x = 1; }] (neg = false) and
    [x = 0; if fl { x = 0; x = x - 1; }] (neg = true). *)
Definition match_flag (k1 : jasmin_cmd) (rest1 : list jasmin_cmd)
    : option (string * string * bool * list jasmin_cmd) :=
  match k1, rest1 with
  | JCset x (JElit z0), JCif (JEvar fl) t JCskip :: rest =>
      if Z.eqb z0 0 && negb (String.eqb x fl) then
        match cmd_to_list t with
        | [JCset x1 (JElit z1)] =>
            if String.eqb x x1 && Z.eqb z1 1 then Some (x, fl, false, rest) else None
        | [JCset x1 (JElit z1); JCset x2 (JEsub (JEvar x3) (JElit z2))] =>
            if String.eqb x x1 && String.eqb x x2 && String.eqb x x3 && Z.eqb z1 0 && Z.eqb z2 1
            then Some (x, fl, true, rest) else None
        | _ => None
        end
      else None
  | _, _ => None
  end.

Definition flag_cmd (x fl : string) (neg : bool) : jasmin_cmd :=
  if neg then JCsbb ct_c x (JEvar x) (JEvar x) fl
  else JCadcx ct_c x (JEvar x) (JEvar x) fl.

Definition flag_cmds (x fl : string) (neg : bool) : list jasmin_cmd :=
  [JCset x (JElit 0); flag_cmd x fl neg].

(** [if (v == 0) { x = a; } else { x = b; }]. *)
Definition match_select (k : jasmin_cmd) : option (string * string * string * string) :=
  match k with
  | JCif (JEeq (JEvar v) (JElit z)) t f =>
      if Z.eqb z 0 then
        match cmd_to_list t, cmd_to_list f with
        | [JCset x (JEvar a)], [JCset x' (JEvar b)] =>
            if String.eqb x x' then Some (v, x, a, b) else None
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** [__ct_m = (v == 0) ? -1 : 0]. *)
Definition mask_cmds (v : string) : list jasmin_cmd :=
  [JCsub_flags ct_f ct_t (JEvar v) (JElit 1);
   JCsbb ct_c ct_m (JEvar ct_t) (JEvar ct_t) ct_f].

(** [x = b ^ ((a ^ b) & __ct_m)]. *)
Definition select_cmds (x a b : string) : list jasmin_cmd :=
  [JCset ct_t (JEvar a);
   JCset ct_t (JExor (JEvar ct_t) (JEvar b));
   JCset ct_t (JEand (JEvar ct_t) (JEvar ct_m));
   JCset x (JEvar b);
   JCset x (JExor (JEvar x) (JEvar ct_t))].

(** The variable whose mask [__ct_m] holds, kept while nothing names it. *)
Definition keep (cache : option string) (l : list string) : option string :=
  match cache with
  | Some w => if existsb (String.eqb w) l then None else cache
  | None => None
  end.

Definition hit (cache : option string) (v : string) : bool :=
  match cache with Some w => String.eqb w v | None => false end.

Fixpoint ct_list (fuel : nat) (cache : option string) (cs : list jasmin_cmd) {struct fuel}
    : list jasmin_cmd :=
  match fuel with
  | O => cs
  | S fuel' =>
      match cs with
      | [] => []
      | k1 :: rest1 =>
          match match_flag k1 rest1 with
          | Some (x, fl, neg, rest) =>
              flag_cmds x fl neg ++ ct_list fuel' (keep cache [x; fl]) rest
          | None =>
              match match_select k1 with
              | Some (v, x, a, b) =>
                  (if hit cache v then [] else mask_cmds v) ++ select_cmds x a b ++
                  ct_list fuel' (if String.eqb x v then None else Some v) rest1
              | None => k1 :: ct_list fuel' (keep cache (names k1)) rest1
              end
          end
      end
  end.

Definition no_ct_helpers (cs : list jasmin_cmd) : bool :=
  forallb (fun k => negb (existsb ct_helper (names k))) cs.

Definition ct_cmd (c : jasmin_cmd) : jasmin_cmd :=
  let cs := cmd_to_list c in
  if no_ct_helpers cs then list_to_cmd (ct_list (S (length cs)) None cs) else c.

Definition ct_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f; jf_params := jf_params f; jf_locals := jf_locals f;
     jf_body := ct_cmd (jf_body f) |}.

(** A body without [if] and [while]: [pp_cmd] prints no conditional. *)
Fixpoint has_branch (c : jasmin_cmd) : bool :=
  match c with
  | JCif _ _ _ | JCwhile _ _ => true
  | JCseq a b => has_branch a || has_branch b
  | JCdecl _ _ b => has_branch b
  | _ => false
  end.

Definition branch_free_funcs (fs : list jasmin_func) : bool :=
  forallb (fun f => negb (has_branch (jf_body f))) fs.

Lemma ct_func_signature : forall f,
  jf_name (ct_func f) = jf_name f /\ jf_params (ct_func f) = jf_params f /\
  jf_locals (ct_func f) = jf_locals f.
Proof. intros; repeat split. Qed.

(* ================================================================ *)
(* Correctness against [AdcChain.run]                                 *)
(* ================================================================ *)

Section Sem.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width} {word_ok : word.ok word}.

  Add Ring wring : (@Properties.word.ring_theory width word word_ok).

  Local Notation wenv := (@env width word).

  (** The mask of [v == 0]. *)
  Definition mask (w : word) : word :=
    if word.eqb w (word.of_Z 0) then word.of_Z (-1) else word.of_Z 0.

  (* ---------------------------------------------------------------- *)
  (* Word facts                                                        *)
  (* ---------------------------------------------------------------- *)

  Lemma xor_0_r : forall x : word, word.xor x (word.of_Z 0) = x.
  Proof.
    intros. apply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_xor_nowrap, Properties.word.unsigned_of_Z_0, Z.lxor_0_r.
    reflexivity.
  Qed.

  Lemma xor_0_l : forall x : word, word.xor (word.of_Z 0) x = x.
  Proof. intros. rewrite Properties.word.xor_comm. apply xor_0_r. Qed.

  Lemma and_m1_r : forall x : word, word.and x (word.of_Z (-1)) = x.
  Proof.
    intros. apply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_and_nowrap, Properties.word.unsigned_of_Z_minus1.
    rewrite Z.land_ones by (pose proof (@word.width_pos width word word_ok); lia).
    apply Properties.word.wrap_unsigned.
  Qed.

  Lemma and_0_r : forall x : word, word.and x (word.of_Z 0) = word.of_Z 0.
  Proof.
    intros. apply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_and_nowrap, !Properties.word.unsigned_of_Z_0, Z.land_0_r.
    reflexivity.
  Qed.

  Lemma xor_self : forall x : word, word.xor x x = word.of_Z 0.
  Proof.
    intros. apply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent, Properties.word.unsigned_of_Z_0.
    reflexivity.
  Qed.

  Lemma sel_mask : forall a b w : word,
    word.xor b (word.and (word.xor a b) (mask w)) =
    (if word.eqb w (word.of_Z 0) then a else b).
  Proof.
    intros a b w. unfold mask. destruct (word.eqb w (word.of_Z 0)).
    - rewrite and_m1_r, (Properties.word.xor_comm a b), Properties.word.xor_assoc,
        xor_self, xor_0_l. reflexivity.
    - rewrite and_0_r. apply xor_0_r.
  Qed.

  Local Open Scope Z_scope.

  (** The borrow of [v - 1] is [v == 0]. *)
  Lemma borrow_m1 : forall w : word,
    bit (borrow w (word.of_Z 1) w0) = b2w (word.eqb w (word.of_Z 0)).
  Proof.
    intros w. rewrite bit_id by apply b2w_bit. unfold borrow. f_equal.
    rewrite word.unsigned_eqb. change (word.of_Z 1) with (@w1 width word).
    rewrite u_w1, u_w0, Properties.word.unsigned_of_Z_0.
    pose proof (Properties.word.unsigned_range w).
    destruct (Z.ltb_spec (word.unsigned w - 1 - 0) 0);
      destruct (Z.eqb_spec (word.unsigned w) 0); first [reflexivity | exfalso; lia].
  Qed.

  Lemma mask_from_borrow : forall y w : word,
    word.sub (word.sub y y) (bit (borrow w (word.of_Z 1) w0)) = mask w.
  Proof.
    intros. rewrite borrow_m1. unfold mask, b2w, w1, w0.
    destruct (word.eqb w (word.of_Z 0)).
    - change (word.of_Z (-1)) with (@word.of_Z width word (Z.opp 1)).
      rewrite Properties.word.ring_morph_opp. ring.
    - ring.
  Qed.

  Local Close Scope Z_scope.

  (* ---------------------------------------------------------------- *)
  (* Names                                                             *)
  (* ---------------------------------------------------------------- *)

  Lemma names_cmd_to_list : forall c y, In y (flat_map names (cmd_to_list c)) -> In y (names c).
  Proof.
    induction c; intros y Hy; cbn [cmd_to_list flat_map] in Hy;
      try (rewrite app_nil_r in Hy; exact Hy).
    - destruct Hy.
    - cbn [names]. rewrite flat_map_app in Hy. apply in_app_or in Hy as [H|H];
        apply in_or_app; [left; apply IHc1 | right; apply IHc2]; exact H.
  Qed.

  Definition NHc (cs : list jasmin_cmd) : Prop :=
    forall x, In x (flat_map names cs) -> ct_helper x = false.

  Lemma NHc_tail : forall k cs, NHc (k :: cs) -> NHc cs.
  Proof. intros k cs H x Hx. apply H. cbn. apply in_or_app; auto. Qed.

  Lemma fm_tail' : forall y k l, In y (flat_map names l) -> In y (flat_map names (k :: l)).
  Proof. intros. cbn [flat_map]. apply in_or_app. right. exact H. Qed.
  Lemma fm_head' : forall y k l, In y (names k) -> In y (flat_map names (k :: l)).
  Proof. intros. cbn [flat_map]. apply in_or_app. left. exact H. Qed.

  Lemma not_helper : forall y h, ct_helper y = false -> ct_helper h = true -> y <> h.
  Proof. intros y h Hy Hh ->. congruence. Qed.

  Lemma helper_t : ct_helper ct_t = true. Proof. reflexivity. Qed.
  Lemma helper_m : ct_helper ct_m = true. Proof. reflexivity. Qed.
  Lemma helper_f : ct_helper ct_f = true. Proof. reflexivity. Qed.
  Lemma helper_c : ct_helper ct_c = true. Proof. reflexivity. Qed.

  Ltac bool_hyps :=
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
    | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
    | H : negb _ = true |- _ => apply negb_true_iff in H
    end.

  Lemma match_flag_spec : forall k1 rest1 x fl neg rest,
    match_flag k1 rest1 = Some (x, fl, neg, rest) ->
    exists t, k1 = JCset x (JElit 0) /\ rest1 = JCif (JEvar fl) t JCskip :: rest /\ x <> fl /\
      cmd_to_list t = (if neg then [JCset x (JElit 0); JCset x (JEsub (JEvar x) (JElit 1))]
                       else [JCset x (JElit 1)]).
  Proof.
    intros k1 rest1 x fl neg rest H. unfold match_flag in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end;
    injection H as <- <- <- <-; bool_hyps;
    eexists; (split; [reflexivity|]); (split; [reflexivity|]);
    (split; [apply String.eqb_neq; assumption|]); assumption.
  Qed.

  Lemma match_select_spec : forall k v x a b,
    match_select k = Some (v, x, a, b) ->
    exists t f, k = JCif (JEeq (JEvar v) (JElit 0)) t f /\
      cmd_to_list t = [JCset x (JEvar a)] /\ cmd_to_list f = [JCset x (JEvar b)].
  Proof.
    intros k v x a b H. unfold match_select in H.
    repeat match goal with
    | H : match ?v with _ => _ end = Some _ |- _ => destruct v eqn:?; try discriminate H
    end.
    injection H as <- <- <- <-. bool_hyps.
    do 2 eexists. split; [reflexivity|]. split; assumption.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Running the pieces                                                *)
  (* ---------------------------------------------------------------- *)

  Ltac upd_side := first [ discriminate | assumption | congruence ].

  Ltac simpl_upd_ct :=
    repeat match goal with
    | |- context [upd ?e ?x ?v ?x] => rewrite (upd_eq e x v)
    | |- context [upd ?e ?x ?v ?y] => rewrite (upd_ne e x v y) by upd_side
    end.

  Lemma mask_run : forall (e : wenv) m v,
    exists e', run_list e m (mask_cmds v) = Some (e', m) /\
      e' ct_m = mask (e v) /\
      (forall y, y <> ct_t -> y <> ct_f -> y <> ct_c -> y <> ct_m -> e' y = e y).
  Proof.
    intros e m v. cbn [mask_cmds run_list run ev]. eexists. split; [reflexivity|].
    split.
    - simpl_upd_ct. apply mask_from_borrow.
    - intros y H1 H2 H3 H4. simpl_upd_ct. reflexivity.
  Qed.

  Lemma select_run : forall (e : wenv) m x a b,
    a <> ct_t -> b <> ct_t -> x <> ct_t ->
    exists e', run_list e m (select_cmds x a b) = Some (e', m) /\
      e' x = word.xor (e b) (word.and (word.xor (e a) (e b)) (e ct_m)) /\
      (forall y, y <> x -> y <> ct_t -> e' y = e y).
  Proof.
    intros e m x a b Ha Hb Hx. cbn [select_cmds run_list run ev]. eexists. split; [reflexivity|].
    split.
    - simpl_upd_ct. reflexivity.
    - intros y Hyx Hyt. simpl_upd_ct. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The simulation                                                    *)
  (* ---------------------------------------------------------------- *)

  (** [__ct_m] holds the mask of the cached variable's original value. *)
  Definition CINV (cache : option string) (e1 e2 : wenv) : Prop :=
    match cache with
    | Some v => e2 ct_m = mask (e1 v)
    | None => True
    end.

  Definition SIM (fuel : nat) : Prop :=
    forall cache cs e1 e2 m e1' m',
      agree_on (flat_map names cs) e1 e2 -> CINV cache e1 e2 -> NHc cs ->
      run_list e1 m cs = Some (e1', m') ->
      exists e2', run_list e2 m (ct_list fuel cache cs) = Some (e2', m').

  Lemma keep_spec : forall cache l (e1 e2 e1' e2' : wenv),
    CINV cache e1 e2 ->
    (forall v, ~ In v l -> e1' v = e1 v) -> e2' ct_m = e2 ct_m ->
    CINV (keep cache l) e1' e2'.
  Proof.
    intros cache l e1 e2 e1' e2' H H1 H2. destruct cache as [w|]; cbn in *; [|exact I].
    destruct (existsb (String.eqb w) l) eqn:E; [exact I|]. unfold CINV.
    rewrite H2, H, H1; [reflexivity|].
    intro Hin. assert (existsb (String.eqb w) l = true) as E'
      by (apply existsb_exists; exists w; split; [exact Hin | apply String.eqb_refl]).
    congruence.
  Qed.

  Lemma plain_case : forall fuel, SIM fuel ->
    forall cache k1 rest1 e1 e2 m e1' m',
    agree_on (flat_map names (k1 :: rest1)) e1 e2 -> CINV cache e1 e2 -> NHc (k1 :: rest1) ->
    run_list e1 m (k1 :: rest1) = Some (e1', m') ->
    exists e2', run_list e2 m (k1 :: ct_list fuel (keep cache (names k1)) rest1) = Some (e2', m').
  Proof.
    intros fuel IH cache k1 rest1 e1 e2 m e1' m' Hag Hc Hnh Hrun.
    cbn [run_list] in Hrun |- *. destruct (run e1 m k1) as [[e1a ma]|] eqn:Hk; [|discriminate].
    destruct (frame k1 e1 e2 m e1a ma Hk) as [e2a [Hk' Hfr]].
    { intros y Hy. apply Hag. apply fm_head'. exact Hy. }
    rewrite Hk'. apply (IH _ rest1 e1a e2a ma e1' m'); [| | exact (NHc_tail _ _ Hnh) | exact Hrun].
    - intros y Hy. destruct (in_dec String.string_dec y (names k1)) as [Hin|Hnin].
      + apply Hfr; exact Hin.
      + destruct (proj2 (Hfr y) Hnin) as [-> ->]. apply Hag. apply fm_tail'. exact Hy.
    - apply (keep_spec cache (names k1) e1 e2); [exact Hc | |].
      + intros v Hv. exact (proj1 (proj2 (Hfr v) Hv)).
      + assert (~ In ct_m (names k1)) as Hm.
        { intro Hin. pose proof (Hnh ct_m (fm_head' _ _ _ Hin)). discriminate. }
        exact (proj2 (proj2 (Hfr ct_m) Hm)).
  Qed.

  Lemma flag_case : forall fuel, SIM fuel ->
    forall cache x fl (neg : bool) t rest (e1 e2 : wenv) m e1' m',
    let cs := JCset x (JElit 0) :: JCif (JEvar fl) t JCskip :: rest in
    x <> fl ->
    cmd_to_list t = (if neg then [JCset x (JElit 0); JCset x (JEsub (JEvar x) (JElit 1))]
                     else [JCset x (JElit 1)]) ->
    agree_on (flat_map names cs) e1 e2 -> CINV cache e1 e2 -> NHc cs ->
    run_list e1 m cs = Some (e1', m') ->
    exists e2', run_list e2 m (flag_cmds x fl neg ++ ct_list fuel (keep cache [x; fl]) rest)
      = Some (e2', m').
  Proof.
    intros fuel IH cache x fl neg t rest e1 e2 m e1' m' cs Hxfl Ht Hag Hc Hnh Hrun.
    unfold cs in *. cbn [run_list run ev] in Hrun.
    rewrite (upd_ne e1 x (word.of_Z 0) fl) in Hrun by (intro E; apply Hxfl; symmetry; exact E).
    assert (Nx : ct_helper x = false) by (apply Hnh; apply fm_head'; cbn; tauto).
    assert (Nfl : ct_helper fl = false) by (apply Hnh; apply fm_tail', fm_head'; cbn; tauto).
    pose proof (not_helper _ _ Nx helper_c) as Hxc.
    pose proof (not_helper _ _ Nx helper_m) as Hxm.
    pose proof (not_helper _ _ Nfl helper_c) as Hflc.
    assert (Hflx : fl <> x) by congruence.
    assert (Hfl : e1 fl = e2 fl) by (apply Hag; apply fm_tail', fm_head'; cbn; tauto).
    assert (Hrest : forall y, In y (flat_map names rest) -> e1 y = e2 y).
    { intros y Hy. apply Hag. apply fm_tail', fm_tail'. exact Hy. }
    assert (HNH : NHc rest) by (do 2 apply NHc_tail in Hnh; exact Hnh).
    rewrite run_list_app.
    (* the value both sides give [x] *)
    set (val := if neg then word.sub w0 (bit (e1 fl)) else bit (e1 fl)).
    assert (Horig : exists e1b, run_list e1b m rest = Some (e1', m') /\
              e1b x = val /\ forall y, y <> x -> e1b y = e1 y).
    { destruct (word.eqb (e1 fl) w0) eqn:Ew.
      - exists (upd e1 x (word.of_Z 0)). split; [exact Hrun|]. split.
        + rewrite upd_eq. unfold val, bit. rewrite Ew. cbn [negb b2w].
          destruct neg; [unfold w0; ring | reflexivity].
        + intros y Hy. apply upd_ne. exact Hy.
      - rewrite (run_cmd_to_list t), Ht in Hrun. destruct neg; cbn [run_list run ev] in Hrun.
        + eexists. split; [exact Hrun|]. split.
          * simpl_upd_ct. unfold val, bit. rewrite Ew. reflexivity.
          * intros y Hy. simpl_upd_ct. reflexivity.
        + eexists. split; [exact Hrun|]. split.
          * simpl_upd_ct. unfold val, bit. rewrite Ew. reflexivity.
          * intros y Hy. simpl_upd_ct. reflexivity. }
    destruct Horig as [e1b [Hrunb [Hxb Hyb]]].
    assert (Hnew : exists e2b, run_list e2 m (flag_cmds x fl neg) = Some (e2b, m) /\
              e2b x = val /\ e2b ct_m = e2 ct_m /\
              forall y, y <> x -> y <> ct_c -> e2b y = e2 y).
    { unfold flag_cmds, flag_cmd. destruct neg; cbn [run_list run ev]; eexists;
        (split; [reflexivity|]); (split; [|split]).
      - simpl_upd_ct. unfold val. rewrite Hfl. unfold w0. ring.
      - simpl_upd_ct. reflexivity.
      - intros y Hy1 Hy2. simpl_upd_ct. reflexivity.
      - simpl_upd_ct. unfold val. rewrite Hfl. rewrite !Properties.word.add_0_l. reflexivity.
      - simpl_upd_ct. reflexivity.
      - intros y Hy1 Hy2. simpl_upd_ct. reflexivity. }
    destruct Hnew as [e2b [Hrun2 [Hx2 [Hm2 Hy2]]]].
    rewrite Hrun2.
    apply (IH _ rest e1b e2b m e1' m'); [| | exact HNH | exact Hrunb].
    - intros y Hy. destruct (String.eqb_spec y x) as [->|Hyx].
      + rewrite Hxb, Hx2. reflexivity.
      + rewrite Hyb by exact Hyx.
        rewrite Hy2 by first [exact Hyx | exact (not_helper _ _ (HNH y Hy) helper_c)].
        apply Hrest. exact Hy.
    - apply (keep_spec cache [x; fl] e1 e2); [exact Hc | | exact Hm2].
      intros v Hv. apply Hyb. intro E; apply Hv; left; symmetry; exact E.
  Qed.

  Lemma select_case : forall fuel, SIM fuel ->
    forall cache v x a b t f rest1 e1 e2 m e1' m',
    let k1 := JCif (JEeq (JEvar v) (JElit 0)) t f in
    cmd_to_list t = [JCset x (JEvar a)] -> cmd_to_list f = [JCset x (JEvar b)] ->
    agree_on (flat_map names (k1 :: rest1)) e1 e2 -> CINV cache e1 e2 -> NHc (k1 :: rest1) ->
    run_list e1 m (k1 :: rest1) = Some (e1', m') ->
    exists e2', run_list e2 m
      ((if hit cache v then [] else mask_cmds v) ++ select_cmds x a b ++
       ct_list fuel (if String.eqb x v then None else Some v) rest1) = Some (e2', m').
  Proof.
    intros fuel IH cache v x a b t f rest1 e1 e2 m e1' m' k1 Ht Hf Hag Hc Hnh Hrun.
    assert (Hin : forall y, In y [v; x; a; b] -> In y (flat_map names (k1 :: rest1))).
    { intros y Hy. apply fm_head'. unfold k1. cbn [names vars_of].
      assert (In x (names t) /\ In a (names t)) as [Hxt Hat].
      { split; apply names_cmd_to_list; rewrite Ht; cbn; tauto. }
      assert (In b (names f)) as Hbf by (apply names_cmd_to_list; rewrite Hf; cbn; tauto).
      cbn [In] in Hy. rewrite !in_app_iff. cbn [In].
      destruct Hy as [<-|[<-|[<-|[<-|[]]]]]; tauto. }
    assert (Hv : e1 v = e2 v) by (apply Hag, Hin; cbn; tauto).
    assert (Ha : e1 a = e2 a) by (apply Hag, Hin; cbn; tauto).
    assert (Hb : e1 b = e2 b) by (apply Hag, Hin; cbn; tauto).
    assert (Nx : ct_helper x = false) by (apply Hnh, Hin; cbn; tauto).
    assert (Na : ct_helper a = false) by (apply Hnh, Hin; cbn; tauto).
    assert (Nb : ct_helper b = false) by (apply Hnh, Hin; cbn; tauto).
    assert (Hrest : forall y, In y (flat_map names rest1) -> e1 y = e2 y).
    { intros y Hy. apply Hag. apply fm_tail'. exact Hy. }
    assert (HNH : NHc rest1) by (apply NHc_tail in Hnh; exact Hnh).
    (* the original *)
    unfold k1 in Hrun. cbn [run_list run ev] in Hrun.
    set (val := if word.eqb (e1 v) (word.of_Z 0) then e1 a else e1 b).
    assert (Horig : run_list (upd e1 x val) m rest1 = Some (e1', m')).
    { unfold val. destruct (word.eqb (e1 v) (word.of_Z 0)) eqn:E; cbn [b2w] in Hrun.
      - rewrite Properties.word.eqb_ne in Hrun by (intro E'; apply w0_ne_w1; symmetry; exact E').
        rewrite (run_cmd_to_list t), Ht in Hrun. cbn [run_list run ev] in Hrun. exact Hrun.
      - rewrite Properties.word.eqb_eq in Hrun by reflexivity.
        rewrite (run_cmd_to_list f), Hf in Hrun. cbn [run_list run ev] in Hrun. exact Hrun. }
    (* the mask, computed or cached *)
    assert (Hmask : exists e2m,
              run_list e2 m (if hit cache v then [] else mask_cmds v) = Some (e2m, m) /\
              e2m ct_m = mask (e1 v) /\
              forall y, ct_helper y = false -> e2m y = e2 y).
    { destruct (hit cache v) eqn:Eh.
      - exists e2. split; [reflexivity|]. split; [|reflexivity].
        destruct cache as [w|]; cbn in Eh; [|discriminate]. apply String.eqb_eq in Eh. subst w.
        exact Hc.
      - destruct (mask_run e2 m v) as [e2m [H1 [H2 H3]]]. exists e2m. split; [exact H1|].
        split; [rewrite H2, Hv; reflexivity|].
        intros y Hy. apply H3; apply (not_helper _ _ Hy); reflexivity. }
    destruct Hmask as [e2m [Hm1 [Hm2 Hm3]]].
    rewrite run_list_app, Hm1.
    destruct (select_run e2m m x a b) as [e2s [Hs1 [Hs2 Hs3]]];
      [exact (not_helper _ _ Na helper_t) | exact (not_helper _ _ Nb helper_t)
      | exact (not_helper _ _ Nx helper_t) |].
    rewrite run_list_app, Hs1.
    apply (IH _ rest1 (upd e1 x val) e2s m e1' m'); [| | exact HNH | exact Horig].
    - intros y Hy. destruct (String.eqb_spec y x) as [->|Hyx].
      + rewrite upd_eq, Hs2, Hm2, (Hm3 a Na), (Hm3 b Nb), <- Ha, <- Hb, sel_mask.
        reflexivity.
      + rewrite upd_ne by exact Hyx.
        rewrite Hs3 by first [exact Hyx | exact (not_helper _ _ (HNH y Hy) helper_t)].
        rewrite (Hm3 y (HNH y Hy)). apply Hrest. exact Hy.
    - destruct (String.eqb_spec x v) as [_|Hxv]; [exact I|]. unfold CINV.
      pose proof (not_helper _ _ Nx helper_m) as Hxm.
      rewrite Hs3 by first [discriminate | congruence].
      rewrite Hm2. rewrite upd_ne by congruence. reflexivity.
  Qed.

  Lemma ct_list_ok : forall fuel, SIM fuel.
  Proof.
    induction fuel as [|fuel IH]; intros cache cs e1 e2 m e1' m' Hag Hc Hnh Hrun.
    - cbn [ct_list]. eapply frame_list; [exact Hrun | exact Hag].
    - destruct cs as [|k1 rest1].
      + cbn [run_list] in Hrun. injection Hrun as <- <-. cbn [ct_list]. eexists; reflexivity.
      + cbn [ct_list].
        destruct (match_flag k1 rest1) as [[[[x fl] neg] rest]|] eqn:F.
        * destruct (match_flag_spec _ _ _ _ _ _ F) as [t [-> [-> [Hxfl Ht]]]].
          exact (flag_case fuel IH cache x fl neg t rest e1 e2 m e1' m' Hxfl Ht Hag Hc Hnh Hrun).
        * destruct (match_select k1) as [[[[v x] a] b]|] eqn:S.
          -- destruct (match_select_spec _ _ _ _ _ S) as [t [f [-> [Ht Hf]]]].
             exact (select_case fuel IH cache v x a b t f rest1 e1 e2 m e1' m' Ht Hf Hag Hc Hnh Hrun).
          -- exact (plain_case fuel IH cache k1 rest1 e1 e2 m e1' m' Hag Hc Hnh Hrun).
  Qed.

  (** Main theorem: whenever the original command runs, the rewritten
      one runs to the same final memory. *)
  Theorem ct_cmd_correct : forall c (e : wenv) m e' m',
    run e m c = Some (e', m') -> exists e'', run e m (ct_cmd c) = Some (e'', m').
  Proof.
    intros c e m e' m' H. unfold ct_cmd. cbv zeta.
    destruct (no_ct_helpers (cmd_to_list c)) eqn:Hn.
    - rewrite run_list_to_cmd. rewrite run_cmd_to_list in H.
      refine (ct_list_ok (S (length (cmd_to_list c))) None (cmd_to_list c) e e m e' m'
                _ I _ H).
      + intros x _. reflexivity.
      + intros x Hx. unfold no_ct_helpers in Hn. rewrite forallb_forall in Hn.
        apply in_flat_map in Hx as [k [Hk Hx]]. specialize (Hn k Hk). apply negb_true_iff in Hn.
        destruct (ct_helper x) eqn:Hh; [|reflexivity]. exfalso.
        assert (existsb ct_helper (names k) = true) by (apply existsb_exists; exists x; auto).
        congruence.
    - exists e'. exact H.
  Qed.

  Theorem ct_func_correct : forall f (e : wenv) m e' m',
    run e m (jf_body f) = Some (e', m') ->
    exists e'', run e m (jf_body (ct_func f)) = Some (e'', m').
  Proof. intros. eapply ct_cmd_correct. eassumption. Qed.

  (** With [AdcChain.adc_func_correct]: the pass after [polish_func_adc]'s
      [adc_func] step keeps the final memory of the straight-line run. *)
  Corollary ct_adc_func_correct : forall f (e : wenv) m e' m',
    run e m (jf_body f) = Some (e', m') ->
    exists e'', run e m (jf_body (ct_func (adc_func f))) = Some (e'', m').
  Proof.
    intros f e m e' m' H. destruct (adc_func_correct f e m e' m' H) as [e1 H1].
    exact (ct_func_correct (adc_func f) e m e1 m' H1).
  Qed.

End Sem.
