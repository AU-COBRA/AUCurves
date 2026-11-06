(** * SpillLiveness: choose Jasmin [#[spill]] hints from liveness.

    [pp_module] (Core.v) marks every non-boolean register local
    [#[spill]]; with [jasminc -auto-spill] each such variable is stored
    after every definition and reloaded before every use.  On the
    Montgomery leaves that is two thirds of the emitted instructions.
    [pp_module_nospill] marks none, and jasminc's register allocator
    then fails on the 4- and 6-limb multiplies, whose live values exceed
    the 16 general registers.

    This file picks the hints in between: a backward liveness analysis
    over the polished [jasmin_cmd], a register-pressure model of what
    [-auto-spill] does, and a greedy choice that annotates only the
    variables needed to bring the pressure within a register budget,
    preferring long-lived, rarely used values.

    Trust.  The analysis needs no correctness proof: [#[spill]] is a
    register-allocation hint, and [-auto-spill] lowers it through the
    [spill]/[unspill] pseudo-instructions, which the verified Jasmin
    compiler's [lowering_spill] pass compiles.  What is proved here is
    that the hints are the only difference: the emitted function is a
    structured value whose annotations erase to exactly the text that
    [pp_func_nospill] prints ([render_erase_live], [pp_func_live_erases],
    [pp_module_live_erases]), the same statement as the existing lemmas
    [pp_locals_decls_nospill_drops_spill] / [pp_locals_decls_spill_form]
    made for every declaration at once, plus the parameter list.  The
    selection only ever annotates register-class [u64] locals and
    pointer parameters, never booleans or the [__wtmp__]/[__mulx_tmp__]
    scratch registers ([spill_choice_candidates]).

    The field leaves are emitted through [AdcChain.polish_func_adc]
    first ([ExtractBN254LeavesLive.v], [ExtractBLS12LeavesLive.v]):
    once fiat's carry windows are [#ADCX]/[#SBB] chains the multiplies
    need far fewer hints. *)

Require Import Bedrock.Jasmin.Core.
From Stdlib Require Import String List ZArith Bool Lia.
From Stdlib Require Import FMapPositive MSetPositive.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* Variables read and written                                        *)
(* ================================================================ *)

Fixpoint expr_vars (e : jasmin_expr) : list string :=
  match e with
  | JEvar x => [x]
  | JElit _ => []
  | JEadd a b | JEsub a b | JEmul a b | JEmulhuu a b | JEand a b
  | JEor a b | JExor a b | JEshr a b | JEshl a b | JEltu a b | JEeq a b =>
      expr_vars a ++ expr_vars b
  | JEload b _ => expr_vars b
  end.

(** Every variable a command may write. *)
Fixpoint cmd_defs (c : jasmin_cmd) : list string :=
  match c with
  | JCskip | JCstore _ _ _ | JCcall _ _ => []
  | JCseq a b | JCif _ a b => cmd_defs a ++ cmd_defs b
  | JCset x _ => [x]
  | JCwhile _ b | JCdecl _ _ b => cmd_defs b
  | JCadd_flags cf r _ _ | JCsub_flags cf r _ _ => [cf; r]
  | JCadcx co r _ _ _ | JCsbb co r _ _ _ => [co; r]
  | JCmulx h l _ _ => [h; l]
  end.

(** Every variable a command may read. *)
Fixpoint cmd_uses (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => []
  | JCseq a b => cmd_uses a ++ cmd_uses b
  | JCset _ e => expr_vars e
  | JCstore b _ v => expr_vars b ++ expr_vars v
  | JCcall _ args => flat_map expr_vars args
  | JCif e a b => expr_vars e ++ cmd_uses a ++ cmd_uses b
  | JCwhile e b => expr_vars e ++ cmd_uses b
  | JCdecl _ _ b => cmd_uses b
  | JCadd_flags _ _ a b | JCsub_flags _ _ a b | JCmulx _ _ a b =>
      expr_vars a ++ expr_vars b
  | JCadcx _ _ a b ci | JCsbb _ _ a b ci => expr_vars a ++ expr_vars b ++ [ci]
  end.

(** An instruction of the straight-line view: what it writes and reads. *)
Record ins := { i_defs : list string; i_uses : list string }.

(** Straight-line view of a body.  [JCseq] is flattened and [JCdecl]
    (a stack array, never a register candidate) is transparent; a
    conditional or a loop is one instruction that reads everything it
    may write, since a write that may not happen keeps the old value
    live.  The [if] of [lower_comparisons] ([x = 0; if b { x = 1; }])
    is the common case. *)
Fixpoint linearize (c : jasmin_cmd) : list ins :=
  match c with
  | JCskip => []
  | JCseq a b => linearize a ++ linearize b
  | JCdecl _ _ b => linearize b
  | JCif _ _ _ | JCwhile _ _ =>
      [ {| i_defs := cmd_defs c; i_uses := cmd_uses c ++ cmd_defs c |} ]
  | _ => [ {| i_defs := cmd_defs c; i_uses := cmd_uses c |} ]
  end.

(* ================================================================ *)
(* Candidates, numbered                                              *)
(* ================================================================ *)

(** Pointer and [u64] parameters, rendered [reg u64]. *)
Definition reg_param (p : string * jasmin_type) : bool :=
  match snd p with JTstack _ => false | _ => true end.

Definition scratch (x : string) : bool :=
  String.eqb x "__wtmp__" || String.eqb x "__mulx_tmp__".

Definition bool_locals (f : jasmin_func) : list string :=
  dedup_strings nil (collect_bool_vars (jf_body f)).

(** The variables a hint may be placed on: register parameters and
    the non-boolean, non-scratch locals that [pp_func_nospill]
    declares [reg u64]. *)
Definition candidates (f : jasmin_func) : list string :=
  let bools := bool_locals f in
  map fst (filter reg_param (jf_params f)) ++
  filter (fun x => negb (string_in x bools) && negb (scratch x))
         (function_locals f).

(** Names are compared as [positive]s: [enc] writes the eight bits of
    each character below a leading [1], so it is injective; the last
    character ends up in the least significant bits, where [Pos.eqb]
    starts comparing. *)
Definition push (b : bool) (p : positive) : positive := if b then xI p else xO p.

Fixpoint enc_from (s : string) (acc : positive) : positive :=
  match s with
  | EmptyString => acc
  | String (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) r =>
      enc_from r (push b7 (push b6 (push b5 (push b4 (push b3 (push b2 (push b1 (push b0 acc))))))))
  end.

Definition enc (s : string) : positive := enc_from s xH.

Definition pmem (x : positive) (l : list positive) : bool := existsb (Pos.eqb x) l.
Definition padd (x : positive) (l : list positive) : list positive :=
  if pmem x l then l else x :: l.
Definition punion (a b : list positive) : list positive := fold_right padd a b.
Definition pminus (a b : list positive) : list positive :=
  filter (fun x => negb (pmem x b)) a.

(** The candidates of an instruction's defs or uses. *)
Definition ids (cand : PositiveSet.t) (xs : list string) : list positive :=
  fold_right (fun x acc => let n := enc x in
                           if PositiveSet.mem n cand then padd n acc else acc) [] xs.

(* ================================================================ *)
(* Liveness and the pressure model                                    *)
(* ================================================================ *)

(** A program point: the candidates live across the instruction
    without being read or written by it, and those it reads or writes. *)
Record point := { pt_across : list positive; pt_here : list positive }.

(** Backward liveness; nothing is live after the body (leaves return
    through memory). *)
Fixpoint points (is : list (list positive * list positive))
    : list point * list positive :=
  match is with
  | [] => ([], [])
  | (d, u) :: rest =>
      let '(ps, live_out) := points rest in
      let live_in := punion (pminus live_out d) u in
      let here := punion d u in
      ({| pt_across := pminus live_in here; pt_here := here |} :: ps, live_in)
  end.

(** Under [-auto-spill] a [#[spill]] variable is unspilled into a
    register for each instruction that reads it and spilled after each
    one that writes it, so it occupies a register only at those
    instructions; every other live candidate holds its register
    throughout.  With [spilled] the chosen set, the occupancy at a
    point is therefore [|here| + |across \ spilled|].  The analysis
    keeps, per point, that count and the unspilled part of [across]. *)
Record state_pt := { sp_count : nat; sp_across : list positive }.

Definition init_pt (p : point) : state_pt :=
  {| sp_count := length (pt_here p) + length (pt_across p); sp_across := pt_across p |}.

Definition spill_at (x : positive) (p : state_pt) : state_pt :=
  if pmem x (sp_across p)
  then {| sp_count := pred (sp_count p);
          sp_across := filter (fun y => negb (Pos.eqb x y)) (sp_across p) |}
  else p.

(** The first point of maximal occupancy. *)
Definition worst (ps : list state_pt) : option state_pt :=
  fold_left (fun acc p =>
      match acc with
      | Some q => if Nat.ltb (sp_count q) (sp_count p) then Some p else acc
      | None => Some p
      end) ps None.

(** Span (instructions between first and last mention; parameters
    start at 0) and number of instructions mentioning the variable. *)
Record stat := { st_first : nat; st_last : nat; st_count : nat }.

Definition bump (n : nat) (x : positive) (m : PositiveMap.t stat) : PositiveMap.t stat :=
  match PositiveMap.find x m with
  | Some s => PositiveMap.add x {| st_first := st_first s; st_last := n;
                                   st_count := S (st_count s) |} m
  | None => PositiveMap.add x {| st_first := n; st_last := n; st_count := 1 |} m
  end.

Fixpoint stats_of (n : nat) (ps : list point) (m : PositiveMap.t stat) : PositiveMap.t stat :=
  match ps with
  | [] => m
  | p :: rest => stats_of (S n) rest (fold_left (fun m x => bump n x m) (pt_here p) m)
  end.

Definition stat_lookup (x : positive) (m : PositiveMap.t stat) : stat :=
  match PositiveMap.find x m with
  | Some s => s
  | None => {| st_first := 0; st_last := 0; st_count := 0 |}
  end.

(** [score_gt a b]: [a] is preferred to [b] as the next spill when its
    span per mention is larger: long-lived, rarely used.  Compared by
    cross-multiplication; ties keep the earlier candidate. *)
Definition score_gt (sa sb : stat) : bool :=
  Nat.ltb ((st_last sb - st_first sb) * S (st_count sa))
          ((st_last sa - st_first sa) * S (st_count sb)).

Definition pick (m : PositiveMap.t stat) (xs : list positive) : option positive :=
  fold_left (fun acc x =>
      match acc with
      | None => Some x
      | Some y => if score_gt (stat_lookup x m) (stat_lookup y m) then Some x else acc
      end) xs None.

(** Greedy spill choice: while the worst point holds more than
    [budget] registers, spill the best-scored candidate live across
    that point (spilling it lowers the occupancy there by one).
    [fuel] bounds the loop by the number of candidates.  Returns the
    chosen set and the occupancy of the worst point left. *)
Fixpoint choose (fuel : nat) (budget : nat) (m : PositiveMap.t stat)
    (ps : list state_pt) (spilled : list positive) : list positive * nat :=
  let k := match worst ps with Some p => sp_count p | None => 0 end in
  match fuel with
  | O => (spilled, k)
  | S fuel' =>
      match worst ps with
      | None => (spilled, 0)
      | Some p =>
          if Nat.leb (sp_count p) budget then (spilled, sp_count p)
          else
            match pick m (sp_across p) with
            | None => (spilled, sp_count p)
            | Some x => choose fuel' budget m (map (spill_at x) ps) (x :: spilled)
            end
      end
  end.

(** The analysis of one function: the chosen set and the residual
    maximal occupancy.  Parameters count as defined before the first
    instruction. *)
Definition analyse (budget : nat) (f : jasmin_func) : list string * nat :=
  let cand := candidates f in
  let cset := fold_right (fun x s => PositiveSet.add (enc x) s) PositiveSet.empty cand in
  let is := map (fun i => (ids cset (i_defs i), ids cset (i_uses i)))
                (linearize (jf_body f)) in
  let '(ps, _) := points is in
  let pids := ids cset (map fst (filter reg_param (jf_params f))) in
  let m0 := fold_left (fun m x => PositiveMap.add x
              {| st_first := 0; st_last := 0; st_count := 0 |} m) pids (PositiveMap.empty _) in
  let m := stats_of 1 ps m0 in
  let '(chosen, k) := choose (length cand) budget m (map init_pt ps) [] in
  (filter (fun x => pmem (enc x) chosen) cand, k).

Definition spill_choice (budget : nat) (f : jasmin_func) : list string :=
  fst (analyse budget f).

(** Maximal occupancy left after the choice: reported by the
    extraction files so the budget can be checked. *)
Definition residual_pressure (budget : nat) (f : jasmin_func) : nat :=
  snd (analyse budget f).

Lemma spill_choice_candidates : forall budget f x,
  In x (spill_choice budget f) -> In x (candidates f).
Proof.
  unfold spill_choice, analyse; intros budget f x H.
  destruct (points _) as [ps l].
  destruct (choose _ _ _ _ _) as [chosen k].
  apply filter_In in H. exact (proj1 H).
Qed.

(* ================================================================ *)
(* The emitted function as a structured value                         *)
(* ================================================================ *)

(** One declaration line: an optional [#[spill]] hint, the storage
    class, the name. *)
Record decl := { d_spill : bool; d_class : string; d_name : string }.

Definition pp_decl (indent : string) (d : decl) : string :=
  indent ++ (if d_spill d then "#[spill] " else "") ++ d_class d ++ " " ++ d_name d ++ ";" ++ LF.

Definition pp_param (d : decl) : string :=
  (if d_spill d then "#[spill] " else "") ++ d_class d ++ " " ++ d_name d.

(** Everything [pp_func_nospill] prints, with a hint bit on each
    parameter and local. *)
Record emitted := {
  e_name : string;
  e_params : list decl;
  e_extra : string;      (* the [__wtmp__] / [__mulx_tmp__] declarations *)
  e_locals : list decl;
  e_body : string;
}.

Definition render (e : emitted) : string :=
  "export fn " ++ e_name e ++ "(" ++
    String.concat ", " (map pp_param (e_params e)) ++
    ") {" ++ LF ++
    e_extra e ++
    String.concat "" (map (pp_decl "  ") (e_locals e)) ++
    e_body e ++
  "}" ++ LF.

Definition erase_decl (d : decl) : decl :=
  {| d_spill := false; d_class := d_class d; d_name := d_name d |}.

(** Erasing the annotations. *)
Definition erase (e : emitted) : emitted :=
  {| e_name := e_name e; e_params := map erase_decl (e_params e);
     e_extra := e_extra e; e_locals := map erase_decl (e_locals e);
     e_body := e_body e |}.

Definition extra_decls (f : jasmin_func) : string :=
  let locals := function_locals f in
  (if string_in "__wtmp__" locals then "" else "  reg u64 __wtmp__;" ++ LF) ++
  (if string_in "__mulx_tmp__" locals then "" else "  reg u64 __mulx_tmp__;" ++ LF).

Definition param_decl (spills : list string) (p : string * jasmin_type) : decl :=
  {| d_spill := reg_param p && string_in (fst p) spills;
     d_class := pp_type (snd p); d_name := fst p |}.

Definition local_decl (bools spills : list string) (x : string) : decl :=
  if string_in x bools
  then {| d_spill := false; d_class := "reg bool"; d_name := x |}
  else {| d_spill := string_in x spills; d_class := "reg u64"; d_name := x |}.

(** The function with hints on the variables of [spills]. *)
Definition emit (spills : list string) (f : jasmin_func) : emitted :=
  {| e_name := jf_name f;
     e_params := map (param_decl spills) (jf_params f);
     e_extra := extra_decls f;
     e_locals := map (local_decl (bool_locals f) spills) (function_locals f);
     e_body := pp_cmd "  " (jf_body f) |}.

Definition default_budget : nat := 16.

Definition pp_func_live_b (budget : nat) (f : jasmin_func) : string :=
  render (emit (spill_choice budget f) f).

Definition pp_func_live (f : jasmin_func) : string := pp_func_live_b default_budget f.

Definition pp_module_live_b (budget : nat) (fs : list jasmin_func) : string :=
  String.concat (LF ++ LF) (map (pp_func_live_b budget) fs).

Definition pp_module_live (fs : list jasmin_func) : string :=
  pp_module_live_b default_budget fs.

(* ================================================================ *)
(* The hints are inert: erasing them gives the hint-free emission     *)
(* ================================================================ *)

Lemma pp_param_decl_nil : forall p,
  pp_param (param_decl [] p) = (let '(name, ty) := p in pp_type ty ++ " " ++ name).
Proof. intros [x ty]. unfold pp_param, param_decl; cbn. rewrite andb_false_r. reflexivity. Qed.

Lemma pp_local_decl_nil : forall bools x,
  pp_decl "  " (local_decl bools [] x) =
    (if string_in x bools
     then "  " ++ "reg bool " ++ x ++ ";" ++ LF
     else "  " ++ "reg u64 " ++ x ++ ";" ++ LF).
Proof. intros. unfold local_decl. destruct (string_in x bools); reflexivity. Qed.

(** Without hints, the structured emission prints exactly what
    [pp_func_nospill] prints. *)
Lemma render_emit_nil : forall f, render (emit [] f) = pp_func_nospill f.
Proof.
  intros f. unfold render, emit, pp_func_nospill, extra_decls, pp_locals_decls_nospill,
    bool_locals; cbn [e_name e_params e_extra e_locals e_body].
  rewrite !map_map, (map_ext _ _ pp_param_decl_nil), (map_ext _ _ (pp_local_decl_nil _)).
  reflexivity.
Qed.

(** Erasing the hints of any selection gives the selection-free emission. *)
Lemma erase_emit : forall spills f, erase (emit spills f) = emit [] f.
Proof.
  intros spills f. unfold erase, emit; cbn [e_name e_params e_extra e_locals e_body].
  rewrite !map_map. f_equal.
  - apply map_ext. intros [x ty]. unfold erase_decl, param_decl; cbn.
    rewrite andb_false_r. reflexivity.
  - apply map_ext. intros x. unfold local_decl. destruct (string_in x _); reflexivity.
Qed.

(** Main statement: the emitted function, with its annotations erased,
    is the hint-free program [pp_func_nospill f]. *)
Theorem render_erase_live : forall budget f,
  render (erase (emit (spill_choice budget f) f)) = pp_func_nospill f.
Proof. intros. rewrite erase_emit. apply render_emit_nil. Qed.

(** The emitted text is [render] of the structured value; [render]
    differs from its erasure only on hinted declarations, each by the
    prefix ["#[spill] "] (the per-line form of the existing lemmas). *)
Lemma pp_decl_erase : forall indent d,
  pp_decl indent d =
    indent ++ (if d_spill d then "#[spill] " else "") ++ (d_class d ++ " " ++ d_name d ++ ";" ++ LF) /\
  pp_decl indent (erase_decl d) = indent ++ (d_class d ++ " " ++ d_name d ++ ";" ++ LF).
Proof. intros; split; reflexivity. Qed.

Theorem pp_func_live_erases : forall budget f,
  pp_func_live_b budget f = render (emit (spill_choice budget f) f) /\
  render (erase (emit (spill_choice budget f) f)) = pp_func_nospill f.
Proof. split; [reflexivity | apply render_erase_live]. Qed.

(** Module level: the hinted module erases to [pp_module_nospill]. *)
Theorem pp_module_live_erases : forall budget fs,
  String.concat (LF ++ LF)
    (map (fun f => render (erase (emit (spill_choice budget f) f))) fs)
  = pp_module_nospill fs.
Proof.
  intros. unfold pp_module_nospill. f_equal.
  apply map_ext. intros f. apply render_erase_live.
Qed.

(** The selection never annotates a boolean or a scratch register. *)
Lemma emit_hint_on_candidate : forall budget f d,
  In d (e_locals (emit (spill_choice budget f) f)) -> d_spill d = true ->
  In (d_name d) (candidates f).
Proof.
  intros budget f d Hin Hs. unfold emit in Hin; cbn [e_locals] in Hin.
  apply in_map_iff in Hin as [x [<- Hx]].
  unfold local_decl in *.
  destruct (string_in x (bool_locals f)) eqn:Hb; cbn in *; [discriminate|].
  unfold string_in in Hs. apply existsb_exists in Hs as [y [Hy Heq]].
  apply String.eqb_eq in Heq; subst y.
  apply spill_choice_candidates in Hy. exact Hy.
Qed.
