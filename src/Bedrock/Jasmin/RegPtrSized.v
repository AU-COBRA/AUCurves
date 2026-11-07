(** * RegPtrSized: the reg-ptr Jasmin printer for any limb count, with local
    functions, export entry points and leaves outside Jasmin.

    [Core.pp_module_regptr] (#227/#241/#259) prints the BN254 tower under the
    [reg ptr u64[N]] convention.  It is fixed to BN254: four limbs, the
    [bn254_*] leaf names, and every function an [export fn].  Jasmin inlines a
    call to an [export fn], so a module whose functions call each other as
    [export fn]s expands the whole call graph into every entry point; for the
    BN254 pairing jasminc then runs for more than eight minutes.  Its leaves are
    the structural stubs [Core.pp_regptr_leaf_stubs], which copy instead of
    computing, so that module is a compile check and does not run.

    This file prints the same [jasmin_func] ASTs ([Core.tr_func_sized] then
    [Core.polish_func]) with four changes, all in the printer:

    - the limb count [rpc_n] is a parameter (6 for BLS12-381);
    - every function of the module is a local [fn] (a real [call], so each body
      is compiled once), the functions named in [rpc_inline] are [inline fn], and
      [rpc_exports] adds [export fn] wrappers, the only symbols of the object;
    - a call to a leaf named in [rpc_ffi] (the Montgomery multiply, square and
      inverse) is printed as a [#randombytes] system call on a stack buffer
      that holds the output followed by the inputs.  Jasmin has no external
      calls; [#randombytes] is the one call it makes to code outside the module,
      with the System V convention (buffer in rdi, length in rsi, every
      caller-saved register killed: [Arch.syscall_kill]).  The crate's
      [__jasmin_syscall_randombytes__] (generated/jasmin_aliases.s) dispatches on
      the length to CryptOpt's multiply / square or to the safegcd inverse.
      Jasmin's semantics treats the system call as an oracle that writes
      arbitrary bytes into the buffer, so the Jasmin program, and by jasminc's
      correctness theorem the object code, is correct for whatever the oracle
      returns; the dispatcher is trusted to return the field operation;
    - a call argument that is a scalar ([rpc_scalar]) or a literal is passed in
      a register ([__la<i>]); a pointer argument is copied into a disjoint
      whole stack buffer [__sg<w>_<i>] and the written ones are copied back,
      as [Core.pp_call_tower_staged] does (#241), with [for] loops that jasminc
      unrolls instead of the [while] loops of #259 -- except an argument whose
      array no other argument of the same call uses and that is a static slice
      of a stack array, or (into a called function) a whole pointer parameter
      of the callee's width: that one is passed as it is;
    - pointer parameters of a called function are kept in [stack ptr] slots and
      reloaded for each access, and its word locals carry [#[spill]], because at
      a call only the six callee-saved registers survive (see [actx]).

    Faithfulness is as for [Core.pp_module_regptr]: the printer reads the
    command stream [jf_body f] and never rewrites it
    ([pp_module_sized_same_bodies]); the bedrock2 meaning of that stream is
    [Core.tr_cmd_correct].  The staging copies move the same words through
    disjoint buffers and back ([Core.pp_copyN_index_correspondence]); the
    callee sees its inputs as they were at the call, which is the meaning the
    safe-Rust printer gives an aliased call as well; an argument is passed
    without a copy only when no other argument of the call shares its array, so
    there is no aliasing to resolve.  None of this is proved: like
    [Core.pp_module_regptr] the printer is trusted, and the emitted modules are
    tested against the safe-Rust path ([tests/jasmin_vs_safe.rs]).  The keyword
    ([fn] / [inline fn] / [export fn]) is the function's storage class and does
    not change what it computes ([pp_fn_keyword_cases]). *)

Require Import bedrock2.Syntax.
From Stdlib Require Import String List ZArith Bool.
From Stdlib Require Import FMapPositive MSetPositive.
Require Import Bedrock.Jasmin.Core.
Require Bedrock.Jasmin.SpillLiveness.
Module SL := Bedrock.Jasmin.SpillLiveness.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Record rp_config := {
  rpc_n : Z;
    (** words per base-field element *)
  rpc_ffi : list (string * Z);
    (** leaves reached through [#randombytes]: name and buffer length in words *)
  rpc_inline : list string;
    (** functions printed [inline fn] *)
  rpc_scalar : list (string * list nat);
    (** parameter positions that hold a word, not a pointer *)
  rpc_skip : list string;
    (** functions of the list that are not printed (their calls go to [rpc_ffi]) *)
  rpc_exports : list (string * string);
    (** (function, symbol) pairs printed as [export fn] wrappers *)
  rpc_widths : list (string * list Z);
    (** parameter widths (words) given instead of inferred, for parameters
        accessed at offsets only known at run time *)
  rpc_export_all : bool;
    (** also export every printed function with at most 6 parameters, as
        ["jasmin_" ++ name], so that jasminc compiles each of them; otherwise
        only the functions reachable from [rpc_exports] are printed *)
  rpc_hints : bool;
    (** [#[spill]] hints (and [stack ptr] slots) chosen by liveness
        ([hint_choice]) instead of on every word local and pointer
        parameter of a called function *)
  rpc_budget : nat;
    (** with [rpc_hints]: the register budget of [hint_choice] (the pressure
        model's limit between calls, and for a call-free leaf the whole
        choice) *)
  rpc_cmov : bool;
    (** print a conditional that assigns one variable from a variable or a
        literal in both branches (or in the then-branch only) as a conditional
        move, [x = b; x = c ? a : x], instead of branches *)
  rpc_direct : bool;
    (** pass static slices of pointer parameters (and of stack arrays) that
        no other argument of the call overlaps without staging them: a
        read-only one as the slice, a written one through a [reg ptr]
        temporary *)
}.

(** ** Spill hints from liveness ([rpc_hints])

    [SpillLiveness] chooses the hints of a straight-line leaf: backward
    liveness, the register-pressure model of [-auto-spill], and a greedy
    choice within a budget.  A module function also makes calls.  A call to a
    local function or the [#randombytes] system call may clobber every
    register (the callee is allocated with the caller, and the system call
    kills all caller-saved registers), so every candidate live after a call
    must be spilled: [live_calls] computes, over the structured body (loops
    iterated to a fixed point within [fuel]), the variables live after some
    call, and [hint_choice] starts [SpillLiveness.choose] from that forced
    set.  A function without calls gets exactly [SpillLiveness.spill_choice].
    As there, nothing here needs a proof: a hint is a register-allocation
    annotation ([Core.pp_locals_decls_spill_form]), jasminc's [-auto-spill]
    lowers it through the verified [lowering_spill] pass, and a choice that
    spills too little fails register allocation instead of changing the
    program. *)
Definition sunion (a b : list string) : list string :=
  List.fold_left (fun acc x => if string_in x acc then acc else List.app acc [x]) b a.

Fixpoint live_calls (fuel : nat) (c : jasmin_cmd) (out : list string)
    : list string * list string :=
  match c with
  | JCseq a b =>
      let '(lb, fb) := live_calls fuel b out in
      let '(la, fa) := live_calls fuel a lb in (la, List.app fa fb)
  | JCdecl _ _ b => live_calls fuel b out
  | JCcall _ args =>
      (* the printer reads the arguments' variables again after the call
         (copying staged outputs back), so they count as live after it *)
      let av := List.flat_map SL.expr_vars args in (sunion out av, sunion out av)
  | JCif e a b =>
      let '(la, fa) := live_calls fuel a out in
      let '(lb, fb) := live_calls fuel b out in
      (sunion (SL.expr_vars e) (sunion la lb), List.app fa fb)
  | JCwhile e body =>
      let fix iter (k : nat) (l : list string) : list string * list string :=
        let '(lb, fb) := live_calls fuel body l in
        let l' := sunion l lb in
        match k with
        | O => (l', fb)
        | S k' => if Nat.eqb (List.length l') (List.length l) then (l', fb) else iter k' l'
        end in
      iter fuel (sunion out (SL.expr_vars e))
  | _ =>
      (sunion (List.filter (fun x => negb (string_in x (SL.cmd_defs c))) out) (SL.cmd_uses c), nil)
  end.

Definition forced_spills (f : jasmin_func) : list string :=
  snd (live_calls 8 (jf_body f) nil).

Definition hint_choice (budget : nat) (f : jasmin_func) : list string :=
  let cand := SL.candidates f in
  let forced := List.filter (fun x => string_in x (forced_spills f)) cand in
  let cset := List.fold_right (fun x s => PositiveSet.add (SL.enc x) s) PositiveSet.empty cand in
  let is := List.map (fun i => (SL.ids cset (SL.i_defs i), SL.ids cset (SL.i_uses i)))
                     (SL.linearize (jf_body f)) in
  let '(ps, _) := SL.points is in
  let pids := SL.ids cset (List.map fst (List.filter SL.reg_param (jf_params f))) in
  let m0 := List.fold_left (fun m x => PositiveMap.add x
              {| SL.st_first := 0; SL.st_last := 0; SL.st_count := 0 |} m) pids
              (PositiveMap.empty _) in
  let m := SL.stats_of 1 ps m0 in
  let fe := List.map SL.enc forced in
  let ps0 := List.fold_left (fun ps x => List.map (SL.spill_at x) ps) fe (List.map SL.init_pt ps) in
  let '(chosen, _) := SL.choose (List.length cand) budget m ps0 fe in
  List.filter (fun x => SL.pmem (SL.enc x) chosen) cand.

Lemma hint_choice_candidates : forall budget f x,
  In x (hint_choice budget f) -> In x (SL.candidates f).
Proof.
  unfold hint_choice; intros budget f x H.
  destruct (SL.points _) as [ps l].
  destruct (SL.choose _ _ _ _ _) as [chosen k].
  apply filter_In in H. exact (proj1 H).
Qed.

Section Printer.
  Variable cfg : rp_config.
  Local Notation n := (rpc_n cfg).

  Definition nthw (ws : list Z) (i : nat) : Z := nth i ws n.

  Definition ffi_len (f : string) : option Z :=
    option_map snd (List.find (fun p => String.eqb (fst p) f) (rpc_ffi cfg)).

  Definition is_ffi (f : string) : bool :=
    match ffi_len f with Some _ => true | None => false end.

  Definition scalar_params (f : string) : list nat :=
    match List.find (fun p => String.eqb (fst p) f) (rpc_scalar cfg) with
    | Some (_, l) => l
    | None => nil
    end.

  Definition is_scalar_param (f : string) (i : nat) : bool :=
    List.existsb (Nat.eqb i) (scalar_params f).

  (** Word reach of parameter [p] in [c], as [Core.param_reach] with default
      width [n] for callees not yet in [env]. *)
  Fixpoint reach (env : regptr_env) (p : string) (c : jasmin_cmd) : Z :=
    match c with
    | JCseq c1 c2 => zmax (reach env p c1) (reach env p c2)
    | JCif _ ct cf => zmax (reach env p ct) (reach env p cf)
    | JCwhile _ body => reach env p body
    | JCdecl _ _ body => reach env p body
    | JCstore base off _ =>
        match ptr_base_off base with
        | Some (b, k) => if String.eqb b p then k + Z.div off 8 + 1 else 0
        | None => 0
        end
    | JCset _ (JEload base off) =>
        match ptr_base_off base with
        | Some (b, k) => if String.eqb b p then k + Z.div off 8 + 1 else 0
        | None => 0
        end
    | JCcall f args =>
        let cw := match env_lookup env f with Some ws => ws | None => nil end in
        zmax_list (List.map (fun ia =>
          let '(i, a) := ia in
          if is_scalar_param f i then 0 else
          match ptr_base_off a with
          | Some (b, k) => if String.eqb b p then k + nthw cw i else 0
          | None => 0
          end) (List.combine (List.seq 0 (List.length args)) args))
    | _ => 0
    end.

  Definition infer_widths (env : regptr_env) (f : jasmin_func) : list Z :=
    List.map (fun '(p, _) => let r := reach env p (jf_body f) in if Z.eqb r 0 then n else r)
      (jf_params f).

  Definition seed : regptr_env :=
    List.map (fun '(f, _) => (f, [n; n; n])) (rpc_ffi cfg).

  Definition infer_step (fs : list jasmin_func) (env : regptr_env) : regptr_env :=
    List.app seed (List.map (fun f =>
      (jf_name f, match env_lookup (rpc_widths cfg) (jf_name f) with
                  | Some ws => ws | None => infer_widths env f end)) fs).

  (** Widths grow monotonically along the call graph; [depth] rounds reach the
      fixed point when the call graph is at most [depth] deep. *)
  Fixpoint infer_iter (depth : nat) (fs : list jasmin_func) (env : regptr_env) : regptr_env :=
    match depth with
    | O => env
    | S d => infer_iter d fs (infer_step fs env)
    end.

  Definition widths_of (env : regptr_env) (f : string) : list Z :=
    match env_lookup (rpc_widths cfg) f with
    | Some ws => ws
    | None => match env_lookup env f with Some ws => ws | None => nil end
    end.

  (** Parameter positions a function writes: stored to, or passed at a
      position its callee writes.  A system-call leaf writes its output. *)
  Definition wenv := list (string * list nat).

  Fixpoint wlookup (we : wenv) (f : string) : list nat :=
    match we with
    | nil => if is_ffi f then [0%nat] else nil
    | (g, l) :: r => if String.eqb g f then l else wlookup r f
    end.

  Definition nat_in (i : nat) (l : list nat) : bool := List.existsb (Nat.eqb i) l.

  (** ** Addresses

      An address is a root array (a pointer parameter or a [stack] array) and a
      byte offset.  bedrock2 code also keeps addresses in variables
      ([bpx = buckets_x + 48 * i]); such a pointer variable is printed as a
      [reg u64] holding its byte offset from its root, and an access through
      it as the byte-addressed [root.[u64 (int) offset]]. *)
  Definition add_off (o b : jasmin_expr) : jasmin_expr :=
    match o, b with
    | JElit 0, _ => b
    | JElit x, JElit y => JElit (x + y)
    | _, _ => JEadd o b
    end.

  Fixpoint addr_of (arrs : list string) (pv : list (string * string)) (e : jasmin_expr)
      : option (string * jasmin_expr) :=
    match e with
    | JEvar x =>
        if string_in x arrs then Some (x, JElit 0) else
        match List.find (fun p => String.eqb (fst p) x) pv with
        | Some (_, r) => Some (r, JEvar x)
        | None => None
        end
    | JEadd a b =>
        match addr_of arrs pv a with
        | Some (r, o) => Some (r, add_off o b)
        | None =>
            match addr_of arrs pv b with
            | Some (r, o) => Some (r, add_off o a)
            | None => None
            end
        end
    | _ => None
    end.

  Fixpoint sets_of (c : jasmin_cmd) : list (string * jasmin_expr) :=
    match c with
    | JCseq c1 c2 => List.app (sets_of c1) (sets_of c2)
    | JCif _ ct cf => List.app (sets_of ct) (sets_of cf)
    | JCwhile _ body => sets_of body
    | JCdecl _ _ body => sets_of body
    | JCset x e => [(x, e)]
    | _ => nil
    end.

  Fixpoint pv_iter (k : nat) (arrs : list string) (sets : list (string * jasmin_expr))
      (pv : list (string * string)) : list (string * string) :=
    match k with
    | O => pv
    | S k' =>
        let pv' := List.fold_left (fun acc xe =>
          let '(x, e) := xe in
          if orb (string_in x arrs) (List.existsb (fun p => String.eqb (fst p) x) acc) then acc
          else match e with
               | JEload _ _ => acc
               | _ => match addr_of arrs acc e with
                      | Some (r, _) => List.app acc [(x, r)]
                      | None => acc
                      end
               end) sets pv in
        pv_iter k' arrs sets pv'
    end.

  (** [ax_spill]: the pointer parameters kept in [stack ptr] slots.  Jasmin
      does not spill a [reg ptr] by itself, and in a function that calls
      another every register but the six callee-saved ones is killed at the
      call (the system call kills all caller-saved registers, and the
      allocation is interprocedural); so a non-inline function saves each
      pointer parameter [p] in [p__s] on entry and reloads it, [p = p__s], for
      each access (and saves it back after a write).  These are moves of the
      pointer, not of the array. *)
  Record actx := { ax_arrs : list string; ax_pv : list (string * string); ax_spill : list string;
                   ax_widths : list (string * Z); ax_params : list string }.

  (** [hs]: with [rpc_hints], the hint choice of [f]; only the pointer
      parameters in it get a [stack ptr] slot. *)
  Definition actx_of (hs : option (list string)) (ws : list Z) (f : jasmin_func) : actx :=
    let ps := List.map snd (List.filter (fun ip => negb (is_scalar_param (jf_name f) (fst ip)))
                (List.combine (List.seq 0 (List.length (jf_params f))) (List.map fst (jf_params f)))) in
    let arrs := List.app ps (List.map fst (collect_array_widths (jf_body f))) in
    {| ax_arrs := arrs; ax_pv := pv_iter 8 arrs (sets_of (jf_body f)) nil;
       ax_spill := if string_in (jf_name f) (rpc_inline cfg) then nil else
                   match hs with
                   | Some h => List.filter (fun p => string_in p h) ps
                   | None => ps
                   end;
       ax_widths := List.app (List.combine (List.map fst (jf_params f)) ws)
                             (collect_array_widths (jf_body f));
       ax_params := ps |}.

  Definition addr (ax : actx) (e : jasmin_expr) := addr_of (ax_arrs ax) (ax_pv ax) e.

  (** The word [w] words past address [(r, o)]; [w] is a Jasmin [inline int]. *)
  Definition pp_at (ro : string * jasmin_expr) (w : string) : string :=
    let '(r, o) := ro in
    match o with
    | JElit k => r ++ "[" ++ pp_int (Z.div k 8) ++ " + " ++ w ++ "]"
    (* [(x << 3) + 8 k], a word index ([words_eq]'s [a + (i << 3)]): an element access, which
       x86 scales by 8; jasminc does not assemble a shift inside an address *)
    | JEadd (JEshl (JEvar x) (JElit 3)) (JElit k) =>
        if Z.eqb (Z.modulo k 8) 0
        then r ++ "[(int) " ++ x ++ " + " ++ pp_int (Z.div k 8) ++ " + " ++ w ++ "]"
        else r ++ ".[u64 (int) (" ++ pp_expr o ++ ") + 8 * " ++ w ++ "]"
    | JEshl (JEvar x) (JElit 3) => r ++ "[(int) " ++ x ++ " + " ++ w ++ "]"
    | _ => r ++ ".[u64 (int) (" ++ pp_expr o ++ ") + 8 * " ++ w ++ "]"
    end.

  Definition pp_elem (ax : actx) (base : jasmin_expr) (off : Z) : string :=
    match addr ax base with
    | Some (r, o) => pp_at (r, add_off o (JElit off)) "0"
    | None => "ERROR_address(" ++ pp_expr base ++ ")"
    end.

  (** Whether [c] writes through an address whose root is [p]: a store, or a
      call argument at a position the callee writes. *)
  Fixpoint writes (we : wenv) (ax : actx) (p : string) (c : jasmin_cmd) : bool :=
    let root_is e := match addr ax e with Some (r, _) => String.eqb r p | None => false end in
    match c with
    | JCseq c1 c2 => orb (writes we ax p c1) (writes we ax p c2)
    | JCif _ ct cf => orb (writes we ax p ct) (writes we ax p cf)
    | JCwhile _ body => writes we ax p body
    | JCdecl _ _ body => writes we ax p body
    | JCstore base _ _ => root_is base
    | JCcall f args =>
        List.existsb (fun ia =>
          let '(i, a) := ia in
          andb (nat_in i (wlookup we f)) (andb (negb (is_scalar_param f i)) (root_is a)))
          (List.combine (List.seq 0 (List.length args)) args)
    | _ => false
    end.

  Definition infer_written (we : wenv) (f : jasmin_func) : list nat :=
    List.map fst (List.filter (fun ip => let '(i, (p, _)) := ip in
                     andb (negb (is_scalar_param (jf_name f) i))
                       (writes we (actx_of None nil f) p (jf_body f)))
      (List.combine (List.seq 0 (List.length (jf_params f))) (jf_params f))).

  Fixpoint written_iter (depth : nat) (fs : list jasmin_func) (we : wenv) : wenv :=
    match depth with
    | O => we
    | S d => written_iter d fs (List.map (fun f => (jf_name f, infer_written we f)) fs)
    end.

  Definition root_of (ax : actx) (e : jasmin_expr) : option string :=
    option_map fst (addr ax e).

  Definition reload (ax : actx) (indent : string) (r : option string) : string :=
    match r with
    | Some p => if string_in p (ax_spill ax) then indent ++ p ++ " = " ++ p ++ "__s;" ++ LF else ""
    | None => ""
    end.

  Definition save (ax : actx) (indent : string) (r : option string) : string :=
    match r with
    | Some p => if string_in p (ax_spill ax) then indent ++ p ++ "__s = " ++ p ++ ";" ++ LF else ""
    | None => ""
    end.

  (** The roots of the loads in [e]. *)
  Fixpoint load_roots (ax : actx) (e : jasmin_expr) : list string :=
    match e with
    | JEload base _ => match root_of ax base with Some r => [r] | None => nil end
    | JEadd a b | JEsub a b | JEmul a b | JEand a b | JEor a b | JExor a b
    | JEshr a b | JEshl a b | JEltu a b | JEeq a b | JEmulhuu a b =>
        List.app (load_roots ax a) (load_roots ax b)
    | _ => nil
    end.

  Definition reload_all (ax : actx) (indent : string) (rs : list string) : string :=
    String.concat "" (List.map (fun r => reload ax indent (Some r)) (dedup_strings nil rs)).

  (** [Core.pp_expr], with the loads printed through [pp_elem]. *)
  Fixpoint pp_expr_ax (ax : actx) (e : jasmin_expr) : string :=
    match e with
    | JEload base off => pp_elem ax base off
    | JEadd e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " + " ++ pp_expr_ax ax e2 ++ ")"
    | JEsub e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " - " ++ pp_expr_ax ax e2 ++ ")"
    | JEmul e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " * " ++ pp_expr_ax ax e2 ++ ")"
    | JEand e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " & " ++ pp_expr_ax ax e2 ++ ")"
    | JEor e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " | " ++ pp_expr_ax ax e2 ++ ")"
    | JExor e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " ^ " ++ pp_expr_ax ax e2 ++ ")"
    | JEshr e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " >> " ++ pp_expr_ax ax e2 ++ ")"
    | JEshl e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " << " ++ pp_expr_ax ax e2 ++ ")"
    | JEltu e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " <u " ++ pp_expr_ax ax e2 ++ ")"
    | JEeq e1 e2 => "(" ++ pp_expr_ax ax e1 ++ " == " ++ pp_expr_ax ax e2 ++ ")"
    | _ => pp_expr e
    end.

  (** [for] copy of [len] words from [src] to [dst]. *)
  (** A byte offset other than a literal or a variable ([fr_divlin]'s [k * 32]) is
      computed into a register first: x86 scales an index by 1, 2, 4 or 8 only. *)
  Definition hoist_off (indent tmp : string) (p : string * jasmin_expr)
      : string * (string * jasmin_expr) :=
    match snd p with
    | JElit _ | JEvar _ => ("", p)
    | e => (indent ++ tmp ++ " = " ++ pp_expr e ++ ";" ++ LF, (fst p, JEvar tmp))
    end.

  (** A copy of more than [copy_unroll_max] words (for instance a staged quotient
      buffer, 16384 words) is a loop over a register byte offset [__jr__] instead of an
      unrolled [for]: [base.[u64 (int) __jr__ + k]] for a literal offset [k], else the
      address [__jx__] / [__jy__] = offset + [__jr__].  The copies of the tower, group and
      KZG modules (at most 72 words) print as before. *)
  Definition copy_unroll_max : Z := 256.

  Definition pp_at_loop (ro : string * jasmin_expr) (tmp : string) : string * string :=
    let '(r, o) := ro in
    match o with
    | JElit k => ("", r ++ ".[u64 (int) __jr__ + " ++ pp_int k ++ "]")
    | _ => (tmp ++ " = " ++ pp_expr o ++ "; " ++ tmp ++ " += __jr__; ",
            r ++ ".[u64 (int) " ++ tmp ++ "]")
    end.

  Definition pp_copy (indent : string) (dst src : string * jasmin_expr) (len : Z) : string :=
    let '(s1, src') := hoist_off indent "__ca__" src in
    let '(s2, dst') := hoist_off indent "__cb__" dst in
    if Z.leb len copy_unroll_max then
      s1 ++ s2 ++
      indent ++ "for __j = 0 to " ++ pp_int len ++ " { __mv__ = " ++ pp_at src' "__j" ++ "; "
        ++ pp_at dst' "__j" ++ " = __mv__; }" ++ LF
    else
      let '(ps, as_) := pp_at_loop src' "__jx__" in
      let '(pd, ad) := pp_at_loop dst' "__jy__" in
      s1 ++ s2 ++
      indent ++ "__jr__ = 0;" ++ LF ++
      indent ++ "while (__jr__ <u " ++ pp_int (8 * len) ++ ") { " ++ ps ++ "__mv__ = " ++ as_
        ++ "; " ++ pd ++ ad ++ " = __mv__; __jr__ += 8; }" ++ LF.

  (** [pp_copy] with the spilled pointer parameters reloaded (and the
      destination saved back). *)
  Definition pp_copy_ax (ax : actx) (indent : string) (dst src : string * jasmin_expr) (len : Z) : string :=
    reload ax indent (Some (fst src)) ++
    (if String.eqb (fst src) (fst dst) then "" else reload ax indent (Some (fst dst))) ++
    pp_copy indent dst src len ++
    save ax indent (Some (fst dst)).

  Definition sg (w : Z) (i : nat) : string := "__sg" ++ pp_int w ++ "_" ++ pp_int (Z.of_nat i).
  Definition la (i : nat) : string := "__la" ++ pp_int (Z.of_nat i).
  Definition ffi_buf (f : string) : string := "__ffi_" ++ f.
  Definition whole (x : string) : string * jasmin_expr := (x, JElit 0).

  (** The word index of a byte offset [e] built from literals divisible by 8, [x * c],
      [c * x] and sums ([kn * 48]); [None] otherwise (then the argument is staged). *)
  Fixpoint div8 (e : jasmin_expr) : option jasmin_expr :=
    match e with
    | JElit k => if Z.eqb (Z.modulo k 8) 0 then Some (JElit (Z.div k 8)) else None
    | JEmul a (JElit c) => if Z.eqb (Z.modulo c 8) 0 then Some (JEmul a (JElit (Z.div c 8))) else None
    | JEmul (JElit c) a => if Z.eqb (Z.modulo c 8) 0 then Some (JEmul a (JElit (Z.div c 8))) else None
    | JEadd a b =>
        match div8 a, div8 b with
        | Some a', Some b' => Some (JEadd a' b')
        | _, _ => None
        end
    | _ => None
    end.

  Definition is_lit (e : jasmin_expr) : bool := match e with JElit _ => true | _ => false end.

  (** One call [f(args)].  Scalars and literals go through [__la<i>]; pointers
      are staged, and the positions the callee writes are copied back.  For
      an [rpc_ffi] leaf the inputs are copied into the buffer after the
      output slot and the output slot is copied back. *)
  Definition pp_call (env : regptr_env) (we : wenv) (ax : actx) (indent f : string)
      (args : list jasmin_expr) : string :=
    let idx := List.combine (List.seq 0 (List.length args)) args in
    let cw := widths_of env f in
    match ffi_len f, args with
    | Some _, a0 :: _ =>
        match addr ax a0 with
        | None => indent ++ "ERROR_ffi_output(" ++ f ++ ");" ++ LF
        | Some d0 =>
            String.concat ""
              (List.map (fun ia =>
                 let '(i, a) := ia in
                 if Nat.eqb i 0 then "" else
                 if is_scalar_param f i then
                   indent ++ "__mv__ = " ++ pp_expr_ax ax a ++ "; " ++ ffi_buf f ++ "["
                     ++ pp_int (n * Z.of_nat i) ++ "] = __mv__;" ++ LF
                 else
                 match addr ax a with
                 | Some src => pp_copy_ax ax indent (ffi_buf f, JElit (8 * n * Z.of_nat i)) src n
                 | None => indent ++ "ERROR_ffi_arg(" ++ f ++ ");" ++ LF
                 end) idx) ++
            indent ++ ffi_buf f ++ " = #randombytes(" ++ ffi_buf f ++ ");" ++ LF ++
            pp_copy_ax ax indent d0 (whole (ffi_buf f)) n
        end
    | _, _ =>
        let scalar_arg i a :=
          orb (is_scalar_param f i)
            (match addr ax a with Some _ => false | None => true end) in
        (* An argument that is a whole array of the callee's width, and whose
           array no other argument of the call uses, is passed as it is; every
           other pointer argument is staged. *)
        let uses r := List.length (List.filter (fun a' =>
                        match root_of ax a' with Some r' => String.eqb r r' | None => false end) args) in
        let written i := nat_in i (wlookup we f) in
        let whole_at i r k :=
          andb (Z.eqb k 0)
            (match awidth_lookup (ax_widths ax) r with
             | Some w => Z.eqb w (nthw cw i) | None => false end) in
        (* [rpc_direct]: another, written argument of the same root overlapping
           this one (a dynamic offset counts as overlapping).  jasminc requires the
           writable arguments of a call to be disjoint from all others; so a
           written argument is passed as it is unless another written one overlaps
           it, and a read argument that overlaps a written one is staged: its copy
           is taken before the call, so the callee reads the value at the call,
           as with full staging. *)
        let clash i a :=
          match addr ax a with
          | Some (r, JElit k) =>
              List.existsb (fun jb =>
                let '(j, b) := jb in
                andb (negb (Nat.eqb i j))
                  (andb (negb (scalar_arg j b))
                    (match addr ax b with
                     | Some (r', JElit k') =>
                         andb (String.eqb r r')
                           (andb (written j)
                             (andb (Z.ltb (Z.div k 8) (Z.div k' 8 + nthw cw j))
                                   (Z.ltb (Z.div k' 8) (Z.div k 8 + nthw cw i))))
                     | Some (r', _) => andb (String.eqb r r') (written j)
                     | None => false
                     end))) idx
          | Some (r, _) =>
              (* a read-only argument at a run-time offset: no written argument of the
                 same root may be passed in the same call *)
              orb (written i)
                (List.existsb (fun jb =>
                   let '(j, b) := jb in
                   andb (negb (Nat.eqb i j))
                     (andb (negb (scalar_arg j b))
                       (match addr ax b with
                        | Some (r', _) => andb (String.eqb r r') (written j)
                        | None => false
                        end))) idx)
          | _ => true
          end in
        let direct i a :=
          andb (negb (scalar_arg i a))
            (match addr ax a with
             | Some (r, JElit k) =>
                 if rpc_direct cfg then negb (clash i a) else
                 andb (Nat.eqb (uses r) 1)
                   (* a slice of a stack array (addressed from the stack pointer),
                      or a whole pointer parameter of the callee's width (into a
                      called function only): a slice of a pointer parameter would
                      keep the parameter in a register across the call *)
                   (orb (negb (string_in r (ax_params ax)))
                        (andb (negb (string_in f (rpc_inline cfg))) (whole_at i r k)))
             | Some (r, off) =>
                 (* [rpc_direct]: a read-only slice of a pointer parameter at a run-time
                    offset [off] (bytes, of the forms of [div8]) is passed through
                    [__rq<w>_<i> = r[__ix<i> : w]], [__ix<i> = off / 8] *)
                 andb (rpc_direct cfg)
                   (andb (string_in r (ax_params ax))
                     (andb (match div8 off with Some _ => true | None => false end)
                       (negb (clash i a))))
             | _ => false
             end) in
        (* a written slice (or the whole) of a pointer parameter, passed through [__rp<w>_<i>]:
           [__rp = r[k : w]; __rp = f(.., __rp, ..); r = r__s; r[k : w] = __rp].
           The parameter itself need not survive the call (it is reloaded from
           its slot); the last assignment writes the callee's result into the
           slice, and is a no-op in the compiled code, where [__rp] points into
           [r]. *)
        (* With [rpc_direct] every pointer-parameter argument goes through a
           temporary of its own: jasminc coalesces an argument variable with the
           callee's parameter, so one variable passed at two positions (or at
           different positions of different calls) cannot be allocated.  A read-only
           one through [__rq<w>_<i> = r[k : w]]. *)
        let param_root a :=
          match addr ax a with
          | Some (r, _) => string_in r (ax_params ax)
          | _ => false
          end in
        let via_temp i a := andb (rpc_direct cfg) (andb (direct i a) (andb (written i) (param_root a))) in
        let via_rq i a := andb (rpc_direct cfg) (andb (direct i a) (andb (negb (written i)) (param_root a))) in
        let rp i := "__rp" ++ pp_int (nthw cw i) ++ "_" ++ pp_int (Z.of_nat i) in
        let rq i := "__rq" ++ pp_int (nthw cw i) ++ "_" ++ pp_int (Z.of_nat i) in
        let name i a :=
          if via_temp i a then rp i else
          if via_rq i a then rq i else
          if direct i a then
            match addr ax a with
            | Some (r, JElit k) =>
                match awidth_lookup (ax_widths ax) r with
                | Some w => if andb (Z.eqb k 0) (Z.eqb w (nthw cw i)) then r
                            else r ++ "[" ++ pp_int (Z.div k 8) ++ " : " ++ pp_int (nthw cw i) ++ "]"
                | None => r ++ "[" ++ pp_int (Z.div k 8) ++ " : " ++ pp_int (nthw cw i) ++ "]"
                end
            | _ => ""
            end
          else sg (nthw cw i) i in
        let ix i := "__ix" ++ pp_int (Z.of_nat i) in
        let slice_of i a :=
          match addr ax a with
          | Some (r, JElit k) => r ++ "[" ++ pp_int (Z.div k 8) ++ " : " ++ pp_int (nthw cw i) ++ "]"
          | Some (r, _) => r ++ "[(uint) " ++ ix i ++ " : " ++ pp_int (nthw cw i) ++ "]"
          | _ => ""
          end in
        let set_ix i a :=
          match addr ax a with
          | Some (_, JElit _) => ""
          | Some (_, off) =>
              match div8 off with
              | Some e => indent ++ ix i ++ " = " ++ pp_expr e ++ ";" ++ LF
              | None => ""
              end
          | None => ""
          end in
        let setup :=
          String.concat ""
            (List.map (fun ia =>
               let '(i, a) := ia in
               if scalar_arg i a then indent ++ la i ++ " = " ++ pp_expr a ++ ";" ++ LF
               else if via_temp i a then
                 reload ax indent (root_of ax a) ++ indent ++ rp i ++ " = " ++ slice_of i a ++ ";" ++ LF
               else if via_rq i a then
                 set_ix i a ++
                 reload ax indent (root_of ax a) ++ indent ++ rq i ++ " = " ++ slice_of i a ++ ";" ++ LF
               else if direct i a then reload ax indent (root_of ax a)
               else match addr ax a with
                    | Some src => pp_copy_ax ax indent (whole (sg (nthw cw i) i)) src (nthw cw i)
                    | None => ""
                    end) idx) in
        let call_args :=
          String.concat ", "
            (List.map (fun ia =>
               let '(i, a) := ia in
               if scalar_arg i a then la i else name i a) idx) in
        let outs := List.filter (fun ia => let '(i, a) := ia in
                      andb (nat_in i (wlookup we f)) (negb (scalar_arg i a))) idx in
        let lhs := String.concat ", " (List.map (fun ia => name (fst ia) (snd ia)) outs) in
        let back :=
          String.concat ""
            (List.map (fun ia =>
               let '(i, a) := ia in
               if via_temp i a then
                 reload ax indent (root_of ax a) ++ indent ++ slice_of i a ++ " = " ++ rp i ++ ";" ++ LF ++
                 save ax indent (root_of ax a)
               else if direct i a then save ax indent (root_of ax a) else
               match addr ax a with
               | Some dst => pp_copy_ax ax indent dst (whole (sg (nthw cw i) i)) (nthw cw i)
               | None => ""
               end) outs) in
        setup ++
        indent ++ (match outs with nil => "" | _ => lhs ++ " = " end) ++
          f ++ "(" ++ call_args ++ ");" ++ LF ++
        back
    end.

  (** The command printer: [Core.pp_cmd_regptr] with [pp_call] for calls and
      [addr] for accesses. *)
  Fixpoint pp_cmd_sized (env : regptr_env) (we : wenv) (ax : actx) (bools : list string)
      (indent : string) (c : jasmin_cmd) : string :=
    match c with
    | JCskip => ""
    | JCseq c1 c2 => pp_cmd_sized env we ax bools indent c1 ++ pp_cmd_sized env we ax bools indent c2
    | JCset x (JEload base off) =>
        reload ax indent (root_of ax base) ++
        indent ++ x ++ " = " ++ pp_elem ax base off ++ ";" ++ LF
    | JCset x e =>
        if List.existsb (fun p => String.eqb (fst p) x) (ax_pv ax) then
          match addr ax e with
          | Some (_, o) => indent ++ x ++ " = " ++ pp_expr o ++ ";" ++ LF
          | None => indent ++ "ERROR_pointer_variable(" ++ x ++ ");" ++ LF
          end
        else
        match e with
        | JEshr a b =>
            match b with
            | JElit _ => indent ++ x ++ " = (" ++ pp_expr a ++ " >> " ++ pp_expr b ++ ");" ++ LF
            | _ =>
                (* the count goes in CL: a fresh register [__shc__] for the one
                   instruction, so that the count variable itself (a loop
                   counter live across calls) is not tied to RCX *)
                indent ++ "__shc__ = " ++ pp_expr b ++ ";" ++ LF ++
                indent ++ "_, _, _, _, _, " ++ x ++ " = #SHR(" ++ pp_expr a ++ ", __shc__);" ++ LF
            end
        | JEshl a b =>
            match b with
            | JElit _ => indent ++ x ++ " = (" ++ pp_expr a ++ " << " ++ pp_expr b ++ ");" ++ LF
            | _ =>
                indent ++ "__shc__ = " ++ pp_expr b ++ ";" ++ LF ++
                indent ++ "_, _, _, _, _, " ++ x ++ " = #SHL(" ++ pp_expr a ++ ", __shc__);" ++ LF
            end
        | JEmulhuu a b =>
            (* a high word without its low half ([polish_func] pairs the
               others into [JCmulx]): one [#MULX], the low word discarded *)
            let b_load := match b with JElit _ => indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF | _ => "" end in
            let b_ref := match b with JElit _ => "__wtmp__" | _ => pp_expr b end in
            b_load ++ indent ++ "__mulx_tmp__ = " ++ pp_expr a ++ ";" ++ LF ++
            indent ++ "(" ++ x ++ ", __mlo__) = #MULX(__mulx_tmp__, " ++ b_ref ++ ");" ++ LF
        (* [k <u b] with a literal [k] ([fr_to_mont]'s [0 <u x]): x86 compares a register
           with an immediate, so [b >u k] *)
        | JEltu (JElit k) (JEvar b) => indent ++ x ++ " = (" ++ b ++ " >u " ++ pp_int k ++ ");" ++ LF
        | _ => reload_all ax indent (load_roots ax e) ++
               indent ++ x ++ " = " ++ pp_expr_ax ax e ++ ";" ++ LF
        end
    | JCstore base off v =>
        match v with
        | JEload _ _ =>
            (* memory to memory goes through a register *)
            reload_all ax indent (load_roots ax v) ++
            indent ++ "__mv__ = " ++ pp_expr_ax ax v ++ ";" ++ LF ++
            reload ax indent (root_of ax base) ++
            indent ++ pp_elem ax base off ++ " = __mv__;" ++ LF ++
            save ax indent (root_of ax base)
        | _ =>
            reload_all ax indent (load_roots ax v) ++
            reload ax indent (root_of ax base) ++
            indent ++ pp_elem ax base off ++ " = " ++ pp_expr_ax ax v ++ ";" ++ LF ++
            save ax indent (root_of ax base)
        end
    | JCcall f args => pp_call env we ax indent f args
    | JCif e ct cf =>
        (* a comparison whose operands are not a register and a register or
           literal is computed into [__ca__] / [__cb__] first: x86 compares a
           register with a register or an immediate *)
        let atoms a b := match a, b with JEvar _, JEvar _ | JEvar _, JElit _ => true | _, _ => false end in
        (* [t = y op b] with [y] a variable is printed [t = y; t = (t op b)] when
           [rpc_hints] is on: x86 adds in place, and jasminc does not copy [y]
           into [t] by itself (under #20 every word local was [#[spill]], and
           -auto-spill's reload of [y] made that copy) *)
        let pp_scratch t a :=
          match a with
          | JEadd (JEvar y) b =>
              if rpc_hints cfg
              then indent ++ t ++ " = " ++ y ++ ";" ++ LF ++
                   indent ++ t ++ " = (" ++ t ++ " + " ++ pp_expr_ax ax b ++ ");" ++ LF
              else indent ++ t ++ " = " ++ pp_expr_ax ax a ++ ";" ++ LF
          | _ => indent ++ t ++ " = " ++ pp_expr_ax ax a ++ ";" ++ LF
          end in
        let setup :=
          match e with
          | JEltu a b | JEeq a b =>
              if atoms a b then "" else
              reload_all ax indent (List.app (load_roots ax a) (load_roots ax b)) ++
              pp_scratch "__ca__" a ++
              pp_scratch "__cb__" b
          | JEvar _ => ""
          (* any other word (ml_or_one's [i1 | i2]) is computed into [__ca__] first *)
          | _ => reload_all ax indent (load_roots ax e) ++ indent ++ "__ca__ = " ++ pp_expr_ax ax e ++ ";" ++ LF
          end in
        let cond_str :=
          match e with
          | JEvar x => if string_in x bools then x else "(" ++ x ++ " != 0)"
          | JEltu a b => if atoms a b then "(" ++ pp_expr e ++ ")" else "(__ca__ <u __cb__)"
          | JEeq a b => if atoms a b then "(" ++ pp_expr e ++ ")" else "(__ca__ == __cb__)"
          | _ => "(__ca__ != 0)"
          end in
        let else_part :=
          match cf with
          | JCskip => ""
          | _ => indent ++ "} else {" ++ LF ++ pp_cmd_sized env we ax bools ("  " ++ indent) cf
          end in
        (* [rpc_cmov]: [if c { x = a } else { x = b }] is [x = b; x = c ? a : x]
           and [if c { x = a }] is [x = c ? a : x], when [a] and [b] are a word
           variable or a literal, [x] is a word variable (not a bool, not a
           pointer variable), and neither [c] nor [a] reads [x] (so the first
           assignment does not change them).  x86 conditional moves take a
           register source: a literal [a] goes through [__wtmp__] first. *)
        let word_atom a :=
          match a with
          | JEvar y => negb (string_in y bools)
          | JElit _ => true
          | _ => false
          end in
        let reads_x x a := match a with JEvar y => String.eqb x y | _ => false end in
        let cmov_ok x a :=
          andb (rpc_cmov cfg)
            (andb (word_atom a)
              (andb (negb (reads_x x a))
                (andb (negb (string_in x (SL.expr_vars e)))
                  (andb (negb (string_in x bools))
                    (negb (List.existsb (fun p => String.eqb (fst p) x) (ax_pv ax))))))) in
        let src a := match a with JElit _ => indent ++ "__wtmp__ = " ++ pp_expr a ++ ";" ++ LF | _ => "" end in
        let src_ref a := match a with JElit _ => "__wtmp__" | _ => pp_expr a end in
        let cmov x a := indent ++ x ++ " = " ++ cond_str ++ " ? " ++ src_ref a ++ " : " ++ x ++ ";" ++ LF in
        match ct, cf with
        | JCset x a, JCset x' b =>
            if andb (String.eqb x x') (andb (cmov_ok x a) (word_atom b))
            then setup ++ indent ++ x ++ " = " ++ pp_expr b ++ ";" ++ LF ++ src a ++ cmov x a
            else setup ++ indent ++ "if " ++ cond_str ++ " {" ++ LF ++
                   pp_cmd_sized env we ax bools ("  " ++ indent) ct ++
                 else_part ++ indent ++ "}" ++ LF
        (* the borrow mask of fiat's subtraction, [if c { x = k; x = x - m }]:
           the branch leaves the constant [k - m] (mod 2^64) in [x] *)
        | JCseq (JCset x (JElit k)) (JCset x' (JEsub (JEvar x'') (JElit m))), JCskip =>
            let a := JElit ((k - m) mod 2 ^ 64) in
            if andb (String.eqb x x') (andb (String.eqb x x'') (cmov_ok x a))
            then setup ++ src a ++ cmov x a
            else setup ++ indent ++ "if " ++ cond_str ++ " {" ++ LF ++
                   pp_cmd_sized env we ax bools ("  " ++ indent) ct ++
                 else_part ++ indent ++ "}" ++ LF
        | JCset x a, JCskip =>
            if cmov_ok x a
            then setup ++ src a ++ cmov x a
            else setup ++ indent ++ "if " ++ cond_str ++ " {" ++ LF ++
                   pp_cmd_sized env we ax bools ("  " ++ indent) ct ++
                 else_part ++ indent ++ "}" ++ LF
        | _, _ =>
            setup ++ indent ++ "if " ++ cond_str ++ " {" ++ LF ++
              pp_cmd_sized env we ax bools ("  " ++ indent) ct ++
            else_part ++ indent ++ "}" ++ LF
        end
    | JCwhile e body =>
        (* a comparison is a Jasmin bool already ([words_eq]'s [i <u n]); any other
           condition is a word, tested against 0 *)
        let c := match e with
                 | JEltu _ _ | JEeq _ _ => pp_expr e
                 | _ => pp_expr e ++ " != 0"
                 end in
        indent ++ "while (" ++ c ++ ") {" ++ LF ++
          pp_cmd_sized env we ax bools ("  " ++ indent) body ++
        indent ++ "}" ++ LF
    | JCdecl x ty body =>
        indent ++ pp_type ty ++ " " ++ x ++ ";" ++ LF ++ pp_cmd_sized env we ax bools indent body
    | JCadd_flags cf result a b =>
        indent ++ "_, " ++ cf ++ ", _, _, _, " ++ result ++ " = #ADD(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ");" ++ LF
    | JCadcx cf_out result a b cf_in =>
        indent ++ cf_out ++ ", " ++ result ++ " = #ADCX(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ", " ++ cf_in ++ ");" ++ LF
    | JCmulx hi lo a b =>
        let b_load := match b with JElit _ => indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF | _ => "" end in
        let b_ref := match b with JElit _ => "__wtmp__" | _ => pp_expr b end in
        b_load ++ indent ++ "__mulx_tmp__ = " ++ pp_expr a ++ ";" ++ LF ++
        indent ++ "(" ++ hi ++ ", " ++ lo ++ ") = #MULX(__mulx_tmp__, " ++ b_ref ++ ");" ++ LF
    | JCsub_flags cf result a b =>
        indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF ++
        indent ++ result ++ " = " ++ pp_expr a ++ ";" ++ LF ++
        indent ++ "_, " ++ cf ++ ", _, _, _, " ++ result ++ " = #SUB(" ++ result ++ ", __wtmp__);" ++ LF
    | JCsbb cf_out result a b cf_in =>
        indent ++ "__wtmp__ = " ++ pp_expr b ++ ";" ++ LF ++
        indent ++ result ++ " = " ++ pp_expr a ++ ";" ++ LF ++
        indent ++ "_, " ++ cf_out ++ ", _, _, _, " ++ result ++ " = #SBB(" ++ result ++ ", __wtmp__, " ++ cf_in ++ ");" ++ LF
    end.

  (** The staging buffers, scalar registers and system-call buffers a body
      uses, so that each function declares exactly those. *)
  Fixpoint calls_of (c : jasmin_cmd) : list (string * list jasmin_expr) :=
    match c with
    | JCseq c1 c2 => List.app (calls_of c1) (calls_of c2)
    | JCif _ ct cf => List.app (calls_of ct) (calls_of cf)
    | JCwhile _ body => calls_of body
    | JCdecl _ _ body => calls_of body
    | JCcall f args => [(f, args)]
    | _ => nil
    end.

  Fixpoint dedup_z (acc : list (Z * nat)) (xs : list (Z * nat)) : list (Z * nat) :=
    match xs with
    | nil => List.rev acc
    | (w, i) :: r =>
        if List.existsb (fun p => andb (Z.eqb (fst p) w) (Nat.eqb (snd p) i)) acc
        then dedup_z acc r else dedup_z ((w, i) :: acc) r
    end.

  (** [str_occurs pat s]: [pat] occurs in [s]. *)
  Fixpoint str_occurs (pat s : string) : bool :=
    match s with
    | EmptyString => String.eqb pat EmptyString
    | String _ s' => orb (String.prefix pat s) (str_occurs pat s')
    end.

  (** [body_s] is the printed body: an [__ix<i>] register (a run-time offset of a read-only
      pointer argument, [rpc_direct]) is declared only when the body assigns it. *)
  Definition decls_for (env : regptr_env) (body : jasmin_cmd) (body_s : string) : string :=
    let cs := calls_of body in
    let max_arity := List.fold_left Nat.max (List.map (fun p => List.length (snd p)) cs) O in
    let sgs := dedup_z nil (List.concat (List.map (fun '(f, args) =>
                 if is_ffi f then nil else
                 List.map (fun i => (nthw (widths_of env f) i, i))
                   (List.seq 0 (List.length args))) cs)) in
    let ffis := dedup_strings nil (List.concat (List.map (fun '(f, _) =>
                  if is_ffi f then [f] else nil) cs)) in
    "  reg u64 __mv__;" ++ LF ++
    "  reg u64 __mlo__;" ++ LF ++
    "  reg u64 __shc__;" ++ LF ++
    "  reg u64 __ca__;" ++ LF ++
    "  reg u64 __cb__;" ++ LF ++
    "  inline int __j;" ++ LF ++
    (if str_occurs "__jr__ = 0;" body_s
     then "  reg u64 __jr__;" ++ LF ++ "  reg u64 __jx__;" ++ LF ++ "  reg u64 __jy__;" ++ LF
     else "") ++
    String.concat "" (List.map (fun i => "  reg u64 " ++ la i ++ ";" ++ LF) (List.seq 0 max_arity)) ++
    (if rpc_direct cfg then
       String.concat "" (List.map (fun i =>
         if str_occurs ("__ix" ++ pp_int (Z.of_nat i) ++ " =") body_s
         then "  reg u64 __ix" ++ pp_int (Z.of_nat i) ++ ";" ++ LF else "")
                           (List.seq 0 max_arity))
     else "") ++
    String.concat "" (List.map (fun '(w, i) => "  stack u64[" ++ pp_int w ++ "] " ++ sg w i ++ ";" ++ LF) sgs) ++
    (if rpc_direct cfg then
       String.concat "" (List.map (fun '(w, i) =>
         "  reg ptr u64[" ++ pp_int w ++ "] __rp" ++ pp_int w ++ "_" ++ pp_int (Z.of_nat i) ++ ";" ++ LF ++
         "  reg const ptr u64[" ++ pp_int w ++ "] __rq" ++ pp_int w ++ "_" ++ pp_int (Z.of_nat i) ++ ";" ++ LF) sgs)
     else "") ++
    String.concat "" (List.map (fun f =>
      match ffi_len f with
      | Some len => "  stack u64[" ++ pp_int len ++ "] " ++ ffi_buf f ++ ";" ++ LF
      | None => ""
      end) ffis).

  (** The locals declared without [#[spill]]: with [rpc_hints] those not in
      the choice [hs], otherwise none (every word local of a called function
      is hinted, the convention of #20). *)
  Definition hint_nospill (hs locals : list string) : list string :=
    if rpc_hints cfg then List.filter (fun x => negb (string_in x hs)) locals else nil.

  Definition pp_fn_keyword (name : string) : string :=
    if string_in name (rpc_inline cfg) then "inline fn " else "fn ".

  Definition pp_params (we : wenv) (hs : list string) (name : string) (ws : list Z)
      (ps : list (string * jasmin_type)) : string :=
    String.concat ", "
      (List.map (fun ip =>
        let '(i, (p, _)) := ip in
        if is_scalar_param name i then (if string_in p hs then "#[spill] " else "") ++ "reg u64 " ++ p
        else (if nat_in i (wlookup we name) then "reg ptr u64[" else "reg const ptr u64[")
               ++ pp_int (nthw ws i) ++ "] " ++ p)
        (List.combine (List.seq 0 (List.length ps)) ps)).

  (** A function returns the pointer parameters it writes, in order. *)
  Definition outs_of (we : wenv) (f : jasmin_func) : list (nat * string) :=
    List.map (fun ip => let '(i, (p, _)) := ip in (i, p))
      (List.filter (fun ip => nat_in (fst ip) (wlookup we (jf_name f)))
         (List.combine (List.seq 0 (List.length (jf_params f))) (jf_params f))).

  Definition pp_ret_ty (we : wenv) (ws : list Z) (f : jasmin_func) : string :=
    match outs_of we f with
    | nil => ""
    | os => " -> " ++ String.concat ", " (List.map (fun ip => "reg ptr u64[" ++ pp_int (nthw ws (fst ip)) ++ "]") os)
    end.

  (** Hint budgets of single functions: fiat's F_r functions (4 limbs; the Montgomery
      conversions printed without [carry_func]) fail register
      allocation at the leaf budget, as the Fp [to_mont] above 14. *)
  Definition budget_override : list (string * nat) :=
    [("bls12_fr_to_mont", 12%nat); ("bls12_fr_from_mont", 12%nat); ("bls12_fr_mul", 12%nat);
     ("bls12_fr_add", 12%nat); ("bls12_fr_sub", 12%nat)].

  Definition pp_func_sized (env : regptr_env) (we : wenv) (f : jasmin_func) : string :=
    let bools := dedup_strings nil (collect_bool_vars (jf_body f)) in
    let locals := function_locals f in
    let ws := widths_of env (jf_name f) in
    let os := outs_of we f in
    let budget := match List.find (fun p => String.eqb (fst p) (jf_name f)) budget_override with
                  | Some (_, b) => b | None => rpc_budget cfg end in
    let hs := if rpc_hints cfg then hint_choice budget f else nil in
    let ax := actx_of (if rpc_hints cfg then Some hs else None) ws f in
    let body_s := pp_cmd_sized env we ax bools "  " (jf_body f) in
    pp_fn_keyword (jf_name f) ++ jf_name f ++ "(" ++
      pp_params we (if string_in (jf_name f) (rpc_inline cfg) then nil else hs)
        (jf_name f) ws (jf_params f) ++ ")"
      ++ pp_ret_ty we ws f ++ " {" ++ LF ++
    (if string_in "__wtmp__" locals then "" else "  reg u64 __wtmp__;" ++ LF) ++
    (if string_in "__mulx_tmp__" locals then "" else "  reg u64 __mulx_tmp__;" ++ LF) ++
    decls_for env (jf_body f) body_s ++
    (* Word locals of a function that is called (not inlined) carry the
       [#[spill]] hint, so that [jasminc -auto-spill] may keep them on the stack
       across calls: at a call only the six callee-saved registers survive.
       The hint does not change the meaning of the program
       ([Core.pp_locals_decls_spill_form] / [pp_locals_decls_nospill_drops_spill],
       [pp_locals_decls_line] for any choice).  With [rpc_hints] only the
       locals of [hint_choice] carry it.  An inlined leaf keeps plain
       registers. *)
    (if string_in (jf_name f) (rpc_inline cfg)
     then pp_locals_decls_nospill "  " bools locals
     else pp_locals_decls "  " bools (hint_nospill hs locals) locals) ++
    String.concat "" (List.map (fun ip =>
      let '(i, (p, _)) := ip in
      if string_in p (ax_spill ax) then
        "  stack ptr u64[" ++ pp_int (nthw ws i) ++ "] " ++ p ++ "__s;" ++ LF else "")
      (List.combine (List.seq 0 (List.length (jf_params f))) (jf_params f))) ++
    String.concat "" (List.map (fun p => "  " ++ p ++ "__s = " ++ p ++ ";" ++ LF) (ax_spill ax)) ++
    body_s ++
    String.concat "" (List.map (fun ip => reload ax "  " (Some (snd ip))) os) ++
    (match os with nil => "" | _ => "  return " ++ String.concat ", " (List.map snd os) ++ ";" ++ LF end) ++
    "}" ++ LF.

  (** [export fn sym(...)]: passes its parameters to the local function. *)
  Definition pp_export (env : regptr_env) (we : wenv) (fs : list jasmin_func)
      (fe : string * string) : string :=
    let '(fname, sym) := fe in
    match List.find (fun f => String.eqb (jf_name f) fname) fs with
    | None => "ERROR_export_missing(" ++ fname ++ ");" ++ LF
    | Some f =>
        let ws := widths_of env fname in
        let names := List.map fst (jf_params f) in
        let os := outs_of we f in
        "export fn " ++ sym ++ "(" ++ pp_params we nil fname ws (jf_params f) ++ ")"
          ++ pp_ret_ty we ws f ++ " {" ++ LF ++
        "  " ++ (match os with nil => "" | _ => String.concat ", " (List.map snd os) ++ " = " end)
          ++ fname ++ "(" ++ String.concat ", " names ++ ");" ++ LF ++
        (match os with nil => "" | _ => "  return " ++ String.concat ", " (List.map snd os) ++ ";" ++ LF end) ++
        "}" ++ LF
    end.

  (** First definition of each name (as [map.of_list] keeps the first
      binding), minus [rpc_skip]. *)
  Fixpoint dedup_funcs (seen : list string) (fs : list jasmin_func) : list jasmin_func :=
    match fs with
    | nil => nil
    | f :: r =>
        if string_in (jf_name f) seen then dedup_funcs seen r
        else f :: dedup_funcs (jf_name f :: seen) r
    end.

  Fixpoint reach_names (fuel : nat) (fs : list jasmin_func) (names : list string) : list string :=
    match fuel with
    | O => names
    | S k =>
        let more := List.concat (List.map (fun f =>
          if string_in (jf_name f) names then List.map fst (calls_of (jf_body f)) else nil) fs) in
        reach_names k fs (dedup_strings nil (List.app names more))
    end.

  Definition candidates (fs : list jasmin_func) : list jasmin_func :=
    List.filter (fun f => negb (string_in (jf_name f) (rpc_skip cfg))) (dedup_funcs nil fs).

  Definition printed (fs : list jasmin_func) : list jasmin_func :=
    let cs := candidates fs in
    if rpc_export_all cfg then cs else
    let names := reach_names (List.length cs) cs (List.map fst (rpc_exports cfg)) in
    List.filter (fun f => string_in (jf_name f) names) cs.

  Definition all_exports (fs : list jasmin_func) : list (string * string) :=
    List.app (rpc_exports cfg)
      (if rpc_export_all cfg then
         List.map (fun f => (jf_name f, "jasmin_" ++ jf_name f))
           (List.filter (fun f =>
              andb (Nat.leb (List.length (jf_params f)) 6)
                   (negb (List.existsb (fun e => String.eqb (fst e) (jf_name f)) (rpc_exports cfg))))
              (printed fs))
       else nil).

  Definition module_env (fs : list jasmin_func) : regptr_env :=
    infer_iter 24 (printed fs) seed.

  (** Callees first: Jasmin requires a function to be defined before it is
      called.  [order] repeatedly takes the functions whose callees are all
      placed (or outside the module). *)
  Definition callees (f : jasmin_func) : list string := List.map fst (calls_of (jf_body f)).

  Fixpoint order (fuel : nat) (placed : list string) (todo : list jasmin_func) : list jasmin_func :=
    match fuel with
    | O => todo
    | S fuel' =>
        let names := List.map jf_name todo in
        let ready := List.filter (fun f =>
          List.forallb (fun g => orb (string_in g placed) (negb (string_in g names)))
            (callees f)) todo in
        match ready with
        | nil => todo
        | _ =>
            let rnames := List.map jf_name ready in
            List.app ready (order fuel' (List.app placed rnames)
                         (List.filter (fun f => negb (string_in (jf_name f) rnames)) todo))
        end
    end.

  Definition ordered (fs : list jasmin_func) : list jasmin_func :=
    order (List.length fs) nil (printed fs).

  Definition module_wenv (fs : list jasmin_func) : wenv :=
    written_iter 24 (printed fs) nil.

  Definition pp_module_sized (fs : list jasmin_func) : string :=
    let env := module_env fs in
    let we := module_wenv fs in
    String.concat (LF ++ LF) (List.map (pp_func_sized env we) (ordered fs)) ++ LF ++ LF ++
    String.concat (LF ++ LF) (List.map (pp_export env we (printed fs)) (all_exports fs)).
End Printer.

(** ** What the printer does not change *)

(** [ordered] is a permutation of [printed]: placing a function never drops or
    duplicates it, so every printed body is one of the input bodies.  We record
    the weaker, directly checkable fact that every function of [ordered fs] is
    a function of [fs] with its body untouched. *)
Lemma order_sub : forall fuel placed todo f,
  In f (order fuel placed todo) -> In f todo.
Proof.
  intros fuel. induction fuel as [| fuel IH]; intros placed todo f H; cbn in H.
  - exact H.
  - destruct (List.filter _ todo) as [| r rs] eqn:Hr.
    + exact H.
    + apply in_app_or in H. destruct H as [H | H].
      * rewrite <- Hr in H. apply filter_In in H. tauto.
      * apply IH in H. apply filter_In in H. tauto.
Qed.

Lemma dedup_funcs_sub : forall seen fs f, In f (dedup_funcs seen fs) -> In f fs.
Proof.
  intros seen fs. revert seen. induction fs as [| g r IH]; intros seen f H; cbn in H.
  - exact H.
  - destruct (string_in (jf_name g) seen).
    + right. eapply IH. exact H.
    + destruct H as [H | H]; [left; exact H | right; eapply IH; exact H].
Qed.

Lemma pp_module_sized_same_bodies : forall cfg fs f,
  In f (ordered cfg fs) -> In f fs.
Proof.
  intros cfg fs f H. unfold ordered in H. apply order_sub in H.
  unfold printed, candidates in H.
  destruct (rpc_export_all cfg); [| apply filter_In in H; destruct H as [H _]];
    apply filter_In in H; destruct H as [H _]; eapply dedup_funcs_sub; exact H.
Qed.

(** The storage class is one of the three keywords; it never depends on the
    body. *)
Lemma pp_fn_keyword_cases : forall cfg name,
  pp_fn_keyword cfg name = "inline fn " \/ pp_fn_keyword cfg name = "fn ".
Proof.
  intros cfg name. unfold pp_fn_keyword.
  destruct (string_in name (rpc_inline cfg)); [left | right]; reflexivity.
Qed.

(** ** The hints are the only difference in the declarations

    With [rpc_hints] the local declarations are [pp_locals_decls] with the
    no-spill set [hint_nospill]; without, with the empty set (#20).  For any
    set, the declarations are the concatenation of one line per local, and
    each line is the hint-free line of [Core.pp_locals_decls_nospill] or that
    line with [#[spill] ] inserted: the two denote the same Jasmin local
    ([Core.pp_locals_decls_spill_form], [Core.pp_locals_decls_nospill_drops_spill]).
    A scalar parameter is printed with the hint only when it is in the choice,
    and never in an export wrapper ([pp_params_no_hints]).  The choice itself
    is a set of candidates of [SpillLiveness] ([hint_choice_candidates]):
    register parameters and non-boolean, non-scratch locals. *)
Lemma pp_locals_decls_lines : forall indent bools ns xs,
  pp_locals_decls indent bools ns xs =
    String.concat "" (List.map (fun x => pp_locals_decls indent bools ns [x]) xs).
Proof.
  intros indent bools ns xs. reflexivity.
Qed.

Lemma pp_locals_decls_nospill_lines : forall indent bools xs,
  pp_locals_decls_nospill indent bools xs =
    String.concat "" (List.map (fun x => pp_locals_decls_nospill indent bools [x]) xs).
Proof.
  intros indent bools xs. reflexivity.
Qed.

Lemma pp_locals_decls_line : forall indent bools ns x,
  pp_locals_decls indent bools ns [x] = pp_locals_decls_nospill indent bools [x] \/
  (pp_locals_decls_nospill indent bools [x] = indent ++ "reg u64 " ++ x ++ ";" ++ LF /\
   pp_locals_decls indent bools ns [x] = indent ++ "#[spill] reg u64 " ++ x ++ ";" ++ LF).
Proof.
  intros indent bools ns x. unfold pp_locals_decls, pp_locals_decls_nospill; cbn.
  destruct (string_in x bools); [left; reflexivity|].
  destruct (string_in x ns); [left; reflexivity | right; split; reflexivity].
Qed.

Lemma pp_params_no_hints : forall cfg we name ws ps,
  pp_params cfg we nil name ws ps =
    String.concat ", "
      (List.map (fun ip =>
        let '(i, (p, _)) := ip in
        if is_scalar_param cfg name i then "reg u64 " ++ p
        else (if nat_in i (wlookup cfg we name) then "reg ptr u64[" else "reg const ptr u64[")
               ++ pp_int (nthw cfg ws i) ++ "] " ++ p)
        (List.combine (List.seq 0 (List.length ps)) ps)).
Proof.
  intros. reflexivity.
Qed.
