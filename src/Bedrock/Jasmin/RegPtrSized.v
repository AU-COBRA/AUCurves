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
Require Import Bedrock.Jasmin.Core.
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
}.

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

  Definition actx_of (ws : list Z) (f : jasmin_func) : actx :=
    let ps := List.map snd (List.filter (fun ip => negb (is_scalar_param (jf_name f) (fst ip)))
                (List.combine (List.seq 0 (List.length (jf_params f))) (List.map fst (jf_params f)))) in
    let arrs := List.app ps (List.map fst (collect_array_widths (jf_body f))) in
    {| ax_arrs := arrs; ax_pv := pv_iter 8 arrs (sets_of (jf_body f)) nil;
       ax_spill := if string_in (jf_name f) (rpc_inline cfg) then nil else ps;
       ax_widths := List.app (List.combine (List.map fst (jf_params f)) ws)
                             (collect_array_widths (jf_body f));
       ax_params := ps |}.

  Definition addr (ax : actx) (e : jasmin_expr) := addr_of (ax_arrs ax) (ax_pv ax) e.

  (** The word [w] words past address [(r, o)]; [w] is a Jasmin [inline int]. *)
  Definition pp_at (ro : string * jasmin_expr) (w : string) : string :=
    let '(r, o) := ro in
    match o with
    | JElit k => r ++ "[" ++ pp_int (Z.div k 8) ++ " + " ++ w ++ "]"
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
                       (writes we (actx_of nil f) p (jf_body f)))
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
  Definition pp_copy (indent : string) (dst src : string * jasmin_expr) (len : Z) : string :=
    indent ++ "for __j = 0 to " ++ pp_int len ++ " { __mv__ = " ++ pp_at src "__j" ++ "; "
      ++ pp_at dst "__j" ++ " = __mv__; }" ++ LF.

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
        let direct i a :=
          andb (negb (scalar_arg i a))
            (match addr ax a with
             | Some (r, JElit k) =>
                 andb (Nat.eqb (uses r) 1)
                   (* a slice of a stack array (addressed from the stack pointer),
                      or a whole pointer parameter of the callee's width (into a
                      called function only): a slice of a pointer parameter would
                      keep the parameter in a register across the call *)
                   (orb (negb (string_in r (ax_params ax)))
                        (andb (negb (string_in f (rpc_inline cfg)))
                          (andb (Z.eqb k 0)
                            (match awidth_lookup (ax_widths ax) r with
                             | Some w => Z.eqb w (nthw cw i) | None => false end))))
             | _ => false
             end) in
        let name i a :=
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
        let setup :=
          String.concat ""
            (List.map (fun ia =>
               let '(i, a) := ia in
               if scalar_arg i a then indent ++ la i ++ " = " ++ pp_expr a ++ ";" ++ LF
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
               if direct i a then save ax indent (root_of ax a) else
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
        let setup :=
          match e with
          | JEltu a b | JEeq a b =>
              if atoms a b then "" else
              reload_all ax indent (List.app (load_roots ax a) (load_roots ax b)) ++
              indent ++ "__ca__ = " ++ pp_expr_ax ax a ++ ";" ++ LF ++
              indent ++ "__cb__ = " ++ pp_expr_ax ax b ++ ";" ++ LF
          | _ => ""
          end in
        let cond_str :=
          match e with
          | JEvar x => if string_in x bools then x else "(" ++ x ++ " != 0)"
          | JEltu a b => if atoms a b then "(" ++ pp_expr e ++ ")" else "(__ca__ <u __cb__)"
          | JEeq a b => if atoms a b then "(" ++ pp_expr e ++ ")" else "(__ca__ == __cb__)"
          | _ => "(" ++ pp_expr e ++ " != 0)"
          end in
        let else_part :=
          match cf with
          | JCskip => ""
          | _ => indent ++ "} else {" ++ LF ++ pp_cmd_sized env we ax bools ("  " ++ indent) cf
          end in
        setup ++ indent ++ "if " ++ cond_str ++ " {" ++ LF ++
          pp_cmd_sized env we ax bools ("  " ++ indent) ct ++
        else_part ++ indent ++ "}" ++ LF
    | JCwhile e body =>
        indent ++ "while (" ++ pp_expr e ++ " != 0) {" ++ LF ++
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

  Definition decls_for (env : regptr_env) (body : jasmin_cmd) : string :=
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
    String.concat "" (List.map (fun i => "  reg u64 " ++ la i ++ ";" ++ LF) (List.seq 0 max_arity)) ++
    String.concat "" (List.map (fun '(w, i) => "  stack u64[" ++ pp_int w ++ "] " ++ sg w i ++ ";" ++ LF) sgs) ++
    String.concat "" (List.map (fun f =>
      match ffi_len f with
      | Some len => "  stack u64[" ++ pp_int len ++ "] " ++ ffi_buf f ++ ";" ++ LF
      | None => ""
      end) ffis).

  Definition pp_fn_keyword (name : string) : string :=
    if string_in name (rpc_inline cfg) then "inline fn " else "fn ".

  Definition pp_params (we : wenv) (name : string) (ws : list Z)
      (ps : list (string * jasmin_type)) : string :=
    String.concat ", "
      (List.map (fun ip =>
        let '(i, (p, _)) := ip in
        if is_scalar_param name i then "reg u64 " ++ p
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

  Definition pp_func_sized (env : regptr_env) (we : wenv) (f : jasmin_func) : string :=
    let bools := dedup_strings nil (collect_bool_vars (jf_body f)) in
    let locals := function_locals f in
    let ws := widths_of env (jf_name f) in
    let os := outs_of we f in
    pp_fn_keyword (jf_name f) ++ jf_name f ++ "(" ++ pp_params we (jf_name f) ws (jf_params f) ++ ")"
      ++ pp_ret_ty we ws f ++ " {" ++ LF ++
    (if string_in "__wtmp__" locals then "" else "  reg u64 __wtmp__;" ++ LF) ++
    (if string_in "__mulx_tmp__" locals then "" else "  reg u64 __mulx_tmp__;" ++ LF) ++
    decls_for env (jf_body f) ++
    (* Word locals of a function that is called (not inlined) carry the
       [#[spill]] hint, so that [jasminc -auto-spill] may keep them on the stack
       across calls: at a call only the six callee-saved registers survive.
       The hint does not change the meaning of the program
       ([Core.pp_locals_decls_spill_form] / [pp_locals_decls_nospill_drops_spill]).
       An inlined leaf keeps plain registers. *)
    (if string_in (jf_name f) (rpc_inline cfg)
     then pp_locals_decls_nospill "  " bools locals
     else pp_locals_decls "  " bools nil locals) ++
    let ax := actx_of ws f in
    String.concat "" (List.map (fun ip =>
      let '(i, (p, _)) := ip in
      if string_in p (ax_spill ax) then
        "  stack ptr u64[" ++ pp_int (nthw ws i) ++ "] " ++ p ++ "__s;" ++ LF else "")
      (List.combine (List.seq 0 (List.length (jf_params f))) (jf_params f))) ++
    String.concat "" (List.map (fun p => "  " ++ p ++ "__s = " ++ p ++ ";" ++ LF) (ax_spill ax)) ++
    pp_cmd_sized env we ax bools "  " (jf_body f) ++
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
        "export fn " ++ sym ++ "(" ++ pp_params we fname ws (jf_params f) ++ ")"
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
