(** * The BLS12-381 G1/G2 group operations and the G1 MSM as one Jasmin module.

    Function lists: [BLS12_G1ArenaRust.bls12_g1_funcs] (Pippenger MSM
    [msm_bls12], window c = 9; [g1_scalar_mul]; the copy-out wrappers;
    [curve_add] = RCB Alg. 7 and [curve_double_a0] = Alg. 9 at a = 0;
    [store_zero], [bls12_three_b], [bls12_felem_copy]) and
    [BLS12_G2ArenaRust.bls12_g2_funcs] ([g2_scalar_mul], the in-place and
    out-of-place Alg. 7 / 9 over Fp2, [bls12_Fp2_three_b]) -- the lists the
    safe-Rust emitters print into [src/g1_msm_extracted.rs] and
    [src/g2_extracted.rs] -- followed by the field functions they call, taken
    from [ExtractBLS12TowerJasmin.bls12_tower_funcs] (fiat-crypto
    [bls12_add]/[bls12_sub]/..., the Fp2 functions of [bls12_extra_funcs]).

    Added here, bedrock2 functions of one call each:
    - [bls12_zero] / [bls12_one]: [bls12_from_word(out, 0 / 1)], the constants
      the safe-Rust runtime ([bedrock_rt.rs]) supplies by hand for
      [store_zero];
    - the entry points [bls12_g1_add], [bls12_g1_double], [bls12_g1_scalar_mul],
      [bls12_g1_msm], [bls12_g2_add], [bls12_g2_double], [bls12_g2_scalar_mul]:
      they take a point as one pointer to x | y | z and pass the coordinate
      pointers to the listed function, with the argument order of the Rust
      wrappers of [src/group.rs] ([em_add], [em_double], [g1_scalar_mul],
      [g1_msm], [em2_add], [em2_double], [g2_scalar_mul]).  Jasmin's export
      functions take at most six arguments, the listed functions up to nine.

    Constant-time scalar multiplication: [g1_scalar_mul_ct] and [g2_scalar_mul_ct]
    ([BLS12_G1_ScalarMulCT], [BLS12_G2_ScalarMulCT]; [g1_scalar_mul_ct_closed],
    [g2_scalar_mul_ct_closed]) and their [ct_cswap] are in [bls12_g1_funcs] /
    [bls12_g2_funcs].  Both lists name their swap ["ct_cswap"] (6 and 12 words); in
    this one module the G2 one is renamed ["ct_cswap12"], in its definition and at
    its call sites in [g2_scalar_mul_ct] ([rename_fn]; [bls12_group_names_nodup]
    checks that the module's names are distinct).  Entry points
    [bls12_g1_scalar_mul_ct] / [bls12_g2_scalar_mul_ct] ([entry_smul_ct]) take the
    output point, a scratch point of the caller, the scalar and the input point.

    Translation and printer: as in [ExtractBLS12TowerJasmin.v]
    ([tr_func_sized 6], [AdcChain.polish_func_adc], [RegPtrSized.pp_module_sized]);
    [bls12_group_tr_faithful] is [tr_cmd_correct] for the whole list.  The MSM
    keeps addresses in variables ([bpx = buckets_x + 48 * i]); the printer
    turns them into byte offsets from their root array.  Its point and scalar
    arrays have a size known only at run time; they are declared for
    [msm_nmax] = 4096 points ([rpc_widths]). *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import bedrock2.Syntax.
Require Import Bedrock.BLS12_G1ArenaRust.
Require Import Bedrock.BLS12_G2ArenaRust.
Require Import Bedrock.ExtractBLS12TowerJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.AdcChain.
Require Import Bedrock.Jasmin.RegPtrSized.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Local Notation var := Syntax.expr.var.
Definition at_off (x : string) (bytes : Z) : expr :=
  expr.op bopname.add (var x) (expr.literal bytes).

Definition bls12_zero : function_t :=
  ("bls12_zero", (["out"], [], cmd.call [] "bls12_from_word" [var "out"; expr.literal 0])).
Definition bls12_one : function_t :=
  ("bls12_one", (["out"], [], cmd.call [] "bls12_from_word" [var "out"; expr.literal 1])).

(** [f(p, q, p+c, q+c, p+2c, q+2c, out, out+c, out+2c)], [c] the coordinate size. *)
Definition entry_add (name callee : string) (c : Z) : function_t :=
  (name, (["out"; "p"; "q"], [],
    cmd.call [] callee
      [var "p"; var "q"; at_off "p" c; at_off "q" c; at_off "p" (2 * c); at_off "q" (2 * c);
       var "out"; at_off "out" c; at_off "out" (2 * c)])).

(** [f(p, p+c, p+2c, out, out+c, out+2c)]. *)
Definition entry_double (name callee : string) (c : Z) : function_t :=
  (name, (["out"; "p"], [],
    cmd.call [] callee
      [var "p"; at_off "p" c; at_off "p" (2 * c); var "out"; at_off "out" c; at_off "out" (2 * c)])).

(** [f(out, out+c, out+2c, k, p, p+c, p+2c)]. *)
Definition entry_smul (name callee : string) (c : Z) : function_t :=
  (name, (["out"; "k"; "p"], [],
    cmd.call [] callee
      [var "out"; at_off "out" c; at_off "out" (2 * c); var "k";
       var "p"; at_off "p" c; at_off "p" (2 * c)])).

(** [msm_bls12(out, out+48, out+96, scalars, px, py, pz, n)]. *)
Definition entry_msm : function_t :=
  ("bls12_g1_msm", (["out"; "scalars"; "px"; "py"; "pz"; "n"], [],
    cmd.call [] "msm_bls12"
      [var "out"; at_off "out" 48; at_off "out" 96; var "scalars";
       var "px"; var "py"; var "pz"; var "n"])).

(** [f(out, out+c, out+2c, t, t+c, t+2c, k, p, p+c, p+2c)]: the constant-time
    ladders take the scratch point [t] (three coordinates) of the caller.  The
    entry takes [out, t, k, p]: jasminc wants the written pointers of an export
    function first. *)
Definition entry_smul_ct (name callee : string) (c : Z) : function_t :=
  (name, (["out"; "t"; "k"; "p"], [],
    cmd.call [] callee
      [var "out"; at_off "out" c; at_off "out" (2 * c);
       var "t"; at_off "t" c; at_off "t" (2 * c); var "k";
       var "p"; at_off "p" c; at_off "p" (2 * c)])).

(** Renaming a callee: the definition named [old] and every call to it. *)
Fixpoint rename_call (old new : string) (c : cmd) : cmd :=
  match c with
  | cmd.call rets f args => cmd.call rets (if String.eqb f old then new else f) args
  | cmd.seq c1 c2 => cmd.seq (rename_call old new c1) (rename_call old new c2)
  | cmd.cond e c1 c2 => cmd.cond e (rename_call old new c1) (rename_call old new c2)
  | cmd.while e c1 => cmd.while e (rename_call old new c1)
  | cmd.stackalloc x n c1 => cmd.stackalloc x n (rename_call old new c1)
  | c => c
  end.

Definition rename_fn (old new : string) (f : function_t) : function_t :=
  let '(name, (args, rets, body)) := f in
  (if String.eqb name old then new else name, (args, rets, rename_call old new body)).

(** A renaming of a name that no command calls changes nothing. *)
Fixpoint calls (f : string) (c : cmd) : bool :=
  match c with
  | cmd.call _ g _ => String.eqb g f
  | cmd.seq c1 c2 | cmd.cond _ c1 c2 => calls f c1 || calls f c2
  | cmd.while _ c1 | cmd.stackalloc _ _ c1 => calls f c1
  | _ => false
  end.

Lemma rename_call_not_called (old new : string) (c : cmd) :
  calls old c = false -> rename_call old new c = c.
Proof.
  induction c; cbn; intros H; try reflexivity;
    repeat match goal with
           | H : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H; destruct H
           end;
    try (rewrite IHc by assumption; reflexivity);
    try (rewrite IHc1, IHc2 by assumption; reflexivity).
  rewrite H. reflexivity.
Qed.

(** The G2 list with its swap renamed (see the header). *)
Definition bls12_g2_funcs_jasmin : list function_t :=
  List.map (rename_fn "ct_cswap" "ct_cswap12") bls12_g2_funcs.

Definition bls12_group_entries : list function_t :=
  [ entry_add "bls12_g1_add" "curve_add" 48;
    entry_double "bls12_g1_double" "curve_double_a0" 48;
    entry_smul "bls12_g1_scalar_mul" "g1_scalar_mul" 48;
    entry_msm;
    entry_add "bls12_g2_add" "g2_curve_add" 96;
    entry_double "bls12_g2_double" "g2_curve_double" 96;
    entry_smul "bls12_g2_scalar_mul" "g2_scalar_mul" 96;
    entry_smul_ct "bls12_g1_scalar_mul_ct" "g1_scalar_mul_ct" 48;
    entry_smul_ct "bls12_g2_scalar_mul_ct" "g2_scalar_mul_ct" 96 ].

Definition bls12_group_funcs : list function_t :=
  bls12_group_entries ++ bls12_g1_funcs ++ bls12_g2_funcs_jasmin ++ [bls12_zero; bls12_one]
    ++ bls12_tower_funcs.

(** The names of the module are distinct (a duplicate would be one Jasmin function
    for two bedrock2 functions). *)
Fixpoint nodupb (l : list string) : bool :=
  match l with
  | [] => true
  | x :: r => negb (List.existsb (String.eqb x) r) && nodupb r
  end.

Lemma bls12_group_names_nodup :
  nodupb (List.map fst (bls12_group_entries ++ bls12_g1_funcs ++ bls12_g2_funcs_jasmin
                        ++ [bls12_zero; bls12_one])) = true.
Proof. vm_compute. reflexivity. Qed.

Definition bls12_group_jasmin : list jasmin_func :=
  List.map (fun f => polish_func_adc (tr_func_sized 6 f)) bls12_group_funcs.

Lemma bls12_group_tr_faithful :
  Forall (fun f : function_t =>
            let '(_, (_, _, body)) := f in
            cmd_jasmin_equiv body (jf_body (tr_func_sized 6 f)))
    bls12_group_funcs.
Proof.
  apply Forall_forall. intros [name [[args rets] body]] _. cbn.
  apply tr_cmd_correct.
Qed.

Definition msm_nmax : Z := 4096.

Definition bls12_group_widths : list (string * list Z) :=
  [ ("msm_bls12", [6; 6; 6; 4 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6])%Z;
    ("bls12_g1_msm", [18; 4 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6])%Z;
    ("g1_scalar_mul", [6; 6; 6; 4; 6; 6; 6])%Z;
    ("g2_scalar_mul", [12; 12; 12; 4; 12; 12; 12])%Z;
    ("g1_scalar_mul_ct", [6; 6; 6; 6; 6; 6; 4; 6; 6; 6])%Z;
    ("g2_scalar_mul_ct", [12; 12; 12; 12; 12; 12; 4; 12; 12; 12])%Z;
    ("ct_cswap", [1; 6; 6])%Z;
    ("ct_cswap12", [1; 12; 12])%Z ].

(** Scalar (register) parameters: the swap bit of [ct_cswap] / [ct_cswap12]. *)
Definition bls12_group_scalars : list (string * list nat) :=
  [("bls12_from_word", [1%nat]); ("bls12_select_znz", [1%nat]);
   ("msm_bls12", [7%nat]); ("bls12_g1_msm", [5%nat]);
   ("ct_cswap", [0%nat]); ("ct_cswap12", [0%nat])].

Definition bls12_group_exports : list (string * string) :=
  [ ("bls12_g1_add", "jasmin_bls12_g1_add");
    ("bls12_g1_double", "jasmin_bls12_g1_double");
    ("bls12_g1_scalar_mul", "jasmin_bls12_g1_scalar_mul");
    ("bls12_g1_msm", "jasmin_bls12_g1_msm");
    ("bls12_g2_add", "jasmin_bls12_g2_add");
    ("bls12_g2_double", "jasmin_bls12_g2_double");
    ("bls12_g2_scalar_mul", "jasmin_bls12_g2_scalar_mul");
    ("bls12_g1_scalar_mul_ct", "jasmin_bls12_g1_scalar_mul_ct");
    ("bls12_g2_scalar_mul_ct", "jasmin_bls12_g2_scalar_mul_ct") ].

(** The configuration of #20 (see [ExtractBLS12TowerJasmin.bls12_tower_cfg]). *)
Definition bls12_group_cfg : rp_config := {|
  rpc_n := 6;
  rpc_ffi := [("bls12_mul", 18%Z); ("bls12_square", 12%Z); ("bls12_inv", 13%Z);
              ("bls12_from_word", 7%Z); ("bls12_opp", 14%Z)];
  rpc_inline := ["bls12_add"; "bls12_sub"; "bls12_select_znz"; "bls12_felem_copy"];
  rpc_scalar := bls12_group_scalars;
  rpc_skip := ["bls12_mul"; "bls12_square"; "bls12_inv"; "bls12_inv_pow_word";
               "bls12_from_word"; "bls12_to_mont"; "bls12_opp"];
  rpc_widths := bls12_group_widths;
  rpc_export_all := false;
  rpc_exports := bls12_group_exports;
  rpc_hints := false;
  rpc_budget := Bedrock.Jasmin.SpillLiveness.default_budget;
  rpc_cmov := false;
  rpc_direct := false |}.

Definition bls12_group_jazz_regptr_pr20 : string :=
  pp_module_sized bls12_group_cfg bls12_group_jasmin.

(** The configurations of this module's emission, as
    [ExtractBLS12TowerJasmin.bls12_tower_cfg_with]. *)
Definition bls12_group_cfg_with (local_leaves : bool) : rp_config := {|
  rpc_n := 6;
  rpc_ffi := (if local_leaves then [] else [("bls12_mul", 18%Z); ("bls12_square", 12%Z)]) ++
             [("bls12_inv", 13%Z); ("bls12_from_word", 7%Z); ("bls12_opp", 14%Z)];
  rpc_inline := bls12_jfast_inline;
  rpc_scalar := bls12_group_scalars;
  rpc_skip := (if local_leaves then [] else ["bls12_mul"; "bls12_square"]) ++
              ["bls12_inv"; "bls12_inv_pow_word"; "bls12_from_word"; "bls12_to_mont"; "bls12_opp"];
  rpc_widths := bls12_group_widths;
  rpc_export_all := false;
  rpc_exports := bls12_group_exports;
  rpc_hints := true;
  rpc_budget := bls12_leaf_budget;
  rpc_cmov := true;
  rpc_direct := true |}.

Definition bls12_group_jazz_regptr : string :=
  pp_module_sized (bls12_group_cfg_with true) bls12_group_jasmin.

Definition bls12_group_jazz_regptr_ffi : string :=
  pp_module_sized (bls12_group_cfg_with false) bls12_group_jasmin.
