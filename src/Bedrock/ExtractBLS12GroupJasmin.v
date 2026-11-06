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

    Translation and printer: as in [ExtractBLS12TowerJasmin.v]
    ([tr_func_sized 6], [polish_func], [RegPtrSized.pp_module_sized]);
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

Definition bls12_group_entries : list function_t :=
  [ entry_add "bls12_g1_add" "curve_add" 48;
    entry_double "bls12_g1_double" "curve_double_a0" 48;
    entry_smul "bls12_g1_scalar_mul" "g1_scalar_mul" 48;
    entry_msm;
    entry_add "bls12_g2_add" "g2_curve_add" 96;
    entry_double "bls12_g2_double" "g2_curve_double" 96;
    entry_smul "bls12_g2_scalar_mul" "g2_scalar_mul" 96 ].

Definition bls12_group_funcs : list function_t :=
  bls12_group_entries ++ bls12_g1_funcs ++ bls12_g2_funcs ++ [bls12_zero; bls12_one]
    ++ bls12_tower_funcs.

Definition bls12_group_jasmin : list jasmin_func :=
  List.map (fun f => polish_func (tr_func_sized 6 f)) bls12_group_funcs.

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

Definition bls12_group_cfg : rp_config := {|
  rpc_n := 6;
  rpc_ffi := [("bls12_mul", 18%Z); ("bls12_square", 12%Z); ("bls12_inv", 13%Z);
              ("bls12_from_word", 7%Z); ("bls12_opp", 14%Z)];
  rpc_inline := ["bls12_add"; "bls12_sub"; "bls12_select_znz"; "bls12_felem_copy"];
  rpc_scalar := [("bls12_from_word", [1%nat]); ("bls12_select_znz", [1%nat]);
                 ("msm_bls12", [7%nat]); ("bls12_g1_msm", [5%nat])];
  rpc_skip := ["bls12_mul"; "bls12_square"; "bls12_inv"; "bls12_inv_pow_word";
               "bls12_from_word"; "bls12_to_mont"; "bls12_opp"];
  rpc_widths :=
    [ ("msm_bls12", [6; 6; 6; 4 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6])%Z;
      ("bls12_g1_msm", [18; 4 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6 * msm_nmax; 6])%Z;
      ("g1_scalar_mul", [6; 6; 6; 4; 6; 6; 6])%Z;
      ("g2_scalar_mul", [12; 12; 12; 4; 12; 12; 12])%Z ];
  rpc_export_all := false;
  rpc_exports :=
    [ ("bls12_g1_add", "jasmin_bls12_g1_add");
      ("bls12_g1_double", "jasmin_bls12_g1_double");
      ("bls12_g1_scalar_mul", "jasmin_bls12_g1_scalar_mul");
      ("bls12_g1_msm", "jasmin_bls12_g1_msm");
      ("bls12_g2_add", "jasmin_bls12_g2_add");
      ("bls12_g2_double", "jasmin_bls12_g2_double");
      ("bls12_g2_scalar_mul", "jasmin_bls12_g2_scalar_mul") ] |}.

Definition bls12_group_jazz_regptr : string :=
  pp_module_sized bls12_group_cfg bls12_group_jasmin.
