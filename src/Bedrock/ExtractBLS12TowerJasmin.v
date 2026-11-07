(** * The BLS12-381 pairing tower as one Jasmin module.

    Companion of [ExtractBN254TowerJasmin.v] for BLS12-381 (Fp = 6 limbs).

    Function list.  [bls12_tower_funcs] is
    [BLS12_PairingFunctionalEnv.bls12_pairing_funcs ++
     BLS12_PairingFunctionalLeaves.bls12_extra_funcs], the environment of the
    functional pairing theorem
    [BLS12_PairingFunctionalLeaves.bls12_pairing_functional_unconditional]:
    the fiat-crypto Fp functions, the whole tower of
    [BLS12_Pairing.bls12_all_pairing_funcs] (Fp6/Fp12 arithmetic, Frobenius,
    line functions, Miller loop, final exponentiation, pairing), and the Fp2
    functions, Fp [from_word]/[to_mont]/[opp] and the Fermat inverse that the
    extraction list lacks.  The safe-Rust tower
    ([bls12-381-safe-rust/generated/bls12_safe_tower.rs],
    [ExtractSafeTowerBLS12.v]) prints [bls12_all_pairing_funcs] and supplies
    the same Fp2 and Fp functions by hand-written Rust; here they are printed
    from their bedrock2 bodies.

    Translation.  Each function goes through [Core.tr_func_sized 6] and
    [AdcChain.polish_func_adc] ([Core.polish_func] with the proved [adc_func]
    rewrite of fiat's add-with-carry / subtract-with-borrow windows into
    [#ADCX] / [#SBB] chains, [AdcChain.adc_cmd_correct]); [tr_cmd_correct] is
    the faithfulness theorem of the first step, and [bls12_tower_tr_faithful]
    instantiates it for every function of the list.  The Fp add and sub of the
    tower are therefore the ASTs of the live-hint leaves of
    [Jasmin/ExtractBLS12LeavesLive.v] ([bls12_tower_add_sub_are_leaves]: the
    same fiat functions, the same translation); the other functions have no
    fiat windows and translate as under [polish_func].  The module is printed by
    [RegPtrSized.pp_module_sized] under the reg-ptr convention (#227), with
    local [fn]s, [export fn] entry points and the three leaves
    [bls12_mul], [bls12_square], [bls12_inv] reached through [#randombytes]
    (see [RegPtrSized.v]; the crate's dispatcher sends them to CryptOpt's
    multiply and square and to safegcd).  The fiat-crypto bodies of
    [bls12_mul]/[bls12_square] and the Fermat ladder [bls12_inv] /
    [bls12_inv_pow_word] are therefore not printed; every other function of
    the list is.

    The text is written to
    [bls12-381-safe-rust/generated/bls12_tower_regptr.jazz] by
    [scripts/emit_bls12_tower_jasmin.sh] (driver
    [scripts/EmitBLS12TowerJasmin.v]); this file only defines it, so that dune
    can build it. *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalLeaves.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.AdcChain.
Require Import Bedrock.Jasmin.RegPtrSized.
Require Bedrock.Jasmin.SpillLiveness.
Require Bedrock.Jasmin.ExtractBLS12LeavesLive.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls12_tower_funcs : list function_t :=
  bls12_pairing_funcs ++ bls12_extra_funcs.

(** The list is the environment of the functional pairing theorem. *)
Lemma bls12_tower_funcs_eq :
  bls12_tower_funcs = bls12_pairing_funcs ++ bls12_extra_funcs.
Proof. reflexivity. Qed.

Definition bls12_tower_jasmin : list jasmin_func :=
  List.map (fun f => polish_func_adc (tr_func_sized 6 f)) bls12_tower_funcs.

(** The first [bls12_add] / [bls12_sub] of the list (the binding the printer
    keeps, [RegPtrSized.dedup_funcs]) are fiat-crypto's [bls12_add] /
    [bls12_sub] of [bls12_prime], the functions [ExtractBLS12LeavesLive.v]
    translates by the same [polish_func_adc (tr_func_sized 6 _)]. *)
Lemma bls12_tower_add_sub_are_leaves :
  List.find (fun f => String.eqb (fst f) "bls12_add") bls12_tower_funcs = Some bls12_add /\
  List.find (fun f => String.eqb (fst f) "bls12_sub") bls12_tower_funcs = Some bls12_sub.
Proof. split; reflexivity. Qed.

(** Every function's translated body is related to its bedrock2 body by
    [cmd_jasmin_equiv] ([Core.tr_cmd_correct]), before [polish_func]. *)
Lemma bls12_tower_tr_faithful :
  Forall (fun f : function_t =>
            let '(_, (_, _, body)) := f in
            cmd_jasmin_equiv body (jf_body (tr_func_sized 6 f)))
    bls12_tower_funcs.
Proof.
  apply Forall_forall. intros [name [[args rets] body]] _. cbn.
  apply tr_cmd_correct.
Qed.

(** The printer configuration of #20: the multiply, square and inverse (and
    from_word, opp) reached through [#randombytes], every word local of a
    called function [#[spill]], slices of pointer parameters staged.
    Positions in [rpc_scalar] are parameters that carry a word: the word of
    [bls12_from_word] and the condition of [bls12_select_znz]. *)
Definition bls12_tower_cfg : rp_config := {|
  rpc_n := 6;
  rpc_ffi := [("bls12_mul", 18%Z); ("bls12_square", 12%Z); ("bls12_inv", 13%Z);
              ("bls12_from_word", 7%Z); ("bls12_opp", 14%Z)];
  rpc_inline := ["bls12_add"; "bls12_sub"; "bls12_select_znz"; "bls12_felem_copy"];
  rpc_scalar := [("bls12_from_word", [1%nat]); ("bls12_select_znz", [1%nat])];
  rpc_skip := ["bls12_mul"; "bls12_square"; "bls12_inv"; "bls12_inv_pow_word";
               "bls12_from_word"; "bls12_to_mont"; "bls12_opp"];
  rpc_widths := [];
  rpc_export_all := true;
  rpc_exports := [];
  rpc_hints := false;
  rpc_budget := Bedrock.Jasmin.SpillLiveness.default_budget;
  rpc_cmov := false;
  rpc_direct := false |}.

Definition bls12_tower_jazz_regptr_pr20 : string :=
  pp_module_sized bls12_tower_cfg bls12_tower_jasmin.

(** The configurations of this module's emission.  [local_leaves]: the
    Montgomery multiply and square are printed from their fiat bodies (the
    [polish_func_adc] ASTs of the live-hint leaves) as local functions,
    called directly; otherwise they stay behind [#randombytes] (the crate's
    dispatcher sends them to CryptOpt or to the separately compiled live-hint
    leaves).  Both: liveness-chosen hints ([RegPtrSized.hint_choice]) and
    slices of pointer parameters passed without staging. *)
(** The register budget of the liveness-chosen hints of the Fp leaves (and of
    the call-free stretches of the other functions).  [SpillLiveness.default_budget]
    is 16; for the BLS12-381 multiply and square, measured on this machine
    (rdtsc, serial chain): budget 12: 125 cycles, 14: 124-127, 16: 115, 18: 111-112,
    20: 106, 21: 103-104, 22: register allocation fails. *)
Definition bls12_leaf_budget : nat := 21.

(** The [polish_func_adc] leaves at this budget: their hints erase to the
    hint-free module as for the default budget.  (The separately compiled
    leaves, [generated/bls12_leaves_live.jazz], the safe-Rust path's and the
    dispatcher's multiply and square, are the branch-free
    [ExtractBLS12LeavesLive.bls12_leaves_jasmin_ct] printed at
    [ExtractBLS12LeavesLive.bls12_leaf_ct_budget] by
    [scripts/EmitBLS12LeavesLive.v]; [bls12_leaves_ct_erases] there.) *)
Lemma bls12_leaves_live_budget_erases :
  String.concat (LF ++ LF)
    (List.map (fun f => SpillLiveness.render (SpillLiveness.erase
                 (SpillLiveness.emit (SpillLiveness.spill_choice bls12_leaf_budget f) f)))
              ExtractBLS12LeavesLive.bls12_leaves_jasmin_adc)
  = pp_module_nospill ExtractBLS12LeavesLive.bls12_leaves_jasmin_adc.
Proof. apply SpillLiveness.pp_module_live_erases. Qed.

(** The functions inlined: the Fp, Fp2, Fp6, Fp12 copies and the Fp select
    (a few registers each).  Fp add and sub are local functions: passed
    pointers instead of staging buffers, an inlined add needs its twelve limbs
    and three pointers in registers at once, which with the caller's live
    values exceeds the fifteen jasminc allocates. *)
Definition bls12_jfast_inline : list string :=
  ["bls12_select_znz"; "bls12_felem_copy"; "bls12_Fp2_felem_copy"; "bls12_Fp6_felem_copy";
   "bls12_Fp12_felem_copy"].

Definition bls12_tower_cfg_with (local_leaves : bool) : rp_config := {|
  rpc_n := 6;
  rpc_ffi := (if local_leaves then [] else [("bls12_mul", 18%Z); ("bls12_square", 12%Z)]) ++
             [("bls12_inv", 13%Z); ("bls12_from_word", 7%Z); ("bls12_opp", 14%Z)];
  rpc_inline := bls12_jfast_inline;
  rpc_scalar := [("bls12_from_word", [1%nat]); ("bls12_select_znz", [1%nat])];
  rpc_skip := (if local_leaves then [] else ["bls12_mul"; "bls12_square"]) ++
              ["bls12_inv"; "bls12_inv_pow_word"; "bls12_from_word"; "bls12_to_mont"; "bls12_opp"];
  rpc_widths := [];
  rpc_export_all := true;
  rpc_exports := [];
  rpc_hints := true;
  rpc_budget := bls12_leaf_budget;
  rpc_cmov := true;
  rpc_direct := true |}.

Definition bls12_tower_jazz_regptr : string :=
  pp_module_sized (bls12_tower_cfg_with true) bls12_tower_jasmin.

Definition bls12_tower_jazz_regptr_ffi : string :=
  pp_module_sized (bls12_tower_cfg_with false) bls12_tower_jasmin.
