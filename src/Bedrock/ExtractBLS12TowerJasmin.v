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
    [Core.polish_func], the path of the BN254 tower; [tr_cmd_correct] is the
    faithfulness theorem of the first step, and [bls12_tower_tr_faithful]
    instantiates it for every function of the list.  The module is printed by
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
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.RegPtrSized.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls12_tower_funcs : list function_t :=
  bls12_pairing_funcs ++ bls12_extra_funcs.

(** The list is the environment of the functional pairing theorem. *)
Lemma bls12_tower_funcs_eq :
  bls12_tower_funcs = bls12_pairing_funcs ++ bls12_extra_funcs.
Proof. reflexivity. Qed.

Definition bls12_tower_jasmin : list jasmin_func :=
  List.map (fun f => polish_func (tr_func_sized 6 f)) bls12_tower_funcs.

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

(** The printer configuration.  Positions in [rpc_scalar] are parameters that
    carry a word: the word of [bls12_from_word] and the condition of
    [bls12_select_znz]. *)
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
  rpc_exports := [] |}.

Definition bls12_tower_jazz_regptr : string :=
  pp_module_sized bls12_tower_cfg bls12_tower_jasmin.
