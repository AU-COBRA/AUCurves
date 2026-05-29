(** * Extract the full BN254 tower to Jasmin, directly from Rocq.
 *
 * Companion to [ExtractSafeTower.v], which emits the same
 * [bn254_tower_funcs] list as safe Rust.  This file emits the very
 * same bedrock2 function list as a Jasmin module, via the verified
 * [tr_func_sized 4] / [polish_func] AST translation and the
 * [pp_module] / [pp_module_nospill] pretty-printers in
 * [Bedrock.Jasmin.Core].
 *
 * Task #222: extract the FULL BN254 tower (Fp2/Fp6/Fp12 arithmetic +
 * miller_loop + final_exp + pairing) to one Jasmin module so the whole
 * pairing becomes a single native verified-front artifact, removing
 * rustc/LLVM and the C shim from the trust base for the
 * tower-composition layer.  The Fp word-level leaves (add/sub/mul/
 * square/...) remain the separate [bn254_leaves.jazz] (#219); the
 * tower module here calls them by their extern symbol names.
 *
 * Faithfulness.  The bedrock2 [cmd] -> [jasmin_cmd] translation is the
 * Qed theorem [Core.tr_cmd_correct : forall c, cmd_jasmin_equiv c
 * (tr_cmd c)].  Since [bn254_tower_funcs] here is byte-for-byte the
 * same list that [ExtractSafeTower.v] feeds to the safe-Rust emitter,
 * the Jasmin tower and the Rust tower are two pretty-prints of one
 * verified bedrock2 program.  The [pp_module] vs [pp_module_nospill]
 * delta is purely the [#[spill]] register-class hint, proven inert by
 * the Qed lemmas [pp_locals_decls_nospill_drops_spill] /
 * [pp_locals_decls_spill_form].
 *
 * Representation note (#222 step 3).  The tower funcs are
 * composition-only: their bodies are [cmd.call]/[cmd.stackalloc]/
 * [cmd.set]/[cmd.store]/[cmd.cond]/[cmd.while] over Fp-pointer
 * arguments addressed by byte offsets (see [BN254_OptimizedOps.v] for
 * the same struct-passing convention compiling under [tr_func_sized
 * 4]).  No field-element multiply is inlined here, so the radix /
 * MULX representation concern is confined to the leaves; the tower
 * emit is representation-agnostic (it only moves and calls). *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Bedrock.Jasmin.Core.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** The tower function list, IDENTICAL to [ExtractSafeTower.v]'s
    [bn254_tower_funcs]: Fp2 base ops (copy/add/sub/mul/sqr) followed by
    the full pairing graph (Fp6/Fp12/Frobenius/make_line/pow_u/
    final_exp/miller_loop/pairing).  Fp2_inv is excluded (it needs the
    Fp leaf [bn254_inv], handled in the leaf layer). *)
Definition bn254_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr ].

Definition bn254_tower_funcs : list function_t :=
  Eval vm_compute in
    (bn254_fp2_funcs ++ BN254_Pairing.bn254_all_pairing_funcs).

(** BN254: Fp is 4 limbs of u64, so [field_size = 4].  Every tower
    function's pointer arguments are declared [reg ptr u64[4]] by
    [tr_func_sized 4]; struct-wider arguments (Fp2/Fp6/Fp12) are
    addressed by the byte offsets baked into the bedrock2 bodies, so
    the pointer-array size is a declaration detail, not a semantic one
    (identical convention to [BN254_OptimizedOps.bn254_opt_jasmin]). *)
Definition bn254_tower_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized 4 f)) bn254_tower_funcs.

(** Spill emit (default): every non-bool temp carries [#[spill]].
    Safe for the composition layer regardless of pressure. *)
Definition bn254_tower_jazz : string :=
  Eval vm_compute in pp_module bn254_tower_jasmin.

(** No-spill emit: temps declared plain [reg u64], leaving spilling to
    jasminc -auto-spill.  The tower funcs are call/add/sub/copy chains
    (no inlined schoolbook multiply), so register pressure stays within
    the 16 GPRs and forced spilling is pure overhead.  Per #219 the
    Montgomery [bn254_mul]/[bn254_square] LEAVES keep [#[spill]] (they
    provably exceed 16 GPRs) — but those leaves are NOT in this module;
    they live in [bn254_leaves.jazz]. *)
Definition bn254_tower_jazz_nospill : string :=
  Eval vm_compute in pp_module_nospill bn254_tower_jasmin.

Redirect "bn254_tower_rocq"         Eval vm_compute in bn254_tower_jazz.
Redirect "bn254_tower_nospill_rocq" Eval vm_compute in bn254_tower_jazz_nospill.
