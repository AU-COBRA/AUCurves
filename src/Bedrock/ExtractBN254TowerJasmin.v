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
(** #227: [Fp2_opp] negates both Fp2 components via the [bn254_opp]
    leaf.  Copied verbatim from [ExtractSafeRust.Fp2_opp] (same bedrock2
    body the Rust tower's hand-written [bn254_Fp2_opp] prelude denotes),
    so the jasmin tower can emit it as a first-class function instead of
    relying on an out-of-band prelude.  Offset 32 = 4 limbs * 8 bytes =
    one BN254 felem. *)
Definition Fp2_opp : function_t :=
  ("bn254_Fp2_opp", (["out"; "x"], []:list String.string,
    (Syntax.cmd.seq
      (Syntax.cmd.call [] "bn254_opp"
        [Syntax.expr.var "out"; Syntax.expr.var "x"])
      (Syntax.cmd.call [] "bn254_opp"
        [Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "out") (Syntax.expr.literal 32%Z);
         Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "x") (Syntax.expr.literal 32%Z)])))).

(** #227: [Fp2_opp] and [Fp2_inv] are called by the higher tower
    (Fp6_opp, Fp12_inv, final_exp).  #222 left them as a hand-written
    Rust prelude (so the jasmin tower omitted them and could never
    link).  Including them as emitted jasmin functions is required to
    compile the FULL tower. *)
Definition bn254_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr; Fp2_opp; Fp2_inv ].

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

(** Reg-ptr emit (#227): close the 39-function jasminc gap.

    [pp_module_regptr] re-renders the SAME [bn254_tower_jasmin] AST
    under the [reg ptr u64[N]] calling convention — typed array
    references instead of raw [reg u64] byte pointers, sub-felem slices
    [base[k:len]] instead of byte arithmetic [(base + 8*k)], and the
    returned-pointer threading [dst = f(dst, ...)].  Every pointer in
    the call graph (tower parameters, stackalloc temporaries, and the
    leaf signatures the tower calls) agrees on the convention via a
    single inferred width environment, so jasminc no longer rejects
    "can not implicitly cast u64[4] into u64": a [stack u64[4]]
    temporary / a [u64[len]] sub-slice now passes to a matching
    [reg ptr u64[len]] parameter.

    Faithfulness: no AST transform happens — [pp_cmd_regptr] consumes
    the identical [jf_body] that [pp_cmd] consumes, and the byte-offset
    / word-index correspondence is exact (offsets in tower bodies are
    multiples of 8; call-argument offsets are multiples of the 32-byte
    felem width).  The reg-ptr emit and the baseline emit therefore
    denote the same bedrock2 program via [tr_cmd_correct]
    ([pp_module_regptr_same_body] records that the command stream is
    unchanged; the delta is the typed-array-slice vs pointer-arithmetic
    Jasmin access syntax, analogous to the inert [#[spill]] delta of
    [pp_module_nospill]). *)
Definition bn254_tower_jazz_regptr : string :=
  Eval vm_compute in
    (Core.pp_regptr_leaf_stubs ++ Core.LF ++ Core.LF ++
     pp_module_regptr bn254_tower_jasmin).

Redirect "bn254_tower_rocq"         Eval vm_compute in bn254_tower_jazz.
Redirect "bn254_tower_nospill_rocq" Eval vm_compute in bn254_tower_jazz_nospill.
Redirect "bn254_tower_regptr_rocq"  Eval vm_compute in bn254_tower_jazz_regptr.
