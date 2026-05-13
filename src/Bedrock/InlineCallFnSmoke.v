(** * InlineCallFn smoke test
 *
 * Demonstrates that [inline_callfn_one] eliminates [REdCallFn] callsites
 * on a small 3-call chain.  Verifies via [Eval vm_compute] and Qed-checked
 * equalities that the resulting command is [callfn_free].
 *
 * NOT wired into any extraction yet — this is the IR-level proof of
 * concept for the whole-protocol Jasmin emission path
 * (docs/whole-protocol-jasmin-plan.md Blocker 2).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.InlineCallFn.

Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. A toy 3-function table                                        *)
(* ================================================================ *)

(** Tiny located_ed helpers. *)
Definition Lfp (s : String.string) : located_ed :=
  {| loc_var := s; loc_type := TFp25519_64 |}.

(** [neg x]: tiny body that calls an external [fe25519_neg] (an
    [REdCall] leaf).  This is the leaf level — once inlined this stays
    as an [REdCall]. *)
Definition neg_body (dst : located_ed) (args : list located_ed) : rust_cmd_ed :=
  REdCall "fe25519_neg" dst args.

(** [double x]: calls [neg] twice via [REdCallFn].  After ONE pass of
    [inline_callfn_one], the [REdCallFn "neg"] sites become
    [REdCall "fe25519_neg"]. *)
Definition double_body (dst : located_ed) (args : list located_ed) : rust_cmd_ed :=
  REdSeq (REdCallFn "neg" dst args)
         (REdCallFn "neg" dst args).

(** [quad x]: calls [double] via [REdCallFn].  Needs TWO passes of
    [inline_callfn_one] to become call-free. *)
Definition quad_body (dst : located_ed) (args : list located_ed) : rust_cmd_ed :=
  REdSeq (REdCallFn "double" dst args)
         (REdCallFn "double" dst args).

Definition toy_ftab : function_table_ed :=
  [ ("neg",    neg_body) ;
    ("double", double_body) ;
    ("quad",   quad_body) ].

(* ================================================================ *)
(* §2. The protocol body: a 3-call chain calling quad                *)
(* ================================================================ *)

Definition toy_main : rust_cmd_ed :=
  REdCallFn "quad" (Lfp "y") [Lfp "x"].

(* ================================================================ *)
(* §3. Inlining results                                              *)
(* ================================================================ *)

(** One pass: [REdCallFn "quad"] becomes the body of [quad_body],
    which still contains [REdCallFn "double"] sites. *)
Definition toy_after_1 : rust_cmd_ed :=
  inline_callfn_one toy_ftab toy_main.

(** Two passes: [REdCallFn "double"] sites become [double_body], which
    still contains [REdCallFn "neg"] sites. *)
Definition toy_after_2 : rust_cmd_ed :=
  inline_callfn_n 2 toy_ftab toy_main.

(** Three passes: all [REdCallFn] sites are gone, only [REdCall]s remain. *)
Definition toy_after_3 : rust_cmd_ed :=
  inline_callfn_n 3 toy_ftab toy_main.

(* ================================================================ *)
(* §4. Smoke checks                                                  *)
(* ================================================================ *)

(** After 3 passes, the result is [callfn_free]. *)
Lemma toy_after_3_callfn_free : callfn_free toy_after_3 = true.
Proof. vm_compute. reflexivity. Qed.

(** After 1 or 2 passes, [REdCallFn] sites remain. *)
Lemma toy_after_1_not_callfn_free : callfn_free toy_after_1 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_after_2_not_callfn_free : callfn_free toy_after_2 = false.
Proof. vm_compute. reflexivity. Qed.

(** The fully inlined toy_main expands to 4 [REdCall "fe25519_neg"]
    invocations (quad → 2 doubles → 4 negs).  This shows the inliner
    structurally unfolds the callgraph. *)
Definition expected_after_3 : rust_cmd_ed :=
  REdSeq (REdSeq (REdCall "fe25519_neg" (Lfp "y") [Lfp "x"])
                 (REdCall "fe25519_neg" (Lfp "y") [Lfp "x"]))
         (REdSeq (REdCall "fe25519_neg" (Lfp "y") [Lfp "x"])
                 (REdCall "fe25519_neg" (Lfp "y") [Lfp "x"])).

Lemma toy_after_3_eq : toy_after_3 = expected_after_3.
Proof. vm_compute. reflexivity. Qed.
