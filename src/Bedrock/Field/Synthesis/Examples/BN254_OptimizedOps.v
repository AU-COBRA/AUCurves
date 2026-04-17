(** * BN254 optimized pairing ops for Jasmin/CryptOpt extraction. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.

Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation ft := (string * (list string * list string * cmd.cmd))%type.

Notation FP2 := 64. Notation FP6 := 192.

Definition off (b: expr.expr) (n: Z) := expr.op bopname.add b (expr.literal n).
Definition cp (i j: Z) (x: expr.expr) := off x (i * FP6 + j * FP2).

Fixpoint seql (cs: list cmd.cmd) : cmd.cmd :=
  match cs with [] => cmd.skip | [c] => c | c :: r => cmd.seq c (seql r) end.

Definition m2 := "bn254_Fp2_mul".
Definition s2 := "bn254_Fp2_square".
Definition a2 := "bn254_Fp2_add".
Definition u2 := "bn254_Fp2_sub".
Definition x2 := "bn254_Fp2_mul_xi".

Definition bn254_fp12_mul_line : ft :=
  ("bn254_fp12_mul_line",
   (["out"; "f"; "l00"; "l01"; "l10"], [],
    cmd.stackalloc "t0" FP2
   (cmd.stackalloc "t1" FP2
   (cmd.stackalloc "t2" FP2
   (cmd.stackalloc "t3" FP2
   (cmd.stackalloc "t4" FP2
   (seql [
     cmd.call [] m2 [expr.var "t0"; (cp 0 0 (expr.var "f")); expr.var "l00"];
     cmd.call [] m2 [expr.var "t1"; (cp 0 1 (expr.var "f")); expr.var "l01"];
     cmd.call [] a2 [expr.var "t3"; (cp 0 1 (expr.var "f")); (cp 0 2 (expr.var "f"))];
     cmd.call [] m2 [expr.var "t3"; expr.var "t3"; expr.var "l01"];
     cmd.call [] u2 [expr.var "t3"; expr.var "t3"; expr.var "t1"];
     cmd.call [] x2 [expr.var "t3"; expr.var "t3"];
     cmd.call [] a2 [(cp 0 0 (expr.var "out")); expr.var "t0"; expr.var "t3"];
     cmd.call [] a2 [expr.var "t3"; (cp 0 0 (expr.var "f")); (cp 0 1 (expr.var "f"))];
     cmd.call [] a2 [expr.var "t4"; expr.var "l00"; expr.var "l01"];
     cmd.call [] m2 [expr.var "t3"; expr.var "t3"; expr.var "t4"];
     cmd.call [] u2 [expr.var "t3"; expr.var "t3"; expr.var "t0"];
     cmd.call [] u2 [expr.var "t3"; expr.var "t3"; expr.var "t1"];
     cmd.call [] m2 [expr.var "t4"; (cp 1 1 (expr.var "f")); expr.var "l10"];
     cmd.call [] x2 [expr.var "t4"; expr.var "t4"];
     cmd.call [] a2 [(cp 0 1 (expr.var "out")); expr.var "t3"; expr.var "t4"];
     cmd.call [] a2 [expr.var "t3"; (cp 0 0 (expr.var "f")); (cp 0 2 (expr.var "f"))];
     cmd.call [] m2 [expr.var "t3"; expr.var "t3"; expr.var "l00"];
     cmd.call [] u2 [expr.var "t3"; expr.var "t3"; expr.var "t0"];
     cmd.call [] a2 [expr.var "t3"; expr.var "t3"; expr.var "t1"];
     cmd.call [] m2 [expr.var "t4"; (cp 1 2 (expr.var "f")); expr.var "l10"];
     cmd.call [] x2 [expr.var "t4"; expr.var "t4"];
     cmd.call [] a2 [(cp 0 2 (expr.var "out")); expr.var "t3"; expr.var "t4"];
     cmd.call [] m2 [expr.var "t0"; (cp 1 0 (expr.var "f")); expr.var "l00"];
     cmd.call [] m2 [expr.var "t3"; (cp 1 2 (expr.var "f")); expr.var "l10"];
     cmd.call [] x2 [expr.var "t3"; expr.var "t3"];
     cmd.call [] a2 [expr.var "t3"; expr.var "t3"; expr.var "t0"];
     cmd.call [] m2 [expr.var "t4"; (cp 0 2 (expr.var "f")); expr.var "l10"];
     cmd.call [] x2 [expr.var "t4"; expr.var "t4"];
     cmd.call [] a2 [(cp 1 0 (expr.var "out")); expr.var "t3"; expr.var "t4"];
     cmd.call [] m2 [expr.var "t3"; (cp 1 0 (expr.var "f")); expr.var "l01"];
     cmd.call [] m2 [expr.var "t4"; (cp 1 1 (expr.var "f")); expr.var "l00"];
     cmd.call [] a2 [expr.var "t3"; expr.var "t3"; expr.var "t4"];
     cmd.call [] m2 [expr.var "t4"; (cp 0 0 (expr.var "f")); expr.var "l10"];
     cmd.call [] a2 [(cp 1 1 (expr.var "out")); expr.var "t3"; expr.var "t4"];
     cmd.call [] m2 [expr.var "t3"; (cp 1 1 (expr.var "f")); expr.var "l01"];
     cmd.call [] m2 [expr.var "t4"; (cp 1 2 (expr.var "f")); expr.var "l00"];
     cmd.call [] a2 [expr.var "t3"; expr.var "t3"; expr.var "t4"];
     cmd.call [] m2 [expr.var "t4"; (cp 0 1 (expr.var "f")); expr.var "l10"];
     cmd.call [] a2 [(cp 1 2 (expr.var "out")); expr.var "t3"; expr.var "t4"]
   ]))))))).

Definition bn254_fp12_cyc_sqr : ft :=
  ("bn254_fp12_cyc_sqr",
   (["out"; "x"], [],
    cmd.stackalloc "A0" FP2 (cmd.stackalloc "A1" FP2
   (cmd.stackalloc "A2" FP2 (cmd.stackalloc "B0" FP2
   (cmd.stackalloc "B1" FP2 (cmd.stackalloc "B2" FP2
   (cmd.stackalloc "t" FP2
   (seql [
     cmd.call [] s2 [expr.var "A0"; (cp 0 0 (expr.var "x"))];
     cmd.call [] s2 [expr.var "A1"; (cp 0 1 (expr.var "x"))];
     cmd.call [] s2 [expr.var "A2"; (cp 0 2 (expr.var "x"))];
     cmd.call [] s2 [expr.var "B0"; (cp 1 0 (expr.var "x"))];
     cmd.call [] s2 [expr.var "B1"; (cp 1 1 (expr.var "x"))];
     cmd.call [] s2 [expr.var "B2"; (cp 1 2 (expr.var "x"))];
     cmd.call [] a2 [expr.var "t"; expr.var "A0"; expr.var "A0"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "A0"];
     cmd.call [] u2 [expr.var "t"; expr.var "t"; (cp 0 0 (expr.var "x"))];
     cmd.call [] u2 [(cp 0 0 (expr.var "out")); expr.var "t"; (cp 0 0 (expr.var "x"))];
     cmd.call [] x2 [expr.var "t"; expr.var "B2"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "t"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "B2"];
     cmd.call [] x2 [expr.var "t"; expr.var "t"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; (cp 0 1 (expr.var "x"))];
     cmd.call [] a2 [(cp 0 1 (expr.var "out")); expr.var "t"; (cp 0 1 (expr.var "x"))];
     cmd.call [] a2 [expr.var "t"; expr.var "A1"; expr.var "A1"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "A1"];
     cmd.call [] u2 [expr.var "t"; expr.var "t"; (cp 0 2 (expr.var "x"))];
     cmd.call [] u2 [(cp 0 2 (expr.var "out")); expr.var "t"; (cp 0 2 (expr.var "x"))];
     cmd.call [] a2 [expr.var "t"; expr.var "B0"; expr.var "B0"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "B0"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; (cp 1 0 (expr.var "x"))];
     cmd.call [] a2 [(cp 1 0 (expr.var "out")); expr.var "t"; (cp 1 0 (expr.var "x"))];
     cmd.call [] a2 [expr.var "t"; expr.var "A2"; expr.var "A2"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "A2"];
     cmd.call [] u2 [expr.var "t"; expr.var "t"; (cp 1 1 (expr.var "x"))];
     cmd.call [] u2 [(cp 1 1 (expr.var "out")); expr.var "t"; (cp 1 1 (expr.var "x"))];
     cmd.call [] a2 [expr.var "t"; expr.var "B1"; expr.var "B1"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; expr.var "B1"];
     cmd.call [] a2 [expr.var "t"; expr.var "t"; (cp 1 2 (expr.var "x"))];
     cmd.call [] a2 [(cp 1 2 (expr.var "out")); expr.var "t"; (cp 1 2 (expr.var "x"))]
   ]))))))))).

Require Import Crypto.Bedrock.Jasmin.Core.

Definition bn254_opt_funcs : list ft :=
  [ bn254_fp12_mul_line; bn254_fp12_cyc_sqr ].

Definition bn254_opt_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized 4 f)) bn254_opt_funcs.

From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".
Extraction "bn254_opt_jasmin_extracted"
  bn254_opt_jasmin pp_func pp_module.
