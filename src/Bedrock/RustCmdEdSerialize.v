(** * RustCmdEdSerialize — rust_cmd_ed → neutral s-expression printer.
 *
 *  R1 of the AUCurves → CatCrypt-compiler retarget pilot (see
 *  [~/Claude/catcrypt-private/docs/retarget-aucurves-to-catcrypt-compiler.md]).
 *
 *  AUCurves can choose what to export: instead of routing a
 *  [rust_cmd_ed] body through its own jasmin backend, we export the
 *  body's *typed AST* in a neutral, prover-agnostic s-expression form.
 *  The CatCrypt (Lean) side then parses it back into its own [RustCmd]
 *  IR (R2) and emits through the owned x86 backend (R4).
 *
 *  This file MIRRORS the recursion of [RustCmdToC.v]'s [c_emit] /
 *  [c_sexpr] / [c_type_of], but the target is a neutral nested
 *  s-expression rather than C text.  Every [rust_cmd_ed] constructor,
 *  every [sexpr_ed] constructor, and every [tower_type_ed] constructor
 *  gets a head-tagged node so the Lean parser is a structural inverse.
 *
 *  Grammar (each node is `(TAG field ...)`, atoms are bare tokens):
 *    tower-type ::= Fp25519 | Fp25519_64 | FpL25519 | (Bytes n)
 *                 | U64 | (Arr n tower-type)
 *    located    ::= (loc "var" tower-type)
 *    sexpr      ::= (Var "x") | (Lit z) | (Add e e) | (Sub e e)
 *                 | (Mul e e) | (Shr e e) | (And e e) | (Lt e e)
 *                 | (Limb "v" i) | (Mul128 e e) | (Add128 e e)
 *    cmd        ::= (Skip) | (Seq c c) | (LetZero "v" t c)
 *                 | (LetU64 "v" e c) | (ScalarSet "v" e)
 *                 | (Call "f" located (located ...))
 *                 | (IfNz e c c) | (WhileNz e c)
 *                 | (ByteStore located e e) | (ByteLoad "v" located e)
 *                 | (For "v" n c) | (Select e located located located)
 *                 | (CallN "f" (located ...) (located ...))
 *                 | (CallFn "f" located (located ...))
 *                 | (Block c) | (SetBytes located (z ...))
 *                 | (ArrLoad located located e)
 *                 | (ArrStore located e located)
 *                 | (LimbStore located i e)
 *
 *  Strings are emitted double-quoted so the Lean parser can recover the
 *  variable / function names verbatim.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Numbers.DecimalString.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Plumbing                                                      *)
(* ================================================================ *)

Definition z_str (z : Z) : string :=
  DecimalString.NilZero.string_of_int (Z.to_int z).

Definition nat_str (n : nat) : string := z_str (Z.of_nat n).

Fixpoint join (sep : string) (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ join sep rest
  end.

(** Emit a string literal token: double-quoted.  Variable / function
    names in this AST contain no double quotes, so no escaping needed. *)
Definition q (s : string) : string := """" ++ s ++ """".

(* ================================================================ *)
(* §1. tower_type_ed serialization (mirror of c_type_of)             *)
(* ================================================================ *)

Fixpoint ser_tower_type (t : tower_type_ed) : string :=
  match t with
  | TFp25519     => "Fp25519"
  | TFp25519_64  => "Fp25519_64"
  | TFpL25519    => "FpL25519"
  | TBytes n     => "(Bytes " ++ nat_str n ++ ")"
  | TU64         => "U64"
  | TArr n t'    => "(Arr " ++ nat_str n ++ " " ++ ser_tower_type t' ++ ")"
  end.

(* ================================================================ *)
(* §2. sexpr_ed serialization (mirror of c_sexpr)                    *)
(* ================================================================ *)

Fixpoint ser_sexpr (e : sexpr_ed) : string :=
  match e with
  | SVar x      => "(Var " ++ q x ++ ")"
  | SLit z      => "(Lit " ++ z_str z ++ ")"
  | SAdd a b    => "(Add " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SSub a b    => "(Sub " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SMul a b    => "(Mul " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SShr a b    => "(Shr " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SAnd a b    => "(And " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SLt a b     => "(Lt " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SLimb v i   => "(Limb " ++ q v ++ " " ++ nat_str i ++ ")"
  | SMul128 a b => "(Mul128 " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  | SAdd128 a b => "(Add128 " ++ ser_sexpr a ++ " " ++ ser_sexpr b ++ ")"
  end.

(* ================================================================ *)
(* §3. located_ed serialization                                      *)
(* ================================================================ *)

Definition ser_located (l : located_ed) : string :=
  "(loc " ++ q l.(loc_var) ++ " " ++ ser_tower_type l.(loc_type) ++ ")".

Definition ser_located_list (ls : list located_ed) : string :=
  "(" ++ join " " (List.map ser_located ls) ++ ")".

Definition ser_z_list (zs : list Z) : string :=
  "(" ++ join " " (List.map z_str zs) ++ ")".

(* ================================================================ *)
(* §4. rust_cmd_ed serialization (mirror of c_emit)                  *)
(* ================================================================ *)

Fixpoint ser_cmd (c : rust_cmd_ed) : string :=
  match c with
  | REdSkip => "(Skip)"
  | REdSeq c1 c2 =>
      "(Seq " ++ ser_cmd c1 ++ " " ++ ser_cmd c2 ++ ")"
  | REdLetZero v t body =>
      "(LetZero " ++ q v ++ " " ++ ser_tower_type t ++ " " ++ ser_cmd body ++ ")"
  | REdLetU64 v e body =>
      "(LetU64 " ++ q v ++ " " ++ ser_sexpr e ++ " " ++ ser_cmd body ++ ")"
  | REdScalarSet v e =>
      "(ScalarSet " ++ q v ++ " " ++ ser_sexpr e ++ ")"
  | REdCall fname dest args =>
      "(Call " ++ q fname ++ " " ++ ser_located dest ++ " "
        ++ ser_located_list args ++ ")"
  | REdIfNz e ct cf =>
      "(IfNz " ++ ser_sexpr e ++ " " ++ ser_cmd ct ++ " " ++ ser_cmd cf ++ ")"
  | REdWhileNz e body =>
      "(WhileNz " ++ ser_sexpr e ++ " " ++ ser_cmd body ++ ")"
  | REdByteStore loc idx val =>
      "(ByteStore " ++ ser_located loc ++ " " ++ ser_sexpr idx ++ " "
        ++ ser_sexpr val ++ ")"
  | REdByteLoad v loc idx =>
      "(ByteLoad " ++ q v ++ " " ++ ser_located loc ++ " " ++ ser_sexpr idx ++ ")"
  | REdFor v n body =>
      "(For " ++ q v ++ " " ++ nat_str n ++ " " ++ ser_cmd body ++ ")"
  | REdSelect cond if_t if_f dest =>
      "(Select " ++ ser_sexpr cond ++ " " ++ ser_located if_t ++ " "
        ++ ser_located if_f ++ " " ++ ser_located dest ++ ")"
  | REdCallN fname dests args =>
      "(CallN " ++ q fname ++ " " ++ ser_located_list dests ++ " "
        ++ ser_located_list args ++ ")"
  | REdCallFn fname dest args =>
      "(CallFn " ++ q fname ++ " " ++ ser_located dest ++ " "
        ++ ser_located_list args ++ ")"
  | REdBlock body =>
      "(Block " ++ ser_cmd body ++ ")"
  | REdSetBytes loc bytes =>
      "(SetBytes " ++ ser_located loc ++ " " ++ ser_z_list bytes ++ ")"
  | REdArrLoad dst src idx_e =>
      "(ArrLoad " ++ ser_located dst ++ " " ++ ser_located src ++ " "
        ++ ser_sexpr idx_e ++ ")"
  | REdArrStore arr idx_e src =>
      "(ArrStore " ++ ser_located arr ++ " " ++ ser_sexpr idx_e ++ " "
        ++ ser_located src ++ ")"
  | REdLimbStore loc i e =>
      "(LimbStore " ++ ser_located loc ++ " " ++ nat_str i ++ " "
        ++ ser_sexpr e ++ ")"
  end.

(* ================================================================ *)
(* §5. Pilot routine: fe25519_xyzt_copy body                          *)
(* ================================================================ *)

(** The pilot is the SMALLEST closed [rust_cmd_ed] available: a single
    [REdCall].  [xyzt_copy_body] (in [XyztCopyBody.v]) is

      fun dest args => match args with
        | [src] => REdCall "fe25519_xyzt_copy" dest [src]
        | _     => REdSkip end

    Instantiated at concrete [dest]/[src] [located_ed]s (matching the
    instantiation in [ExtractXyztCopyJasmin.v], whose jasmin export is
    the R4 KAT reference). *)
Definition xyzt_copy_pilot : rust_cmd_ed :=
  xyzt_copy_body
    {| loc_var := "dest"; loc_type := TBytes 200 |}
    [{| loc_var := "src"; loc_type := TBytes 200 |}].

(** Confirm the concrete normal form (sanity: it is a single Call). *)
Example xyzt_copy_pilot_value :
  xyzt_copy_pilot
    = REdCall "fe25519_xyzt_copy"
        {| loc_var := "dest"; loc_type := TBytes 200 |}
        [{| loc_var := "src"; loc_type := TBytes 200 |}].
Proof. reflexivity. Qed.

Definition xyzt_copy_sexpr : string :=
  Eval vm_compute in ser_cmd xyzt_copy_pilot.

(** Inspect via [Print xyzt_copy_sexpr] or [Eval vm_compute in
    ser_cmd xyzt_copy_pilot] in an interactive session; the resulting
    string is committed verbatim to
    [bench/retarget_aucurves/xyzt_copy.sexpr] for the Lean importer (R2). *)

(** **R1 certified artifact**: the exported s-expression for the pilot is
    exactly the string committed to [bench/retarget_aucurves/xyzt_copy.sexpr]
    in the CatCrypt repo.  This [Qed] pins the byte-exact serialization, so
    the Lean importer (R2) and the cross-check (R3/R4) consume a value that
    AUCurves itself has certified. *)
Example xyzt_copy_sexpr_value :
  ser_cmd xyzt_copy_pilot
    = "(Call ""fe25519_xyzt_copy"" (loc ""dest"" (Bytes 200)) ((loc ""src"" (Bytes 200))))".
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §6. Serializer sanity smoke test (exercises more constructors)    *)
(* ================================================================ *)

(** A demo body touching Seq / LetZero / Call / LimbStore / sexpr ops,
    so the serializer's coverage is visible at a glance. *)
Definition demo_rs : rust_cmd_ed :=
  REdLetZero "h" (TBytes 64) (
  REdSeq
    (REdCall "sha512_64"
      {| loc_var := "h"; loc_type := TBytes 64 |}
      [{| loc_var := "msg"; loc_type := TBytes 32 |}])
    (REdLimbStore {| loc_var := "acc"; loc_type := TFp25519 |} 0%nat
       (SAdd (SLimb "a" 0%nat) (SLimb "b" 0%nat)))).

Definition demo_sexpr : string := Eval vm_compute in ser_cmd demo_rs.
