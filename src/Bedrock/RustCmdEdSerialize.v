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
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
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

(* ================================================================ *)
(* §7. R5 — real field-op body export (fe25519_add) + runtime-valued *)
(*     limb store, for the CatCrypt RLimbStoreExpr round-trip.        *)
(* ================================================================ *)

(** [fe25519_add_body] (End2End/Ed25519/Fe25519AddSubBody.v) is the
    inline 5-limb radix-2^51 add chain: five [REdLimbStore dest i
    (SAdd (SLimb a i) (SLimb b i))] writes.  Each stored value is a
    *runtime* [sexpr_ed], so this body has no image under CatCrypt's
    old [RLimbStore] (literal-only) — it is exactly the body the R-pilot
    flagged as blocked.  Instantiated at concrete [dest]/[a]/[b] slots. *)
Definition fe25519_add_pilot : rust_cmd_ed :=
  fe25519_add_body
    {| loc_var := "dest"; loc_type := TFp25519 |}
    [ {| loc_var := "a"; loc_type := TFp25519 |}
    ; {| loc_var := "b"; loc_type := TFp25519 |} ].

(** **R5 certified artifact** — the exported s-expression for the real
    [fe25519_add] inline body.  Pins the byte-exact serialization (Qed),
    mirroring [xyzt_copy_sexpr_value].  Each stored value is a runtime
    [(Add (Limb …) (Limb …))] — the runtime-valued limb store that
    [RLimbStoreExpr] now carries on the CatCrypt side. *)
Example fe25519_add_sexpr_value :
  ser_cmd fe25519_add_pilot
    = "(Seq (LimbStore (loc ""dest"" Fp25519) 0 (Add (Limb ""a"" 0) (Limb ""b"" 0))) (Seq (LimbStore (loc ""dest"" Fp25519) 1 (Add (Limb ""a"" 1) (Limb ""b"" 1))) (Seq (LimbStore (loc ""dest"" Fp25519) 2 (Add (Limb ""a"" 2) (Limb ""b"" 2))) (Seq (LimbStore (loc ""dest"" Fp25519) 3 (Add (Limb ""a"" 3) (Limb ""b"" 3))) (LimbStore (loc ""dest"" Fp25519) 4 (Add (Limb ""a"" 4) (Limb ""b"" 4)))))))".
Proof. vm_compute. reflexivity. Qed.

(** A single runtime-valued limb store whose value lies in the
    *scalar* [sexpr_ed] fragment ([SAdd (SVar _) (SVar _)], no [SLimb]).
    This is the node CatCrypt's importer round-trips end-to-end into
    [RLimbStoreExpr] (its [SExpr] is scalar-only, so the [SLimb]-valued
    [fe25519_add] body above awaits the [SExpr]-over-tower extension —
    the R6 obstacle).  Pinned here so the Lean [importedLimbStoreExpr_eq]
    consumes an AUCurves-certified string. *)
Definition limb_store_expr_demo : rust_cmd_ed :=
  REdLimbStore {| loc_var := "dest"; loc_type := TFp25519 |} 0%nat
    (SAdd (SVar "ai0") (SVar "bi0")).

Example limb_store_expr_demo_sexpr_value :
  ser_cmd limb_store_expr_demo
    = "(LimbStore (loc ""dest"" Fp25519) 0 (Add (Var ""ai0"") (Var ""bi0"")))".
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §8. CONN-3j — BN254/BLS Fp2 tower op bodies as rust_cmd_ed.        *)
(*     Brings the pairing-tower Fp2 add / Fp2 mul op BODIES through   *)
(*     the same neutral-s-expression round-trip the field ops use.    *)
(* ================================================================ *)

(** The BN254 Fp2 tower ops are bedrock2 [cmd] trees
    (Field/Synthesis/Examples/bn254_Fp2.v): each Fp2 op is a sequence
    of [cmd.call]s to the Fp LEAF functions ([bn254_add], [bn254_mul],
    [bn254_sub]), one per Fp2 component, with the imaginary component
    addressed by [expr_2nd_felem] (= base pointer + 32 bytes, one BN254
    Fp felem = 4 limbs * 8 bytes).

    At the [rust_cmd_ed] level this is naturally an [REdSeq] of
    [REdCall]s over flat [located_ed] slots — the same [REdCall]-per-leaf
    shape the [fe25519_xyzt_copy] pilot uses, lifted to the two-component
    Fp2 layer.  Each Fp2 component is a [TBytes 32] slot (one BN254 Fp
    felem); distinct slot names (`out_re`/`out_im`, etc.) name the real
    and imaginary halves that the bedrock2 body reaches by byte offset.
    The leaf names (`bn254_add`/`bn254_mul`/`bn254_sub`) are recovered
    verbatim, so the CatCrypt importer maps them onto the same Fp leaf
    call graph AUCurves' own jasmin tower calls. *)

Notation Fp_loc v := {| loc_var := v; loc_type := TBytes 32 |}.

(** Fp2 ADD: [out = inx + iny] over Fp2 = two component-wise Fp adds.
    Mirrors [bn254_Fp2.Fp2_add]'s two [cmd.call (AbstractField.add)]:
      out.re = inx.re + iny.re ;  out.im = inx.im + iny.im.            *)
Definition bn254_fp2_add_rs : rust_cmd_ed :=
  REdSeq
    (REdCall "bn254_add" (Fp_loc "out_re") [Fp_loc "inx_re"; Fp_loc "iny_re"])
    (REdCall "bn254_add" (Fp_loc "out_im") [Fp_loc "inx_im"; Fp_loc "iny_im"]).

(** **CONN-3j certified artifact** — Fp2 add body serialization (Qed). *)
Example bn254_fp2_add_sexpr_value :
  ser_cmd bn254_fp2_add_rs
    = "(Seq (Call ""bn254_add"" (loc ""out_re"" (Bytes 32)) ((loc ""inx_re"" (Bytes 32)) (loc ""iny_re"" (Bytes 32)))) (Call ""bn254_add"" (loc ""out_im"" (Bytes 32)) ((loc ""inx_im"" (Bytes 32)) (loc ""iny_im"" (Bytes 32)))))".
Proof. vm_compute. reflexivity. Qed.

(** Fp2 MUL (Karatsuba): [(a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u].
    Mirrors [bn254_Fp2.Fp2_mul]'s 8-call chain over three scratch Fp
    felems [v0]/[v1]/[v2] (allocated via [REdLetZero … (TBytes 32)],
    the [rust_cmd_ed] image of bedrock2 [stackalloc 32]).  Component
    slots: [inx_re]/[inx_im] = a/b, [iny_re]/[iny_im] = c/d,
    [out_re]/[out_im] the result halves.  Call order is byte-identical
    to the bedrock2 body:
      v0=a*c ; v1=b*d ; v2=a+b ; out.im=c+d ; out.im=(a+b)(c+d) ;
      out.im-=v0 ; out.im-=v1 ; out.re=v0-v1.                          *)
Definition bn254_fp2_mul_rs : rust_cmd_ed :=
  REdLetZero "v0" (TBytes 32) (
  REdLetZero "v1" (TBytes 32) (
  REdLetZero "v2" (TBytes 32) (
  REdSeq (REdCall "bn254_mul" (Fp_loc "v0")     [Fp_loc "inx_re"; Fp_loc "iny_re"]) (
  REdSeq (REdCall "bn254_mul" (Fp_loc "v1")     [Fp_loc "inx_im"; Fp_loc "iny_im"]) (
  REdSeq (REdCall "bn254_add" (Fp_loc "v2")     [Fp_loc "inx_re"; Fp_loc "inx_im"]) (
  REdSeq (REdCall "bn254_add" (Fp_loc "out_im") [Fp_loc "iny_re"; Fp_loc "iny_im"]) (
  REdSeq (REdCall "bn254_mul" (Fp_loc "out_im") [Fp_loc "out_im"; Fp_loc "v2"]) (
  REdSeq (REdCall "bn254_sub" (Fp_loc "out_im") [Fp_loc "out_im"; Fp_loc "v0"]) (
  REdSeq (REdCall "bn254_sub" (Fp_loc "out_im") [Fp_loc "out_im"; Fp_loc "v1"]) (
         (REdCall "bn254_sub" (Fp_loc "out_re") [Fp_loc "v0"; Fp_loc "v1"])
  )))))))))).

(** **CONN-3j certified artifact** — Fp2 mul body serialization (Qed). *)
Example bn254_fp2_mul_sexpr_value :
  ser_cmd bn254_fp2_mul_rs
    = "(LetZero ""v0"" (Bytes 32) (LetZero ""v1"" (Bytes 32) (LetZero ""v2"" (Bytes 32) (Seq (Call ""bn254_mul"" (loc ""v0"" (Bytes 32)) ((loc ""inx_re"" (Bytes 32)) (loc ""iny_re"" (Bytes 32)))) (Seq (Call ""bn254_mul"" (loc ""v1"" (Bytes 32)) ((loc ""inx_im"" (Bytes 32)) (loc ""iny_im"" (Bytes 32)))) (Seq (Call ""bn254_add"" (loc ""v2"" (Bytes 32)) ((loc ""inx_re"" (Bytes 32)) (loc ""inx_im"" (Bytes 32)))) (Seq (Call ""bn254_add"" (loc ""out_im"" (Bytes 32)) ((loc ""iny_re"" (Bytes 32)) (loc ""iny_im"" (Bytes 32)))) (Seq (Call ""bn254_mul"" (loc ""out_im"" (Bytes 32)) ((loc ""out_im"" (Bytes 32)) (loc ""v2"" (Bytes 32)))) (Seq (Call ""bn254_sub"" (loc ""out_im"" (Bytes 32)) ((loc ""out_im"" (Bytes 32)) (loc ""v0"" (Bytes 32)))) (Seq (Call ""bn254_sub"" (loc ""out_im"" (Bytes 32)) ((loc ""out_im"" (Bytes 32)) (loc ""v1"" (Bytes 32)))) (Call ""bn254_sub"" (loc ""out_re"" (Bytes 32)) ((loc ""v0"" (Bytes 32)) (loc ""v1"" (Bytes 32))))))))))))))".
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §9. CONN-3j — BN254/BLS Fp6 + Fp12 (GT) tower op bodies.          *)
(*     Scales the pairing-tower round-trip from the Fp2 layer (§8)   *)
(*     up to the cubic (Fp6) and dodecic (Fp12 = GT) layers, which   *)
(*     is the full pairing-tower arithmetic the KZG/Halo2 (#349, T3) *)
(*     pairing check needs.                                          *)
(* ================================================================ *)

(** The Fp6 tower ops are bedrock2 [cmd] trees built ON TOP of the Fp2
    LEAF functions — exactly the compositional pattern the Fp2 ops use
    over the Fp LEAF functions.  An Fp6 element is three Fp2 components
    (c0/c1/c2); each Fp6 op is a sequence of [cmd.call]s to the Fp2 leaf
    functions ([bn254_Fp2_add], [bn254_Fp2_mul], [bn254_Fp2_sub],
    [bn254_Fp2_mul_xi]), one or more per Fp6 component.

    Call schedules mirror AUCurves' own cubic-extension bodies
    (Field/FieldExtensions/CubicFieldExtensions.v's [Fp6_add] / [Fp6_mul]).
    Each Fp2 component is a [TBytes 64] slot (one BN254 Fp2 felem =
    2 Fp felems * 32 bytes); component slot names (`out_c0`/`out_c1`/
    `out_c2`, etc.) name the three cubic-tower coordinates the bedrock2
    body reaches by byte offset (c_i at base + i*64).  The Fp2 leaf names
    are recovered verbatim so the CatCrypt importer maps them onto the
    same Fp2 leaf call graph AUCurves' jasmin tower calls. *)

Notation Fp2_loc v := {| loc_var := v; loc_type := TBytes 64 |}.

(** Fp6 ADD: [out = inx + iny] over Fp6 = three component-wise Fp2 adds.
    Mirrors [CubicFieldExtensions.Fp6_add]'s three [cmd.call (add (F:=Fp2))]:
      out.c0 = inx.c0 + iny.c0 ;  out.c1 = … ;  out.c2 = … .             *)
Definition bn254_fp6_add_rs : rust_cmd_ed :=
  REdSeq
    (REdCall "bn254_Fp2_add" (Fp2_loc "out_c0") [Fp2_loc "inx_c0"; Fp2_loc "iny_c0"])
    (REdSeq
      (REdCall "bn254_Fp2_add" (Fp2_loc "out_c1") [Fp2_loc "inx_c1"; Fp2_loc "iny_c1"])
      (REdCall "bn254_Fp2_add" (Fp2_loc "out_c2") [Fp2_loc "inx_c2"; Fp2_loc "iny_c2"])).

(** **CONN-3j certified artifact** — Fp6 add body serialization (Qed). *)
Example bn254_fp6_add_sexpr_value :
  ser_cmd bn254_fp6_add_rs
    = "(Seq (Call ""bn254_Fp2_add"" (loc ""out_c0"" (Bytes 64)) ((loc ""inx_c0"" (Bytes 64)) (loc ""iny_c0"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""out_c1"" (Bytes 64)) ((loc ""inx_c1"" (Bytes 64)) (loc ""iny_c1"" (Bytes 64)))) (Call ""bn254_Fp2_add"" (loc ""out_c2"" (Bytes 64)) ((loc ""inx_c2"" (Bytes 64)) (loc ""iny_c2"" (Bytes 64))))))".
Proof. vm_compute. reflexivity. Qed.

(** Fp6 MUL (Toom/Karatsuba over Fp2): the three-coordinate schedule
    [CubicFieldExtensions.Fp6_mul] emits, over five Fp2 scratch felems
    [a0b0]/[a1b1]/[a2b2]/[t]/[u] (each [REdLetZero … (TBytes 64)], the
    [rust_cmd_ed] image of bedrock2 [stackalloc 64]).  Component slots
    [inx_c0..2] = a, [iny_c0..2] = b, [out_c0..2] the result coordinates.
    Call order is byte-identical to the bedrock2 body (a 19-call chain over
    [bn254_Fp2_{mul,add,sub,mul_xi}]):
      a0b0=a0*b0; a1b1=a1*b1; a2b2=a2*b2;
      c0: t=a1+a2; u=b1+b2; t=t*u; t-=a1b1; t-=a2b2; t=xi*t; out.c0=a0b0+t;
      c1: t=a0+a1; u=b0+b1; t=t*u; t-=a0b0; t-=a1b1; u=xi*a2b2; out.c1=t+u;
      c2: t=a0+a2; u=b0+b2; t=t*u; t-=a0b0; t-=a2b2; out.c2=t+a1b1.        *)
Definition bn254_fp6_mul_rs : rust_cmd_ed :=
  REdLetZero "a0b0" (TBytes 64) (
  REdLetZero "a1b1" (TBytes 64) (
  REdLetZero "a2b2" (TBytes 64) (
  REdLetZero "t" (TBytes 64) (
  REdLetZero "u" (TBytes 64) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "a0b0") [Fp2_loc "inx_c0"; Fp2_loc "iny_c0"]) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "a1b1") [Fp2_loc "inx_c1"; Fp2_loc "iny_c1"]) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "a2b2") [Fp2_loc "inx_c2"; Fp2_loc "iny_c2"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "t") [Fp2_loc "inx_c1"; Fp2_loc "inx_c2"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "u") [Fp2_loc "iny_c1"; Fp2_loc "iny_c2"]) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "u"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a1b1"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a2b2"]) (
  REdSeq (REdCall "bn254_Fp2_mul_xi" (Fp2_loc "t") [Fp2_loc "t"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "out_c0") [Fp2_loc "a0b0"; Fp2_loc "t"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "t") [Fp2_loc "inx_c0"; Fp2_loc "inx_c1"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "u") [Fp2_loc "iny_c0"; Fp2_loc "iny_c1"]) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "u"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a0b0"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a1b1"]) (
  REdSeq (REdCall "bn254_Fp2_mul_xi" (Fp2_loc "u") [Fp2_loc "a2b2"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "out_c1") [Fp2_loc "t"; Fp2_loc "u"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "t") [Fp2_loc "inx_c0"; Fp2_loc "inx_c2"]) (
  REdSeq (REdCall "bn254_Fp2_add" (Fp2_loc "u") [Fp2_loc "iny_c0"; Fp2_loc "iny_c2"]) (
  REdSeq (REdCall "bn254_Fp2_mul" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "u"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a0b0"]) (
  REdSeq (REdCall "bn254_Fp2_sub" (Fp2_loc "t") [Fp2_loc "t"; Fp2_loc "a2b2"]) (
         (REdCall "bn254_Fp2_add" (Fp2_loc "out_c2") [Fp2_loc "t"; Fp2_loc "a1b1"])
  ))))))))))))))))))))))))))).

(** **CONN-3j certified artifact** — Fp6 mul body serialization (Qed). *)
Example bn254_fp6_mul_sexpr_value :
  ser_cmd bn254_fp6_mul_rs
    = "(LetZero ""a0b0"" (Bytes 64) (LetZero ""a1b1"" (Bytes 64) (LetZero ""a2b2"" (Bytes 64) (LetZero ""t"" (Bytes 64) (LetZero ""u"" (Bytes 64) (Seq (Call ""bn254_Fp2_mul"" (loc ""a0b0"" (Bytes 64)) ((loc ""inx_c0"" (Bytes 64)) (loc ""iny_c0"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul"" (loc ""a1b1"" (Bytes 64)) ((loc ""inx_c1"" (Bytes 64)) (loc ""iny_c1"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul"" (loc ""a2b2"" (Bytes 64)) ((loc ""inx_c2"" (Bytes 64)) (loc ""iny_c2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""t"" (Bytes 64)) ((loc ""inx_c1"" (Bytes 64)) (loc ""inx_c2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""u"" (Bytes 64)) ((loc ""iny_c1"" (Bytes 64)) (loc ""iny_c2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""u"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a1b1"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a2b2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul_xi"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""out_c0"" (Bytes 64)) ((loc ""a0b0"" (Bytes 64)) (loc ""t"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""t"" (Bytes 64)) ((loc ""inx_c0"" (Bytes 64)) (loc ""inx_c1"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""u"" (Bytes 64)) ((loc ""iny_c0"" (Bytes 64)) (loc ""iny_c1"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""u"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a0b0"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a1b1"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul_xi"" (loc ""u"" (Bytes 64)) ((loc ""a2b2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""out_c1"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""u"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""t"" (Bytes 64)) ((loc ""inx_c0"" (Bytes 64)) (loc ""inx_c2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_add"" (loc ""u"" (Bytes 64)) ((loc ""iny_c0"" (Bytes 64)) (loc ""iny_c2"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_mul"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""u"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a0b0"" (Bytes 64)))) (Seq (Call ""bn254_Fp2_sub"" (loc ""t"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a2b2"" (Bytes 64)))) (Call ""bn254_Fp2_add"" (loc ""out_c2"" (Bytes 64)) ((loc ""t"" (Bytes 64)) (loc ""a1b1"" (Bytes 64)))))))))))))))))))))))))))))))".
Proof. vm_compute. reflexivity. Qed.

(** The Fp12 = GT tower ops are the quadratic extension over Fp6
    (Field/FieldExtensions/GenericQuadratic.v's [QE_add] / [QE_mul]
    instantiated at BaseField = Fp6).  An Fp12 element is two Fp6
    components (c0/c1, addressed by [qe_expr_2nd] = base + 192 bytes,
    one BN254 Fp6 felem = 3 Fp2 felems * 64 bytes); each Fp12 op is a
    sequence of [cmd.call]s to the Fp6 LEAF functions ([bn254_Fp6_add],
    [bn254_Fp6_mul], [bn254_Fp6_sub], [bn254_Fp6_mul_by_v]).  This is the
    SAME compositional pattern, one tower level up: Fp12-over-Fp6 leaf
    calls just as Fp6-over-Fp2 and Fp2-over-Fp.  Each Fp6 component is a
    [TBytes 192] slot. *)

Notation Fp6_loc v := {| loc_var := v; loc_type := TBytes 192 |}.

(** Fp12 ADD: [out = inx + iny] over Fp12 = two component-wise Fp6 adds.
    Mirrors [GenericQuadratic.QE_add]'s two [cmd.call (add (F:=BaseField))]
    with BaseField = Fp6:  out.c0 = inx.c0 + iny.c0 ; out.c1 = … .         *)
Definition bn254_fp12_add_rs : rust_cmd_ed :=
  REdSeq
    (REdCall "bn254_Fp6_add" (Fp6_loc "out_c0") [Fp6_loc "inx_c0"; Fp6_loc "iny_c0"])
    (REdCall "bn254_Fp6_add" (Fp6_loc "out_c1") [Fp6_loc "inx_c1"; Fp6_loc "iny_c1"]).

(** **CONN-3j certified artifact** — Fp12 add body serialization (Qed). *)
Example bn254_fp12_add_sexpr_value :
  ser_cmd bn254_fp12_add_rs
    = "(Seq (Call ""bn254_Fp6_add"" (loc ""out_c0"" (Bytes 192)) ((loc ""inx_c0"" (Bytes 192)) (loc ""iny_c0"" (Bytes 192)))) (Call ""bn254_Fp6_add"" (loc ""out_c1"" (Bytes 192)) ((loc ""inx_c1"" (Bytes 192)) (loc ""iny_c1"" (Bytes 192)))))".
Proof. vm_compute. reflexivity. Qed.

(** Fp12 MUL (Karatsuba over Fp6): the [GenericQuadratic.QE_mul] schedule,
    BaseField = Fp6, over three Fp6 scratch felems [v0]/[v1]/[v2] (each
    [REdLetZero … (TBytes 192)], the image of bedrock2 [stackalloc 192]).
    Component slots [inx_c0]/[inx_c1] = a, [iny_c0]/[iny_c1] = b,
    [out_c0]/[out_c1] the result halves.  Call order is byte-identical to
    the bedrock2 body (a 9-call chain over [bn254_Fp6_{mul,add,sub,mul_by_v}]):
      v0=a0*b0; v1=a1*b1; v2=a0+a1; out.c1=b0+b1; out.c1=out.c1*v2;
      out.c1-=v0; out.c1-=v1; v2=mul_by_v(v1); out.c0=v0+v2.
    The [mul_by_v] = multiply by the Fp12 non-residue (the Fp6 element v),
    the dodecic-tower analogue of Fp2's [mul_xi].                          *)
Definition bn254_fp12_mul_rs : rust_cmd_ed :=
  REdLetZero "v0" (TBytes 192) (
  REdLetZero "v1" (TBytes 192) (
  REdLetZero "v2" (TBytes 192) (
  REdSeq (REdCall "bn254_Fp6_mul" (Fp6_loc "v0")     [Fp6_loc "inx_c0"; Fp6_loc "iny_c0"]) (
  REdSeq (REdCall "bn254_Fp6_mul" (Fp6_loc "v1")     [Fp6_loc "inx_c1"; Fp6_loc "iny_c1"]) (
  REdSeq (REdCall "bn254_Fp6_add" (Fp6_loc "v2")     [Fp6_loc "inx_c0"; Fp6_loc "inx_c1"]) (
  REdSeq (REdCall "bn254_Fp6_add" (Fp6_loc "out_c1") [Fp6_loc "iny_c0"; Fp6_loc "iny_c1"]) (
  REdSeq (REdCall "bn254_Fp6_mul" (Fp6_loc "out_c1") [Fp6_loc "out_c1"; Fp6_loc "v2"]) (
  REdSeq (REdCall "bn254_Fp6_sub" (Fp6_loc "out_c1") [Fp6_loc "out_c1"; Fp6_loc "v0"]) (
  REdSeq (REdCall "bn254_Fp6_sub" (Fp6_loc "out_c1") [Fp6_loc "out_c1"; Fp6_loc "v1"]) (
  REdSeq (REdCall "bn254_Fp6_mul_by_v" (Fp6_loc "v2") [Fp6_loc "v1"]) (
         (REdCall "bn254_Fp6_add" (Fp6_loc "out_c0") [Fp6_loc "v0"; Fp6_loc "v2"])
  ))))))))))).

(** **CONN-3j certified artifact** — Fp12 (GT) mul body serialization (Qed). *)
Example bn254_fp12_mul_sexpr_value :
  ser_cmd bn254_fp12_mul_rs
    = "(LetZero ""v0"" (Bytes 192) (LetZero ""v1"" (Bytes 192) (LetZero ""v2"" (Bytes 192) (Seq (Call ""bn254_Fp6_mul"" (loc ""v0"" (Bytes 192)) ((loc ""inx_c0"" (Bytes 192)) (loc ""iny_c0"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_mul"" (loc ""v1"" (Bytes 192)) ((loc ""inx_c1"" (Bytes 192)) (loc ""iny_c1"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_add"" (loc ""v2"" (Bytes 192)) ((loc ""inx_c0"" (Bytes 192)) (loc ""inx_c1"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_add"" (loc ""out_c1"" (Bytes 192)) ((loc ""iny_c0"" (Bytes 192)) (loc ""iny_c1"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_mul"" (loc ""out_c1"" (Bytes 192)) ((loc ""out_c1"" (Bytes 192)) (loc ""v2"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_sub"" (loc ""out_c1"" (Bytes 192)) ((loc ""out_c1"" (Bytes 192)) (loc ""v0"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_sub"" (loc ""out_c1"" (Bytes 192)) ((loc ""out_c1"" (Bytes 192)) (loc ""v1"" (Bytes 192)))) (Seq (Call ""bn254_Fp6_mul_by_v"" (loc ""v2"" (Bytes 192)) ((loc ""v1"" (Bytes 192)))) (Call ""bn254_Fp6_add"" (loc ""out_c0"" (Bytes 192)) ((loc ""v0"" (Bytes 192)) (loc ""v2"" (Bytes 192)))))))))))))))".
Proof. vm_compute. reflexivity. Qed.
