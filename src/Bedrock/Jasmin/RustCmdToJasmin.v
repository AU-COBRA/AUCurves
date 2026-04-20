(** * RustCmdToJasmin.v
 *
 * Translates [rust_cmd] to [jasmin_cmd].
 *
 * With the borrow-checked rust_cmd approach, the source is handwritten
 * [rust_cmd] (not bedrock2).  This file provides the compilation path
 * from that source to [jasmin_cmd], complementing the existing
 * [bedrock2 → tr_cmd → jasmin_cmd] route in [Core.v].
 *
 * Calling convention: all struct arguments are passed as pointer-like
 * variable references, matching the existing bedrock2→jasmin convention.
 * For [RCall f dest args]:
 *   - [dest.loc_var] is the output pointer (first jasmin arg)
 *   - each [arg.loc_var] is an input pointer (subsequent jasmin args)
 *
 * Contents:
 *   §1  tt_to_jtype — tower_type to jasmin stack-array type
 *   §2  rj_expr — sexpr → jasmin_expr
 *   §3  rj_translate — rust_cmd → jasmin_cmd
 *   §4  Structural lemmas
 *   §5  Note on simulation (deferred to a future file)
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.Jasmin.Core.

(* ================================================================ *)
(* §1. Tower type → jasmin stack-array type                        *)
(* ================================================================ *)

(** Each tower level is a stack array of u64 limbs.
    [N] is the Fp limb count (e.g. 6 for BLS12-381, 4 for BN254).
    [JTstack k] declares [stack u64[k]] in Jasmin. *)
Definition tt_to_jtype (N : Z) (t : tower_type) : jasmin_type :=
  match t with
  | TFp   => JTstack N
  | TFp2  => JTstack (2 * N)
  | TFp6  => JTstack (6 * N)
  | TFp12 => JTstack (12 * N)
  end.

Example tt_to_jtype_fp_bls12 :
  tt_to_jtype 6 TFp = JTstack 6.
Proof. reflexivity. Qed.

Example tt_to_jtype_fp12_bls12 :
  tt_to_jtype 6 TFp12 = JTstack 72.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §2. Scalar expression → jasmin_expr                             *)
(* ================================================================ *)

Fixpoint rj_expr (e : sexpr) : jasmin_expr :=
  match e with
  | SVar x   => JEvar x
  | SLit n   => JElit (Z.of_nat n)
  | SAdd a b => JEadd (rj_expr a) (rj_expr b)
  | SSub a b => JEsub (rj_expr a) (rj_expr b)
  | SShr a b => JEshr (rj_expr a) (rj_expr b)
  | SAnd a b => JEand (rj_expr a) (rj_expr b)
  end.

(* ================================================================ *)
(* §3. rust_cmd → jasmin_cmd translation                           *)
(* ================================================================ *)

(** For [RCloneCall x src f dest args]: Jasmin has no clone primitive.
    We emit [x = src_var] (copy of the base variable) followed by the
    call with aliased argument positions replaced by [x].
    The variable [x] is assumed declared in an enclosing [RLetU64Zero]. *)
Fixpoint rj_translate (N : Z) (c : rust_cmd) : jasmin_cmd :=
  match c with
  | RSkip =>
      JCskip

  | RSeq c1 c2 =>
      JCseq (rj_translate N c1) (rj_translate N c2)

  | RLetZero x t body =>
      JCdecl x (tt_to_jtype N t) (rj_translate N body)

  | RLetU64Zero x body =>
      JCdecl x JTu64 (rj_translate N body)

  | RScalarSet x e =>
      JCset x (rj_expr e)

  | RCall f dest args =>
      JCcall f
        (JEvar (loc_var dest) ::
         List.map (fun a => JEvar (loc_var a)) args)

  | RCloneCall x src f dest args =>
      JCseq
        (JCset x (JEvar (loc_var src)))
        (JCcall f
           (JEvar (loc_var dest) ::
            List.map (fun a =>
              if String.eqb (loc_var a) (loc_var src)
              then JEvar x
              else JEvar (loc_var a)) args))

  | RIfNz e ct cf =>
      JCif (rj_expr e) (rj_translate N ct) (rj_translate N cf)

  | RWhileNz e body =>
      JCwhile (rj_expr e) (rj_translate N body)

  | RLimbStore loc k e =>
      JCstore (JEvar (loc_var loc)) (Z.of_nat k * 8) (rj_expr e)
  end.

(* ================================================================ *)
(* §4. Structural lemmas                                           *)
(* ================================================================ *)

Lemma rj_translate_skip : forall N,
  rj_translate N RSkip = JCskip.
Proof. reflexivity. Qed.

Lemma rj_translate_seq : forall N c1 c2,
  rj_translate N (RSeq c1 c2) =
    JCseq (rj_translate N c1) (rj_translate N c2).
Proof. reflexivity. Qed.

Lemma rj_translate_let_zero : forall N x t body,
  rj_translate N (RLetZero x t body) =
    JCdecl x (tt_to_jtype N t) (rj_translate N body).
Proof. reflexivity. Qed.

Lemma rj_translate_call : forall N f dest args,
  rj_translate N (RCall f dest args) =
    JCcall f (JEvar (loc_var dest) ::
              List.map (fun a => JEvar (loc_var a)) args).
Proof. reflexivity. Qed.

Lemma rj_translate_while : forall N e body,
  rj_translate N (RWhileNz e body) =
    JCwhile (rj_expr e) (rj_translate N body).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §5. Note on simulation (deferred)                               *)
(* ================================================================ *)

(** The full simulation theorem would state:

      ∀ N u64_max leaf_spec c s1 s2,
        rust_exec N u64_max leaf_spec c s1 s2 →
        jasmin_exec (rj_translate (Z.of_nat N) c)
                    (rs_to_js N s1) (rs_to_js N s2)

    where [rs_to_js N : rust_state → jasmin_state] maps each named
    tower variable to a pointer-addressed memory region of the right
    size, and [jasmin_exec] wraps [JasminBridgeReal.to_jasmin_cmd] +
    [psem.sem].

    The proof is by structural induction on [rust_exec]:
    - structural cases: direct from [rj_translate] definition
    - [RCall]: JCcall passes all loc_vars as pointer args; agreement
      follows from the pointer calling convention
    - [RCloneCall]: JCset + JCcall mirrors clone-then-call semantics

    This is deferred pending a standalone [rs_to_js] definition and
    a [jasmin_exec] wrapper that does not require importing Jasmin's
    full Coq library.  The translation function above is the correct
    input to that future proof. *)
