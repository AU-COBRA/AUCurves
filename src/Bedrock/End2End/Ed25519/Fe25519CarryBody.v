(** * Fe25519CarryBody — rust_cmd_ed AST for [fe25519_carry]
 *
 *  Phase 0c sibling of [Fe25519AddSubBody.v] / [Fe25519MulBody.v]:
 *  inline radix-2^51 carry-propagation chain in [rust_cmd_ed], emitted
 *  through the [REdLimbStore] + [SLimb] + [SShr] + [SAnd] + [SMul]
 *  + [SLit] constructors introduced in commit f9578ce.  Removes one
 *  more [extern "C"] symbol from the [curve25519-jasmin-rs] crate.
 *
 *  Algorithm (fiat-crypto's [chained_carries 5 (2^255) [(1,19)] _ idxs]
 *  with [idxs = [0;1;2;3;4;0]] — see [fiat-crypto/src/Arithmetic/Core.v]):
 *
 *    For each carry step [c : src → dst] where [src,dst] are limb
 *    indices and [factor] is the wrap-around multiplier (1 for
 *    intra-limb, 19 for the high→low wrap on [(1,19)] mod 2^255 - 19):
 *
 *      dst' := dst + factor * (src >> 51)
 *      src' := src  & (2^51 - 1)
 *
 *    With chain [0;1;2;3;4;0] this yields six carry steps and twelve
 *    [REdLimbStore]s (one per limb write).
 *
 *  Body shape (12 [REdLimbStore]s — explicit list below):
 *
 *    step 0 (carry 0 → 1, factor 1):
 *      dest[0] := SLimb a 0 & mask51
 *      dest[1] := SLimb a 1 + (SLimb a 0 >> 51)
 *    step 1 (carry 1 → 2):
 *      dest[1] := dest[1] & mask51
 *      dest[2] := SLimb a 2 + (dest[1] >> 51)        -- pre-mask form
 *      ...
 *    step 4 (carry 4 → 0, factor 19):
 *      dest[4] := dest[4] & mask51
 *      dest[0] := dest[0] + 19 * (dest[4] >> 51)
 *    step 5 (final carry 0 → 1):
 *      dest[0] := dest[0] & mask51
 *      dest[1] := dest[1] + (dest[0] >> 51)
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_carry_body]  : Inline 12-[REdLimbStore] chain.  No
 *                            [extern "C"] FFI in the surface AST.
 *  - [carry_inline_correct]: Section hypothesis in
 *                            [Fe25519CarryCorrect.v] (scaffold);
 *                            full mechanical discharge against
 *                            fiat-crypto's [chained_carries] +
 *                            [Positional.eval] is left as Phase 0d.
 *
 *  History
 *  =======
 *  Phase 0a (commit 6999797): [fe25519_carry] body did not exist
 *    (the X25519 build only emits [carry_add] / [carry_sub]).
 *  Phase 0c (this file, 2026-05-13): introduced standalone carry as
 *    an inline 12-step chain.  Useful as a composable building block
 *    after an [add] / [sub] when the caller wants a fully-reduced
 *    output (radix-2^51 carry-propagated representative of the
 *    coset [F p]).  Matches fiat-crypto's stand-alone carry op
 *    (the same primitive that [carry_add] inlines after [add]).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  Helpers — radix-2^51 constants and locator construction.    *)
(* ================================================================ *)

(** Radix used by the 5-limb unsaturated Solinas representation. *)
Definition fe25519_radix : Z := 51.

(** Low 51-bit mask, as a literal value (not yet through [SLit] —
    callers wrap with [SLit] when embedding into a [sexpr_ed]). *)
Definition fe25519_mask51_z : Z := Z.ones 51.

(** The reduction factor for [c = [(1, 19)]] / modulus [2^255 - 19]:
    a high-limb carry past limb 4 wraps around and is multiplied by
    [19] before being added back to limb 0. *)
Definition fe25519_reduction_c : Z := 19.

(** Construct a [located_ed] for a [TFp25519] slot by name.  (Same as
    [Fe25519AddSubBody.LFp]; duplicated here so this file is
    independent.) *)
Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(* ================================================================ *)
(* §2.  fe25519_carry body                                           *)
(* ================================================================ *)

(** Helper: shift-right of a limb expression by [fe25519_radix].
    Wrapped here so the body reads cleanly. *)
Definition sShr51 (e : sexpr_ed) : sexpr_ed :=
  SShr e (SLit fe25519_radix).

(** Helper: low-51-bit mask of an expression. *)
Definition sMask51 (e : sexpr_ed) : sexpr_ed :=
  SAnd e (SLit fe25519_mask51_z).

(** Helper: [19 * (e >> 51)] — the wrap-around-and-multiply step at
    the high-limb boundary. *)
Definition sWrap19 (e : sexpr_ed) : sexpr_ed :=
  SMul (SLit fe25519_reduction_c) (sShr51 e).

(** [fe25519_carry_body] computes [dest := chained_carries 5 s c a
    [0;1;2;3;4;0]] for [s = 2^255], [c = [(1,19)]] — i.e. propagates
    carries through the five limbs of [a] and folds the high carry
    back into limb 0 (multiplied by [19], the [(1,19)] reduction
    coefficient).

    The 12 [REdLimbStore]s are grouped in 6 carry steps; each step's
    two writes are stacked as nested [REdSeq]s.  Aliasing
    [dest = a] is not supported (the body would need a temp limb
    list to avoid clobbering; the IR's [REdLimbStore] writes one
    limb at a time, so reading [SLimb a i] after [dest[i]] has been
    written is unsafe unless [dest <> a]).  The matching frame
    hypothesis in [Fe25519CarryCorrect.v] enforces [dest <> a]. *)
Definition fe25519_carry_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        let a_v := a_loc.(loc_var) in
        let d_v := dest.(loc_var) in
        (* Step 0: carry from a[0] into limb 1, mask low to dest[0]. *)
        REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb a_v 0%nat)))
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb a_v 1%nat) (sShr51 (SLimb a_v 0%nat))))
        (* Step 1: carry from dest[1] into limb 2, mask low to dest[1].
           Note ordering: we mask dest[1] AFTER reading it for the
           >>51, so we compute dest[2] first then dest[1] := mask51. *)
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb a_v 2%nat) (sShr51 (SLimb d_v 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb d_v 1%nat)))
        (* Step 2. *)
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb a_v 3%nat) (sShr51 (SLimb d_v 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb d_v 2%nat)))
        (* Step 3. *)
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb a_v 4%nat) (sShr51 (SLimb d_v 3%nat))))
        (REdSeq
          (REdLimbStore dest 3%nat (sMask51 (SLimb d_v 3%nat)))
        (* Step 4: high-limb wrap. dest[0] += 19 * (dest[4] >> 51). *)
        (REdSeq
          (REdLimbStore dest 0%nat
             (SAdd (SLimb d_v 0%nat) (sWrap19 (SLimb d_v 4%nat))))
        (REdSeq
          (REdLimbStore dest 4%nat (sMask51 (SLimb d_v 4%nat)))
        (* Step 5: final carry into dest[1], mask dest[0]. *)
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb d_v 1%nat) (sShr51 (SLimb d_v 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb d_v 0%nat)))
        ))))))))))
    | _ => REdSkip
    end.

(** Public function-table entry.  Downstream callers extend their
    [function_table_ed] with this so [REdCallFn] can dispatch
    [fe25519_carry]. *)
Definition fe25519_carry_table : function_table_ed :=
  [ ("fe25519_carry", fe25519_carry_body) ].

(* ================================================================ *)
(* §3.  Sanity: count of REdLimbStores                               *)
(* ================================================================ *)

(** [num_red_limb_stores] gives the surface count.  This is checked
    to be 12 below (matching the 6-step / 2-writes-per-step
    carry-chain shape [0;1;2;3;4;0] from fiat-crypto's
    [chained_carries]). *)
Fixpoint num_red_limb_stores (c : rust_cmd_ed) : nat :=
  match c with
  | REdLimbStore _ _ _ => 1%nat
  | REdSeq c1 c2 => Nat.add (num_red_limb_stores c1) (num_red_limb_stores c2)
  | _ => 0%nat
  end.

Example fe25519_carry_body_stores_12 :
  num_red_limb_stores
    (fe25519_carry_body
       (LFp "dest"%string) [LFp "a"%string]) = 12%nat.
Proof. reflexivity. Qed.
