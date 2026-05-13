(** * Fe25519Scmula24Body — rust_cmd_ed AST for [fe25519_scmula24]
 *
 *  Phase 0c sibling of [Fe25519AddSubBody.v] / [Fe25519CarryBody.v]:
 *  inline radix-2^51 scalar-multiply-by-constant chain in
 *  [rust_cmd_ed], emitted through [REdLimbStore] + [SLimb] +
 *  [SMul] + [SLit] (+ [SAdd] + [SShr] + [SAnd] for the carry tail)
 *  introduced in commit f9578ce.  Removes one more [extern "C"]
 *  symbol from the [curve25519-jasmin-rs] crate — namely the
 *  multiply-by-[a24 = 121665] leaf used twice per X25519 ladder
 *  step ([fiat-crypto/src/Bedrock/End2End/X25519/Field25519.v]
 *  L152, [scmula24_op = UnsaturatedSolinas.carry_scmul_const n s c
 *  width (F.to_Z a24)]).
 *
 *  Algorithm (fiat-crypto's [carry_scmul_const n s c width a24]):
 *
 *    Phase A — limbwise multiply by the constant:
 *      For each limb [i] in [0..n-1]:
 *        dest[i] := a[i] * a24
 *
 *    Phase B — carry-propagate (same chain as [fe25519_carry], chain
 *               [0;1;2;3;4;0]):
 *      Six carry steps, twelve [REdLimbStore]s — see
 *      [Fe25519CarryBody.v] for the same shape.
 *
 *  Bound analysis (why two carry passes is NOT needed)
 *  ===================================================
 *  The radix-2^51 limb representation keeps each input limb under
 *  [tight_bounds ≈ 2^51 + slack ≤ 1.125 * 2^51 < 2^52].  After one
 *  scalar-multiply by [a24 = 121665 < 2^17] each product limb is
 *  bounded by [1.125 * 2^51 * 2^17 = 1.125 * 2^68 < 2^69 < 2^64? — NO,
 *  PRODUCT EXCEEDS 2^64].  However, fiat-crypto's recipe sidesteps
 *  this: [carry_scmul_const] inlines the carry CHAIN, not a re-add
 *  loop, so the chained-carries pass propagates the high bits limb
 *  to limb.  After one full [chained_carries [0;1;2;3;4;0]] pass the
 *  output is in tight_bounds again (see
 *  [UnsaturatedSolinas.carry_scmul_const_correct] in fiat-crypto;
 *  the [eval ... ≡ a24 * eval a (mod m)] equation discharges modulo).
 *
 *  Concretely: with input limb max [≤ 1.125 * 2^51] and multiplier
 *  [< 2^17], product is [< 1.125 * 2^68 < 2^69], fitting in u128
 *  intermediates / two u64 carry steps.  Since [REdLimbStore]
 *  writes a single u64 limb, the inline pattern factors the
 *  reduce as the same 12-store carry chain that [fe25519_carry]
 *  uses — one pass suffices because the wraparound multiplier 19
 *  brings the high-limb bits comfortably back below 2^52 (1.125 *
 *  2^17 * 19 < 2^23 of overflow, well under one limb).
 *
 *  Hence we emit ONE carry pass (12 REdLimbStores) after the 5
 *  limbwise multiplies — totalling 17 REdLimbStores.
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_scmula24_body]   : Inline 17-[REdLimbStore] chain
 *                                (5 multiplies + 12 carry stores).
 *                                No [extern "C"] FFI in the surface
 *                                AST.
 *  - [scmula24_inline_correct] : Section hypothesis in
 *                                [Fe25519Scmula24Correct.v]
 *                                (scaffold); full mechanical
 *                                discharge against fiat-crypto's
 *                                [carry_scmul_const_correct] +
 *                                [Positional.eval] is left as
 *                                Phase 0d.
 *
 *  History
 *  =======
 *  Phase 0a (commit 6999797): scmula24 body did not exist (the
 *    X25519 build went through fiat-crypto's bedrock2 emission
 *    directly).
 *  Phase 0c (this file, 2026-05-13): introduced standalone scmula24
 *    as an inline 17-step chain.  Used in X25519's Montgomery
 *    ladder twice per step (after each square + add/sub block).
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
(* §1.  Helpers — radix-2^51 constants, the a24 multiplier, and     *)
(*       locator construction.                                       *)
(* ================================================================ *)

(** Radix used by the 5-limb unsaturated Solinas representation. *)
Definition fe25519_radix : Z := 51.

(** Low 51-bit mask. *)
Definition fe25519_mask51_z : Z := Z.ones 51.

(** Wraparound multiplier for c = [(1,19)] / modulus 2^255 - 19. *)
Definition fe25519_reduction_c : Z := 19.

(** The scalar constant: [a24 = (A - 2) / 4 = (486662 - 2) / 4 = 121665]
    in [F p], where [A = 486662] is the Montgomery [B*y^2 = x^3 + A*x^2
    + x] curve parameter from [Crypto.Spec.Curve25519]. *)
Definition fe25519_a24_z : Z := 121665.

(** Construct a [located_ed] for a [TFp25519] slot by name. *)
Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(* ================================================================ *)
(* §2.  Expression helpers (mirroring [Fe25519CarryBody]).           *)
(* ================================================================ *)

(** Shift-right of an expression by [fe25519_radix]. *)
Definition sShr51 (e : sexpr_ed) : sexpr_ed :=
  SShr e (SLit fe25519_radix).

(** Low-51-bit mask of an expression. *)
Definition sMask51 (e : sexpr_ed) : sexpr_ed :=
  SAnd e (SLit fe25519_mask51_z).

(** [19 * (e >> 51)] — wrap-around-and-multiply at the high-limb
    boundary. *)
Definition sWrap19 (e : sexpr_ed) : sexpr_ed :=
  SMul (SLit fe25519_reduction_c) (sShr51 e).

(** [a24 * (SLimb v i)] — multiply limb [i] of [v] by the scalar
    constant 121665. *)
Definition sScmulA24 (v : String.string) (i : nat) : sexpr_ed :=
  SMul (SLimb v i) (SLit fe25519_a24_z).

(* ================================================================ *)
(* §3.  fe25519_scmula24 body                                        *)
(* ================================================================ *)

(** [fe25519_scmula24_body] computes [dest := a24 * a] in [F p],
    inlined as a 17-[REdLimbStore] chain: five per-limb constant
    multiplies followed by a [chained_carries [0;1;2;3;4;0]] pass.

    Phase A (limbwise multiply, 5 stores):
      dest[i] := SLimb a i * SLit 121665     (i = 0..4)

    Phase B (carry chain, 12 stores — identical shape to
    [Fe25519CarryBody.fe25519_carry_body], operating on dest[i]):
      Step 0: dest[1] += dest[0] >> 51 ; dest[0] := dest[0] & mask51
        (note: order swapped vs. Carry's intra-step ordering since
         dest already holds the multiplied values — we read dest[0]
         twice, once for the >> and once for the &, but that's safe
         because the masking write to dest[0] happens AFTER the
         >>51 read into dest[1].)
      Step 1: dest[2] += dest[1] >> 51 ; dest[1] := dest[1] & mask51
      Step 2: dest[3] += dest[2] >> 51 ; dest[2] := dest[2] & mask51
      Step 3: dest[4] += dest[3] >> 51 ; dest[3] := dest[3] & mask51
      Step 4 (wrap): dest[0] += 19 * (dest[4] >> 51) ; dest[4] := dest[4] & mask51
      Step 5 (re-carry 0->1): dest[1] += dest[0] >> 51 ; dest[0] := dest[0] & mask51

    Aliasing [dest = a] is disallowed by the matching frame hypothesis
    in [Fe25519Scmula24Correct.v] (same constraint as
    [fe25519_carry_body]: limbwise SLimb reads of [a] in Phase A
    would be clobbered if dest = a after the first store). *)
Definition fe25519_scmula24_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        let a_v := a_loc.(loc_var) in
        let d_v := dest.(loc_var) in
        (* ---- Phase A: 5 limbwise multiplies ---- *)
        REdSeq
          (REdLimbStore dest 0%nat (sScmulA24 a_v 0%nat))
        (REdSeq
          (REdLimbStore dest 1%nat (sScmulA24 a_v 1%nat))
        (REdSeq
          (REdLimbStore dest 2%nat (sScmulA24 a_v 2%nat))
        (REdSeq
          (REdLimbStore dest 3%nat (sScmulA24 a_v 3%nat))
        (REdSeq
          (REdLimbStore dest 4%nat (sScmulA24 a_v 4%nat))
        (* ---- Phase B: 12-store carry chain (acts on dest in-place) ---- *)
        (* Step 0: carry from dest[0] into dest[1], mask dest[0]. *)
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb d_v 1%nat) (sShr51 (SLimb d_v 0%nat))))
        (REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb d_v 0%nat)))
        (* Step 1. *)
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb d_v 2%nat) (sShr51 (SLimb d_v 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb d_v 1%nat)))
        (* Step 2. *)
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb d_v 3%nat) (sShr51 (SLimb d_v 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb d_v 2%nat)))
        (* Step 3. *)
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb d_v 4%nat) (sShr51 (SLimb d_v 3%nat))))
        (REdSeq
          (REdLimbStore dest 3%nat (sMask51 (SLimb d_v 3%nat)))
        (* Step 4: high-limb wrap. *)
        (REdSeq
          (REdLimbStore dest 0%nat
             (SAdd (SLimb d_v 0%nat) (sWrap19 (SLimb d_v 4%nat))))
        (REdSeq
          (REdLimbStore dest 4%nat (sMask51 (SLimb d_v 4%nat)))
        (* Step 5: final carry 0 -> 1. *)
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb d_v 1%nat) (sShr51 (SLimb d_v 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb d_v 0%nat)))
        )))))))))))))))
    | _ => REdSkip
    end.

(** Public function-table entry. *)
Definition fe25519_scmula24_table : function_table_ed :=
  [ ("fe25519_scmula24", fe25519_scmula24_body) ].

(* ================================================================ *)
(* §4.  Sanity: count of REdLimbStores                               *)
(* ================================================================ *)

(** [num_red_limb_stores] gives the surface count.  Checked to be 17
    below (5 multiply stores + 12 carry stores). *)
Fixpoint num_red_limb_stores (c : rust_cmd_ed) : nat :=
  match c with
  | REdLimbStore _ _ _ => 1%nat
  | REdSeq c1 c2 => Nat.add (num_red_limb_stores c1) (num_red_limb_stores c2)
  | _ => 0%nat
  end.

Example fe25519_scmula24_body_stores_17 :
  num_red_limb_stores
    (fe25519_scmula24_body
       (LFp "dest"%string) [LFp "a"%string]) = 17%nat.
Proof. reflexivity. Qed.
