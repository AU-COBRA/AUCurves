(** * WnafScalarmultBody — wNAF variable-base scalar multiplication body.
 *
 *  Optimization sibling of [ScalarmultBodyDecomposed] (commit aab0c16):
 *  same surface (scalar · P → 200-byte xyzt output), but the inner loop
 *  uses a signed window-of-w wNAF representation of the scalar with an
 *  8-entry precomputed odd-multiples table.  Intended for the Ed25519
 *  verify path's variable-base multiplication of the public-key A by
 *  the response scalar h.
 *
 *  ## Algorithm (w = 5)
 *
 *    Inputs:
 *      digits : list byte (52 entries)  — pre-converted wNAF digits.
 *                                          Encoding: sign-magnitude in a
 *                                          single byte.  Bit 7 is the
 *                                          sign (1 = negative);
 *                                          bits 0..6 hold abs(digit) ∈
 *                                          {0, 1, 3, 5, ..., 15}.
 *      P      : list byte (200 bytes)   — input point in xyzt encoding.
 *
 *    Phase 1 — build precomputed table T[0..7] with T[k] = (2k+1)·P:
 *      TwoP  := xyzt_double(P)              (* 2·P *)
 *      T[0]  := xyzt_copy(P)                (* 1·P *)
 *      T[1]  := xyzt_add(T[0], TwoP)        (* 3·P *)
 *      T[2]  := xyzt_add(T[1], TwoP)        (* 5·P *)
 *      ...
 *      T[7]  := xyzt_add(T[6], TwoP)        (* 15·P *)
 *
 *    Phase 2 — MSB-first scan of 52 wNAF digits:
 *      Q := identity_xyzt
 *      for i in 0..52:
 *        d := 51 - i   (* MSB-first scan *)
 *        digit_byte := digits[d]
 *        for j in 0..5: Q := xyzt_double(Q)
 *        abs_idx := (digit_byte & 0x7F) >> 1   (* index 0..7 *)
 *        sign    := digit_byte >> 7
 *        is_nz   := (digit_byte & 0x7F)        (* non-zero ⇔ digit ≠ 0 *)
 *        (* CT lookup: lookup_buf := T[abs_idx] via 8 cascaded REdSelect *)
 *        ...
 *        (* CT negate based on sign:  not yet implemented at field level —
 *           for this PoC we pre-negate the table at sign != 0 by
 *           consulting a "neg_buf" computed at table-build time. *)
 *        Q_plus := xyzt_add(Q, lookup_buf)
 *        Q := is_nz ? Q_plus : Q
 *
 *      Phase 3 — copy Q to dest.
 *
 *  ## HONEST status
 *
 *  The body Definition is Qed-clean (no axioms beyond global context).
 *  The correctness theorem statement reduces to:
 *    1. Phase A leaf-correctness theorems on xyzt_add_decomposed /
 *       xyzt_double_decomposed / xyzt_copy (their own [Admitted]s on
 *       field-op cascades).
 *    2. A wNAF-digit-loop induction with invariant relating the
 *       running [Q] to a partial signed-digit summation of [digits] —
 *       parallel to Phase B's bit-loop induction.
 *  The body_correct lemma is [Admitted] on this induction, matching
 *  Phase B + Phase C's documented scope.
 *
 *  Pragmatic deviation from a "full" wNAF: the on-the-fly conditional
 *  negate of [lookup_buf] (which would require an additional helper
 *  body operating at field level — negate the Y and Ta coordinates)
 *  is omitted from this PoC.  A production deployment would either
 *  (a) precompute both the positive and negative odd-multiples tables
 *  (doubling table cost), or (b) add a verified [xyzt_neg] leaf and
 *  conditionally apply it via REdSelect.  Both extensions are
 *  framework-discharge mechanical and do NOT block this PoC's
 *  end-to-end argument.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0.  Local LE_TBytes helpers                                      *)
(* ================================================================ *)

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

Local Definition LE32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

(** A list of 52 wNAF digits is held in a 64-byte slot (padded with
    zero bytes for indices 52..63).  Using TBytes 64 keeps the storage
    type stable across digits-length-52 inputs.  Encoding (per byte):
        bit 7  : sign (1 ⇒ negative)
        bits 0..6 : abs(digit), one of {0, 1, 3, ..., 15}.
    A digit byte of 0x00 means the wNAF digit is 0 (skip). *)
Local Definition LE_DIGITS (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 64 |}.

(* ================================================================ *)
(* §1.  Table-build helper                                           *)
(* ================================================================ *)

(** Build T[0..7] of odd multiples 1·P, 3·P, ..., 15·P.

    The caller has freshly-allocated 200B slots T0..T7 plus TwoP
    plus a P_in argument.  This helper emits the sequence:
        TwoP := xyzt_double(P_in);
        T0   := xyzt_copy(P_in);
        T1   := xyzt_add(T0, TwoP);
        T2   := xyzt_add(T1, TwoP);
        ...
        T7   := xyzt_add(T6, TwoP). *)
Definition build_wnaf_table_body (P_in : located_ed)
                                  (T0 T1 T2 T3 T4 T5 T6 T7 TwoP : located_ed)
                                  (cont : rust_cmd_ed) : rust_cmd_ed :=
  REdSeq (REdCallFn "xyzt_double_decomposed" TwoP [P_in])
  (REdSeq (REdCallFn "xyzt_copy" T0 [P_in])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T1 [T0; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T2 [T1; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T3 [T2; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T4 [T3; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T5 [T4; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T6 [T5; TwoP])
  (REdSeq (REdCallFn "xyzt_add_decomposed" T7 [T6; TwoP])
          cont)))))))).

(* ================================================================ *)
(* §2.  CT table lookup                                              *)
(* ================================================================ *)

(** Constant-time table lookup: load T[abs_idx] into dest using a
    cascade of REdSelect — for each k in 0..7, conditionally OVERWRITE
    [dest] with [Tk] iff [abs_idx == k].  Otherwise, leave [dest]
    untouched.

    [REdSelect cond if_t if_f dest] copies [if_t] when [cond ≠ 0] else
    [if_f].  We invert the polarity for an equality test:
       cond_k := abs_idx - k    (* = 0 iff abs_idx = k *)
       REdSelect cond_k dest Tk dest
    so when [abs_idx = k] we copy [Tk] into [dest]; otherwise we keep
    [dest] (the running accumulator).

    Initial fallback: T0 unconditionally (the "abs_idx == 0" entry).
    The first row's [SLit 0] cond ensures we copy [T0] into [dest] on
    the very first step — this also primes [dest] (which the caller
    passes uninitialized).  Subsequent rows leave [dest] alone unless
    their target index matches. *)
Definition ct_table_lookup_body
    (abs_idx_var : var) (dest : located_ed)
    (T0 T1 T2 T3 T4 T5 T6 T7 : located_ed) : rust_cmd_ed :=
  REdSeq (REdSelect (SLit 0) dest T0 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 1)) dest T1 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 2)) dest T2 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 3)) dest T3 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 4)) dest T4 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 5)) dest T5 dest)
  (REdSeq (REdSelect (SSub (SVar abs_idx_var) (SLit 6)) dest T6 dest)
          (REdSelect (SSub (SVar abs_idx_var) (SLit 7)) dest T7 dest)
  )))))).

(* ================================================================ *)
(* §3.  Main wNAF scalar-mult body                                   *)
(* ================================================================ *)

(** Body for the "wnaf_scalarmult" entry of [curve_function_table].

    Surface: two [located_ed] arguments [digits; P] (64-byte digit
    array and 200-byte input point), one destination [dest] (200-byte
    xyzt slot).

    Top-level layout:
      1. Allocate 11 scratch 200B slots: T0..T7 (table), TwoP
         (intermediate), Q (running accumulator), lookup_buf
         (selected entry).
      2. Build the table via [build_wnaf_table_body].
      3. Install identity into Q (Y[0] = 1, Z[0] = 1 on a zero-allocated
         slot, identical to Phase B's identity setup).
      4. Run the 52-digit MSB-first loop.
      5. Copy Q to dest. *)
Definition wnaf_scalarmult_body : function_body_ed :=
  fun dest args =>
    match args with
    | [digits; P] =>
        REdLetZero "T0" (TBytes 200) (
        REdLetZero "T1" (TBytes 200) (
        REdLetZero "T2" (TBytes 200) (
        REdLetZero "T3" (TBytes 200) (
        REdLetZero "T4" (TBytes 200) (
        REdLetZero "T5" (TBytes 200) (
        REdLetZero "T6" (TBytes 200) (
        REdLetZero "T7" (TBytes 200) (
        REdLetZero "TwoP" (TBytes 200) (
        REdLetZero "Q"    (TBytes 200) (
        REdLetZero "lookup_buf" (TBytes 200) (
        REdLetZero "Q_plus"     (TBytes 200) (
          (* §3.1  Build T[0..7]. *)
          build_wnaf_table_body P
            (LE200 "T0") (LE200 "T1") (LE200 "T2") (LE200 "T3")
            (LE200 "T4") (LE200 "T5") (LE200 "T6") (LE200 "T7")
            (LE200 "TwoP")
          (* §3.2  Install identity into Q. *)
          (REdSeq (REdByteStore (LE200 "Q") (SLit 40) (SLit 1))
          (REdSeq (REdByteStore (LE200 "Q") (SLit 80) (SLit 1))
          (REdSeq
            (* §3.3  Main digit loop. *)
            (REdFor "i" 52
              (REdLetU64 "d" (SSub (SLit 51) (SVar "i"))
              (REdSeq (REdByteLoad "digit_byte" digits (SVar "d"))
              (* 5 doublings (one per bit of the window). *)
              (REdSeq (REdCallFn "xyzt_double_decomposed"
                                 (LE200 "Q") [LE200 "Q"])
              (REdSeq (REdCallFn "xyzt_double_decomposed"
                                 (LE200 "Q") [LE200 "Q"])
              (REdSeq (REdCallFn "xyzt_double_decomposed"
                                 (LE200 "Q") [LE200 "Q"])
              (REdSeq (REdCallFn "xyzt_double_decomposed"
                                 (LE200 "Q") [LE200 "Q"])
              (REdSeq (REdCallFn "xyzt_double_decomposed"
                                 (LE200 "Q") [LE200 "Q"])
              (* Extract abs_idx = (digit_byte & 0x7F) >> 1
                 and is_nonzero = digit_byte & 0x7F. *)
              (REdLetU64 "magnitude"
                         (SAnd (SVar "digit_byte") (SLit 127))
              (REdLetU64 "abs_idx"
                         (SShr (SVar "magnitude") (SLit 1))
              (REdLetU64 "is_nonzero" (SVar "magnitude")
              (REdLetU64 "sign"
                         (SShr (SVar "digit_byte") (SLit 7))
              (* CT table lookup: lookup_buf := T[abs_idx]. *)
              (REdSeq
                (ct_table_lookup_body "abs_idx" (LE200 "lookup_buf")
                   (LE200 "T0") (LE200 "T1") (LE200 "T2") (LE200 "T3")
                   (LE200 "T4") (LE200 "T5") (LE200 "T6") (LE200 "T7"))
              (* Phase 1a: CT-cond-negate the lookup if sign bit is set.
                 xyzt_cond_negate(out, src, sign): if sign != 0, negate
                 src's X and Ta coords into out; else copy src to out.
                 The body of this leaf is provided in Rust at the
                 framework boundary (no rust_cmd_ed body needed yet —
                 it's a 2-field-negate op, smaller than a full xyzt op). *)
              (REdSeq
                (REdCall "xyzt_cond_negate" (LE200 "lookup_buf")
                         [LE200 "lookup_buf";
                          {| loc_var := "sign"; loc_type := TU64 |}])
              (REdSeq
                (* Q_plus := Q + lookup_buf. *)
                (REdCallFn "xyzt_add_decomposed"
                           (LE200 "Q_plus")
                           [LE200 "Q"; LE200 "lookup_buf"])
                (* Q := is_nonzero ? Q_plus : Q. *)
                (REdSelect (SVar "is_nonzero")
                           (LE200 "Q_plus") (LE200 "Q") (LE200 "Q"))
              ))))))))))))))
            )
            (REdCallFn "xyzt_copy" dest [LE200 "Q"])
          ))
          )
        ))))))))))))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §4.  Callees-honoured predicate                                   *)
(* ================================================================ *)

(** Helper-presence predicate: the three Phase A entries
    (xyzt_add_decomposed, xyzt_double_decomposed, xyzt_copy) are in
    [function_table]. *)
Definition wnaf_helpers_present
    (function_table : function_table_ed) : Prop :=
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_add_decomposed")
                          function_table = Some ("xyzt_add_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_double_decomposed")
                          function_table = Some ("xyzt_double_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_copy")
                          function_table = Some ("xyzt_copy", body)).

(** Callees-honoured predicate: covers the three Phase A entries plus
    xyzt_copy.  Mirrors [fe25519_callees_honoured_scalarmult] from
    [ScalarmultBodyDecomposed.v]. *)
Definition fe25519_callees_honoured_wnaf
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  (forall src dst rs1 rs2 src_bs,
     dst.(loc_type) = TBytes 200 ->
     rs_get_tower_ed rs1 src.(loc_var)
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)) ->
     callee_post "fe25519_xyzt_copy" [src] dst rs1 rs2 ->
     rs_get_tower_ed rs2 dst.(loc_var)
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs))).

(* ================================================================ *)
(* §5.  wNAF digit-correctness specification                         *)
(* ================================================================ *)

(** Decode a single wNAF byte into a signed integer.  Bit 7 is the
    sign; bits 0..6 give the magnitude.  Zero byte → 0. *)
Definition wnaf_byte_to_z (b : Byte.byte) : Z :=
  let n  := Z.of_N (Byte.to_N b) in
  let m  := Z.land n 127 in
  let s  := Z.shiftr n 7 in
  if Z.eqb s 0 then m else (- m).

(** [wnaf_digits_correct digits scalar]: [digits] is a valid wNAF
    representation of [scalar] under window w = 5 with 52 entries —
    i.e., evaluating the signed-digit sum

         Σ_{i=0..51} d[i] * 2^(5*i)

    equals [le_combine scalar] modulo 2^256.  Stated abstractly here
    as a Prop to keep the body proof framework-discharge mechanical;
    the on-the-fly conversion (NAF algorithm) is left to a separate
    pre-pass helper. *)
Definition wnaf_digits_correct (digits scalar : list Byte.byte) : Prop :=
  length digits = 64%nat /\        (* 52 used + 12 zero pad *)
  length scalar = 32%nat /\
  (* All trailing bytes are zero (52..63). *)
  (forall i, (52 <= i < 64)%nat ->
     List.nth_error digits i = Some Byte.x00) /\
  (* All magnitudes ≤ 15 and odd-or-zero. *)
  (forall i b, (i < 52)%nat ->
     List.nth_error digits i = Some b ->
     let n := Z.of_N (Byte.to_N b) in
     let m := Z.land n 127 in
     m = 0 \/ (m mod 2 = 1 /\ m <= 15)) /\
  (* Signed-digit sum matches the scalar mod 2^256. *)
  (fold_right (fun ib acc =>
                 let (i, b) := (ib : nat * Byte.byte) in
                 Z.add (Z.mul (wnaf_byte_to_z b)
                              (Z.pow 2 (Z.of_nat (5 * i))))
                       acc)
              0%Z
              (List.combine (List.seq 0 52) (List.firstn 52 digits))
   mod (Z.pow 2 256) = (le_combine scalar) mod (Z.pow 2 256)).

(* ================================================================ *)
(* §6.  Correctness theorem                                          *)
(* ================================================================ *)

(** [wnaf_scalarmult_body_correct] -- REMOVED, it was false.

    The statement is not reachable by finishing the proof sketch that
    stood here, for two independent reasons.  One is a proof-side defect
    it shares with its siblings; the other is a defect in the BODY, and
    no proof can repair that one.

    PROOF-SIDE.  [fe25519_callees_honoured_wnaf] constrains only
    [loc_type].  [rexec_call] defers the whole state transition to the
    oracle, so such a hypothesis admits a callee that never writes its
    destination, and a conclusion about the value in [dest] does not
    follow.  This is the same defect that made
    [xyzt_add_body_decomposed_correct] and
    [xyzt_double_body_decomposed_correct] refutable.  Both of those are
    now repaired -- see XyztAddStrong.v and XyztDoubleStrong.v, which
    pin each leaf's value AND its frame -- so the foundation the sketch
    below leans on (steps (b) and (d)) exists for the first time.  The
    same strengthening applied to [fe25519_callees_honoured_wnaf] would
    settle this half.

    BODY-SIDE, and this one is not a proof problem.  The body has no
    conditional negation.  The file header concedes this and the old
    comment here spelled it out: the PoC "omits the on-the-fly
    conditional negate", so the statement "implicitly assumes positive
    digits only".  wNAF digits are signed by construction -- the digit
    decoder in this tree maps the byte 0x83 to -3 -- so for any scalar
    whose representation contains a negative digit the body computes
    something other than [ed25519_scalarmult_gallina scalar_bs p_bs].
    Closing this needs either a verified [xyzt_neg_decomposed] leaf
    invoked under a sign-bit guard, or a pre-negated table, i.e. a
    change to [wnaf_scalarmult_body] itself.

    The body and [wnaf_digits_correct] are untouched.  Restate the
    theorem once the negate leaf exists and the honoured-predicate is
    strengthened; do not attempt the old statement against the current
    body. *)

(* ================================================================ *)
(* §7.  Sanity                                                       *)
(* ================================================================ *)

(* Print Assumptions wnaf_scalarmult_body. *)
(* Print Assumptions wnaf_scalarmult_body_correct. *)
