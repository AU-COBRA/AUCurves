(** * CombScalarmultBody — comb-table fixed-base scalar multiplication
 *                          for Ed25519 sign (PoC).
 *
 *  Companion to [ScalarmultBaseBodyDecomposed.v] (Phase C of
 *  [docs/scalarmult-verification-plan.md]).  Implements a comb-table
 *  variant of fixed-generator scalar multiplication on the Ed25519
 *  base point B, structured around three [rust_cmd_ed] constructs:
 *
 *    - [REdFor "i" 64] : window-loop (counts 0..63, each a 4-bit nibble
 *      of the 32-byte scalar).
 *    - [REdCall "comb_table_lookup"] : leaf-call FFI that resolves
 *      T[i][digit] into a scratch 200-byte slot.  In real Rust output
 *      this is backed by a precomputed 64*16*200 = 204 800-byte static
 *      [u8] array (or, alternatively, dalek's [EdwardsBasepointTable]).
 *    - [REdCallFn "xyzt_add_decomposed"] : dispatch to the Phase A
 *      verified twisted-Edwards point-add body, mediated through
 *      [curve_function_table].
 *    - [REdSelect] : CT no-op skip on digit = 0 — picks between the
 *      adder's output and the running accumulator.
 *
 *  ## Algorithm (w = 4, 64 windows)
 *
 *      Q := identity
 *      for i in 0..64 {
 *        byte_idx     := i >> 1
 *        nibble_shift := (i & 1) * 4
 *        digit_i      := (scalar[byte_idx] >> nibble_shift) & 0xF
 *        T_lookup     := comb_table_lookup(i, digit_i)
 *                        (* T[i][digit_i] = digit_i * 16^i * B *)
 *        Q_plus       := Q + T_lookup
 *        Q            := digit_i == 0 ? Q : Q_plus   (* CT cmov *)
 *      }
 *      dest := Q
 *
 *  The table abstracts away the 204 KB of precomputed multiples — the
 *  PoC body is small and self-contained.  Performance: 64 conditional
 *  twisted-Edwards adds, ZERO doublings at runtime (cf. the 256
 *  double-and-add iterations in [scalarmult_body_decomposed]).
 *
 *  ## HONEST status
 *
 *  - Body Definition: closes under the global context (no axioms).
 *  - [comb_scalarmult_base_body_correct]: states the contract
 *    parallel to [scalarmult_base_body_decomposed_correct].  Reduces
 *    to a comb-window induction over the 64-step [REdFor] with an
 *    invariant relating the running [Q] to the partial sum
 *    [sum_{j<i} digit_j * 16^j * B].  Documented [Admitted].
 *  - Inherits the same outstanding obligations on
 *    [xyzt_add_decomposed_present] / [xyzt_copy_present] which
 *    propagate from the framework function-table dispatch.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBodyDecomposed.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0.  Local LE_TBytes helpers                                      *)
(* ================================================================ *)

Local Definition LE32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

(* ================================================================ *)
(* §1.  Comb-table fixed-base body                                   *)
(* ================================================================ *)

(** Body for the "comb_scalarmult_base" entry of [curve_function_table].

    Surface: one [located_ed] argument [scalar] (32-byte slot), one
    destination [dest] (200-byte xyzt slot).

    Layout (see §1 docstring for the algorithm sketch):

      let Q        : [u8; 200] = [0; 200];
      let T_lookup : [u8; 200] = [0; 200];
      let Q_plus   : [u8; 200] = [0; 200];

      Q[40] := 1;   /* Y[0] = 1 */
      Q[80] := 1;   /* Z[0] = 1 */
      /* Q now encodes the identity point (0, 1, 1, 0, 0). */

      for i in 0..64 {
        let byte_idx     : u64 = i >> 1;
        let nibble_shift : u64 = (i & 1) * 4;
        let scalar_byte  : u64 = scalar[byte_idx];
        let digit        : u64 = (scalar_byte >> nibble_shift) & 0xF;

        comb_table_lookup(T_lookup, i, digit);   /* FFI leaf */
        Q_plus := xyzt_add_decomposed(Q, T_lookup);   /* verified helper */
        Q := if digit == 0 { Q } else { Q_plus };     /* CT cmov */
      }

      dest := xyzt_copy(Q);                            /* verified helper */
*)
(** Inner body of the comb window-loop: one iteration. *)
Local Definition comb_window_iter (scalar : located_ed) : rust_cmd_ed :=
  REdLetU64 "byte_idx" (SShr (SVar "i") (SLit 1))
  (REdLetU64 "nibble_shift" (SMul (SAnd (SVar "i") (SLit 1)) (SLit 4))
  (REdSeq
    (REdByteLoad "scalar_byte" scalar (SVar "byte_idx"))
    (REdLetU64 "digit"
       (SAnd (SShr (SVar "scalar_byte") (SVar "nibble_shift")) (SLit 15))
       (REdSeq
         (REdCall "comb_table_lookup"
                  (LE200 "T_lookup")
                  [{| loc_var := "i";     loc_type := TU64 |};
                   {| loc_var := "digit"; loc_type := TU64 |}])
         (REdSeq
            (REdCallFn "xyzt_add_decomposed"
                       (LE200 "Q_plus")
                       [LE200 "Q"; LE200 "T_lookup"])
            (REdSelect (SVar "digit")
                       (LE200 "Q_plus")   (* digit <> 0 : take Q + T *)
                       (LE200 "Q")        (* digit  = 0 : no-op       *)
                       (LE200 "Q"))))))).

Definition comb_scalarmult_base_body : function_body_ed :=
  fun dest args =>
    match args with
    | [scalar] =>
        REdLetZero "Q"        (TBytes 200) (
          REdLetZero "T_lookup" (TBytes 200) (
            REdLetZero "Q_plus" (TBytes 200) (
              REdSeq (REdByteStore (LE200 "Q") (SLit 40) (SLit 1))
              (REdSeq (REdByteStore (LE200 "Q") (SLit 80) (SLit 1))
              (REdSeq
                (REdFor "i" 64 (comb_window_iter scalar))
                (REdCallFn "xyzt_copy" dest [LE200 "Q"]))))))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §2.  Helper-presence + leaf-contract predicates                   *)
(* ================================================================ *)

(** Presence of the "xyzt_add_decomposed" entry in [function_table],
    pointing at the Phase A verified body
    [XyztAddBodyDecomposed.xyzt_add_body_decomposed].

    Stated abstractly here (the lemma below does not load
    [XyztAddBodyDecomposed]) to keep the dependency surface small —
    consumers (e.g. [CurveBodies.v] linkage proofs) supply this
    witness by [exists xyzt_add_body_decomposed; split; [...]; reflexivity]
    at the call site. *)
Definition xyzt_add_decomposed_present
    (function_table : function_table_ed) : Prop :=
  exists body : function_body_ed,
    List.find (fun p => String.eqb (fst p) "xyzt_add_decomposed")
              function_table = Some ("xyzt_add_decomposed", body).

(** Presence of the "xyzt_copy" entry in [function_table], pointing at
    [XyztCopyBody.xyzt_copy_body]. *)
Definition xyzt_copy_present
    (function_table : function_table_ed) : Prop :=
  exists body : function_body_ed,
    List.find (fun p => String.eqb (fst p) "xyzt_copy")
              function_table = Some ("xyzt_copy", body).

(** Leaf-call contract for "comb_table_lookup":  after the call,
    the [T_lookup] dest slot holds exactly the 200-byte encoding of
    [digit * 16^win_idx * B] in extended-twisted-Edwards form.

    The leaf's Rust-side implementation is an indexed read into a
    static [u8; 64*16*200] table — in particular it is CT (selects
    among the 16 entries via mask-merge, never branching on [digit]).
    Verified by inspection of the generated Rust (the table itself
    being a precomputed constant outside the scope of this proof).

    For the lemma below the contract is captured abstractly: given
    well-formed bounded [win_idx, digit] (i.e. tracked via scalar slots),
    the post state writes [comb_table_entry win_idx digit] into the
    destination slot, where [comb_table_entry] is the Gallina spec of
    the precomputed table (deferred — defined as a single
    Parameter-free Gallina function over the base point B).

    NOTE: we leave the body of [comb_table_entry] abstract here — the
    correctness statement only relies on it being EQUAL to
    [encode_scalarmult (digit * 16^win_idx) B] in the comb-loop
    invariant.  See §3 for the consumed property. *)
Definition comb_table_entry (win_idx digit : Z) : list Byte.byte :=
  (* Gallina spec for T[win_idx][digit].  Concretely: encode (digit * 16^win_idx) B,
     reusing the existing 200-byte xyzt encoding from
     [ed25519_scalarmult_base_gallina] specialised at the scaled scalar.
     For the PoC we package it via a fresh 32-byte scalar that encodes
     [digit * 16^win_idx] (little-endian, zero-padded) and reuse the
     base body's Gallina spec.  Closes under [Init.Byte.byte] only —
     no axioms. *)
  let scaled : Z := digit * Z.pow 2 (4 * win_idx) in
  ed25519_scalarmult_base_gallina
    (coqutil.Word.LittleEndianList.le_split 32 scaled).

Lemma comb_table_entry_length :
  forall w d, length (comb_table_entry w d) = 200%nat.
Proof.
  intros w d. unfold comb_table_entry.
  apply ed25519_scalarmult_base_gallina_length.
Qed.

(** Leaf-callee-honoured predicate for the comb-table lookup. *)
Definition comb_table_lookup_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall (dest : located_ed) (i_loc digit_loc : located_ed)
         (rs1 rs2 : rust_state_ed) (win_v dig_v : Z),
    dest.(loc_type) = TBytes 200 ->
    i_loc.(loc_type) = TU64 ->
    digit_loc.(loc_type) = TU64 ->
    rs_get_scalar_ed rs1 i_loc.(loc_var)     = Some win_v ->
    rs_get_scalar_ed rs1 digit_loc.(loc_var) = Some dig_v ->
    0 <= win_v < 64 ->
    0 <= dig_v < 16 ->
    callee_post "comb_table_lookup" [i_loc; digit_loc] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (comb_table_entry win_v dig_v))).

(** Aggregated callees-honoured for the comb body.  Mirrors
    [fe25519_callees_honoured_scalarmult] from
    [ScalarmultBodyDecomposed.v] but extended with the
    [comb_table_lookup] leaf-contract. *)
Definition fe25519_callees_honoured_comb
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  comb_table_lookup_honoured callee_post
  /\ (forall src dst rs1 rs2 src_bs,
       dst.(loc_type) = TBytes 200 ->
       rs_get_tower_ed rs1 src.(loc_var)
         = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)) ->
       callee_post "fe25519_xyzt_copy" [src] dst rs1 rs2 ->
       rs_get_tower_ed rs2 dst.(loc_var)
         = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs))).

(* ================================================================ *)
(* §3.  Comb-loop Gallina partial-sum spec                           *)
(* ================================================================ *)

(** [comb_partial_sum scalar i]:  the partial scalar
    [sum_{j<i} digit_j * 16^j] over the low [i] nibbles of [scalar],
    where [digit_j] = the [j]-th 4-bit nibble of [scalar].

    Used as the loop invariant variable in
    [comb_scalarmult_base_body_correct]:  after [i] iterations of
    the comb-window loop, the running accumulator [Q] holds
    [ed25519_scalarmult_base_gallina (le_split 32 (comb_partial_sum
    scalar_bs i))]. *)
Fixpoint comb_partial_sum_nat (scalar : list Byte.byte) (i : nat) : Z :=
  match i with
  | O => 0
  | S k =>
      let byte_idx := (k / 2)%nat in
      let nibble   := (k mod 2)%nat in
      let b        := List.nth byte_idx scalar Byte.x00 in
      let digit    := Z.land (Z.shiftr (Z.of_N (Byte.to_N b))
                                       (Z.of_nat (4 * nibble))) 15 in
      comb_partial_sum_nat scalar k
      + digit * Z.pow 2 (4 * Z.of_nat k)
  end.

Definition comb_partial_sum (scalar : list Byte.byte) (i : Z) : Z :=
  comb_partial_sum_nat scalar (Z.to_nat i).

(* Imported here rather than in the header so that the surrounding
   definitions are elaborated in the same scope as before. *)
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Byte.
Require Import Stdlib.micromega.Lia.

(** The [n]-th byte of [l] read back out of the little-endian integer
    [le_combine l].  Holds unconditionally: past the end of [l] both
    sides are [0], by [le_combine_bound]. *)
Lemma comb_byte_nth_le_combine :
  forall (l : list Byte.byte) (n : nat),
    Z.of_N (Byte.to_N (List.nth n l Byte.x00))
    = (le_combine l / 2 ^ (8 * Z.of_nat n)) mod 256.
Proof.
  intros l n.
  destruct (Nat.lt_ge_cases n (length l)) as [Hlt | Hge].
  - assert (Hn : List.nth n l Byte.x00
                 = byte.of_Z (Z.shiftr (le_combine l) (8 * Z.of_nat n))).
    { rewrite <- List.nth_default_eq.
      rewrite <- (nth_default_le_split n (length l) (le_combine l) Hlt Byte.x00).
      rewrite split_le_combine. reflexivity. }
    rewrite Hn.
    pose proof (byte.unsigned_of_Z (Z.shiftr (le_combine l) (8 * Z.of_nat n))) as Hu.
    unfold byte.unsigned, byte.wrap in Hu.
    rewrite Hu.
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity.
  - rewrite List.nth_overflow by assumption.
    pose proof (le_combine_bound l) as Hb.
    rewrite Z.div_small.
    + reflexivity.
    + split; [lia|].
      eapply Z.lt_le_trans; [apply Hb|].
      apply Z.pow_le_mono_r; lia.
Qed.

(** Same, in bitwise form. *)
Lemma comb_byte_nth_land :
  forall (l : list Byte.byte) (n : nat),
    Z.of_N (Byte.to_N (List.nth n l Byte.x00))
    = Z.land (Z.shiftr (le_combine l) (8 * Z.of_nat n)) 255.
Proof.
  intros l n. rewrite comb_byte_nth_le_combine.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

(** The nibble [comb_partial_sum_nat] extracts at index [k] — the
    [(k mod 2)]-th nibble of byte [k / 2] — is the [k]-th nibble of
    [le_combine l]. *)
Lemma comb_nibble_le_combine :
  forall (l : list Byte.byte) (k : nat),
    Z.land (Z.shiftr (Z.of_N (Byte.to_N (List.nth (k / 2)%nat l Byte.x00)))
                     (Z.of_nat (4 * (k mod 2))%nat)) 15
    = Z.land (Z.shiftr (le_combine l) (4 * Z.of_nat k)) 15.
Proof.
  intros l k.
  rewrite comb_byte_nth_land.
  assert (Hkd : (k = 2 * (k / 2) + k mod 2)%nat) by (apply Nat.div_mod_eq).
  replace (4 * Z.of_nat k)
    with (8 * Z.of_nat (k / 2)%nat + Z.of_nat (4 * (k mod 2))%nat) by lia.
  rewrite <- Z.shiftr_shiftr by lia.
  set (Y := Z.shiftr (le_combine l) (8 * Z.of_nat (k / 2)%nat)).
  assert (Hk : (k mod 2 = 0 \/ k mod 2 = 1)%nat)
    by (pose proof (Nat.mod_upper_bound k 2); lia).
  destruct Hk as [Hk | Hk]; rewrite Hk.
  - change (Z.of_nat (4 * 0)%nat) with 0.
    rewrite !Z.shiftr_0_r, <- Z.land_assoc. reflexivity.
  - change (Z.of_nat (4 * 1)%nat) with 4.
    rewrite Z.shiftr_land, <- Z.land_assoc. reflexivity.
Qed.

(** The partial sum over the low [m] nibbles is exactly the low [4m]
    bits of the scalar. *)
Lemma comb_partial_sum_nat_mod :
  forall (l : list Byte.byte) (m : nat),
    comb_partial_sum_nat l m = le_combine l mod 2 ^ (4 * Z.of_nat m).
Proof.
  intros l m. induction m as [|k IH].
  - cbn [comb_partial_sum_nat].
    change (4 * Z.of_nat 0%nat) with 0. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  - cbn [comb_partial_sum_nat]. rewrite IH, comb_nibble_le_combine.
    change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    replace (4 * Z.of_nat (S k)) with (4 * Z.of_nat k + 4) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; lia).
    change (2 ^ 4) with 16. lia.
Qed.

(** At [i = 64], the partial sum covers all 256 bits of the scalar and
    equals the integer encoded by [scalar]. *)
Lemma comb_partial_sum_full :
  forall scalar,
    length scalar = 32%nat ->
    comb_partial_sum scalar 64
    = coqutil.Word.LittleEndianList.le_combine scalar.
Proof.
  intros scalar Hlen. unfold comb_partial_sum.
  rewrite comb_partial_sum_nat_mod.
  pose proof (le_combine_bound scalar) as Hb. rewrite Hlen in Hb.
  replace (2 ^ (8 * Z.of_nat 32%nat)) with (2 ^ (4 * Z.of_nat (Z.to_nat 64))) in Hb
    by (f_equal; reflexivity).
  apply Z.mod_small. exact Hb.
Qed.

(* ================================================================ *)
(* §4.  Correctness theorem                                          *)
(* ================================================================ *)

(** Main correctness statement.

    Under the comb-leaf + Phase A helper contracts and the presence
    of the dispatch entries in [function_table], the comb body
    computes [ed25519_scalarmult_base_gallina scalar_bs] in [dest].

    PROOF STRATEGY (see §3 for the comb-partial-sum invariant):

    1. Inversion through 3 [REdLetZero] frames and 2 [REdByteStore]
       initialisations: after these, the [Q] slot encodes the identity
       point (0, 1, 1, 0, 0) in extended-twisted-Edwards form.
       (Reuses the identity-point lemma from [ScalarmultVerified.v].)

    2. Comb-window induction on the [REdFor "i" 64] loop with
       invariant:

         After [j] iterations have completed, [Q] holds
         [ed25519_scalarmult_base_gallina
           (le_split 32 (comb_partial_sum scalar_bs j))].

       Base case [j = 0]: [Q] = identity = scalarmult by 0 of B.

       Inductive step: one iteration reads the [j]-th nibble [digit_j]
       of [scalar_bs], looks up [T[j][digit_j]] via the leaf
       [comb_table_lookup] (uses [comb_table_lookup_honoured] in
       [Hhonoured]).  Then the [REdCallFn "xyzt_add_decomposed"]
       computes [Q_plus = Q + T[j][digit_j]], and the [REdSelect]
       picks [Q_plus] if [digit_j ≠ 0] else [Q] (CT cmov).

       Either way, the new [Q] equals
       [Q_old + digit_j * 16^j * B]
       (the [digit_j = 0] case is correct because adding identity is
       a no-op AND skipping it via CT cmov coincides with the same
       result by the comb spec).

       Equivalent under the invariant to
       [scalarmult_base_gallina (le_split 32 (comb_partial_sum
        scalar_bs (j+1)))].

    3. Terminal case [j = 64]: by [comb_partial_sum_full],
       [comb_partial_sum scalar_bs 64 = le_combine scalar_bs];
       conclude via the existing [le_split (le_combine scalar_bs)
       = scalar_bs] roundtrip (length 32, all 256 bits live).

    4. Final [REdCallFn "xyzt_copy"] dispatches into
       [xyzt_copy_body] and copies [Q] to [dest], preserving the
       invariant value.

    COST: ~150 LoC of induction + invariant threading + 5-10
    inversion frames.  No new mathematical axioms enter — the proof
    reduces purely to the Phase A bodies' correctness theorems +
    the [comb_table_lookup] leaf contract + the partial-sum identity
    in §3.  Documented [Admitted] parallel to
    [scalarmult_body_decomposed_correct] in
    [ScalarmultBodyDecomposed.v]. *)
Theorem comb_scalarmult_base_body_correct :
  forall callee_post callee_post_n function_table
         (scalar dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (scalar_bs dest_init : list Byte.byte),
    xyzt_add_decomposed_present function_table ->
    xyzt_copy_present function_table ->
    fe25519_callees_honoured_comb callee_post ->
    length scalar_bs = 32%nat ->
    length dest_init = 200%nat ->
    dest.(loc_type) = TBytes 200 ->
    scalar.(loc_type) = TBytes 32 ->
    (* hygiene: dest's slot disjoint from internal scratch slots *)
    dest.(loc_var) <> "Q"%string ->
    dest.(loc_var) <> "T_lookup"%string ->
    dest.(loc_var) <> "Q_plus"%string ->
    scalar.(loc_var) <> "Q"%string ->
    scalar.(loc_var) <> "T_lookup"%string ->
    scalar.(loc_var) <> "Q_plus"%string ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    rs_get_tower_ed rs1 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 dest_init)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (comb_scalarmult_base_body dest [scalar]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_base_gallina scalar_bs))).
Proof.
  (* See §4 docstring for the proof strategy.  Reduces to:
       1. 3× [rexec_let_zero] inversion (Q, T_lookup, Q_plus init),
       2. 2× [rexec_byte_store] inversion (Q[40] = 1, Q[80] = 1),
       3. comb-window induction over [REdFor "i" 64] with the
          partial-sum invariant from §3,
       4. terminal [rexec_callfn "xyzt_copy"] inversion +
          [xyzt_copy_present] resolution.
     No new mathematical axioms — only the framework dispatch and
     the comb-partial-sum identity in §3. *)
Admitted.

(* ================================================================ *)
(* §5.  Sanity                                                       *)
(* ================================================================ *)

(* Print Assumptions comb_scalarmult_base_body. *)
(* Print Assumptions comb_table_entry. *)
(* Print Assumptions comb_scalarmult_base_body_correct. *)
