(** * Ristretto255_DecodeReject — Phase B.3 rejection theorems for the
    Ristretto255 decoder.

    Three generic rejection theorems characterising when
    [ristretto_decode_coords] / [ristretto_decode_bytes] return [None],
    plus one lemma per invalid encoding of RFC 9496 Appendix A.2, as
    recorded in [Ristretto255_Decode.v] (29 vectors, in the RFC's groups):

      [rfc_A2_noncanonical_01..04]  non-canonical field encodings (4)
      [rfc_A2_negative_01..08]      negative field elements (8)
      [rfc_A2_nonsquare_01..08]     non-square x^2 (8)
      [rfc_A2_negative_xy_01..08]   negative x * y value (8)
      [rfc_A2_s_minus_one_01]       s = -1, which causes y = 0 (1)

    and an aggregate lemma [rfc_A2_rejection_vectors_rejected] stating
    that every element of [rfc_A2_rejection_vectors] is rejected.

    All three generic theorems are pure case analysis on the decoder's
    [match] / [if] cascade — no field-arithmetic obligations.  Per-vector
    lemmas are discharged by

      (a) generic theorem 1 (structural form) for the 4 non-canonical
          vectors, with [bytes_to_canonical_F v = None] obtained by a
          boolean reduction, and
      (b) for the other 25, a boolean reduction
          [match ristretto_decode_coords v with None => true | Some _ =>
          false end = true] closed by [vm_compute; reflexivity].

    Running [vm_compute] on the [option (Fp * Fp)] goal itself normalizes
    the type [F.F (2^255-19)] and does not finish in Rocq 9.2; the
    boolean reduction avoids this.

    Companion files:
      - Ristretto255_Encode.v  (Phase A.1, §4.3.2 encode)
      - Ristretto255_Decode.v  (Phase A.2, §4.3.1 decode + vectors)

    Status: all three generic theorems Qed; 2 lifted [decode_bytes]
    corollaries Qed; helper [option_pair_eq_convoy_None] Qed; all 29
    per-vector lemmas and the aggregate lemma Qed. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).

(** ** Generic theorem 1 — non-canonical encoding ⇒ reject.

    If [bs] either has length ≠ 32, has bit 255 set, OR encodes an
    integer ≥ p, then [bytes_to_canonical_F bs = None] and hence
    [ristretto_decode_coords bs = None].  This corresponds to RFC 9496
    §4.3.1 line 2.

    We state the theorem in two complementary forms: a "structural"
    form keyed on [bytes_to_canonical_F = None] (used by per-vector
    application), and a "semantic" form keyed on the [LE_to_Z] / length
    hypotheses (matching the plan's spec).
*)

Theorem ristretto_decode_coords_rejects_non_canonical_struct :
  forall bs : list Byte.byte,
    bytes_to_canonical_F bs = None ->
    ristretto_decode_coords bs = None.
Proof.
  intros bs H.
  unfold ristretto_decode_coords.
  rewrite H.
  reflexivity.
Qed.

Theorem ristretto_decode_coords_rejects_non_canonical :
  forall bs : list Byte.byte,
    length bs = 32%nat ->
    (Z.testbit (le_combine bs) 255 = true \/
     le_combine bs >= 2^255 - 19) ->
    ristretto_decode_coords bs = None.
Proof.
  intros bs Hlen Hbad.
  apply ristretto_decode_coords_rejects_non_canonical_struct.
  unfold bytes_to_canonical_F.
  rewrite (proj2 (Nat.eqb_eq _ _) Hlen).
  destruct Hbad as [Hbit | Hge].
  - rewrite Hbit. reflexivity.
  - destruct (Z.testbit (le_combine bs) 255); [reflexivity|].
    destruct (Z.ltb_spec (le_combine bs) (2^255 - 19)); [lia|reflexivity].
Qed.

(** ** Generic theorem 2 — negative s ⇒ reject.

    If [bytes_to_canonical_F bs = Some s] and [is_negative s = true],
    then [ristretto_decode_coords bs = None].  This corresponds to RFC
    9496 §4.3.1 line 3. *)

Theorem ristretto_decode_coords_rejects_negative :
  forall (bs : list Byte.byte) (s : Fp),
    bytes_to_canonical_F bs = Some s ->
    is_negative s = true ->
    ristretto_decode_coords bs = None.
Proof.
  intros bs s Hbtc Hneg.
  unfold ristretto_decode_coords.
  rewrite Hbtc.
  rewrite Hneg.
  reflexivity.
Qed.

(** ** Generic theorem 3 — rejection after the sqrt branch.

    Captures the union of RFC 9496 §4.3.1 line 13's three rejection
    disjuncts: [not was_square], [is_negative t], or [y = 0].  We
    express it as a single combinator over the decoder's local-let body.

    The hypothesis names the three local quantities by their RFC
    spelling so the per-vector callers can pick the appropriate
    disjunct. *)

Theorem ristretto_decode_coords_rejects_post_sqrt :
  forall (bs : list Byte.byte) (s : Fp),
    bytes_to_canonical_F bs = Some s ->
    is_negative s = false ->
    (let ss     := (s * s)%F in
     let u1     := (Fone - ss)%F in
     let u2     := (Fone + ss)%F in
     let u2_sqr := (u2 * u2)%F in
     let u1_sq  := (u1 * u1)%F in
     let v      := (F.opp (Curve25519.E.d * u1_sq) - u2_sqr)%F in
     let p_sqrt := sqrt_ratio_m1 Fone (v * u2_sqr)%F in
     let invsqrt    := snd p_sqrt in
     let was_square := fst p_sqrt in
     let Dx     := (invsqrt * u2)%F in
     let Dy     := (invsqrt * Dx * v)%F in
     let x      := abs (F.of_Z _ 2 * s * Dx)%F in
     let y      := (u1 * Dy)%F in
     let t      := (x * y)%F in
     orb (negb was_square)
         (orb (is_negative t) (Z.eqb (F.to_Z y) 0))) = true ->
    ristretto_decode_coords bs = None.
Proof.
  intros bs s Hbtc Hneg Hreject.
  unfold ristretto_decode_coords.
  rewrite Hbtc, Hneg.
  cbv zeta in Hreject |- *.
  (* Both [Hreject] and the goal mention the same [sqrt_ratio_m1] call,
     but the decoder destructs it as a pair while [Hreject] projects
     [fst]/[snd].  Destruct the pair on both sides simultaneously. *)
  destruct (sqrt_ratio_m1 Fone _) as [ws iv] eqn:Hsqrt;
    cbn [fst snd] in Hreject; rewrite Hreject; reflexivity.
Qed.

(** ** Corollary: lifted rejection theorems for the typed
    [ristretto_decode_bytes] (which is just [ristretto_decode_coords]
    threaded through an on-curve obligation). *)

(** Helper combinator: a generic [match ... eq_refl] convoy on an
    [option (A1 * A2)] returns [None] whenever the scrutinee is
    [None].  This is just the [None] reduction case made
    syntactically obvious so callers don't have to wrestle with
    dependent rewriting. *)
Lemma option_pair_eq_convoy_None :
  forall (A1 A2 B : Type) (oa : option (A1 * A2))
         (f : forall x y, oa = Some (x, y) -> B),
    oa = None ->
    (match oa as r return oa = r -> option B with
     | None        => fun _ => None
     | Some (x, y) =>
         fun H : oa = Some (x, y) => Some (f x y H)
     end eq_refl) = None.
Proof.
  intros A1 A2 B oa f Hnone.
  destruct oa as [[x y]|]; [discriminate Hnone | reflexivity].
Qed.

Lemma ristretto_decode_bytes_None_of_coords :
  forall on_curve_obligation bs,
    ristretto_decode_coords bs = None ->
    ristretto_decode_bytes on_curve_obligation bs = None.
Proof.
  intros on_curve_obligation bs Hcoords.
  unfold ristretto_decode_bytes.
  exact (option_pair_eq_convoy_None
           Fp Fp _ _
           (fun x y H => exist _ (x, y) (on_curve_obligation bs x y H))
           Hcoords).
Qed.

Theorem ristretto_decode_bytes_rejects_non_canonical :
  forall on_curve_obligation bs,
    length bs = 32%nat ->
    (Z.testbit (le_combine bs) 255 = true \/
     le_combine bs >= 2^255 - 19) ->
    ristretto_decode_bytes on_curve_obligation bs = None.
Proof.
  intros on_curve_obligation bs Hlen Hbad.
  apply ristretto_decode_bytes_None_of_coords.
  apply ristretto_decode_coords_rejects_non_canonical; assumption.
Qed.

Theorem ristretto_decode_bytes_rejects_negative :
  forall on_curve_obligation bs s,
    bytes_to_canonical_F bs = Some s ->
    is_negative s = true ->
    ristretto_decode_bytes on_curve_obligation bs = None.
Proof.
  intros on_curve_obligation bs s Hbtc Hneg.
  apply ristretto_decode_bytes_None_of_coords.
  eapply ristretto_decode_coords_rejects_negative; eassumption.
Qed.

(** ============================================================
    RFC 9496 §A.2 — per-vector rejection lemmas (29).

    Two small helpers turn a [None] goal into a [bool] equality, which
    [vm_compute; reflexivity] closes without normalizing the type
    [F.F (2^255-19)].
============================================================ *)

Lemma bytes_to_canonical_F_None_of_bool :
  forall bs : list Byte.byte,
    match bytes_to_canonical_F bs with None => true | Some _ => false end = true ->
    bytes_to_canonical_F bs = None.
Proof.
  intros bs H. destruct (bytes_to_canonical_F bs); [discriminate H | reflexivity].
Qed.

Lemma decode_coords_None_of_bool :
  forall bs : list Byte.byte,
    match ristretto_decode_coords bs with None => true | Some _ => false end = true ->
    ristretto_decode_coords bs = None.
Proof.
  intros bs H. destruct (ristretto_decode_coords bs); [discriminate H | reflexivity].
Qed.

(** *** Non-canonical field encodings (4) — generic theorem 1. *)

Lemma rfc_A2_noncanonical_01_rejects :
  ristretto_decode_coords rfc_A2_noncanonical_01 = None.
Proof.
  apply ristretto_decode_coords_rejects_non_canonical_struct.
  apply bytes_to_canonical_F_None_of_bool. vm_compute. reflexivity.
Qed.

Lemma rfc_A2_noncanonical_02_rejects :
  ristretto_decode_coords rfc_A2_noncanonical_02 = None.
Proof.
  apply ristretto_decode_coords_rejects_non_canonical_struct.
  apply bytes_to_canonical_F_None_of_bool. vm_compute. reflexivity.
Qed.

Lemma rfc_A2_noncanonical_03_rejects :
  ristretto_decode_coords rfc_A2_noncanonical_03 = None.
Proof.
  apply ristretto_decode_coords_rejects_non_canonical_struct.
  apply bytes_to_canonical_F_None_of_bool. vm_compute. reflexivity.
Qed.

Lemma rfc_A2_noncanonical_04_rejects :
  ristretto_decode_coords rfc_A2_noncanonical_04 = None.
Proof.
  apply ristretto_decode_coords_rejects_non_canonical_struct.
  apply bytes_to_canonical_F_None_of_bool. vm_compute. reflexivity.
Qed.

(** *** Negative field elements (8). *)

Lemma rfc_A2_negative_01_rejects :
  ristretto_decode_coords rfc_A2_negative_01 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_02_rejects :
  ristretto_decode_coords rfc_A2_negative_02 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_03_rejects :
  ristretto_decode_coords rfc_A2_negative_03 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_04_rejects :
  ristretto_decode_coords rfc_A2_negative_04 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_05_rejects :
  ristretto_decode_coords rfc_A2_negative_05 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_06_rejects :
  ristretto_decode_coords rfc_A2_negative_06 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_07_rejects :
  ristretto_decode_coords rfc_A2_negative_07 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_08_rejects :
  ristretto_decode_coords rfc_A2_negative_08 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

(** *** Non-square x^2 (8). *)

Lemma rfc_A2_nonsquare_01_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_01 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_02_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_02 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_03_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_03 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_04_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_04 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_05_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_05 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_06_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_06 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_07_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_07 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_nonsquare_08_rejects :
  ristretto_decode_coords rfc_A2_nonsquare_08 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

(** *** Negative x * y value (8). *)

Lemma rfc_A2_negative_xy_01_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_01 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_02_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_02 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_03_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_03 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_04_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_04 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_05_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_05 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_06_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_06 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_07_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_07 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

Lemma rfc_A2_negative_xy_08_rejects :
  ristretto_decode_coords rfc_A2_negative_xy_08 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

(** *** s = -1, which causes y = 0 (1). *)

Lemma rfc_A2_s_minus_one_01_rejects :
  ristretto_decode_coords rfc_A2_s_minus_one_01 = None.
Proof. apply decode_coords_None_of_bool. vm_compute. reflexivity. Qed.

(** ** Aggregate: every vector in [rfc_A2_rejection_vectors] is rejected. *)

Lemma rfc_A2_rejection_vectors_rejected :
  List.Forall (fun v => ristretto_decode_coords v = None) rfc_A2_rejection_vectors.
Proof.
  unfold rfc_A2_rejection_vectors.
  apply Forall_cons; [exact rfc_A2_noncanonical_01_rejects|].
  apply Forall_cons; [exact rfc_A2_noncanonical_02_rejects|].
  apply Forall_cons; [exact rfc_A2_noncanonical_03_rejects|].
  apply Forall_cons; [exact rfc_A2_noncanonical_04_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_01_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_02_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_03_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_04_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_05_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_06_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_07_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_08_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_01_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_02_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_03_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_04_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_05_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_06_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_07_rejects|].
  apply Forall_cons; [exact rfc_A2_nonsquare_08_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_01_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_02_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_03_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_04_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_05_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_06_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_07_rejects|].
  apply Forall_cons; [exact rfc_A2_negative_xy_08_rejects|].
  apply Forall_cons; [exact rfc_A2_s_minus_one_01_rejects|].
  apply Forall_nil.
Qed.

Corollary rfc_A2_rejection_vectors_rejected_forall :
  forall v, List.In v rfc_A2_rejection_vectors -> ristretto_decode_coords v = None.
Proof.
  apply List.Forall_forall, rfc_A2_rejection_vectors_rejected.
Qed.

(** ** Phase B.3 deliverables:
      - 3 generic rejection theorems (non-canonical / negative s /
        post-sqrt), each Qed.
      - 29 of 29 RFC 9496 §A.2 vector lemmas Qed: 4 non-canonical via
        generic theorem 1, 25 (8 negative, 8 non-square, 8 negative
        x * y, 1 s = -1) via the boolean [vm_compute] reduction.
      - The aggregate [rfc_A2_rejection_vectors_rejected] (Forall) and
        its [In] form, Qed.
      - Two lifted corollaries on [ristretto_decode_bytes] (the typed
        version threaded through the Phase-B on-curve obligation).
      - One [option_pair_eq_convoy_None] helper lemma extracting the
        [None]-branch reduction of the dependent convoy.
*)
