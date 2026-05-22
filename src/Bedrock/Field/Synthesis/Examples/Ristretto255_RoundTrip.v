(** * Ristretto255_RoundTrip — Phase B.1 round-trip theorems.
 *
 * RFC 9496 §4 dictates two round-trip properties:
 *
 *   (T1) [encode -> decode] recovers an equivalent point (modulo the
 *        ristretto255 quotient by E[4]):
 *
 *          on_main_subgroup P  ->
 *          exists Q,
 *            ristretto_decode_bytes (ristretto_encode_bytes P) = Some Q /\
 *            is_4torsion (P - Q).
 *
 *   (T2) [decode -> encode] is the identity on canonical byte strings:
 *
 *          length bs = 32  ->
 *          ristretto_decode_bytes bs = Some P  ->
 *          ristretto_encode_bytes P = bs.
 *
 * Both theorems factor through the SAME hard algebraic lemma — that the
 * canonical-representative selection (RFC 9496 §4.3.2 steps 10-13) picks
 * the same byte string for any two ristretto-equivalent inputs.  See the
 * companion plan [BLS/writeup/RISTRETTO255_ENCODING_PLAN.md] §3 and §7.1
 * for the Jacobi-quartic detour path; that proof is estimated at 200-400
 * LoC and is the [canonical_rep_selection] lemma below.
 *
 * Strategy of this file:
 *   1.  State the auxiliary predicates ([on_main_subgroup], [is_4torsion],
 *       [point_sub]) over the Curve25519 affine [E.point] view.
 *   2.  State and partially prove the structural decomposition lemmas
 *       ([roundtrip_struct], [encode_decoded_bytes]).
 *   3.  Prove the two round-trip theorems modulo the algebraic
 *       [canonical_rep_selection] / [sqrt_ratio_m1_correct] lemmas
 *       (Admitted with explicit TODO).
 *
 * Sister files:
 *   - [Ristretto255_Encode.v]       (A.1, RFC 9496 §4.3.2)
 *   - [Ristretto255_Decode.v]       (A.2, RFC 9496 §4.3.1)
 *   - [Ristretto255_DecodeReject.v] (B.3, RFC 9496 §A.2 rejection vectors)
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Open Scope F_scope.

(* ========================================================================
   Section 1: Auxiliary predicates over Edwards25519 points.

   We work with affine coordinates [(x, y) : Fp * Fp] satisfying the
   Edwards25519 on-curve equation.  These are the same coordinates the
   Phase-A.2 decoder returns.  For points represented as the typed
   sigma [Curve25519.E.point], we project to coordinates via
   [E.coordinates].

   The encoder takes extended coordinates [(X, Y, Z, T)]; we provide
   [to_extended] which lifts the affine pair [(x, y)] to [(x, y, 1, x*y)]
   matching the standard projective embedding [Z := 1].
   ======================================================================== *)

(** ** [to_extended (x, y)] — lift affine -> extended (Z := 1, T := x*y). *)
Definition to_extended (xy : Fp * Fp) : Fp * Fp * Fp * Fp :=
  let '(x, y) := xy in (x, y, Fone, (x * y)%F).

(** ** [point_coords P] — extract affine [(x, y)] from a typed point. *)
Definition point_coords (P : Curve25519.E.point) : Fp * Fp :=
  proj1_sig P.

(** ** [is_4torsion_affine (x, y)] — same definition as the spec in
       [Crypto.Spec.Ristretto255], specialised to our [Fp].

    The 4-torsion subgroup E[4] for Edwards25519 consists of exactly
    four points (cf. RFC 9496 §4.1):

      O   = (0, 1)      — identity (order 1)
      T1  = (0, -1)     — order 2
      T2  = (SQRT_M1, 0)  — order 4
      T3  = (-SQRT_M1, 0) — order 4
*)
Definition is_4torsion_affine (xy : Fp * Fp) : Prop :=
  let '(x, y) := xy in
     (x = Fzero /\ y = Fone)
  \/ (x = Fzero /\ y = F.opp Fone)
  \/ (x = SQRT_M1 /\ y = Fzero)
  \/ (x = F.opp SQRT_M1 /\ y = Fzero).

(** ** [point_sub P Q] — Edwards subtraction at the [E.point] level.

    [E.add(opp Q) P] would be the standard formulation but [opp] lives
    in [Crypto.Curves.Edwards.AffineProofs.E.opp].  For this file's
    purposes we work directly on coordinates: subtraction in the
    Edwards group is [P + (- Q)] where [-(x, y) = (-x, y)] (cf.
    [AffineProofs.E.opp]). *)
Definition opp_affine (xy : Fp * Fp) : Fp * Fp :=
  let '(x, y) := xy in (F.opp x, y).

Definition sub_affine (P Q : Fp * Fp) : Fp * Fp :=
  let '(x1, y1) := P in
  let '(x2, y2) := opp_affine Q in
  let denx := (Fone + Curve25519.E.d * x1 * x2 * y1 * y2)%F in
  let deny := (Fone - Curve25519.E.d * x1 * x2 * y1 * y2)%F in
  (((x1 * y2 + y1 * x2) / denx)%F,
   ((y1 * y2 - Curve25519.E.a * x1 * x2) / deny)%F).

(** ** [is_4torsion P Q] — the ristretto-equivalence relation.

    [P] and [Q] are ristretto-equivalent iff their Edwards difference
    [P - Q] lies in the 4-torsion subgroup. *)
Definition ristretto_equiv (P Q : Curve25519.E.point) : Prop :=
  is_4torsion_affine (sub_affine (point_coords P) (point_coords Q)).

(** ** [on_main_subgroup P] — [P] has order dividing [l].

    The Edwards25519 group has order [8 * l] (cofactor 8); the prime-
    order subgroup is the image of the Ed25519 basepoint.  We carry
    the predicate abstractly here — the round-trip theorems care only
    that the input is a representative of a [ristretto_point] (= coset
    of E[4]) which is automatic when [P] is on the main subgroup
    (since the only main-subgroup-AND-4-torsion point is the identity).

    Concretely, [P] is on the main subgroup iff there exists a scalar
    [k : Z] with [P = k * B] where [B] is the Ed25519 basepoint.  We
    use an abstract characterisation to keep this file independent of
    the concrete scalar-mult implementation. *)
(** We model "P is on the main subgroup" abstractly as a predicate
    [on_main_subgroup_pred P].  The concrete definition (existence of
    a scalar [k] with [P = k * B]) is intentionally kept opaque at
    this layer to avoid threading [E.mul]'s six implicit field
    parameters through the round-trip theorem.  A future refinement
    can replace [on_main_subgroup] with the concrete characterisation
    and re-prove the theorems unchanged. *)
Definition on_main_subgroup (P : Curve25519.E.point) : Prop :=
  (* The Phase-B downstream proof will instantiate this with the
     concrete scalar-mult predicate; meanwhile, the round-trip theorem
     uses it only as a hypothesis (no destruction). *)
  True.

(* ========================================================================
   Section 2: The canonical-representative selection lemma.

   This is THE hard algebraic content (per plan §7.1).  We state it
   precisely here and admit the proof — the body would be ~200-400 LoC
   following a Jacobi-quartic detour (cf. Hamburg's Decaf paper, §5;
   de Valence et al.'s Ristretto note, §3).
   ======================================================================== *)

(** ** [canonical_rep_selection] — the key algebraic invariant.

    For any two extended-Edwards representatives of the SAME ristretto
    quotient class, the canonical-representative selection (RFC §4.3.2
    steps 7-13) yields the same field element [s].  In particular:

      P, Q : E.point  with  ristretto_equiv P Q
      ===>
      ristretto_encode (to_extended (point_coords P))
      =  ristretto_encode (to_extended (point_coords Q))

    PROOF STRATEGY (TODO):
      - Cf. Hamburg "Decaf: Eliminating cofactors through point
        compression" (CRYPTO 2015), §5.  The Jacobi-quartic detour
        gives a 1:1 correspondence between cosets of E[4] in the
        Edwards model and points on a related Jacobi quartic; the
        canonical-rep selection in step 10 of the encoder is exactly
        the choice of the unique Jacobi-quartic representative.
      - Cf. de Valence et al., "The Ristretto Group" technical note,
        §3.2, for the explicit ristretto-equivalence relation and its
        coset structure.
      - Concrete Rocq path: introduce a [JacobiQuartic25519] module
        (~150 LoC), define the [JQ <-> E/E[4]] isomorphism (~100 LoC),
        prove the canonical-rep selection on the JQ side where it
        reduces to absolute-value uniqueness in a field (~100 LoC),
        transport via the isomorphism (~50 LoC).  Estimated 400 LoC
        total.

    This lemma is the SOLE blocker for the encode-then-decode and
    decode-then-encode theorems below; with it the rest of the file
    discharges. *)
Lemma canonical_rep_selection :
  forall (P Q : Curve25519.E.point),
    ristretto_equiv P Q ->
    ristretto_encode_bytes (to_extended (point_coords P))
    = ristretto_encode_bytes (to_extended (point_coords Q)).
Proof.
  (* TODO Phase B (200-400 LoC):  Jacobi-quartic detour.  See the
     [canonical_rep_selection] docstring for the proof plan. *)
Admitted.

(* ========================================================================
   Section 3: [sqrt_ratio_m1] correctness.

   Per RFC 9496 §3.1.3, [sqrt_ratio_m1 u v] returns [(was_square, r)]
   such that:
     was_square = true   <->  v * r^2 = u
     was_square = false  <->  v * r^2 = SQRT_M1 * u
   AND [r] has [is_negative r = false].

   This characterisation feeds into BOTH round-trip theorems via the
   following pattern: in the encoder, the [invsqrt] satisfies
   [u1 * (u2^2) * invsqrt^2 = 1], so [den1 = invsqrt * u1] and [den2
   = invsqrt * u2] are well-defined inverses of [u2] and [u1*u2] (up
   to signs); in the decoder, the [invsqrt] satisfies [u^2 * v *
   invsqrt^2 = 1], so [den_x = invsqrt * u] is an inverse of [u*v]^{1/2}.
   ======================================================================== *)

(** ** [sqrt_ratio_m1_correct] — algebraic invariant of [sqrt_ratio_m1].

    PROOF STRATEGY (TODO):
      - The body of [sqrt_ratio_m1] is RFC's [p mod 8 = 5] shortcut:
        [r0 := u * v^3 * (u * v^7)^((p-5)/8)] guarantees [v * r0^2
        in {u, -u, SQRT_M1 * u, -SQRT_M1 * u}], and the [check] branch
        picks the right sign.
      - The proof factors through Fermat's little theorem ([F.pow x
        (p - 1) = 1]) plus the [p mod 8 = 5] arithmetic, both of
        which are present in [PrimeFieldTheorems] but not directly
        applicable to abstract [F.pow] without unfolding.
      - Estimated 100-200 LoC.  Standard but tedious.

    Used by the round-trip theorems to discharge the [den_x],
    [den_y] inverses in the decoder. *)
Lemma sqrt_ratio_m1_correct :
  forall (u v : Fp),
    v <> Fzero ->
    let '(was_square, r) := sqrt_ratio_m1 u v in
    ((was_square = true  /\ (v * r * r)%F = u) \/
     (was_square = false /\ (v * r * r)%F = (SQRT_M1 * u)%F))
    /\ is_negative r = false.
Proof.
  (* TODO Phase B (100-200 LoC).  See docstring. *)
Admitted.

(** Corollary: when [sqrt_ratio_m1 1 (u^2 * v)] reports a square, the
    invsqrt satisfies [(u^2 * v) * invsqrt^2 = 1] (used in the decoder
    body to argue [den_x * u^2 * v = u^2]).  The hypothesis [Hnz : u*u*v
    <> 0] is exposed because [sqrt_ratio_m1_correct] requires the
    denominator to be nonzero; in the decoder this is provided by the
    [was_square = true] branch already failing fast on the rejection
    side. *)
Lemma sqrt_ratio_m1_decode_invariant :
  forall (s : Fp),
    let ss := (s * s)%F in
    let u  := (Fone - ss)%F in
    let v  := (Curve25519.E.d * ss - Fone)%F in
    (u * u * v)%F <> Fzero ->
    forall ws iv,
      sqrt_ratio_m1 Fone (u * u * v)%F = (ws, iv) ->
      ws = true ->
      ((u * u * v) * iv * iv)%F = Fone.
Proof.
  intros s ss u v Hnz ws iv Hcall Hws.
  pose proof (sqrt_ratio_m1_correct Fone (u * u * v)%F Hnz) as Hcorrect.
  rewrite Hcall in Hcorrect.
  destruct Hcorrect as [Hdisj _].
  destruct Hdisj as [[_ Heqq]|[Hwsf _]]; [exact Heqq | congruence].
Qed.

(* ========================================================================
   Section 4: Structural roundtrip lemmas.

   These don't depend on [canonical_rep_selection] — they package the
   length/shape invariants that DO hold unconditionally.
   ======================================================================== *)

(** ** [encode_decode_bytes_length_preserved] — the encode-then-decode
    pipeline preserves length 32 unconditionally.  This is purely
    syntactic. *)
Lemma encode_bytes_length_32 : forall P,
  length (ristretto_encode_bytes P) = 32%nat.
Proof. apply ristretto_encode_bytes_length. Qed.

(** ** [bytes_to_canonical_F_le_combine] — the canonical parse is just
    [le_combine] (modulo the rejection guards). *)
Lemma bytes_to_canonical_F_of_split :
  forall z,
    0 <= z < 2^255 - 19 ->
    bytes_to_canonical_F (le_split 32 z) = Some (F.of_Z _ z).
Proof.
  intros z [Hlo Hhi].
  unfold bytes_to_canonical_F.
  rewrite length_le_split. cbn [Nat.eqb].
  rewrite le_combine_split.
  assert (Hp256 : (2 ^ (Z.of_nat 32 * 8) = 2 * 2 ^ 255)%Z).
  { change (Z.of_nat 32 * 8)%Z with 256%Z.
    replace 256%Z with (255 + 1)%Z by reflexivity.
    rewrite Z.pow_add_r by lia. ring. }
  assert (Hzlt255 : (z < 2 ^ 255)%Z) by lia.
  assert (Hmod : (z mod 2 ^ (Z.of_nat 32 * 8) = z)%Z).
  { apply Z.mod_small. split; [lia|]. rewrite Hp256. lia. }
  rewrite Hmod.
  assert (Hbit : Z.testbit z 255 = false).
  { apply Z.testbit_false; [lia|].
    rewrite Z.div_small; [reflexivity|]. split; [lia|]. assumption. }
  rewrite Hbit.
  destruct (Z.ltb_spec z (2^255 - 19)); [reflexivity|lia].
Qed.

(** ** [le_split_of_F] — re-decoding [le_split 32 (F.to_Z s)] for any
    [s : Fp] recovers [s]. *)
Lemma le_split_F_round_trip :
  forall (s : Fp),
    bytes_to_canonical_F (le_split 32 (F.to_Z s)) = Some s.
Proof.
  intros s.
  destruct s as [z Hz]. cbn [F.to_Z proj1_sig].
  assert (Hbnd : (0 <= z < 2^255 - 19)%Z).
  { rewrite Hz.
    pose proof (Z.mod_pos_bound z (2^255 - 19)%Z) as Hb.
    assert ((2 ^ 255 - 19 > 0)%Z) by (cbv; reflexivity).
    apply Hb. lia. }
  rewrite (bytes_to_canonical_F_of_split z Hbnd).
  f_equal. unfold F.of_Z.
  set (P := fun z0 : Z => z0 = z0 mod Z.pos p) in *.
  generalize (ModularArithmetic.F.of_Z_obligation_1 p z).
  intros e.
  assert (Heq : ((z mod Z.pos p) = z)%Z) by (symmetry; assumption).
  generalize e; rewrite Heq; intros e0.
  f_equal. apply Eqdep_dec.UIP_dec.
  decide equality; apply Pos.eq_dec.
Qed.

(* ========================================================================
   Section 5: The two round-trip theorems.

   Both are stated against the typed [edwards25519_point] interface
   per the plan.  Note that [ristretto_decode_bytes] in
   [Ristretto255_Decode.v] is parameterised on an [on_curve_obligation];
   we take that as a hypothesis ("the Phase-B on-curve lemma") so the
   roundtrip statements compose with whatever discharges it.
   ======================================================================== *)

(** A reified version of the on-curve obligation, exposed so the
    round-trip theorems can be applied without forcing the caller to
    commit to its proof. *)
Definition OnCurveObligation : Type :=
  forall (bs : list Byte.byte) (x y : Fp),
    ristretto_decode_coords bs = Some (x, y) ->
    (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F.

(** Helper: a typed [E.point] satisfies the on-curve equation by
    construction (drop-out from [proj2_sig]). *)
Lemma typed_point_on_curve :
  forall (P : Curve25519.E.point),
    let '(x, y) := point_coords P in
    (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F.
Proof.
  intros P.
  destruct P as [[x y] Hxy]. cbn [point_coords proj1_sig].
  exact Hxy.
Qed.

(** ** Theorem 1 (encode-then-decode round-trip).

    For any point [P] on the main (prime-order) subgroup of
    Edwards25519, [encode P] followed by [decode] recovers a point
    [Q] equal to [P] modulo the ristretto255 quotient (i.e. their
    Edwards difference is a 4-torsion element).

    PROOF SKETCH (the algebraic content is in [canonical_rep_selection]):

      1.  By the encoder spec, [s := ristretto_encode P] is a
          well-defined field element in [Fp].
      2.  By [le_split_F_round_trip], [bytes_to_canonical_F
          (ristretto_encode_bytes P) = Some s].
      3.  By the decoder's branch structure and [sqrt_ratio_m1_correct],
          the decoder's [(x', y')] reconstruct a valid extended-Edwards
          point [(x', y', 1, x'*y')] that is a representative of the
          SAME ristretto quotient class as [P].
      4.  Equivalence in the quotient is exactly [is_4torsion (P - Q)].

    Step 3 is the deepest step; it factors into:
      (a) the decoder's [u^2 * v] is a square iff the input came from
          a valid encoding (uses [canonical_rep_selection] to argue
          existence of the square root);
      (b) the decoder's [(x, y)] satisfy [a*x^2 + y^2 = 1 + d*x^2*y^2]
          (the on-curve obligation, dischargeable by the Z-mirror in
          [Bedrock.End2End.Lizard.RistrettoDecode]);
      (c) the resulting [(x, y, 1, x*y)] is in the same E[4]-coset
          as [P]'s extended representation. *)
Theorem ristretto_encode_decode_roundtrip :
  forall (on_curve_obligation : OnCurveObligation) (P : Curve25519.E.point),
    on_main_subgroup P ->
    exists Q : Curve25519.E.point,
      ristretto_decode_bytes on_curve_obligation
        (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q
      /\ ristretto_equiv P Q.
Proof.
  intros oc P Hmain.
  (* The proof needs [canonical_rep_selection] (admitted above) PLUS
     the Phase-B on-curve obligation supplied by the caller PLUS the
     [sqrt_ratio_m1] correctness (admitted above).  Each of the three
     enables one of steps 1, 2, 3 in the sketch above.

     The full reconstruction proof would unfold both
     [ristretto_encode_bytes] and [ristretto_decode_bytes] and trace
     the field-element through the 14-step encode followed by the
     14-step decode, using [sqrt_ratio_m1_correct] at the two
     sqrt-branch points.  Conservative estimate: 300-500 LoC of
     case analysis on the [rotate] branch of the encoder and the
     [was_square] branch of the decoder. *)
  (* TODO Phase B.1 (300-500 LoC): see proof sketch in docstring. *)
Admitted.

(** ** Theorem 2 (decode-then-encode round-trip).

    Every valid byte string is the unique encoding of the point it
    decodes to.  Equivalently: the encoder is the canonical inverse
    of the decoder on its image.

    PROOF SKETCH:
      1.  By [le_split_F_round_trip] + the decoder's parse guard,
          [s := le_combine bs (mod p)] is a well-defined [Fp].
      2.  The decoder produces affine [(x, y)] such that re-encoding
          [(x, y, 1, x*y)] runs the encoder pipeline.  The encoder's
          canonical-representative selection (steps 10-13) picks
          exactly the [s] from step 1 (NOT just an equivalent
          representative — bytewise equal).
      3.  Hence [le_split 32 (F.to_Z s) = bs].

    Step 2 is again the algebraic core, requiring
    [canonical_rep_selection] specialised to "the decoded point
    encodes back to the same s".  This is a STRENGTHENING of
    [canonical_rep_selection]: not just "any two equivalent
    representatives map to the same byte string", but "the unique
    canonical representative IS the decoder's output". *)
Theorem ristretto_decode_encode_roundtrip :
  forall (on_curve_obligation : OnCurveObligation) (bs : list Byte.byte),
    length bs = 32%nat ->
    forall (P : Curve25519.E.point),
      ristretto_decode_bytes on_curve_obligation bs = Some P ->
      ristretto_encode_bytes (to_extended (point_coords P)) = bs.
Proof.
  intros oc bs Hlen P Hdec.
  (* The proof factors as:
       a. Argue [bytes_to_canonical_F bs = Some s] for some [s] (else
          [ristretto_decode_coords bs = None] and [Hdec] contradicts).
       b. Argue the decoder's [(x, y)] satisfy [x*y = ...] expressions
          in terms of [s] (from [sqrt_ratio_m1_correct]).
       c. Push through the encoder pipeline to derive
          [ristretto_encode (to_extended (x, y)) = s].
       d. Apply [le_split_F_round_trip] to recover [bs] (using that
          [bytes_to_canonical_F bs = Some s] forces [bs = le_split 32
          (F.to_Z s)]).

     Step (c) is the canonical-rep selection in DECODER-FACING form:
     not "P ~ Q implies same byte string" but "the explicit (x, y)
     produced by the decoder is THE canonical representative of its
     coset".  This is a slightly different shape from
     [canonical_rep_selection] above and would need its own (or a
     refined) admitted lemma. *)
  (* TODO Phase B.1 (200-400 LoC): see proof sketch in docstring. *)
Admitted.

(* ========================================================================
   Section 6: Trivial corollaries from the structural lemmas.

   These DO NOT depend on the admitted [canonical_rep_selection] /
   [sqrt_ratio_m1_correct] and are useful sanity checks plus building
   blocks for callers.
   ======================================================================== *)

(** ** The pipeline preserves the 32-byte invariant. *)
Theorem encode_then_decode_length_invariant :
  forall (oc : OnCurveObligation) P,
    length (ristretto_encode_bytes (to_extended (point_coords P))) = 32%nat.
Proof.
  intros oc P. apply encode_bytes_length_32.
Qed.

(** Helper combinator: same trick as sister file's
    [option_pair_eq_convoy_None].  Lets us discharge the [None]
    branch of [ristretto_decode_bytes] without triggering the
    dependent-rewrite obstacle. *)
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

(** Helper: lift [ristretto_decode_coords bs = None] to
    [ristretto_decode_bytes oc bs = None]. *)
Lemma ristretto_decode_bytes_None_of_coords :
  forall (oc : OnCurveObligation) bs,
    ristretto_decode_coords bs = None ->
    ristretto_decode_bytes oc bs = None.
Proof.
  intros oc bs Hcoords.
  unfold ristretto_decode_bytes.
  exact (option_pair_eq_convoy_None
           Fp Fp _ _
           (fun x y H => exist _ (x, y) (oc bs x y H))
           Hcoords).
Qed.

(** ** If the decoder returns [Some], the input must have been a
       canonical 32-byte string. *)
Theorem decode_some_implies_canonical :
  forall (oc : OnCurveObligation) bs P,
    ristretto_decode_bytes oc bs = Some P ->
    length bs = 32%nat /\
    exists s : Fp, bytes_to_canonical_F bs = Some s.
Proof.
  intros oc bs P Hdec.
  destruct (bytes_to_canonical_F bs) as [s|] eqn:Hbtc.
  - split; [| eauto].
    unfold bytes_to_canonical_F in Hbtc.
    destruct (Nat.eqb (length bs) 32) eqn:Hlen32; [|discriminate].
    apply Nat.eqb_eq. exact Hlen32.
  - exfalso.
    assert (Hcoords : ristretto_decode_coords bs = None).
    { unfold ristretto_decode_coords. rewrite Hbtc. reflexivity. }
    rewrite (ristretto_decode_bytes_None_of_coords oc bs Hcoords)
            in Hdec.
    discriminate.
Qed.

(** ** Length corollary of [ristretto_decode_encode_roundtrip] —
    holds unconditionally (no admit dependency). *)
Theorem decode_encode_length :
  forall (oc : OnCurveObligation) bs P,
    length bs = 32%nat ->
    ristretto_decode_bytes oc bs = Some P ->
    length (ristretto_encode_bytes (to_extended (point_coords P))) = length bs.
Proof.
  intros oc bs P Hlen Hdec.
  rewrite encode_bytes_length_32. symmetry. assumption.
Qed.

(* ========================================================================
   Phase B.1 deliverables summary:

   STATED (with full algebraic shape):
     - ristretto_encode_decode_roundtrip  (Theorem 1)
     - ristretto_decode_encode_roundtrip  (Theorem 2)
     - canonical_rep_selection            (algebraic core lemma)
     - sqrt_ratio_m1_correct              (sqrt-ratio invariant)

   QED:
     - bytes_to_canonical_F_of_split      (structural parse lemma)
     - le_split_F_round_trip              (F-level round trip on parse)
     - sqrt_ratio_m1_decode_invariant     (decoder's sqrt corollary)
     - typed_point_on_curve               (sigma-type projection)
     - encode_then_decode_length_invariant
     - decode_some_implies_canonical
     - decode_encode_length

   ADMITTED (with TODOs and proof strategy):
     - canonical_rep_selection            (Jacobi-quartic detour, 200-400 LoC)
     - sqrt_ratio_m1_correct              (FLT + p≡5 mod 8, 100-200 LoC)
     - ristretto_encode_decode_roundtrip  (300-500 LoC, factors through above)
     - ristretto_decode_encode_roundtrip  (200-400 LoC, factors through above)

   Total admit count: 4 (2 algebraic lemmas + 2 theorems).  All four
   are factored into a clean dependency graph so future agents can
   discharge them in order:

     1.  sqrt_ratio_m1_correct       (base)
     2.  canonical_rep_selection     (relies on 1)
     3.  ristretto_decode_encode_roundtrip   (relies on 1, 2)
     4.  ristretto_encode_decode_roundtrip   (relies on 1, 2, on_curve obligation)
   ======================================================================== *)
