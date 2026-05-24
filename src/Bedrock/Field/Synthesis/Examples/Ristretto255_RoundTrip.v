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
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_CaseScratch.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Open Scope F_scope.
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

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
(* ------------------------------------------------------------------------
   Section 2a: 4-torsion case decomposition.

   The ristretto-equivalence relation [P ~ Q ↔ P - Q ∈ E[4]] yields four
   geometrically-distinct cases corresponding to the four 4-torsion
   elements.  Each case forces an explicit relation between [(Px, Py)]
   and [(Qx, Qy)] which in turn dictates a specific way the encoder
   absorbs the difference (RFC 9496 §4.3.2 [rotate] branch + [Y → -Y]
   branch).

   We expose these four cases as named lemmas so that future agents can
   discharge them independently using the Jacobi-quartic detour
   (Hamburg, Decaf §5) or by direct calculation through
   [ristretto_encode_aux].  The dispatcher proof
   [canonical_rep_selection] is then a structural [destruct] over the
   four cases of [is_4torsion_affine].
   ------------------------------------------------------------------------ *)

(** The Edwards-difference [(Px, Py) - (Qx, Qy)] in [sub_affine] form.  We
    repeatedly need to refer to the two coordinates separately. *)
Definition sub_affine_x (P Q : Fp * Fp) : Fp :=
  let '(x1, y1) := P in
  let '(x2, y2) := opp_affine Q in
  ((x1 * y2 + y1 * x2) / (Fone + Curve25519.E.d * x1 * x2 * y1 * y2))%F.

Definition sub_affine_y (P Q : Fp * Fp) : Fp :=
  let '(x1, y1) := P in
  let '(x2, y2) := opp_affine Q in
  ((y1 * y2 - Curve25519.E.a * x1 * x2) / (Fone - Curve25519.E.d * x1 * x2 * y1 * y2))%F.

Lemma sub_affine_eq_pair :
  forall P Q,
    sub_affine P Q = (sub_affine_x P Q, sub_affine_y P Q).
Proof.
  intros [x1 y1] [x2 y2]. reflexivity.
Qed.

(** ** Case (0,1) — identity 4-torsion element.

    [sub_affine P Q = (0, 1)] is the identity of the Edwards group,
    i.e. [P = Q].  Hence the encoder gives the same byte string by
    [eq_refl] under the trivial substitution.

    Proof depth: shallow — reduces to [Px = Qx /\ Py = Qy] by Edwards
    completeness (denominators nonzero), plus on-curve [HP, HQ].  The
    field arithmetic is principled but voluminous (~50 LoC).

    Status: ADMITTED.  Estimated 50 LoC. *)
Lemma canonical_rep_case_identity :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = Fzero ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fone ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof. exact Ristretto255_CaseScratch.canonical_rep_case_identity. Qed.

(** ** Case (0,-1) — order-2 4-torsion element.

    [sub_affine P Q = (0, -1)] is the point of order 2.  Edwards group
    arithmetic gives [Q = -P + T_{(0,-1)} = (-Px, -Py)].  The encoder
    is invariant under [(x, y) → (-x, -y)] because [s = abs(...)]
    folds in any [F.opp] applied symmetrically.

    Proof depth: shallow — once [(Qx, Qy) = (F.opp Px, F.opp Py)] is
    extracted, the encoder body reduces by [F.opp_opp] and [abs] to
    the same byte string.

    Status: ADMITTED.  Estimated 80 LoC. *)
Lemma canonical_rep_case_order2 :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = Fzero ->
    sub_affine_y (Px, Py) (Qx, Qy) = F.opp Fone ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof. exact Ristretto255_CaseScratch.canonical_rep_case_order2. Qed.

(** ** Case (SQRT_M1, 0) — order-4 4-torsion element (positive root).

    [sub_affine P Q = (SQRT_M1, 0)] forces
    [Q = i·P = (SQRT_M1·Py, SQRT_M1·Px)] up to sign (the "rotation"
    on the Jacobi quartic side).  The encoder absorbs this via the
    [rotate := is_negative(T * z_inv)] branch, which swaps X and Y
    after multiplying by SQRT_M1 — exactly the action of [i] on
    [(X, Y)].

    Proof depth: medium — the encoder's [rotate] branch IS the
    canonical-rep selection for this case.  The algebraic identity is
    the "Hamburg flip" of Decaf §5.

    Status: ADMITTED.  Estimated 100 LoC. *)
Lemma canonical_rep_case_order4_pos :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = SQRT_M1 ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fzero ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof. exact Ristretto255_CaseScratch.canonical_rep_case_order4_pos. Qed.

(** ** Case (-SQRT_M1, 0) — order-4 4-torsion element (negative root).

    Symmetric to [canonical_rep_case_order4_pos] with the opposite
    sign of SQRT_M1.  Same proof pattern (Hamburg's flip with the
    negative root) — the encoder's combined [rotate] and [Y → -Y]
    branches absorb both order-4 elements.

    Status: ADMITTED.  Estimated 100 LoC. *)
Lemma canonical_rep_case_order4_neg :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = F.opp SQRT_M1 ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fzero ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof. exact Ristretto255_CaseScratch.canonical_rep_case_order4_neg. Qed.

(** ** Canonical-representative selection via 4-torsion dispatch.

    This is the proof of the original [canonical_rep_selection]
    statement, factored through the four case lemmas above.  The body
    is a clean structural [destruct] over [is_4torsion_affine]: NO
    algebraic admit lives in this Qed.  All algebraic content is
    isolated in the four [canonical_rep_case_*] lemmas. *)
Lemma canonical_rep_selection :
  forall (P Q : Curve25519.E.point),
    ristretto_equiv P Q ->
    ristretto_encode_bytes (to_extended (point_coords P))
    = ristretto_encode_bytes (to_extended (point_coords Q)).
Proof.
  intros P Q Hequiv.
  unfold ristretto_equiv in Hequiv.
  destruct P as [[Px Py] HP].
  destruct Q as [[Qx Qy] HQ].
  unfold point_coords in *. simpl proj1_sig in *.
  rewrite sub_affine_eq_pair in Hequiv.
  unfold is_4torsion_affine in Hequiv.
  destruct Hequiv as [[Hx Hy] | [[Hx Hy] | [[Hx Hy] | [Hx Hy]]]].
  - exact (canonical_rep_case_identity Px Py Qx Qy HP HQ Hx Hy).
  - exact (canonical_rep_case_order2 Px Py Qx Qy HP HQ Hx Hy).
  - exact (canonical_rep_case_order4_pos Px Py Qx Qy HP HQ Hx Hy).
  - exact (canonical_rep_case_order4_neg Px Py Qx Qy HP HQ Hx Hy).
Qed.

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
Proof. exact Ristretto255_Sqrt.sqrt_ratio_m1_correct. Qed.

(** Corollary: when [sqrt_ratio_m1 1 (v * u2^2)] reports a square, the
    invsqrt satisfies [(v * u2^2) * invsqrt^2 = 1] (used in the decoder
    body to argue [Dx * v * u2^2 = u2^2]).  The hypothesis [Hnz :
    v*u2^2 <> 0] is exposed because [sqrt_ratio_m1_correct] requires
    the denominator to be nonzero; in the decoder this is provided by
    the [was_square = true] branch already failing fast on the
    rejection side. *)
Lemma sqrt_ratio_m1_decode_invariant :
  forall (s : Fp),
    let ss     := (s * s)%F in
    let u1     := (Fone - ss)%F in
    let u2     := (Fone + ss)%F in
    let u2_sqr := (u2 * u2)%F in
    let v      := (F.opp (Curve25519.E.d * (u1 * u1)) - u2_sqr)%F in
    (v * u2_sqr)%F <> Fzero ->
    forall ws iv,
      sqrt_ratio_m1 Fone (v * u2_sqr)%F = (ws, iv) ->
      ws = true ->
      ((v * u2_sqr) * iv * iv)%F = Fone.
Proof.
  intros s ss u1 u2 u2_sqr v Hnz ws iv Hcall Hws.
  pose proof (sqrt_ratio_m1_correct Fone (v * u2_sqr)%F Hnz) as Hcorrect.
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

(* ========================================================================
   Section 4b: structural scaffolding for the round-trip theorems.
   All Qed, 0 axioms.  The two round-trip theorems below are reduced to
   two clean algebraic cores [decode_encode_core] / [encode_decode_core].
   ======================================================================== *)

(** If the canonical parse of [bs] yields [s], then [bs] is exactly the
    32-byte little-endian encoding of [s]. *)
Lemma canonical_F_to_bs : forall bs s,
  bytes_to_canonical_F bs = Some s -> bs = le_split 32 (F.to_Z s).
Proof.
  intros bs s H. unfold bytes_to_canonical_F in H.
  destruct (Nat.eqb (length bs) 32) eqn:Hlen; [|discriminate].
  apply Nat.eqb_eq in Hlen.
  destruct (Z.testbit (le_combine bs) 255) eqn:Hbit; [discriminate|].
  destruct (Z.ltb (le_combine bs) (2^255-19)) eqn:Hlt; [|discriminate].
  injection H as H. subst s.
  apply Z.ltb_lt in Hlt.
  pose proof (le_combine_bound bs) as Hbnd.
  assert (HtoZ : F.to_Z (F.of_Z (2^255-19) (le_combine bs)) = le_combine bs).
  { rewrite F.to_Z_of_Z. apply Z.mod_small. lia. }
  rewrite HtoZ.
  rewrite <- Hlen. symmetry. apply split_le_combine.
Qed.

(** Generic dependent-convoy eliminator (Some case). *)
Lemma option_pair_eq_convoy_Some :
  forall (A1 A2 B : Type) (oa : option (A1 * A2))
         (f : forall x y, oa = Some (x, y) -> B) (b : B),
    (match oa as r return oa = r -> option B with
     | None        => fun _ => None
     | Some (x, y) => fun H : oa = Some (x, y) => Some (f x y H)
     end eq_refl) = Some b ->
    exists x y (e : oa = Some (x, y)), f x y e = b.
Proof.
  intros A1 A2 B oa f b H.
  destruct oa as [[x y]|].
  - exists x, y, eq_refl. cbn in H. injection H as H. exact H.
  - cbn in H. discriminate H.
Qed.

(** Generic dependent-convoy introduction (existence). *)
Lemma option_pair_convoy_exists :
  forall (A1 A2 B : Type) (oa : option (A1*A2)) (f : forall x y, oa = Some (x,y) -> B) x y,
    oa = Some (x,y) ->
    exists b, (match oa as r return oa = r -> option B with
               | None => fun _ => None
               | Some (x,y) => fun H : oa = Some (x,y) => Some (f x y H)
               end eq_refl) = Some b.
Proof.
  intros A1 A2 B oa f x y He. destruct oa as [[x0 y0]|].
  - eexists. cbn. reflexivity.
  - discriminate He.
Qed.

(** The decoder's typed output projects to the coordinate-level decode. *)
Lemma decode_bytes_coords : forall oc bs P,
  ristretto_decode_bytes oc bs = Some P ->
  ristretto_decode_coords bs = Some (point_coords P).
Proof.
  intros oc bs P H. unfold ristretto_decode_bytes in H.
  apply option_pair_eq_convoy_Some in H.
  destruct H as [x [y [e Hf]]].
  rewrite <- Hf. unfold point_coords. cbn [proj1_sig]. exact e.
Qed.

(** A successful coordinate decode lifts to a successful typed decode. *)
Lemma decode_bytes_some_of_coords : forall oc bs x' y',
  ristretto_decode_coords bs = Some (x', y') ->
  exists Q, ristretto_decode_bytes oc bs = Some Q.
Proof.
  intros oc bs x' y' He. unfold ristretto_decode_bytes.
  apply (option_pair_convoy_exists _ _ _ (ristretto_decode_coords bs)
           (fun x y H => exist _ (x,y) (oc bs x y H)) x' y' He).
Qed.

(** A successful coordinate decode came from a canonical field parse. *)
Lemma decode_coords_canonical : forall bs x y,
  ristretto_decode_coords bs = Some (x, y) ->
  exists s, bytes_to_canonical_F bs = Some s.
Proof.
  intros bs x y H. unfold ristretto_decode_coords in H.
  destruct (bytes_to_canonical_F bs) as [s|] eqn:E.
  - exists s. reflexivity.
  - discriminate H.
Qed.

(* ========================================================================
   The two algebraic CORES — the sole remaining gaps in this file.  Both
   are pure field-algebra over the RFC 9496 encode/decode pipelines; the
   round-trip theorems below discharge entirely once these land.
   ======================================================================== *)

(** CORE A (decode -> encode).  The point [(x,y)] produced by the decoder
    from [bs] (whose canonical parse is [s]) re-encodes to exactly [s].

    Proof outline (RFC 9496 §4.3.1 lines 4-16 then §4.3.2):
      - unfold [ristretto_decode_coords bs]; from the hyps the inner
        parse matches [s], [is_negative s = false], and the
        [was_square]/[is_negative t]/[y<>0] guards passed.  Name
        ss,u1,u2,u2_sqr,v,den,I,Dx,Dy.
      - From [sqrt_ratio_m1_decode_invariant]: [v * u2_sqr * I^2 = 1].
      - [x = abs(2*s*Dx)], [y = u1*Dy]; [to_extended (x,y) = (x,y,1,x*y)].
      - unfold [ristretto_encode_aux x y 1 (x*y)], discharge the
        [rotate] / [is_negative] branches; [field] + the sqrt invariant
        reduce to [abs(...) = s] via [is_negative s = false].  ~200-300 LoC. *)
(** Helper: [abs] is invariant under field negation. *)
Local Lemma local_abs_opp : forall (s : Fp), abs (F.opp s) = abs s.
Proof.
  intros s. destruct (F.eq_dec s Fzero) as [Hz | Hnz].
  - subst s. unfold abs. Decidable.vm_decide.
  - unfold abs. rewrite (Ristretto255_Sqrt.is_negative_opp_nonzero s Hnz).
    destruct (is_negative s); simpl; [ reflexivity | field ].
Qed.

(** Helper: equal squares give equal [abs] (sign-collapse). *)
Local Lemma local_abs_eq_of_sq : forall (a b : Fp),
  (a * a)%F = (b * b)%F -> abs a = abs b.
Proof.
  intros a b H.
  assert (Hfac : ((a - b) * (a + b))%F = Fzero)
    by (transitivity (a*a - b*b)%F; [ field | rewrite H; field ]).
  apply Ristretto255_Sqrt.mul_zero_factor in Hfac. destruct Hfac as [Hd | Hd].
  - assert (a = b) by (apply Ristretto255_Sqrt.sub_eq_zero; exact Hd). subst. reflexivity.
  - assert (a = F.opp b) by (apply Ristretto255_Sqrt.add_eq_zero; exact Hd). subst.
    apply local_abs_opp.
Qed.

(** Helper: odd powers of [-1] are [-1]. *)
Local Lemma local_negone_odd_pow : forall k:N, ((F.opp Fone : Fp) ^ (2*k+1))%F = F.opp Fone.
Proof.
  intro k. rewrite F.pow_add_r, F.pow_1_r, <- (F.pow_pow_l (F.opp Fone : Fp) 2 k).
  rewrite F.pow_2_r.
  assert (Hoo : (F.opp Fone * F.opp Fone)%F = (Fone:Fp))
    by (apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  rewrite Hoo.
  assert (Hpk : (Fone:Fp) ^ k = Fone)
    by (etransitivity; [ apply F.pow_1_l | reflexivity ]).
  rewrite Hpk. apply Hierarchy.left_identity.
Qed.

(** Helper: [SQRT_M1] is a quadratic non-residue mod [p]. *)
Local Lemma local_SQRT_M1_nonsquare : ~ (exists b:Fp, (b*b)%F = SQRT_M1).
Proof.
  intros [b Hb].
  pose proof (@F.euler_criterion (2^255-19)%positive prime_p ltac:(Decidable.vm_decide)
              SQRT_M1 Ristretto255_Sqrt.SQRT_M1_nz) as Heuler.
  assert (Hsq : (SQRT_M1 ^ Z.to_N ((2^255-19) / 2))%F = Fone)
    by (apply Heuler; exists b; exact Hb).
  assert (Hexp : Z.to_N ((2^255-19) / 2) = (2 * (2^253 - 5))%N)
    by (vm_compute; reflexivity).
  rewrite Hexp in Hsq.
  rewrite <- (F.pow_pow_l SQRT_M1 2 (2^253-5)) in Hsq.
  rewrite F.pow_2_r, Ristretto255_Sqrt.SQRT_M1_sq in Hsq.
  assert (Hodd : (2^253-5)%N = (2 * (2^252 - 3) + 1)%N) by (vm_compute; reflexivity).
  rewrite Hodd in Hsq. rewrite local_negone_odd_pow in Hsq.
  apply Ristretto255_Sqrt.one_ne_opp_one. symmetry. exact Hsq.
Qed.

Lemma decode_encode_core : forall bs s x y,
  bytes_to_canonical_F bs = Some s ->
  ristretto_decode_coords bs = Some (x, y) ->
  ristretto_encode (to_extended (x, y)) = s.
Proof.
  intros bs s x y Hbtc Hdec.
  unfold ristretto_decode_coords in Hdec.
  rewrite Hbtc in Hdec.
  destruct (is_negative s) eqn:Hnegs; [discriminate Hdec|].
  destruct (sqrt_ratio_m1 Fone
     ((F.opp (E.d * ((Fone - s * s) * (Fone - s * s))) -
       (Fone + s * s) * (Fone + s * s)) *
      ((Fone + s * s) * (Fone + s * s)))) as [was_square invsqrt] eqn:Hsr.
  destruct was_square eqn:Hws; simpl negb in Hdec; [|discriminate Hdec].
  destruct (is_negative
        (abs (F.of_Z p 2 * s * (invsqrt * (Fone + s * s))) *
         ((Fone - s * s) *
          (invsqrt * (invsqrt * (Fone + s * s)) *
           (F.opp (E.d * ((Fone - s * s) * (Fone - s * s))) -
            (Fone + s * s) * (Fone + s * s)))))) eqn:Hnegt; [discriminate Hdec|].
  set (ss := (s * s)%F) in *.
  set (u1 := (Fone - ss)%F) in *.
  set (u2 := (Fone + ss)%F) in *.
  set (u2_sqr := (u2 * u2)%F) in *.
  set (v := (F.opp (E.d * (u1 * u1)) - u2_sqr)%F) in *.
  set (den := (v * u2_sqr)%F) in *.
  rewrite !orb_false_l in Hdec.
  destruct (F.to_Z (u1 * (invsqrt * (invsqrt * u2) * v)) =? 0)%Z eqn:Hyz; [discriminate Hdec|].
  injection Hdec as Hx Hy.
  assert (Hynz : y <> Fzero).
  { intro Hcontra. apply Z.eqb_neq in Hyz. apply Hyz. rewrite Hy, Hcontra.
    rewrite ModularArithmeticTheorems.F.to_Z_of_Z. reflexivity. }
  assert (Hdennz : den <> Fzero).
  { intro Hd. apply Hynz. rewrite <- Hy.
    unfold den in Hd. apply Ristretto255_Sqrt.mul_zero_factor in Hd.
    destruct Hd as [Hv|Hu2s].
    - rewrite Hv. ring.
    - unfold u2_sqr in Hu2s. apply Ristretto255_Sqrt.mul_zero_factor in Hu2s.
      destruct Hu2s as [Hu|Hu]; rewrite Hu; ring. }
  pose proof (sqrt_ratio_m1_decode_invariant s Hdennz true invsqrt Hsr eq_refl) as Hinv.
  fold ss u1 u2 u2_sqr v den in Hinv.
  subst x y.
  unfold ristretto_encode, to_extended, ristretto_encode_aux.
  set (xv := abs (F.of_Z p 2 * s * (invsqrt * u2))) in *.
  set (yv := (u1 * (invsqrt * (invsqrt * u2) * v))%F) in *.
  (* Decoder algebraic facts: yv = u1/u2 and xv^2 * v = 4 s^2. *)
  assert (Hu2nz : u2 <> Fzero).
  { intro Hk. apply Hdennz. unfold den, u2_sqr. rewrite Hk. ring. }
  assert (Hvnz : v <> Fzero).
  { intro Hk. apply Hdennz. unfold den. rewrite Hk. ring. }
  assert (Hyvu2 : (yv * u2)%F = u1).
  { unfold yv.
    transitivity (u1 * ((v * u2_sqr) * invsqrt * invsqrt))%F.
    - unfold u2_sqr. ring.
    - fold den. rewrite Hinv. ring. }
  assert (Hxvsq : (xv * xv)%F
                  = (F.of_Z p 2 * s * (invsqrt * u2)) * (F.of_Z p 2 * s * (invsqrt * u2))).
  { unfold xv. apply Ristretto255_Sqrt.abs_sq. }
  assert (Hxv2v : (xv * xv * v)%F = (F.of_Z p 4 * (s * s))%F).
  { rewrite Hxvsq.
    transitivity ((F.of_Z p 4 * (s*s)) * (v * u2_sqr * invsqrt * invsqrt))%F.
    - unfold u2_sqr. ring_simplify.
      replace (F.of_Z p 2 * F.of_Z p 2)%F with (F.of_Z p 4)
        by (apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
      ring.
    - fold den. rewrite Hinv. ring. }
  destruct (F.eq_dec s Fzero) as [Hs0 | Hsnz].
  2:{
    (* MAIN case: s <> 0.  The encoder's sqrt argument is a nonzero square,
       so its [was_square] is true; that forces [rotate = false] (via Hnegt)
       and the sign flip false (xv is an abs), collapsing the four branches
       to the identity branch, whose output squares to s^2. *)
    assert (H4nz : (F.of_Z p 4 : Fp) <> Fzero) by (Decidable.vm_decide).
    assert (H4s2nz : (F.of_Z p 4 * (s * s))%F <> Fzero).
    { intro Hk. apply Ristretto255_Sqrt.mul_zero_factor in Hk.
      destruct Hk as [Hk|Hk].
      - apply H4nz; assumption.
      - apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk; apply Hsnz; assumption. }
    assert (Hxvnz : xv <> Fzero).
    { intro Hk. apply H4s2nz. rewrite <- Hxv2v, Hk. ring. }
    assert (Hxyvnz : (xv * yv)%F <> Fzero).
    { intro Hk. apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk as [Hk|Hk].
      - apply Hxvnz; assumption.
      - apply Hynz; assumption. }
    assert (Hu1yvnz : ((Fone + yv) * (Fone - yv))%F <> Fzero).
    { intro Hk. apply H4s2nz.
      transitivity (((Fone + yv) * (Fone - yv)) * (u2 * u2))%F.
      - transitivity ((u2 * u2) - (yv * u2) * (yv * u2))%F.
        + rewrite Hyvu2. unfold u2, u1, ss. ring.
        + ring.
      - rewrite Hk. ring. }
    assert (Hargnz : ((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv)))%F <> Fzero).
    { intro Hk. apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk as [Hk|Hk].
      - apply Hu1yvnz; assumption.
      - apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk; apply Hxyvnz; assumption. }
    pose proof (sqrt_ratio_m1_correct Fone _ Hargnz) as Hsqe.
    destruct (sqrt_ratio_m1 Fone ((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv))))
      as [wse I0] eqn:Hsre.
    destruct Hsqe as [Hsqe_disj Hsqe_neg].
    set (M := (I0 * ((Fone + yv) * (Fone - yv)) * (I0 * (xv * yv)) * (xv * yv))%F) in *.
    assert (HMval : M = ((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv)) * I0 * I0)%F)
      by (unfold M; ring).
    assert (Hb : ((Fone + yv) * (Fone - yv) * (u2 * u2))%F = (F.of_Z p 4 * (s*s))%F).
    { transitivity ((u2 * u2) - (yv * u2) * (yv * u2))%F.
      - ring.
      - rewrite Hyvu2. unfold u2, u1, ss. ring. }
    assert (Hargu2 : ((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv)) * (u2 * u2))%F
                     = ((F.of_Z p 4 * s * s * invsqrt * u1) * (F.of_Z p 4 * s * s * invsqrt * u1))%F).
    { apply (Ristretto255_Sqrt.mul_cancel_l (u2 * u2)).
      - intro Hk. apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk; apply Hu2nz; assumption.
      - transitivity (((Fone + yv) * (Fone - yv) * (u2*u2)) * ((xv*xv) * (yv*u2) * (yv*u2)))%F.
        + field.
        + rewrite Hb, Hyvu2, Hxvsq. ring. }
    assert (HMone : M = Fone).
    { destruct Hsqe_disj as [[Hwse Heq]|[Hwse Heq]].
      - rewrite HMval. exact Heq.
      - exfalso. apply local_SQRT_M1_nonsquare.
        exists (F.of_Z p 4 * s * s * invsqrt * u1 * I0 * F.inv u2)%F.
        apply (Ristretto255_Sqrt.mul_cancel_l (u2 * u2)).
        + intro Hk. apply Ristretto255_Sqrt.mul_zero_factor in Hk. destruct Hk; apply Hu2nz; assumption.
        + transitivity ((F.of_Z p 4 * s * s * invsqrt * u1) * (F.of_Z p 4 * s * s * invsqrt * u1) * (I0 * I0))%F.
          * field; exact Hu2nz.
          * rewrite <- Hargu2.
            transitivity (((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv)) * I0 * I0) * (u2 * u2))%F.
            -- ring.
            -- rewrite Heq. ring. }
    assert (Hxvneg : is_negative xv = false) by (unfold xv; apply Ristretto255_Sqrt.is_negative_abs).
    rewrite HMone.
    replace (xv * yv * Fone)%F with (xv * yv)%F by ring.
    rewrite Hnegt.
    replace (xv * Fone)%F with xv by ring.
    rewrite Hxvneg.
    assert (Habs_s : abs s = s) by (unfold abs; rewrite Hnegs; reflexivity).
    rewrite <- Habs_s.
    apply local_abs_eq_of_sq.
    assert (H1yvnz : (Fone + yv)%F <> Fzero).
    { intro Hk. apply Hu1yvnz. rewrite Hk. ring. }
    assert (Hs2 : (s * s * (Fone + yv))%F = (Fone - yv)%F).
    { apply (Ristretto255_Sqrt.mul_cancel_l u2).
      - exact Hu2nz.
      - transitivity ((s*s) * (yv * u2) + (s*s)*u2)%F.
        + ring.
        + transitivity (u2 - (yv * u2))%F.
          * rewrite Hyvu2. unfold u2, u1, ss. ring.
          * ring. }
    apply (Ristretto255_Sqrt.mul_cancel_l (Fone + yv) _ _ H1yvnz).
    transitivity ((Fone - yv) * ((Fone + yv) * (Fone - yv) * (xv * yv * (xv * yv)) * I0 * I0))%F.
    - ring.
    - rewrite <- HMval, HMone.
      transitivity (s * s * (Fone + yv))%F.
      + rewrite Hs2. ring.
      + ring.
  }
  (* DEGENERATE case: s = 0, so xv = 0 and the encoder's sqrt argument is 0,
     forcing the canonical inverse-sqrt to 0; the whole output is abs 0 = 0 = s. *)
  subst s.
  unfold ristretto_encode, to_extended, ristretto_encode_aux.
  assert (Hxv0 : xv = Fzero).
  { unfold xv. replace (F.of_Z p 2 * Fzero * (invsqrt * u2))%F with (Fzero:Fp) by ring.
    unfold abs. Decidable.vm_decide. }
  rewrite Hxv0.
  replace ((Fone + yv) * (Fone - yv) * (Fzero * yv * (Fzero * yv)))%F with (Fzero:Fp) by ring.
  assert (Hsr0 : snd (sqrt_ratio_m1 Fone Fzero) = Fzero).
  { unfold sqrt_ratio_m1. cbv zeta. cbn [snd].
    set (r0 := (Fone * (Fzero * Fzero * Fzero) *
      (Fone * (Fzero * Fzero * Fzero * (Fzero * Fzero * Fzero) * Fzero))
      ^ Z.to_N ((2 ^ 255 - 19 - 5) / 8))%F).
    assert (Hr0 : r0 = Fzero) by (unfold r0; field). rewrite Hr0.
    destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z Fone)%Z;
      [ unfold abs; Decidable.vm_decide
      | destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z (F.opp Fone))%Z;
        [ replace (Fzero * SQRT_M1)%F with (Fzero:Fp) by ring; unfold abs; Decidable.vm_decide
        | destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z (F.opp (SQRT_M1 * Fone)))%Z;
          [ replace (Fzero * SQRT_M1)%F with (Fzero:Fp) by ring; unfold abs; Decidable.vm_decide
          | unfold abs; Decidable.vm_decide ] ] ]. }
  destruct (sqrt_ratio_m1 Fone Fzero) as [wse0 I0] eqn:Hsre0.
  cbn [snd] in Hsr0. subst I0.
  transitivity (abs Fzero);
    [ f_equal;
      (destruct (is_negative (Fzero * yv * (Fzero * ((Fone + yv) * (Fone - yv)) * (Fzero * (Fzero * yv)) * (Fzero * yv))));
       destruct (is_negative ((if is_negative (Fzero * yv * (Fzero * ((Fone + yv) * (Fone - yv)) * (Fzero * (Fzero * yv)) * (Fzero * yv))) then yv * SQRT_M1 else Fzero) * (Fzero * ((Fone + yv) * (Fone - yv)) * (Fzero * (Fzero * yv)) * (Fzero * yv)))); field)
    | unfold abs; Decidable.vm_decide ].
Qed.

(** CORE B (encode -> decode).  Encoding an on-curve affine point and
    decoding the result succeeds and recovers a ristretto-equivalent
    representative.

    Proof outline:
      - [s := ristretto_encode (to_extended (x,y)) = abs(...)], so
        [is_negative s = false] and [F.to_Z s < p]; hence
        [bytes_to_canonical_F (le_split 32 (F.to_Z s)) = Some s]
        (le_split_F_round_trip) and decode enters its main branch.
      - Trace §4.3.1 with this [s]: [was_square] holds (the encoder's
        [s] is a genuine square); [t],[y] nonzero by the curve equation;
        produce [(x',y')].
      - The decoded [(x',y')] and [(x,y)] differ by an E[4] element
        (the encoder's [rotate]/[Y:=-Y] choices land in the same coset),
        giving [is_4torsion_affine (sub_affine (x,y) (x',y'))].
      - Decode-facing dual of [canonical_rep_selection].  ~200-400 LoC. *)
(** IMPORTANT CORRECTION: the existence form above is FALSE.  A generic
    on-curve point's encoding is rejected by the decoder's [was_square]
    guard (RFC 9496 §4.3.1 line 15), so [ristretto_decode_coords ... =
    None] (verified counterexample via vm_compute); the round-trip holds
    only for valid ristretto representatives.  We therefore keep only the
    TRUE conditional content as [encode_decode_equiv] below, and state
    Theorem 1 in conditional form.  [encode_decode_equiv] is the
    decode-facing equivalence dual of [canonical_rep_selection]:

    Proof outline — let s := ristretto_encode (to_extended pP); by
    [decode_encode_core] (Qed) + [le_split_F_round_trip] the decoded pQ
    re-encodes to s, so pP and pQ encode identically; the encoder's
    [rotate]/[Y:=-Y] branch structure then forces their Edwards
    difference [sub_affine pP pQ] into E[4].  ~150-250 LoC. *)
Lemma encode_decode_equiv : forall (pP pQ : Fp * Fp),
  ristretto_decode_coords (ristretto_encode_bytes (to_extended pP)) = Some pQ ->
  is_4torsion_affine (sub_affine pP pQ).
Proof.
Admitted.

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
(** CONDITIONAL FORM (the unconditional existence claim is false — see the
    correction note above [encode_decode_equiv]).  Whenever the encoding of
    [P] decodes successfully to [Q], the two are ristretto-equivalent. *)
Theorem ristretto_encode_decode_roundtrip :
  forall (on_curve_obligation : OnCurveObligation) (P Q : Curve25519.E.point),
    ristretto_decode_bytes on_curve_obligation
      (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q ->
    ristretto_equiv P Q.
Proof.
  intros oc P Q Hdec.
  pose proof (decode_bytes_coords oc _ Q Hdec) as HQc.
  unfold ristretto_equiv.
  apply (encode_decode_equiv (point_coords P) (point_coords Q)).
  exact HQc.
Qed.

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
  pose proof (decode_bytes_coords oc bs P Hdec) as Hcoords.
  destruct (point_coords P) as [x y] eqn:Hpc.
  destruct (decode_coords_canonical bs x y Hcoords) as [s Hs].
  pose proof (decode_encode_core bs s x y Hs Hcoords) as Hcore.
  unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F.
  rewrite Hcore.
  symmetry. apply (canonical_F_to_bs bs s Hs).
Qed.

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
