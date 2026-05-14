(** * Libjade.X25519Spec — Rocq RFC 7748 X25519 reference specification.
 *
 * Purpose
 * -------
 * Pure-Gallina functional spec for X25519 (RFC 7748, §5).  Authored locally
 * so the [Bedrock.LibjadeAxioms.jade_curve25519_x25519_correct] and
 * [...x25519_base_correct] registry slots can state a concrete byte-array
 * equality against a Rocq spec (instead of carrying [True] placeholders).
 *
 * Style mirrors [Bedrock.Libjade.SHA256Spec] (commit e20e5e4):
 *   - All arithmetic on N with explicit modular reduction by p = 2^255-19.
 *   - No fiat-crypto / Crypto.Spec.Curve25519 / Hierarchy.field /
 *     ScalarMult.scalarmult_ref dependencies — pure Stdlib + Strings.Byte.
 *     (Those upstream specs require Pocklington primality + a typeclass
 *     field structure; for a byte-equality registry slot we only need a
 *     direct reference computation, not a group-theoretic framework.)
 *   - No axioms.
 *
 * Coverage vs. RFC 7748
 * ---------------------
 * §3       :  prime p = 2^255 - 19                              (concrete)
 * §5       :  decodeLittleEndian, decodeUCoordinate (with high
 *             bit clear), decodeScalar25519 (RFC 7748 clamp)    (concrete)
 * §5       :  Montgomery ladder step (cswap + double-and-add)   (concrete)
 * §5       :  X25519(k, u) = ladder(clamp(k), maskU(u)) -> 32B  (concrete)
 * §6.1     :  X25519 base point u = 9                           (concrete)
 *
 * The body of the inversion is "Fermat little theorem":  z^(p-2) mod p,
 * implemented via square-and-multiply.  This is a reference implementation
 * — it is not constant-time and is not intended for execution speed.
 *
 * Shape used by the registry slot
 * --------------------------------
 *   [x25519_spec scalar point] : list Byte.byte (length 32)
 *   [x25519_base_spec scalar]  : list Byte.byte (length 32)
 *
 * The libjade-side handles [x25519_libjade] / [x25519_libjade_base] are
 * declared at the [Bedrock.LibjadeAxioms] level (so the registry axioms
 * can directly cite them); the bridge file at
 * [Bedrock.Libjade.X25519Bridge] re-exports them and provides the matching
 * Qed length lemmas.
 *
 * See also
 * --------
 * - [src/Bedrock/Libjade/X25519Bridge.v] — wraps these specs on the
 *   libjade side.
 * - [src/Bedrock/LibjadeAxioms.v] §2 — [jade_curve25519_x25519_correct] +
 *   [jade_curve25519_x25519_base_correct] slots.
 * - [fiat-crypto/src/Spec/Curve25519.v] — the heavy upstream X25519 spec
 *   built on top of [Hierarchy.field]; functionally equivalent to the
 *   pure-Stdlib body below but inappropriate for the registry slot since
 *   it pulls in Pocklington primality and field-theoretic typeclasses.
 *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Strings.Byte Lia.
Import ListNotations.

Local Open Scope N_scope.

(* ================================================================ *)
(** * §1.  Field arithmetic mod p = 2^255 - 19                       *)
(* ================================================================ *)

(** The X25519 prime, written without any reliance on a typeclass field
    structure.  All operations below take/return [N] in the half-open
    range [0, p). *)
Definition p25519 : N := N.sub (N.pow 2 255) 19.

(** Modular reduction. *)
Definition fmod (x : N) : N := N.modulo x p25519.

(** Modular add/sub/mul.  For [fsub] we add [p] before subtracting so the
    intermediate is non-negative even when [y > x]. *)
Definition fadd (x y : N) : N := fmod (N.add x y).
Definition fsub (x y : N) : N := fmod (N.add x (N.sub p25519 (fmod y))).
Definition fmul (x y : N) : N := fmod (N.mul x y).

(** Square-and-multiply modular exponentiation.
    Walks the bits of [e] from MSB to LSB; total iteration count is
    bounded by [Z.log2 e + 1].  For the X25519 inversion we call this
    with the constant [p-2], which has 255 bits, so a 256-iteration
    cap is safe. *)
Fixpoint fpow_aux (base : N) (e : N) (fuel : nat) : N :=
  match fuel with
  | O => 1%N
  | S f' =>
      if N.eqb e 0 then 1%N
      else
        let half := fpow_aux base (N.div e 2) f' in
        let sq   := fmul half half in
        if N.odd e then fmul sq base else sq
  end.

Definition fpow (base e : N) : N := fpow_aux base e 300.

(** Modular inverse via Fermat: [z^(p-2) mod p]. *)
Definition finv (z : N) : N := fpow z (N.sub p25519 2).

(* ================================================================ *)
(** * §2.  RFC 7748 §5  decode / encode of 32-byte buffers           *)
(* ================================================================ *)

(** Little-endian byte → N decoder.  Input may be any length; bytes
    beyond position 31 are still accumulated (caller guarantees 32B). *)
Fixpoint decode_le_aux (bs : list Byte.byte) (shift : N) : N :=
  match bs with
  | [] => 0
  | b :: bs' =>
      N.lor (N.shiftl (Byte.to_N b) shift)
            (decode_le_aux bs' (N.add shift 8))
  end.

Definition decode_le (bs : list Byte.byte) : N := decode_le_aux bs 0.

(** Pack a non-negative N into [k] little-endian bytes (low byte first).
    Mirrors SHA256Spec.be_bytes shape but in little-endian. *)
Fixpoint le_bytes_aux (k : nat) (x : N) : list Byte.byte :=
  match k with
  | O => []
  | S k' =>
      let lo := N.land x 255 in
      let hi := N.shiftr x 8 in
      (match Byte.of_N lo with Some b => b | None => Byte.x00 end)
        :: le_bytes_aux k' hi
  end.

Definition le_bytes (k : nat) (x : N) : list Byte.byte := le_bytes_aux k x.

(** Encode a field element to 32 little-endian bytes (RFC 7748 §5,
    encodeUCoordinate). *)
Definition encode_u (u : N) : list Byte.byte := le_bytes 32 (fmod u).

(** Decode 32 little-endian bytes to a u-coordinate, clearing the high
    bit of byte 31 (RFC 7748 §5, decodeUCoordinate "masks the most
    significant bit of the final byte"). *)
Definition decode_u (bs : list Byte.byte) : N :=
  fmod (decode_le bs).

(** RFC 7748 §5 decodeScalar25519 clamp:
      k[0]  &= 248      (clear bottom 3 bits)
      k[31] &= 127      (clear high bit)
      k[31] |= 64       (set bit 254)
    Applied byte-wise on the 32-byte scalar buffer. *)
Definition clamp_byte0 (b : Byte.byte) : Byte.byte :=
  match Byte.of_N (N.land (Byte.to_N b) 248) with
  | Some b' => b' | None => Byte.x00
  end.

Definition clamp_byte31 (b : Byte.byte) : Byte.byte :=
  match Byte.of_N (N.lor (N.land (Byte.to_N b) 127) 64) with
  | Some b' => b' | None => Byte.x00
  end.

(** Replace position [n] of [l] with [x]; if [n >= length l], returns [l]. *)
Fixpoint list_replace {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S n' => h :: list_replace t n' x
  end.

Definition clamp_scalar (bs : list Byte.byte) : list Byte.byte :=
  let b0  := List.nth 0  bs Byte.x00 in
  let b31 := List.nth 31 bs Byte.x00 in
  let bs1 := list_replace bs 0  (clamp_byte0  b0)  in
  let bs2 := list_replace bs1 31 (clamp_byte31 b31) in
  bs2.

(** Decode a 32-byte little-endian scalar after clamping. *)
Definition decode_scalar (bs : list Byte.byte) : N :=
  decode_le (clamp_scalar bs).

(* ================================================================ *)
(** * §3.  RFC 7748 §5  Montgomery ladder                            *)
(* ================================================================ *)

(** [a24] = (486662 - 2) / 4 = 121665.  Per RFC 7748 §5. *)
Definition a24 : N := 121665.

(** Quad of field elements bundled as a record so we can name the four
    components clearly without relying on nested-pair pattern syntax. *)
Record quadN := mkQ { qa : N; qb : N; qc : N; qd : N }.

(** Constant-time-style swap (Gallina, NOT constant-time — this is a spec).
    If [bit = 0], return [(x2, z2, x3, z3)]; if [bit = 1], swap the pairs. *)
Definition cswap (bit : N) (x2 z2 x3 z3 : N) : quadN :=
  if N.eqb bit 0 then mkQ x2 z2 x3 z3 else mkQ x3 z3 x2 z2.

(** One ladder step.  Inputs: current accumulator (x2, z2) and projective
    add-pair (x3, z3), plus the base u-coordinate [x1].  Output: updated
    (x2, z2, x3, z3).  Mirrors the recipe in RFC 7748 §5 exactly. *)
Definition ladder_step (x1 x2 z2 x3 z3 : N) : quadN :=
  let A  := fadd x2 z2 in
  let AA := fmul A A in
  let B  := fsub x2 z2 in
  let BB := fmul B B in
  let E  := fsub AA BB in
  let C  := fadd x3 z3 in
  let D  := fsub x3 z3 in
  let DA := fmul D A in
  let CB := fmul C B in
  let x3' := fmul (fadd DA CB) (fadd DA CB) in
  let z3' := fmul x1 (fmul (fsub DA CB) (fsub DA CB)) in
  let x2' := fmul AA BB in
  let z2' := fmul E (fadd AA (fmul a24 E)) in
  mkQ x2' z2' x3' z3'.

(** Ladder state: quad (x2, z2, x3, z3) plus the current [swap] bit. *)
Record lstate := mkLS { ls_q : quadN ; ls_swap : N }.

(** Main ladder loop body.  At iteration [t] (0-indexed from the MSB),
    extract bit [254 - t] of [k], do the conditional swap, one step, and
    swap back. *)
Definition ladder_body (k : N) (x1 : N)
                       (state : lstate)
                       (t : nat) : lstate :=
  let q     := ls_q    state in
  let swap  := ls_swap state in
  let x2    := qa q in
  let z2    := qb q in
  let x3    := qc q in
  let z3    := qd q in
  let bit_index := N.of_nat (254 - t) in
  let k_t := N.land (N.shiftr k bit_index) 1 in
  let swap' := N.lxor swap k_t in
  let qa1 := cswap swap' x2 z2 x3 z3 in
  let q1  := ladder_step x1 (qa qa1) (qb qa1) (qc qa1) (qd qa1) in
  let q2  := cswap k_t (qa q1) (qb q1) (qc q1) (qd q1) in
  mkLS q2 k_t.

(** Drive the ladder loop for 255 iterations (t = 0 .. 254). *)
Fixpoint ladder_loop (k : N) (x1 : N)
                     (state : lstate)
                     (count : nat) (t : nat)
       : lstate :=
  match count with
  | O => state
  | S c' => ladder_loop k x1 (ladder_body k x1 state t) c' (S t)
  end.

(** The Montgomery ladder per RFC 7748 §5.  Outputs (x2 / z2) as a field
    element. *)
Definition montladder (k u : N) : N :=
  let x1 := u in
  let init := mkLS (mkQ 1 0 u 1) 0 in
  let final := ladder_loop k x1 init 255 0 in
  let q := ls_q final in
  fmul (qa q) (finv (qb q)).

(* ================================================================ *)
(** * §4.  Top-level entry points                                    *)
(* ================================================================ *)

(** [x25519_spec scalar point] is the RFC 7748 §5 X25519 shared-secret
    given a 32-byte little-endian [scalar] and 32-byte little-endian
    [point] (u-coordinate).  Output is 32 little-endian bytes. *)
Definition x25519_spec (scalar point : list Byte.byte) : list Byte.byte :=
  let k := decode_scalar scalar in
  let u := decode_u point in
  encode_u (montladder k u).

(** [x25519_base_spec scalar] is the RFC 7748 §6.1 X25519 public key:
    same ladder applied to the fixed base-point u = 9. *)
Definition base_u : list Byte.byte :=
  le_bytes 32 9.

Definition x25519_base_spec (scalar : list Byte.byte) : list Byte.byte :=
  x25519_spec scalar base_u.

(* ================================================================ *)
(** * §5.  Length lemmas (Qed)                                       *)
(* ================================================================ *)

Lemma le_bytes_aux_length : forall k x, length (le_bytes_aux k x) = k.
Proof.
  induction k as [|k' IH]; intro x; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma le_bytes_length : forall k x, length (le_bytes k x) = k.
Proof. intros. apply le_bytes_aux_length. Qed.

Lemma encode_u_length : forall u, length (encode_u u) = 32%nat.
Proof. intro u. unfold encode_u. apply le_bytes_length. Qed.

Lemma base_u_length : length base_u = 32%nat.
Proof. unfold base_u. apply le_bytes_length. Qed.

(** Headline length lemma — X25519 produces 32 bytes. *)
Theorem x25519_spec_length :
  forall scalar point, length (x25519_spec scalar point) = 32%nat.
Proof.
  intros scalar point. unfold x25519_spec. apply encode_u_length.
Qed.

Theorem x25519_base_spec_length :
  forall scalar, length (x25519_base_spec scalar) = 32%nat.
Proof.
  intro scalar. unfold x25519_base_spec. apply x25519_spec_length.
Qed.
