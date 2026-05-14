(** * Libjade.SHA512Spec — Rocq FIPS-180-4 SHA-512 reference specification.
 *
 * Purpose
 * -------
 * Pure-Gallina functional spec for SHA-512 (FIPS 180-4, §6.4).  Authored
 * locally so the [Bedrock.LibjadeAxioms.jade_hash_sha512_correct] registry
 * slot can state a concrete byte-array equality against a Rocq spec
 * (instead of carrying a [True] placeholder).
 *
 * Style mirrors [Bedrock.Libjade.SHA256Spec] (the A107 sibling spec):
 *   - All arithmetic on N (64-bit words via mask).
 *   - All hash-internal state passed by explicit list-of-N.
 *   - No bedrock2 / VST / CompCert / Mathlib dependencies — pure Stdlib +
 *     Strings.Byte.
 *   - No axioms.
 *
 * Coverage vs. FIPS 180-4
 * -----------------------
 * §4.1.3 :  Ch, Maj, big/little Σ/σ (64-bit, SHA-512 rotation amounts)  (concrete)
 * §4.2.3 :  K_512 round-constant table (80 entries)                     (concrete)
 * §5.1.2 :  message padding (1024-bit blocks, 128-bit length tail)      (concrete)
 * §5.2.2 :  parsing message into 1024-bit blocks                        (concrete)
 * §5.3.5 :  H_0 initial-hash-value table                                (concrete)
 * §6.4.2 :  80-round compression function                               (concrete)
 *
 * Difference vs. SHA-256 (A107)
 * -----------------------------
 * The compression-function *structure* is identical between SHA-256 and
 * SHA-512 — only the following parameters differ:
 *
 *   parameter         SHA-256       SHA-512
 *   ----------------  ------------  ------------
 *   word size         32 bits       64 bits
 *   block size        512 bits      1024 bits
 *   #rounds           64            80
 *   K table           K256 (64)     K512 (80)
 *   H0 table          8 × 32 bits   8 × 64 bits
 *   Σ0 rotations      2, 13, 22     28, 34, 39
 *   Σ1 rotations      6, 11, 25     14, 18, 41
 *   σ0 rotations      7, 18, SHR 3  1,  8,  SHR 7
 *   σ1 rotations      17, 19, SHR 10 19, 61, SHR 6
 *   pad alignment     56 mod 64     112 mod 128
 *   length tail       8 bytes       16 bytes
 *   digest size       32 bytes      64 bytes
 *
 * Refactoring opportunity: a shared word-size-parameterised core could
 * collapse both specs into one functor.  Kept separate here because
 * (a) the two specs are small (each <400 LoC), and (b) word size affects
 * literally every line, so the functor abstraction adds more visual noise
 * than it removes.
 *
 * Output orientation
 * ------------------
 * SHA-512 emits big-endian 64-bit words; this spec returns the final
 * [list Byte.byte] of length 64 in the FIPS 180-4 wire order so it can be
 * compared bytewise against the libjade output via
 *   [jade_hash_sha512_correct].
 *
 * KAT NOT VALIDATED in-Coq
 * ------------------------
 * No vm_compute KAT is asserted here (vectors would inflate compile time
 * dramatically through nested N.shiftl chains).  The spec is intended as a
 * trust-localization handle, not a fast computational kernel.
 *
 * See also
 * --------
 * - [src/Bedrock/Libjade/SHA512Bridge.v]  — wraps this spec on the libjade side.
 * - [src/Bedrock/Libjade/SHA256Spec.v]    — sibling SHA-256 spec (A107).
 * - [src/Bedrock/LibjadeAxioms.v] §1      — [jade_hash_sha512_correct] slot.
 *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Strings.Byte Lia.
Import ListNotations.

Local Open Scope N_scope.

(* ================================================================ *)
(** * §1.  64-bit word machinery                                     *)
(* ================================================================ *)

(** A SHA-512 word is a 64-bit unsigned integer.  We carry it as [N]
    and mask after every operation that could grow it. *)
Definition mask64 : N := N.ones 64.

Definition w64_of_N (x : N) : N := N.land x mask64.

(** Rotate-right within 64 bits. *)
Definition rotr64 (x : N) (n : N) : N :=
  w64_of_N (N.lor (N.shiftr x n) (N.shiftl x (64 - n))).

(** Shift-right (logical), masked. *)
Definition shr64 (x : N) (n : N) : N :=
  w64_of_N (N.shiftr x n).

(** 64-bit modular add. *)
Definition add64 (x y : N) : N := w64_of_N (N.add x y).

(** Bitwise ops on 64-bit words. *)
Definition xor64 (x y : N) : N := w64_of_N (N.lxor x y).
Definition and64 (x y : N) : N := w64_of_N (N.land x y).
Definition not64 (x : N) : N := w64_of_N (N.lxor x mask64).

(* ================================================================ *)
(** * §2.  FIPS 180-4 §4.1.3 functions                               *)
(* ================================================================ *)

Definition Ch (x y z : N) : N :=
  xor64 (and64 x y) (and64 (not64 x) z).

Definition Maj (x y z : N) : N :=
  xor64 (and64 x y) (xor64 (and64 x z) (and64 y z)).

(** Σ_0^{512}(x) = ROTR^28(x) XOR ROTR^34(x) XOR ROTR^39(x) *)
Definition Sigma0 (x : N) : N :=
  xor64 (rotr64 x 28) (xor64 (rotr64 x 34) (rotr64 x 39)).

(** Σ_1^{512}(x) = ROTR^14(x) XOR ROTR^18(x) XOR ROTR^41(x) *)
Definition Sigma1 (x : N) : N :=
  xor64 (rotr64 x 14) (xor64 (rotr64 x 18) (rotr64 x 41)).

(** σ_0^{512}(x) = ROTR^1(x) XOR ROTR^8(x) XOR SHR^7(x) *)
Definition sigma0 (x : N) : N :=
  xor64 (rotr64 x 1) (xor64 (rotr64 x 8) (shr64 x 7)).

(** σ_1^{512}(x) = ROTR^19(x) XOR ROTR^61(x) XOR SHR^6(x) *)
Definition sigma1 (x : N) : N :=
  xor64 (rotr64 x 19) (xor64 (rotr64 x 61) (shr64 x 6)).

(* ================================================================ *)
(** * §3.  FIPS 180-4 §4.2.3 round constants (80 × 64-bit)           *)
(* ================================================================ *)

Definition K512 : list N :=
  [0x428a2f98d728ae22; 0x7137449123ef65cd; 0xb5c0fbcfec4d3b2f; 0xe9b5dba58189dbbc;
   0x3956c25bf348b538; 0x59f111f1b605d019; 0x923f82a4af194f9b; 0xab1c5ed5da6d8118;
   0xd807aa98a3030242; 0x12835b0145706fbe; 0x243185be4ee4b28c; 0x550c7dc3d5ffb4e2;
   0x72be5d74f27b896f; 0x80deb1fe3b1696b1; 0x9bdc06a725c71235; 0xc19bf174cf692694;
   0xe49b69c19ef14ad2; 0xefbe4786384f25e3; 0x0fc19dc68b8cd5b5; 0x240ca1cc77ac9c65;
   0x2de92c6f592b0275; 0x4a7484aa6ea6e483; 0x5cb0a9dcbd41fbd4; 0x76f988da831153b5;
   0x983e5152ee66dfab; 0xa831c66d2db43210; 0xb00327c898fb213f; 0xbf597fc7beef0ee4;
   0xc6e00bf33da88fc2; 0xd5a79147930aa725; 0x06ca6351e003826f; 0x142929670a0e6e70;
   0x27b70a8546d22ffc; 0x2e1b21385c26c926; 0x4d2c6dfc5ac42aed; 0x53380d139d95b3df;
   0x650a73548baf63de; 0x766a0abb3c77b2a8; 0x81c2c92e47edaee6; 0x92722c851482353b;
   0xa2bfe8a14cf10364; 0xa81a664bbc423001; 0xc24b8b70d0f89791; 0xc76c51a30654be30;
   0xd192e819d6ef5218; 0xd69906245565a910; 0xf40e35855771202a; 0x106aa07032bbd1b8;
   0x19a4c116b8d2d0c8; 0x1e376c085141ab53; 0x2748774cdf8eeb99; 0x34b0bcb5e19b48a8;
   0x391c0cb3c5c95a63; 0x4ed8aa4ae3418acb; 0x5b9cca4f7763e373; 0x682e6ff3d6b2b8a3;
   0x748f82ee5defb2fc; 0x78a5636f43172f60; 0x84c87814a1f0ab72; 0x8cc702081a6439ec;
   0x90befffa23631e28; 0xa4506cebde82bde9; 0xbef9a3f7b2c67915; 0xc67178f2e372532b;
   0xca273eceea26619c; 0xd186b8c721c0c207; 0xeada7dd6cde0eb1e; 0xf57d4f7fee6ed178;
   0x06f067aa72176fba; 0x0a637dc5a2c898a6; 0x113f9804bef90dae; 0x1b710b35131c471b;
   0x28db77f523047d84; 0x32caab7b40c72493; 0x3c9ebe0a15c9bebc; 0x431d67c49c100d4c;
   0x4cc5d4becb3e42b6; 0x597f299cfc657e2a; 0x5fcb6fab3ad6faec; 0x6c44198c4a475817]%N.

(* ================================================================ *)
(** * §4.  FIPS 180-4 §5.3.5 initial hash value H^{(0)}              *)
(* ================================================================ *)

Definition H0_init : list N :=
  [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1;
   0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]%N.

(* ================================================================ *)
(** * §5.  FIPS 180-4 §5.1.2 padding                                 *)
(* ================================================================ *)

(** Pack a non-negative N into [k] big-endian bytes (low byte last). *)
Fixpoint be_bytes_aux (k : nat) (x : N) : list Byte.byte :=
  match k with
  | O => []
  | S k' =>
      let lo := N.land x 255 in
      let hi := N.shiftr x 8 in
      be_bytes_aux k' hi
      ++ [match Byte.of_N lo with Some b => b | None => Byte.x00 end]
  end.

Definition be_bytes (k : nat) (x : N) : list Byte.byte := be_bytes_aux k x.

(** SHA-512 pad: append 0x80, then enough 0x00 to reach length ≡ 112 mod 128,
    then 16 big-endian bytes encoding the original message length in bits.
    (The FIPS-180-4 length tail is technically 128 bits; we encode it as a
    big-endian 16-byte N which suffices for any practical message size.) *)
Definition sha512_pad (msg : list Byte.byte) : list Byte.byte :=
  let L := length msg in
  (* k zero bytes such that (L + 1 + k) ≡ 112 (mod 128), 0 ≤ k < 128. *)
  let k := Nat.modulo (112 + 128 - ((L + 1) mod 128)) 128 in
  let len_bits := N.mul 8 (N.of_nat L) in
  msg ++ [Byte.x80] ++ List.repeat Byte.x00 k ++ be_bytes 16 len_bits.

(* ================================================================ *)
(** * §6.  Block parsing — 16 big-endian 64-bit words per block      *)
(* ================================================================ *)

Fixpoint take {A} (n : nat) (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | _, [] => []
  | S n', x :: l' => x :: take n' l'
  end.

Fixpoint drop {A} (n : nat) (l : list A) : list A :=
  match n with
  | O => l
  | S n' => match l with [] => [] | _ :: l' => drop n' l' end
  end.

(** Big-endian 64-bit word from 8 bytes. *)
Definition word_be
  (b0 b1 b2 b3 b4 b5 b6 b7 : Byte.byte) : N :=
  N.lor (N.shiftl (Byte.to_N b0) 56)
   (N.lor (N.shiftl (Byte.to_N b1) 48)
    (N.lor (N.shiftl (Byte.to_N b2) 40)
     (N.lor (N.shiftl (Byte.to_N b3) 32)
      (N.lor (N.shiftl (Byte.to_N b4) 24)
       (N.lor (N.shiftl (Byte.to_N b5) 16)
        (N.lor (N.shiftl (Byte.to_N b6) 8)
                         (Byte.to_N b7))))))).

Definition word_be_at (block : list Byte.byte) (i : nat) : N :=
  let b0 := List.nth (i*8 + 0) block Byte.x00 in
  let b1 := List.nth (i*8 + 1) block Byte.x00 in
  let b2 := List.nth (i*8 + 2) block Byte.x00 in
  let b3 := List.nth (i*8 + 3) block Byte.x00 in
  let b4 := List.nth (i*8 + 4) block Byte.x00 in
  let b5 := List.nth (i*8 + 5) block Byte.x00 in
  let b6 := List.nth (i*8 + 6) block Byte.x00 in
  let b7 := List.nth (i*8 + 7) block Byte.x00 in
  word_be b0 b1 b2 b3 b4 b5 b6 b7.

(** Cut the padded message into 128-byte blocks.  Caller guarantees that
    [length msg] is a multiple of 128. *)
Fixpoint chunks128 (msg : list Byte.byte) (n_blocks : nat)
  : list (list Byte.byte) :=
  match n_blocks with
  | O => []
  | S nb' => take 128 msg :: chunks128 (drop 128 msg) nb'
  end.

(** First 16 message-schedule words from a 128-byte block. *)
Definition block_W0_15 (block : list Byte.byte) : list N :=
  List.map (fun i => word_be_at block i) (List.seq 0 16).

(* ================================================================ *)
(** * §7.  Message schedule W[0..79]                                  *)
(* ================================================================ *)

(** Extend W by one word using the FIPS 180-4 §6.4.2 step 1 recurrence:
      W_t = σ1(W_{t-2}) + W_{t-7} + σ0(W_{t-15}) + W_{t-16}  (mod 2^64). *)
Definition W_step (W : list N) : list N :=
  let t := List.length W in
  let w_2  := List.nth (t - 2)  W 0%N in
  let w_7  := List.nth (t - 7)  W 0%N in
  let w_15 := List.nth (t - 15) W 0%N in
  let w_16 := List.nth (t - 16) W 0%N in
  let new := add64 (sigma1 w_2) (add64 w_7 (add64 (sigma0 w_15) w_16)) in
  W ++ [new].

(** Extend a 16-word seed up to 80 words. *)
Fixpoint extend_W_aux (W : list N) (count : nat) : list N :=
  match count with
  | O => W
  | S c' => extend_W_aux (W_step W) c'
  end.

Definition message_schedule (block : list Byte.byte) : list N :=
  extend_W_aux (block_W0_15 block) 64.

(* ================================================================ *)
(** * §8.  Compression                                                *)
(* ================================================================ *)

(** Working variable record: (a, b, c, d, e, f, g, h). *)
Record state8 := mkS { sa:N; sb:N; sc:N; sd:N; se:N; sf:N; sg:N; sh:N }.

Definition s8_of_list (l : list N) : state8 :=
  mkS (List.nth 0 l 0)%N (List.nth 1 l 0)%N (List.nth 2 l 0)%N (List.nth 3 l 0)%N
      (List.nth 4 l 0)%N (List.nth 5 l 0)%N (List.nth 6 l 0)%N (List.nth 7 l 0)%N.

Definition s8_to_list (s : state8) : list N :=
  [sa s; sb s; sc s; sd s; se s; sf s; sg s; sh s].

(** One round of the compression function (FIPS 180-4 §6.4.2 step 3). *)
Definition compress_round (s : state8) (kt wt : N) : state8 :=
  let T1 := add64 (sh s)
            (add64 (Sigma1 (se s))
            (add64 (Ch (se s) (sf s) (sg s))
            (add64 kt wt))) in
  let T2 := add64 (Sigma0 (sa s)) (Maj (sa s) (sb s) (sc s)) in
  mkS (add64 T1 T2)        (* a *)
      (sa s)                (* b *)
      (sb s)                (* c *)
      (sc s)                (* d *)
      (add64 (sd s) T1)    (* e *)
      (se s)                (* f *)
      (sf s)                (* g *)
      (sg s).               (* h *)

(** 80 rounds of compression — fold over the K/W pairs.  K512 and W must
    each have length 80. *)
Fixpoint compress_loop (s : state8) (ks ws : list N) : state8 :=
  match ks, ws with
  | k :: ks', w :: ws' => compress_loop (compress_round s k w) ks' ws'
  | _, _ => s
  end.

(** Process one 1024-bit block.  Takes the previous 8-word hash state. *)
Definition hash_block (H : list N) (block : list Byte.byte) : list N :=
  let W := message_schedule block in
  let s := s8_of_list H in
  let s' := compress_loop s K512 W in
  (* Add compressed working variables back into H, mod 2^64. *)
  List.map (fun '(h, x) => add64 h x)
           (List.combine H (s8_to_list s')).

(** Iterate [hash_block] over a sequence of 128-byte blocks. *)
Fixpoint hash_blocks (H : list N) (blocks : list (list Byte.byte)) : list N :=
  match blocks with
  | [] => H
  | b :: bs => hash_blocks (hash_block H b) bs
  end.

(* ================================================================ *)
(** * §9.  Top-level entry point                                      *)
(* ================================================================ *)

(** Convert a 64-bit word [w] to its 8 big-endian bytes. *)
Definition word_to_be_bytes (w : N) : list Byte.byte := be_bytes 8 w.

(** [sha512_spec msg] is the 64-byte SHA-512 digest of [msg] per FIPS 180-4. *)
Definition sha512_spec (msg : list Byte.byte) : list Byte.byte :=
  let padded := sha512_pad msg in
  let n_blocks := Nat.div (length padded) 128 in
  let blocks := chunks128 padded n_blocks in
  let H_final := hash_blocks H0_init blocks in
  List.concat (List.map word_to_be_bytes H_final).

(* ================================================================ *)
(** * §10.  Length lemmas (Qed)                                       *)
(* ================================================================ *)

Lemma be_bytes_aux_length : forall k x, length (be_bytes_aux k x) = k.
Proof.
  induction k as [|k' IH]; intro x; [reflexivity|].
  simpl. rewrite length_app. simpl. rewrite IH. lia.
Qed.

Lemma be_bytes_length : forall k x, length (be_bytes k x) = k.
Proof. intros. apply be_bytes_aux_length. Qed.

Lemma word_to_be_bytes_length : forall w, length (word_to_be_bytes w) = 8%nat.
Proof. intro w. unfold word_to_be_bytes. apply be_bytes_length. Qed.

(** Length of [List.concat (List.map word_to_be_bytes l)] is [8 * length l]. *)
Lemma concat_word_bytes_length : forall l,
  length (List.concat (List.map word_to_be_bytes l)) = (8 * length l)%nat.
Proof.
  induction l as [|w l' IH]; [reflexivity|].
  simpl. rewrite IH. lia.
Qed.

(** hash_block preserves length = 8. *)
Lemma hash_block_length : forall H b,
  length H = 8%nat -> length (hash_block H b) = 8%nat.
Proof.
  intros H b HH. unfold hash_block.
  rewrite List.length_map. rewrite List.length_combine. unfold s8_to_list. simpl.
  rewrite HH. reflexivity.
Qed.

(** hash_blocks preserves length = 8. *)
Lemma hash_blocks_length : forall blocks H,
  length H = 8%nat -> length (hash_blocks H blocks) = 8%nat.
Proof.
  induction blocks as [|b bs IH]; intros H HH; simpl; [exact HH|].
  apply IH. apply hash_block_length. exact HH.
Qed.

Lemma H0_init_length : length H0_init = 8%nat.
Proof. reflexivity. Qed.

(** Headline length lemma — SHA-512 produces 64 bytes. *)
Theorem sha512_spec_length : forall msg, length (sha512_spec msg) = 64%nat.
Proof.
  intro msg. unfold sha512_spec.
  rewrite concat_word_bytes_length.
  rewrite hash_blocks_length by apply H0_init_length.
  reflexivity.
Qed.
