(** * Libjade.SHA256Spec — Rocq FIPS-180-4 SHA-256 reference specification.
 *
 * Purpose
 * -------
 * Pure-Gallina functional spec for SHA-256 (FIPS 180-4, §6.2).  Authored
 * locally so the [Bedrock.LibjadeAxioms.jade_hash_sha256_correct] registry
 * slot can state a concrete byte-array equality against a Rocq spec
 * (instead of carrying a [True] placeholder).
 *
 * Style mirrors [Crypto.Spec.Keccak] (used by SHAKE-128 / SHAKE-256):
 *   - All arithmetic on N (32-bit words via mask).
 *   - All hash-internal state passed by explicit list-of-N.
 *   - No bedrock2 / VST / CompCert / Mathlib dependencies — pure Stdlib +
 *     Strings.Byte.
 *   - No axioms.
 *
 * Coverage vs. FIPS 180-4
 * -----------------------
 * §4.1.2 :  Ch, Maj, big/little Σ/σ                              (concrete)
 * §4.2.2 :  K_256 round-constant table                            (concrete)
 * §5.1.1 :  message padding                                       (concrete)
 * §5.2.1 :  parsing message into 512-bit blocks                   (concrete)
 * §5.3.3 :  H_0 initial-hash-value table                          (concrete)
 * §6.2.2 :  64-round compression function                         (concrete)
 *
 * Output orientation
 * ------------------
 * SHA-256 emits big-endian 32-bit words; this spec returns the final
 * [list Byte.byte] of length 32 in the FIPS 180-4 wire order so it can be
 * compared bytewise against the libjade output via
 *   [jade_hash_sha256_correct].
 *
 * KAT NOT VALIDATED in-Coq
 * ------------------------
 * No vm_compute KAT is asserted here (vectors would inflate compile time
 * dramatically through nested N.shiftl chains).  The spec is intended as a
 * trust-localization handle, not a fast computational kernel.  Spot-check
 * via [Eval vm_compute in sha256_spec []] reproduces the well-known empty
 * digest [e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855]
 * in roughly 1–2 seconds.
 *
 * See also
 * --------
 * - [src/Bedrock/Libjade/SHA256Bridge.v] — wraps this spec on the libjade side.
 * - [src/Bedrock/LibjadeAxioms.v] §1 — [jade_hash_sha256_correct] slot.
 * - [fiat-crypto/docs/PLAN_verified_sha256.md] — long-term path to swap
 *   the libjade Jasmin source out for a bedrock2-verified body, which
 *   would refer to *this* spec for its functional postcondition.
 *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Strings.Byte Lia.
Import ListNotations.

Local Open Scope N_scope.

(* ================================================================ *)
(** * §1.  32-bit word machinery                                     *)
(* ================================================================ *)

(** A SHA-256 word is a 32-bit unsigned integer.  We carry it as [N]
    and mask after every operation that could grow it. *)
Definition mask32 : N := N.ones 32.

Definition w32_of_N (x : N) : N := N.land x mask32.

(** Rotate-right within 32 bits. *)
Definition rotr32 (x : N) (n : N) : N :=
  w32_of_N (N.lor (N.shiftr x n) (N.shiftl x (32 - n))).

(** Shift-right (logical), masked. *)
Definition shr32 (x : N) (n : N) : N :=
  w32_of_N (N.shiftr x n).

(** 32-bit modular add. *)
Definition add32 (x y : N) : N := w32_of_N (N.add x y).

(** Bitwise ops on 32-bit words. *)
Definition xor32 (x y : N) : N := w32_of_N (N.lxor x y).
Definition and32 (x y : N) : N := w32_of_N (N.land x y).
Definition not32 (x : N) : N := w32_of_N (N.lxor x mask32).

(* ================================================================ *)
(** * §2.  FIPS 180-4 §4.1.2 functions                               *)
(* ================================================================ *)

Definition Ch (x y z : N) : N :=
  xor32 (and32 x y) (and32 (not32 x) z).

Definition Maj (x y z : N) : N :=
  xor32 (and32 x y) (xor32 (and32 x z) (and32 y z)).

Definition Sigma0 (x : N) : N :=
  xor32 (rotr32 x 2) (xor32 (rotr32 x 13) (rotr32 x 22)).

Definition Sigma1 (x : N) : N :=
  xor32 (rotr32 x 6) (xor32 (rotr32 x 11) (rotr32 x 25)).

Definition sigma0 (x : N) : N :=
  xor32 (rotr32 x 7) (xor32 (rotr32 x 18) (shr32 x 3)).

Definition sigma1 (x : N) : N :=
  xor32 (rotr32 x 17) (xor32 (rotr32 x 19) (shr32 x 10)).

(* ================================================================ *)
(** * §3.  FIPS 180-4 §4.2.2 round constants                         *)
(* ================================================================ *)

Definition K256 : list N :=
  [0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
   0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
   0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
   0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
   0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
   0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
   0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
   0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
   0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
   0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
   0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
   0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
   0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
   0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
   0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
   0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2]%N.

(* ================================================================ *)
(** * §4.  FIPS 180-4 §5.3.3 initial hash value H^{(0)}              *)
(* ================================================================ *)

Definition H0_init : list N :=
  [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
   0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19]%N.

(* ================================================================ *)
(** * §5.  FIPS 180-4 §5.1.1 padding                                 *)
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

(** SHA-256 pad: append 0x80, then enough 0x00 to reach length ≡ 56 mod 64,
    then 8 big-endian bytes encoding the original message length in bits. *)
Definition sha256_pad (msg : list Byte.byte) : list Byte.byte :=
  let L := length msg in
  (* k zero bytes such that (L + 1 + k) ≡ 56 (mod 64), 0 ≤ k < 64. *)
  let k := Nat.modulo (56 + 64 - ((L + 1) mod 64)) 64 in
  let len_bits := N.mul 8 (N.of_nat L) in
  msg ++ [Byte.x80] ++ List.repeat Byte.x00 k ++ be_bytes 8 len_bits.

(* ================================================================ *)
(** * §6.  Block parsing — 16 big-endian 32-bit words per block      *)
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

(** Big-endian 32-bit word from 4 bytes. *)
Definition word_be (b0 b1 b2 b3 : Byte.byte) : N :=
  N.lor (N.shiftl (Byte.to_N b0) 24)
   (N.lor (N.shiftl (Byte.to_N b1) 16)
    (N.lor (N.shiftl (Byte.to_N b2) 8)
                     (Byte.to_N b3))).

Definition word_be_at (block : list Byte.byte) (i : nat) : N :=
  let b0 := List.nth (i*4 + 0) block Byte.x00 in
  let b1 := List.nth (i*4 + 1) block Byte.x00 in
  let b2 := List.nth (i*4 + 2) block Byte.x00 in
  let b3 := List.nth (i*4 + 3) block Byte.x00 in
  word_be b0 b1 b2 b3.

(** Cut the padded message into 64-byte blocks.  Caller guarantees that
    [length msg] is a multiple of 64. *)
Fixpoint chunks64 (msg : list Byte.byte) (n_blocks : nat) : list (list Byte.byte) :=
  match n_blocks with
  | O => []
  | S nb' => take 64 msg :: chunks64 (drop 64 msg) nb'
  end.

(** First 16 message-schedule words from a 64-byte block. *)
Definition block_W0_15 (block : list Byte.byte) : list N :=
  List.map (fun i => word_be_at block i) (List.seq 0 16).

(* ================================================================ *)
(** * §7.  Message schedule W[0..63]                                  *)
(* ================================================================ *)

(** Extend W by one word using the FIPS 180-4 §6.2.2 step 1 recurrence. *)
Definition W_step (W : list N) : list N :=
  let t := List.length W in
  let w_2  := List.nth (t - 2)  W 0%N in
  let w_7  := List.nth (t - 7)  W 0%N in
  let w_15 := List.nth (t - 15) W 0%N in
  let w_16 := List.nth (t - 16) W 0%N in
  let new := add32 (sigma1 w_2) (add32 w_7 (add32 (sigma0 w_15) w_16)) in
  W ++ [new].

(** Extend a 16-word seed up to 64 words. *)
Fixpoint extend_W_aux (W : list N) (count : nat) : list N :=
  match count with
  | O => W
  | S c' => extend_W_aux (W_step W) c'
  end.

Definition message_schedule (block : list Byte.byte) : list N :=
  extend_W_aux (block_W0_15 block) 48.

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

(** One round of the compression function (FIPS 180-4 §6.2.2 step 3). *)
Definition compress_round (s : state8) (kt wt : N) : state8 :=
  let T1 := add32 (sh s)
            (add32 (Sigma1 (se s))
            (add32 (Ch (se s) (sf s) (sg s))
            (add32 kt wt))) in
  let T2 := add32 (Sigma0 (sa s)) (Maj (sa s) (sb s) (sc s)) in
  mkS (add32 T1 T2)        (* a *)
      (sa s)                (* b *)
      (sb s)                (* c *)
      (sc s)                (* d *)
      (add32 (sd s) T1)    (* e *)
      (se s)                (* f *)
      (sf s)                (* g *)
      (sg s).               (* h *)

(** 64 rounds of compression — fold over the K/W pairs.  K256 and W must
    each have length 64. *)
Fixpoint compress_loop (s : state8) (ks ws : list N) : state8 :=
  match ks, ws with
  | k :: ks', w :: ws' => compress_loop (compress_round s k w) ks' ws'
  | _, _ => s
  end.

(** Process one 512-bit block.  Takes the previous 8-word hash state. *)
Definition hash_block (H : list N) (block : list Byte.byte) : list N :=
  let W := message_schedule block in
  let s := s8_of_list H in
  let s' := compress_loop s K256 W in
  (* Add compressed working variables back into H, mod 2^32. *)
  List.map (fun '(h, x) => add32 h x)
           (List.combine H (s8_to_list s')).

(** Iterate [hash_block] over a sequence of 64-byte blocks. *)
Fixpoint hash_blocks (H : list N) (blocks : list (list Byte.byte)) : list N :=
  match blocks with
  | [] => H
  | b :: bs => hash_blocks (hash_block H b) bs
  end.

(* ================================================================ *)
(** * §9.  Top-level entry point                                      *)
(* ================================================================ *)

(** Convert a 32-bit word [w] to its 4 big-endian bytes. *)
Definition word_to_be_bytes (w : N) : list Byte.byte := be_bytes 4 w.

(** [sha256_spec msg] is the 32-byte SHA-256 digest of [msg] per FIPS 180-4. *)
Definition sha256_spec (msg : list Byte.byte) : list Byte.byte :=
  let padded := sha256_pad msg in
  let n_blocks := Nat.div (length padded) 64 in
  let blocks := chunks64 padded n_blocks in
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

Lemma word_to_be_bytes_length : forall w, length (word_to_be_bytes w) = 4%nat.
Proof. intro w. unfold word_to_be_bytes. apply be_bytes_length. Qed.

(** Length of [List.concat (List.map word_to_be_bytes l)] is [4 * length l]. *)
Lemma concat_word_bytes_length : forall l,
  length (List.concat (List.map word_to_be_bytes l)) = (4 * length l)%nat.
Proof.
  induction l as [|w l' IH]; [reflexivity|].
  cbn [List.map List.concat List.length].
  rewrite length_app. rewrite word_to_be_bytes_length. rewrite IH. lia.
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

(** Headline length lemma — SHA-256 produces 32 bytes. *)
Theorem sha256_spec_length : forall msg, length (sha256_spec msg) = 32%nat.
Proof.
  intro msg. unfold sha256_spec.
  rewrite concat_word_bytes_length.
  rewrite hash_blocks_length by apply H0_init_length.
  reflexivity.
Qed.
