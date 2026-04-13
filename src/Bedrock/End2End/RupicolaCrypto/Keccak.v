(** * Keccak/SHAKE-256 — bedrock2 implementation

    Implements the Keccak-f[1600] permutation and SHAKE-256 sponge
    in bedrock2, following the Gallina spec in Spec/Keccak.v.

    State: 25 × u64 words (200 bytes) stored as a memory array.
    The permutation is 24 rounds of theta-rho-pi-chi-iota.

    For XEdDSA: SHAKE-256 with 64-byte output (rate=136, dsep=0x1F).

    ## Verification chain
    bedrock2 WP proof → ToJasmin → jasminc → x86-64

    ## Design decisions
    - keccak_f: 24-round LOOP (not unrolled) — keeps code small
    - absorb: loop over rate-sized blocks, XOR into state, permute
    - squeeze: single extraction (outlen ≤ rate for SHAKE-256 with 64 bytes)
    - State in memory (not locals) — 200 bytes too large for registers *)

From Coq Require Import String List ZArith.
From Coq.Init Require Import Byte.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

(** * Round constants (from NIST FIPS 202) *)

Definition keccak_RC : list Z :=
  [ 1; 32898; 9223372036854808714; 9223372039002292224;
    32907; 2147483649; 9223372039002292353; 9223372036854808585;
    138; 136; 2147516425; 2147483658;
    2147516555; 9223372036854775947; 9223372036854808713;
    9223372036854808579; 9223372036854808578; 9223372036854775936;
    32778; 9223372039002259466; 9223372039002292353; 9223372036854808704;
    2147483649; 9223372039002292232 ].

(** * Rotation offsets *)

Definition keccak_rotl : list Z :=
  [ 0; 1; 62; 28; 27; 36; 44; 6; 55; 20;
    3; 10; 43; 25; 39; 41; 45; 15; 21; 8;
    18; 2; 61; 56; 14 ].

(** * Pi permutation source indices *)

Definition keccak_pi_src : list Z :=
  [ 0; 6; 12; 18; 24; 3; 9; 10; 16; 22;
    1; 7; 13; 19; 20; 4; 5; 11; 17; 23;
    2; 8; 14; 15; 21 ].

(** * bedrock2 Keccak-f[1600] permutation

    Operates on a 25-word (200-byte) state array in memory.
    24 rounds of theta-rho-pi-chi-iota. *)

(** Helper: 64-bit rotate left *)
Definition rotl64 := func! (x, n) {
  if (n == $0) { x = x }
  else { x = (x << n) | (x >> ($64 - n)) }
}.

(** One round of Keccak-f *)
Definition keccak_round := func! (state, rc) {
  (* Theta: compute column parities, XOR into state *)
  stackalloc 40 as C; (* 5 × u64 *)
  stackalloc 40 as D;

  (* C[x] = state[x] ^ state[x+5] ^ state[x+10] ^ state[x+15] ^ state[x+20] *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder for theta loop *)
  ;

  (* Rho + Pi: rotate and permute *)
  stackalloc 200 as B; (* 25 × u64 temporary *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder for rho-pi *)
  ;

  (* Chi: nonlinear step *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder for chi *)
  ;

  (* Iota: XOR round constant *)
  store(state, load(state) ^ rc)
}.

(** Full 24-round Keccak-f permutation *)
Definition keccak_f := func! (state) {
  (* 24 rounds with round constants *)
  (* For bedrock2: use a loop counter and index into RC array *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: 24 iterations of keccak_round *)
}.

(** * Sponge construction *)

(** XOR rate_bytes of message into state, then permute *)
Definition absorb_block := func! (state, block, rate_bytes) {
  (* XOR block[0..rate_bytes-1] into state[0..rate_bytes-1] *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: byte-wise XOR loop *)
  ;
  keccak_f(state)
}.

(** Pad message, absorb all blocks *)
Definition sponge_absorb := func! (state, msg, msg_len, rate, dsep) {
  (* Process full blocks *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: loop over full blocks *)
  ;
  (* Pad last block: msg || dsep || 0* || 0x80 *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: padding *)
  ;
  keccak_f(state)
}.

(** Extract output bytes from state *)
Definition sponge_squeeze := func! (out, state, outlen, rate) {
  (* For SHAKE-256 with outlen=64 and rate=136: outlen < rate,
     so only one squeeze step is needed (no extra permutations). *)
  (* Copy first outlen bytes from state to out *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: memcpy state[0..outlen-1] → out *)
}.

(** * SHAKE-256: rate=136, dsep=0x1F, outlen=64 *)

Definition shake256_64 := func! (out, msg, msg_len) {
  stackalloc 200 as state;
  (* Zero-initialize state *)
  coq:(cmd.seq cmd.skip cmd.skip) (* placeholder: memset 0 *)
  ;
  sponge_absorb(state, msg, msg_len, $136, $31);
  sponge_squeeze(out, state, $64, $136)
}.

(** * Specification *)

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
From Coq.Init Require Import Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

(** SHAKE-256 with 64-byte output: the spec links to Keccak.keccak_sponge.

    The bedrock2 function shake256_64(out, msg, msg_len) computes:
      out[0..63] = keccak_sponge(136, 0x1F, msg[0..msg_len-1], 64)

    For the full spec_of and WP proof, we need:
    1. The keccak_f permutation correctness (24-round loop = Keccak.keccak_f)
    2. The absorb loop correctness (block-by-block = Keccak.absorb)
    3. The squeeze correctness (single step since 64 < 136)
    4. Composition: sponge = absorb + squeeze *)

(* TODO: spec_of_shake256_64 and WP proof.
   The function bodies above use placeholders (cmd.skip).
   The actual implementation requires:
   - Unrolled theta/rho/pi/chi/iota OR loop-based keccak_round
   - Byte-wise XOR for absorb (or lane-wise for efficiency)
   - Memcpy for squeeze output

   The WP proof follows the absorb/squeeze structure from Keccak.v,
   using the existing length preservation lemmas (SHAKE128_length pattern).

   Estimated: 2-3 weeks for the full implementation + WP proof.
   The keccak_f permutation alone is ~500 lines of bedrock2 + proof. *)
