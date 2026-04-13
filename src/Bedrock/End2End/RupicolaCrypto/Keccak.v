(** * Keccak-f[1600] + SHAKE-256 — bedrock2 implementation

    25 × u64 state in memory. 24-round permutation.
    SHAKE-256: rate=136, dsep=0x1F, outlen=64 for XEdDSA.

    The inner operations (theta, rho, pi, chi, iota) are implemented
    as bedrock2 functions operating on the 200-byte state array.

    ## Verification chain
    bedrock2 WP → ToJasmin → jasminc → x86-64 *)

From Coq Require Import String List ZArith.
From Coq.Init Require Import Byte.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

(** * Constants *)

(** Round constants for iota step (24 rounds). *)
Definition RC : list Z :=
  [ 1; 32898; 9223372036854808714; 9223372039002292224;
    32907; 2147483649; 9223372039002292353; 9223372036854808585;
    138; 136; 2147516425; 2147483658;
    2147516555; 9223372036854775947; 9223372036854808713;
    9223372036854808579; 9223372036854808578; 9223372036854775936;
    32778; 9223372039002259466; 9223372039002292353; 9223372036854808704;
    2147483649; 9223372039002292232 ].

(** Rotation offsets for rho step (25 lanes). *)
Definition ROT : list Z :=
  [ 0; 1; 62; 28; 27; 36; 44; 6; 55; 20;
    3; 10; 43; 25; 39; 41; 45; 15; 21; 8;
    18; 2; 61; 56; 14 ].

(** Pi source indices. pi(i) = PI_SRC[i]. *)
Definition PI_SRC : list Z :=
  [ 0; 6; 12; 18; 24; 3; 9; 10; 16; 22;
    1; 7; 13; 19; 20; 4; 5; 11; 17; 23;
    2; 8; 14; 15; 21 ].

(** * Helper: 64-bit rotate left
    rotl64(x, n) = (x << n) | (x >> (64 - n)) *)
Definition rotl64 := func! (ret, x, n) {
  if (n == $0) {
    store(ret, x)
  } else {
    store(ret, (x << n) | (x >> ($64 - n)))
  }
}.

(** * Theta step
    C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]
    D[x] = C[x-1] ^ rotl(C[x+1], 1)
    A[x,y] ^= D[x]

    state layout: A[x,y] at offset (x + 5*y) * 8 bytes *)

Definition keccak_theta := func! (state) {
  stackalloc 40 as C;  (* 5 × u64 *)
  stackalloc 40 as D;

  (* C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4] *)
  (* x = 0..4 *)
  store(C,      load(state)      ^ load(state+$40)  ^ load(state+$80)  ^ load(state+$120) ^ load(state+$160));
  store(C+$8,   load(state+$8)   ^ load(state+$48)  ^ load(state+$88)  ^ load(state+$128) ^ load(state+$168));
  store(C+$16,  load(state+$16)  ^ load(state+$56)  ^ load(state+$96)  ^ load(state+$136) ^ load(state+$176));
  store(C+$24,  load(state+$24)  ^ load(state+$64)  ^ load(state+$104) ^ load(state+$144) ^ load(state+$184));
  store(C+$32,  load(state+$32)  ^ load(state+$72)  ^ load(state+$112) ^ load(state+$152) ^ load(state+$192));

  (* D[x] = C[(x+4)%5] ^ rotl(C[(x+1)%5], 1) *)
  store(D,      load(C+$32) ^ ((load(C+$8)  << $1) | (load(C+$8)  >> $63)));
  store(D+$8,   load(C)     ^ ((load(C+$16) << $1) | (load(C+$16) >> $63)));
  store(D+$16,  load(C+$8)  ^ ((load(C+$24) << $1) | (load(C+$24) >> $63)));
  store(D+$24,  load(C+$16) ^ ((load(C+$32) << $1) | (load(C+$32) >> $63)));
  store(D+$32,  load(C+$24) ^ ((load(C)     << $1) | (load(C)     >> $63)));

  (* A[i] ^= D[i % 5] for all 25 lanes *)
  store(state,      load(state)      ^ load(D));
  store(state+$8,   load(state+$8)   ^ load(D+$8));
  store(state+$16,  load(state+$16)  ^ load(D+$16));
  store(state+$24,  load(state+$24)  ^ load(D+$24));
  store(state+$32,  load(state+$32)  ^ load(D+$32));

  store(state+$40,  load(state+$40)  ^ load(D));
  store(state+$48,  load(state+$48)  ^ load(D+$8));
  store(state+$56,  load(state+$56)  ^ load(D+$16));
  store(state+$64,  load(state+$64)  ^ load(D+$24));
  store(state+$72,  load(state+$72)  ^ load(D+$32));

  store(state+$80,  load(state+$80)  ^ load(D));
  store(state+$88,  load(state+$88)  ^ load(D+$8));
  store(state+$96,  load(state+$96)  ^ load(D+$16));
  store(state+$104, load(state+$104) ^ load(D+$24));
  store(state+$112, load(state+$112) ^ load(D+$32));

  store(state+$120, load(state+$120) ^ load(D));
  store(state+$128, load(state+$128) ^ load(D+$8));
  store(state+$136, load(state+$136) ^ load(D+$16));
  store(state+$144, load(state+$144) ^ load(D+$24));
  store(state+$152, load(state+$152) ^ load(D+$32));

  store(state+$160, load(state+$160) ^ load(D));
  store(state+$168, load(state+$168) ^ load(D+$8));
  store(state+$176, load(state+$176) ^ load(D+$16));
  store(state+$184, load(state+$184) ^ load(D+$24));
  store(state+$192, load(state+$192) ^ load(D+$32))
}.

(** * Rho + Pi combined step
    B[y, 2x+3y mod 5] = rotl(A[x,y], rho_offset[x + 5y])
    We precompute: for output index i, source = PI_SRC[i], rot = ROT[PI_SRC[i]]

    Since both rho and pi are fixed permutations, we unroll completely:
    B[i] = rotl(state[PI_SRC[i]], ROT[PI_SRC[i]])
    Then copy B back to state. *)

Definition keccak_rho_pi := func! (state) {
  stackalloc 200 as B;

  (* B[0]  = rotl(state[0*8],  0) = state[0] *)
  store(B,       load(state));
  (* B[1]  = rotl(state[6*8],  44) *)
  store(B+$8,    (load(state+$48)  << $44) | (load(state+$48)  >> $20));
  (* B[2]  = rotl(state[12*8], 43) *)
  store(B+$16,   (load(state+$96)  << $43) | (load(state+$96)  >> $21));
  (* B[3]  = rotl(state[18*8], 21) *)
  store(B+$24,   (load(state+$144) << $21) | (load(state+$144) >> $43));
  (* B[4]  = rotl(state[24*8], 14) *)
  store(B+$32,   (load(state+$192) << $14) | (load(state+$192) >> $50));
  (* B[5]  = rotl(state[3*8],  28) *)
  store(B+$40,   (load(state+$24)  << $28) | (load(state+$24)  >> $36));
  (* B[6]  = rotl(state[9*8],  20) *)
  store(B+$48,   (load(state+$72)  << $20) | (load(state+$72)  >> $44));
  (* B[7]  = rotl(state[10*8], 3) *)
  store(B+$56,   (load(state+$80)  << $3)  | (load(state+$80)  >> $61));
  (* B[8]  = rotl(state[16*8], 45) *)
  store(B+$64,   (load(state+$128) << $45) | (load(state+$128) >> $19));
  (* B[9]  = rotl(state[22*8], 61) *)
  store(B+$72,   (load(state+$176) << $61) | (load(state+$176) >> $3));
  (* B[10] = rotl(state[1*8],  1) *)
  store(B+$80,   (load(state+$8)   << $1)  | (load(state+$8)   >> $63));
  (* B[11] = rotl(state[7*8],  6) *)
  store(B+$88,   (load(state+$56)  << $6)  | (load(state+$56)  >> $58));
  (* B[12] = rotl(state[13*8], 25) *)
  store(B+$96,   (load(state+$104) << $25) | (load(state+$104) >> $39));
  (* B[13] = rotl(state[19*8], 8) *)
  store(B+$104,  (load(state+$152) << $8)  | (load(state+$152) >> $56));
  (* B[14] = rotl(state[20*8], 18) *)
  store(B+$112,  (load(state+$160) << $18) | (load(state+$160) >> $46));
  (* B[15] = rotl(state[4*8],  27) *)
  store(B+$120,  (load(state+$32)  << $27) | (load(state+$32)  >> $37));
  (* B[16] = rotl(state[5*8],  36) *)
  store(B+$128,  (load(state+$40)  << $36) | (load(state+$40)  >> $28));
  (* B[17] = rotl(state[11*8], 10) *)
  store(B+$136,  (load(state+$88)  << $10) | (load(state+$88)  >> $54));
  (* B[18] = rotl(state[17*8], 15) *)
  store(B+$144,  (load(state+$136) << $15) | (load(state+$136) >> $49));
  (* B[19] = rotl(state[23*8], 56) *)
  store(B+$152,  (load(state+$184) << $56) | (load(state+$184) >> $8));
  (* B[20] = rotl(state[2*8],  62) *)
  store(B+$160,  (load(state+$16)  << $62) | (load(state+$16)  >> $2));
  (* B[21] = rotl(state[8*8],  55) *)
  store(B+$168,  (load(state+$64)  << $55) | (load(state+$64)  >> $9));
  (* B[22] = rotl(state[14*8], 39) *)
  store(B+$176,  (load(state+$112) << $39) | (load(state+$112) >> $25));
  (* B[23] = rotl(state[15*8], 41) *)
  store(B+$184,  (load(state+$120) << $41) | (load(state+$120) >> $23));
  (* B[24] = rotl(state[21*8], 2) *)
  store(B+$192,  (load(state+$168) << $2)  | (load(state+$168) >> $62));

  (* Copy B back to state — 25 stores *)
  store(state,      load(B));      store(state+$8,   load(B+$8));
  store(state+$16,  load(B+$16));  store(state+$24,  load(B+$24));
  store(state+$32,  load(B+$32));  store(state+$40,  load(B+$40));
  store(state+$48,  load(B+$48));  store(state+$56,  load(B+$56));
  store(state+$64,  load(B+$64));  store(state+$72,  load(B+$72));
  store(state+$80,  load(B+$80));  store(state+$88,  load(B+$88));
  store(state+$96,  load(B+$96));  store(state+$104, load(B+$104));
  store(state+$112, load(B+$112)); store(state+$120, load(B+$120));
  store(state+$128, load(B+$128)); store(state+$136, load(B+$136));
  store(state+$144, load(B+$144)); store(state+$152, load(B+$152));
  store(state+$160, load(B+$160)); store(state+$168, load(B+$168));
  store(state+$176, load(B+$176)); store(state+$184, load(B+$184));
  store(state+$192, load(B+$192))
}.

(** * Chi step
    A[x,y] = B[x,y] ^ ((~B[x+1,y]) & B[x+2,y])
    We read from state (which has B after rho_pi) and write back.
    Process 5 lanes at a time per row. *)

Definition keccak_chi := func! (state) {
  stackalloc 40 as T; (* 5-lane temporary per row *)
  (* Row 0: lanes 0..4 *)
  store(T,      load(state)      ^ ((load(state+$8)   ^ coq:(expr.literal (2^64 - 1))) & load(state+$16)));
  store(T+$8,   load(state+$8)   ^ ((load(state+$16)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$24)));
  store(T+$16,  load(state+$16)  ^ ((load(state+$24)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$32)));
  store(T+$24,  load(state+$24)  ^ ((load(state+$32)  ^ coq:(expr.literal (2^64 - 1))) & load(state)));
  store(T+$32,  load(state+$32)  ^ ((load(state)       ^ coq:(expr.literal (2^64 - 1))) & load(state+$8)));
  store(state,      load(T));      store(state+$8,   load(T+$8));
  store(state+$16,  load(T+$16)); store(state+$24,  load(T+$24));
  store(state+$32,  load(T+$32));

  (* Row 1: lanes 5..9 *)
  store(T,      load(state+$40)  ^ ((load(state+$48)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$56)));
  store(T+$8,   load(state+$48)  ^ ((load(state+$56)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$64)));
  store(T+$16,  load(state+$56)  ^ ((load(state+$64)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$72)));
  store(T+$24,  load(state+$64)  ^ ((load(state+$72)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$40)));
  store(T+$32,  load(state+$72)  ^ ((load(state+$40)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$48)));
  store(state+$40,  load(T));      store(state+$48,  load(T+$8));
  store(state+$56,  load(T+$16)); store(state+$64,  load(T+$24));
  store(state+$72,  load(T+$32));

  (* Row 2: lanes 10..14 *)
  store(T,      load(state+$80)  ^ ((load(state+$88)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$96)));
  store(T+$8,   load(state+$88)  ^ ((load(state+$96)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$104)));
  store(T+$16,  load(state+$96)  ^ ((load(state+$104) ^ coq:(expr.literal (2^64 - 1))) & load(state+$112)));
  store(T+$24,  load(state+$104) ^ ((load(state+$112) ^ coq:(expr.literal (2^64 - 1))) & load(state+$80)));
  store(T+$32,  load(state+$112) ^ ((load(state+$80)  ^ coq:(expr.literal (2^64 - 1))) & load(state+$88)));
  store(state+$80,  load(T));      store(state+$88,  load(T+$8));
  store(state+$96,  load(T+$16)); store(state+$104, load(T+$24));
  store(state+$112, load(T+$32));

  (* Row 3: lanes 15..19 *)
  store(T,      load(state+$120) ^ ((load(state+$128) ^ coq:(expr.literal (2^64 - 1))) & load(state+$136)));
  store(T+$8,   load(state+$128) ^ ((load(state+$136) ^ coq:(expr.literal (2^64 - 1))) & load(state+$144)));
  store(T+$16,  load(state+$136) ^ ((load(state+$144) ^ coq:(expr.literal (2^64 - 1))) & load(state+$152)));
  store(T+$24,  load(state+$144) ^ ((load(state+$152) ^ coq:(expr.literal (2^64 - 1))) & load(state+$120)));
  store(T+$32,  load(state+$152) ^ ((load(state+$120) ^ coq:(expr.literal (2^64 - 1))) & load(state+$128)));
  store(state+$120, load(T));      store(state+$128, load(T+$8));
  store(state+$136, load(T+$16)); store(state+$144, load(T+$24));
  store(state+$152, load(T+$32));

  (* Row 4: lanes 20..24 *)
  store(T,      load(state+$160) ^ ((load(state+$168) ^ coq:(expr.literal (2^64 - 1))) & load(state+$176)));
  store(T+$8,   load(state+$168) ^ ((load(state+$176) ^ coq:(expr.literal (2^64 - 1))) & load(state+$184)));
  store(T+$16,  load(state+$176) ^ ((load(state+$184) ^ coq:(expr.literal (2^64 - 1))) & load(state+$192)));
  store(T+$24,  load(state+$184) ^ ((load(state+$192) ^ coq:(expr.literal (2^64 - 1))) & load(state+$160)));
  store(T+$32,  load(state+$192) ^ ((load(state+$160) ^ coq:(expr.literal (2^64 - 1))) & load(state+$168)));
  store(state+$160, load(T));      store(state+$168, load(T+$8));
  store(state+$176, load(T+$16)); store(state+$184, load(T+$24));
  store(state+$192, load(T+$32))
}.

(** * Iota step: state[0] ^= round_constant *)
Definition keccak_iota := func! (state, rc) {
  store(state, load(state) ^ rc)
}.

(** * One round = theta + rho_pi + chi + iota *)
Definition keccak_round := func! (state, rc) {
  keccak_theta(state);
  keccak_rho_pi(state);
  keccak_chi(state);
  keccak_iota(state, rc)
}.

(** * Keccak-f[1600]: 24 rounds *)
Definition keccak_f := func! (state) {
  keccak_round(state, $1);
  keccak_round(state, $32898);
  keccak_round(state, $9223372036854808714);
  keccak_round(state, $9223372039002292224);
  keccak_round(state, $32907);
  keccak_round(state, $2147483649);
  keccak_round(state, $9223372039002292353);
  keccak_round(state, $9223372036854808585);
  keccak_round(state, $138);
  keccak_round(state, $136);
  keccak_round(state, $2147516425);
  keccak_round(state, $2147483658);
  keccak_round(state, $2147516555);
  keccak_round(state, $9223372036854775947);
  keccak_round(state, $9223372036854808713);
  keccak_round(state, $9223372036854808579);
  keccak_round(state, $9223372036854808578);
  keccak_round(state, $9223372036854775936);
  keccak_round(state, $32778);
  keccak_round(state, $9223372039002259466);
  keccak_round(state, $9223372039002292353);
  keccak_round(state, $9223372036854808704);
  keccak_round(state, $2147483649);
  keccak_round(state, $9223372039002292232)
}.

(** * Sponge: absorb + squeeze *)

(** XOR one byte into state at byte offset i.
    Since state is stored as u64 lanes, byte i is in lane i/8,
    bit position (i%8)*8. *)
Definition xor_byte_into_state := func! (state, byte_val, offset) {
  store(state + (offset & coq:(expr.literal (Z.land (Z.ones 3 * (-8)) (2^64 - 1)))) (* align to 8 *),
    load(state + (offset & coq:(expr.literal (Z.land (Z.ones 3 * (-8)) (2^64 - 1))))) ^
    (byte_val << ((offset & $7) << $3)))
}.

(** Absorb: pad message and absorb into state.
    For SHAKE-256: rate=136 bytes, dsep=0x1F.
    For simplicity with XEdDSA (msg ≤ a few KB),
    we process byte-by-byte. A production implementation
    would process 8-byte lanes at a time. *)
Definition shake256_absorb := func! (state, msg, msg_len) {
  (* XOR message bytes into state, permuting every 136 bytes *)
  coq:(cmd.set "i" (expr.literal 0));
  coq:(cmd.set "pos" (expr.literal 0));
  while (coq:(expr.op bopname.ltu (expr.var "i") (expr.var "msg_len"))) {
    (* XOR msg[i] into state at byte position pos.
       Lane index = pos / 8, byte shift = (pos % 8) * 8.
       We XOR the byte (zero-extended to u64, shifted) into the lane. *)
    coq:(cmd.set "lane_off" (expr.op bopname.and (expr.var "pos") (expr.literal (Z.lnot 7))));
    coq:(cmd.set "byte_shift" (expr.op bopname.slu
           (expr.op bopname.and (expr.var "pos") (expr.literal 7))
           (expr.literal 3)));
    coq:(cmd.set "msg_byte" (expr.load access_size.one
           (expr.op bopname.add (expr.var "msg") (expr.var "i"))));
    coq:(cmd.store access_size.word
           (expr.op bopname.add (expr.var "state") (expr.var "lane_off"))
           (expr.op bopname.xor
              (expr.load access_size.word
                 (expr.op bopname.add (expr.var "state") (expr.var "lane_off")))
              (expr.op bopname.slu (expr.var "msg_byte") (expr.var "byte_shift"))))
    ;
    coq:(cmd.set "pos" (expr.op bopname.add (expr.var "pos") (expr.literal 1)));
    coq:(cmd.set "i" (expr.op bopname.add (expr.var "i") (expr.literal 1)));
    if (coq:(expr.op bopname.eq (expr.var "pos") (expr.literal 136))) {
      keccak_f(state);
      coq:(cmd.set "pos" (expr.literal 0))
    } else {
      coq:(cmd.skip)
    }
  };
  (* Padding: XOR dsep (0x1F for SHAKE-256) at byte position pos *)
  coq:(cmd.set "lane_off" (expr.op bopname.and (expr.var "pos") (expr.literal (Z.lnot 7))));
  coq:(cmd.set "byte_shift" (expr.op bopname.slu
         (expr.op bopname.and (expr.var "pos") (expr.literal 7))
         (expr.literal 3)));
  coq:(cmd.store access_size.word
         (expr.op bopname.add (expr.var "state") (expr.var "lane_off"))
         (expr.op bopname.xor
            (expr.load access_size.word
               (expr.op bopname.add (expr.var "state") (expr.var "lane_off")))
            (expr.op bopname.slu (expr.literal 0x1F) (expr.var "byte_shift"))));

  (* XOR 0x80 at byte position rate-1 = 135 *)
  (* Lane 135/8 = 16, byte 135%8 = 7, shift = 56 *)
  coq:(cmd.store access_size.word
         (expr.op bopname.add (expr.var "state") (expr.literal 128))
         (expr.op bopname.xor
            (expr.load access_size.word
               (expr.op bopname.add (expr.var "state") (expr.literal 128)))
            (expr.literal (0x80 * 2^56)))) (* 0x80 << 56 *)
  ;
  keccak_f(state)
}.

(** Squeeze 64 bytes from state (SHAKE-256 with outlen=64).
    Since 64 < 136 (rate), only one squeeze step — no extra permutations. *)
Definition shake256_squeeze_64 := func! (out, state) {
  (* Copy first 64 bytes (8 lanes) from state to out *)
  store(out,      load(state));
  store(out+$8,   load(state+$8));
  store(out+$16,  load(state+$16));
  store(out+$24,  load(state+$24));
  store(out+$32,  load(state+$32));
  store(out+$40,  load(state+$40));
  store(out+$48,  load(state+$48));
  store(out+$56,  load(state+$56))
}.

(** * SHAKE-256 with 64-byte output *)
Definition shake256_64 := func! (out, msg, msg_len) {
  stackalloc 200 as state;
  (* Zero state: 25 × u64 = 200 bytes *)
  store(state,      $0); store(state+$8,   $0); store(state+$16,  $0);
  store(state+$24,  $0); store(state+$32,  $0); store(state+$40,  $0);
  store(state+$48,  $0); store(state+$56,  $0); store(state+$64,  $0);
  store(state+$72,  $0); store(state+$80,  $0); store(state+$88,  $0);
  store(state+$96,  $0); store(state+$104, $0); store(state+$112, $0);
  store(state+$120, $0); store(state+$128, $0); store(state+$136, $0);
  store(state+$144, $0); store(state+$152, $0); store(state+$160, $0);
  store(state+$168, $0); store(state+$176, $0); store(state+$184, $0);
  store(state+$192, $0);

  shake256_absorb(state, msg, msg_len);
  shake256_squeeze_64(out, state)
}.

(** * WP Proofs *)

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.SortedListWord.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Local Existing Instances SortedListString.map SortedListWord.map coqutil.Word.Naive.word.

(** Keccak state: 200 bytes (25 × u64).
    We represent it as a list of 200 bytes for sep-logic. *)

(** spec_of for shake256_64: the top-level function.
    Computes SHAKE-256 with 64-byte output. *)
Global Instance spec_of_shake256_64 : spec_of "shake256_64" :=
  fnspec! "shake256_64" out msg msg_len /
    (out_bytes msg_bytes : list Byte.byte) (R : _ -> Prop),
  { requires t m :=
      m =* out_bytes$@out * msg_bytes$@msg * R /\
      length out_bytes = 64%nat /\
      length msg_bytes = Z.to_nat (word.unsigned msg_len);
    ensures t' m :=
      t = t' /\
      exists result : list Byte.byte,
        m =* result$@out * msg_bytes$@msg * R /\
        length result = 64%nat
        (* Functional correctness:
           result = Keccak.keccak_sponge 136 Byte.x1f msg_bytes 64 *)
  }.

(** spec_of for keccak_f: the 24-round permutation.
    Transforms 200 bytes of state in-place. *)
Global Instance spec_of_keccak_f : spec_of "keccak_f" :=
  fnspec! "keccak_f" state /
    (state_bytes : list Byte.byte) (R : _ -> Prop),
  { requires t m :=
      m =* state_bytes$@state * R /\
      length state_bytes = 200%nat;
    ensures t' m :=
      t = t' /\
      exists state_bytes' : list Byte.byte,
        m =* state_bytes'$@state * R /\
        length state_bytes' = 200%nat
        (* Functional correctness:
           state_bytes' = Keccak.keccak_f applied to state_bytes *)
  }.

(** spec_of for squeeze: copies first 64 bytes from state to out. *)
Global Instance spec_of_shake256_squeeze_64 : spec_of "shake256_squeeze_64" :=
  fnspec! "shake256_squeeze_64" out state /
    (out_bytes state_bytes : list Byte.byte) (R : _ -> Prop),
  { requires t m :=
      m =* out_bytes$@out * state_bytes$@state * R /\
      length out_bytes = 64%nat /\
      length state_bytes = 200%nat;
    ensures t' m :=
      t = t' /\
      exists result : list Byte.byte,
        m =* result$@out * state_bytes$@state * R /\
        length result = 64%nat /\
        result = firstn 64 state_bytes
  }.

(** * WP Proof Strategy

    The [program_logic_goal_for_function!] macro fails on complex
    function bodies (Keccak functions have hundreds of operations).
    Instead, we prove correctness by:

    1. Stating the spec as [spec_of] instances (done above)
    2. Proving each function correct MANUALLY with targeted
       [straightline] calls, NOT [repeat straightline] on the
       whole body (which causes term-size explosion)
    3. For each store/load: one [straightline] step
    4. For function calls: [straightline_call; ssplit]
    5. For loops: explicit invariant + [Loops.tailrec_earlyout]

    The proofs are STRUCTURALLY simple (straightline code) but
    LARGE (hundreds of steps for theta/rho_pi/chi). *)

(** Proof for squeeze: 8 word copies (state → out).
    Manual proof instead of [program_logic_goal_for_function!]. *)
Lemma shake256_squeeze_64_ok :
  forall functions,
    spec_of_shake256_squeeze_64 (("shake256_squeeze_64", shake256_squeeze_64) :: functions) ->
    forall t m out state out_bytes state_bytes R,
      m =* out_bytes$@out * state_bytes$@state * R ->
      length out_bytes = 64%nat ->
      length state_bytes = 200%nat ->
      WeakestPrecondition.call
        (("shake256_squeeze_64", shake256_squeeze_64) :: functions)
        "shake256_squeeze_64" t m [out; state]
        (fun t' m' =>
           t = t' /\
           exists result,
             m' =* result$@out * state_bytes$@state * R /\
             length result = 64%nat /\
             result = firstn 64 state_bytes).
Proof.
  (* The proof would proceed:
     - Unfold shake256_squeeze_64 (8 store instructions)
     - For each store(out + k*8, load(state + k*8)):
       1. [straightline] to handle the load
       2. [straightline] to handle the store
     - Final sep-logic: the 8 stored words = firstn 64 state_bytes *)
Admitted.

(** Proof for keccak_f: 24 calls to keccak_round.
    Each call preserves state length = 200. *)
Lemma keccak_f_ok :
  forall functions,
    spec_of_keccak_f (("keccak_f", keccak_f) :: functions) ->
    forall t m state state_bytes R,
      m =* state_bytes$@state * R ->
      length state_bytes = 200%nat ->
      WeakestPrecondition.call
        (("keccak_f", keccak_f) :: functions)
        "keccak_f" t m [state]
        (fun t' m' =>
           t = t' /\
           exists state_bytes',
             m' =* state_bytes'$@state * R /\
             length state_bytes' = 200%nat).
Proof.
  (* 24 sequential straightline_call invocations.
     Each keccak_round preserves length = 200.
     NOT using [repeat straightline] — too slow on 24 calls.
     Instead: 24× [straightline_call; ssplit; [ecancel_assumption | ...]]. *)
Admitted.

(** Proof for shake256_64: zero + absorb + squeeze. *)
Lemma shake256_64_ok :
  forall functions,
    spec_of_shake256_64 (("shake256_64", shake256_64) :: functions) ->
    forall t m out msg msg_len out_bytes msg_bytes R,
      m =* out_bytes$@out * msg_bytes$@msg * R ->
      length out_bytes = 64%nat ->
      length msg_bytes = Z.to_nat (word.unsigned msg_len) ->
      WeakestPrecondition.call
        (("shake256_64", shake256_64) :: functions)
        "shake256_64" t m [out; msg; msg_len]
        (fun t' m' =>
           t = t' /\
           exists result,
             m' =* result$@out * msg_bytes$@msg * R /\
             length result = 64%nat).
Proof.
  (* 1. stackalloc 200 as state (25 zero-stores)
     2. straightline_call shake256_absorb (loop)
     3. straightline_call shake256_squeeze_64 (8 copies) *)
Admitted.

(** WP proof chain summary:

    shake256_64_ok
      → 25 straightline steps (zero-init state)
      → straightline_call shake256_absorb_ok
        → loop invariant: i bytes processed, state updated
        → straightline_call keccak_f_ok (per block)
          → 24× straightline_call keccak_round_ok
            → straightline_call keccak_theta_ok (50 load/XOR/store)
            → straightline_call keccak_rho_pi_ok (25 rotl + 25 copy)
            → straightline_call keccak_chi_ok (5 rows × 5 NOT-AND)
            → straightline_call keccak_iota_ok (1 XOR)
      → straightline_call shake256_squeeze_64_ok (8 store)

    Total: ~800 lines of targeted straightline.
    Each leaf function's proof is independent and can be verified separately. *)
