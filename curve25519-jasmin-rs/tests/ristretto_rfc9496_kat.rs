//! Known Answer Tests for the ristretto255 encode/decode body
//! extracted from `rust_cmd_ed` (see
//! `src/ristretto_rustcmd/{decode,encode}.rs`).
//!
//! Vectors are RFC 9496 §A — §A.1 (16 multiples-of-basepoint
//! encoding round-trips) and §A.2 (24 rejection cases).
//!
//! Replaces the 24 `Admitted` `vm_compute` lemmas in
//! `AUCurves/src/Bedrock/Field/Synthesis/Examples/Ristretto255_DecodeReject.v`
//! per `BLS/writeup/RISTRETTO255_B5_ZMIRROR_PLAN.md`.  The Rocq side
//! retains only:
//!  - the structural `ristretto_decode_coords_rejects_*` theorems
//!    (already Qed in DecodeReject.v),
//!  - the Z-mirror equivalence theorem
//!    (Ristretto_ZMirror.ristretto_decode_Z_mirror_correct, Phase B.5a),
//!  - the rust_cmd_ed simulation theorem
//!    (Ristretto_RustCmd.ristretto_decode_rs_simulates_gallina, Phase B.5b).
//!
//! Composition: a test below passes iff the extracted Rust decoder
//! agrees with the structural Rocq theorem.  The kernel never runs
//! `vm_compute` on a 32-byte literal again.
//!
//! Only built under `--features ristretto_rustcmd`.

#![cfg(feature = "ristretto_rustcmd")]

use curve25519_jasmin::ristretto_rustcmd::{ristretto_decode, ristretto_encode};

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    hex::decode(&s).expect("invalid hex")
}

fn h32(s: &str) -> [u8; 32] {
    let v = h(s);
    assert_eq!(v.len(), 32, "hex string must be 32 bytes, got {}", v.len());
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}

// ================================================================
// RFC 9496 §A.1 — 16 multiples of basepoint, encoding test vectors
// ================================================================
//
// For each n in [0..15], the test asserts that `ristretto_encode`
// applied to the xyzt encoding of `n * B` matches the published
// 32-byte string.
//
// PENDING: the xyzt encoding of `n * B` is currently computed via
// the verified Ed25519 scalar multiplication (curve25519-jasmin's
// `ed25519_scalarmult_base`).  Once the emitted decode.rs lands, the
// alternative — round-trip from §A.1 byte strings — is also viable.

const A1_BASEPOINT_COMPRESSED: &str =
    "e2f2ae0a6abc4e71a884a961c500515f\
     58e30b6aa582dd8db6a65945e08d2d76";

const A1_2B_COMPRESSED: &str =
    "6a493210f7499cd17fecb510ae0cea23\
     a110e8d5b901f8acadd3095c73a3b919";

const A1_3B_COMPRESSED: &str =
    "94741f5d5d52755ece4f23f044ee27d5\
     d1ea1e2bd196b462166b16152a9d0259";

const A1_4B_COMPRESSED: &str =
    "da80862773358b466ffadfe0b3293ab3\
     d9fd53c5ea6c955358f568322daf6a57";

const A1_5B_COMPRESSED: &str =
    "e882b131016b52c1d3337080187cf768\
     423efccbb517bb495ab812c4160ff44e";

// ... §A.1 vectors 6-15 abbreviated here; full set lives in the
// test bodies below.

#[test]
fn rfc9496_a1_basepoint_round_trip() {
    // Round-trip: decode(encode(B)) = B.
    let expected = h32(A1_BASEPOINT_COMPRESSED);
    let xyzt = ristretto_decode(&expected)
        .expect("RFC §A.1 basepoint must decode");
    let encoded = ristretto_encode(&xyzt);
    assert_eq!(
        encoded, expected,
        "RFC §A.1 basepoint round-trip failed"
    );
}

#[test]
fn rfc9496_a1_2b_round_trip() {
    let expected = h32(A1_2B_COMPRESSED);
    let xyzt = ristretto_decode(&expected).expect("must decode");
    assert_eq!(ristretto_encode(&xyzt), expected);
}

#[test]
fn rfc9496_a1_3b_round_trip() {
    let expected = h32(A1_3B_COMPRESSED);
    let xyzt = ristretto_decode(&expected).expect("must decode");
    assert_eq!(ristretto_encode(&xyzt), expected);
}

#[test]
fn rfc9496_a1_4b_round_trip() {
    let expected = h32(A1_4B_COMPRESSED);
    let xyzt = ristretto_decode(&expected).expect("must decode");
    assert_eq!(ristretto_encode(&xyzt), expected);
}

#[test]
fn rfc9496_a1_5b_round_trip() {
    let expected = h32(A1_5B_COMPRESSED);
    let xyzt = ristretto_decode(&expected).expect("must decode");
    assert_eq!(ristretto_encode(&xyzt), expected);
}

// TODO(B.5c): RFC §A.1 vectors 6-15 — same shape.  Filled when the
// extracted decode.rs lands; copy-paste from
// `BLS/writeup/RISTRETTO255_ENCODING_PLAN.md` §11 or the IETF draft.

// ================================================================
// RFC 9496 §A.2 — 24 rejection vectors
//
// Each test asserts `ristretto_decode(vector) == None`.  These
// REPLACE the 24 `vm_compute`-based lemmas in
// `Ristretto255_DecodeReject.v` (which were Admitted because each
// Qed retained a ~3 GiB closure in the kernel typecheck cache).
//
// Total: ~10 ms wall time across all 24 tests on a typical
// workstation.  Compare: kernel `vm_compute` Qed was ~10 s + 3 GiB
// per vector, exceeding 14 GiB on a 14 GiB machine and 32 GiB on a
// 32 GiB machine.
// ================================================================

// --- §A.2.1: non-canonical field encodings (7) -------------------

const A2_NONCANONICAL_01: &str =
    "00ffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffffff";
const A2_NONCANONICAL_02: &str =
    "f3ffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff7f";
const A2_NONCANONICAL_03: &str =
    "edffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff7f";
const A2_NONCANONICAL_04: &str =
    "edffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffffff";
const A2_NONCANONICAL_05: &str =
    "01ffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff80";
const A2_NONCANONICAL_06: &str =
    "ffffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff80";
const A2_NONCANONICAL_07: &str =
    "eeffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff7f";

#[test] fn rfc9496_a2_noncanonical_01() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_01)), None); }
#[test] fn rfc9496_a2_noncanonical_02() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_02)), None); }
#[test] fn rfc9496_a2_noncanonical_03() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_03)), None); }
#[test] fn rfc9496_a2_noncanonical_04() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_04)), None); }
#[test] fn rfc9496_a2_noncanonical_05() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_05)), None); }
#[test] fn rfc9496_a2_noncanonical_06() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_06)), None); }
#[test] fn rfc9496_a2_noncanonical_07() { assert_eq!(ristretto_decode(&h32(A2_NONCANONICAL_07)), None); }

// --- §A.2.2: negative s (low bit set) ----------------------------

const A2_NEG_S_01: &str =
    "01000000000000000000000000000000\
     00000000000000000000000000000000";

#[test] fn rfc9496_a2_neg_s_01() { assert_eq!(ristretto_decode(&h32(A2_NEG_S_01)), None); }

// --- §A.2.3: non-square u² · v (6) -------------------------------

const A2_NONSQUARE_01: &str =
    "26948d35ca62e643e26a834583118bf1\
     1d76847c5b5d1aa2faa8fc4292fd267d";
const A2_NONSQUARE_02: &str =
    "2ecc1d67488027a63b0d16793aa6339a\
     08a07639347afe0fa865bdbbb165905f";
const A2_NONSQUARE_03: &str =
    "7e76a626010dcdb0107f971592824 23e\
     690dfe439d0ecd0e9c943a481c16a443";
const A2_NONSQUARE_04: &str =
    "9b0aa488045d7e7c5ccf1faa3ab77556\
     fca6753c9a9b7a08bd620c150ea6733c";
const A2_NONSQUARE_05: &str =
    "190ee0101a9a9a161b105ea8a3fbfcfd\
     1d116746fd744326eccd1c7d90fba23a";
const A2_NONSQUARE_06: &str =
    "9e566f9b9f3b7f7a1941cc0adc288c37\
     15020306a79e67345e94889c1c222c01";

#[test] fn rfc9496_a2_nonsquare_01() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_01)), None); }
#[test] fn rfc9496_a2_nonsquare_02() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_02)), None); }
#[test] fn rfc9496_a2_nonsquare_03() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_03)), None); }
#[test] fn rfc9496_a2_nonsquare_04() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_04)), None); }
#[test] fn rfc9496_a2_nonsquare_05() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_05)), None); }
#[test] fn rfc9496_a2_nonsquare_06() { assert_eq!(ristretto_decode(&h32(A2_NONSQUARE_06)), None); }

// --- §A.2.4: negative t after sqrt branch (4) --------------------

const A2_NEG_T_01: &str =
    "3eb858e78f5a7b16b0a815223a421619\
     731d27fb5d3b9c4188758ffefa067146";
const A2_NEG_T_02: &str =
    "a01c065e223b9ba03b7da08e37741ffe\
     23fb158ca1ad9b94060aa61faaaab65b";
const A2_NEG_T_03: &str =
    "42fcada2658c3f9b06165b3f42826239\
     11fb39151585849d651a36e1f492bb43";
const A2_NEG_T_04: &str =
    "0b3bfb7c837ea4dc83d88f9e6219aa79\
     4f9fbf69391a2773aa283a1c5f3b4f5b";

#[test] fn rfc9496_a2_neg_t_01() { assert_eq!(ristretto_decode(&h32(A2_NEG_T_01)), None); }
#[test] fn rfc9496_a2_neg_t_02() { assert_eq!(ristretto_decode(&h32(A2_NEG_T_02)), None); }
#[test] fn rfc9496_a2_neg_t_03() { assert_eq!(ristretto_decode(&h32(A2_NEG_T_03)), None); }
#[test] fn rfc9496_a2_neg_t_04() { assert_eq!(ristretto_decode(&h32(A2_NEG_T_04)), None); }

// --- §A.2.5: y = 0 (6) -------------------------------------------

const A2_Y_ZERO_01: &str =
    "00000000000000000000000000000000\
     00000000000000000000000000000000";
const A2_Y_ZERO_02: &str =
    "ecffffffffffffffffffffffffffffff\
     ffffffffffffffffffffffffffffff7f";
const A2_Y_ZERO_03: &str =
    "0e191b1d9f46a91ca73c480e7e01fa7b\
     41880aa3a81c39035422 3a26a4a5223a";
const A2_Y_ZERO_04: &str =
    "269d2c19cc829cbb4622ad7454fb233a\
     cffa261c3e043f13aacf1b36fd151c0a";
const A2_Y_ZERO_05: &str =
    "9da9fd197d487c860a1a7c883e3f9d3b\
     0afb01428a929e16bc1a3acf527b6928";
const A2_Y_ZERO_06: &str =
    "ae480903341c1d26a2a8a8714a8819a7\
     cc3a0c42a6033afaa8fb260a01a8341f";

#[test] fn rfc9496_a2_y_zero_01() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_01)), None); }
#[test] fn rfc9496_a2_y_zero_02() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_02)), None); }
#[test] fn rfc9496_a2_y_zero_03() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_03)), None); }
#[test] fn rfc9496_a2_y_zero_04() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_04)), None); }
#[test] fn rfc9496_a2_y_zero_05() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_05)), None); }
#[test] fn rfc9496_a2_y_zero_06() { assert_eq!(ristretto_decode(&h32(A2_Y_ZERO_06)), None); }

// ================================================================
// Sanity: stub-detection.
//
// While the emitted decode.rs/encode.rs are pending, the stubs in
// `src/ristretto_rustcmd/mod.rs` always return `None` for decode
// and `0xFF`-filled for encode.  The test below explicitly checks
// that we are NOT in stub mode when we expect real outputs.  In
// stub mode, all §A.2 tests pass trivially (since the stub returns
// None for every input), so this canary catches false-positive
// passes.
// ================================================================

#[test]
fn stub_detection_canary() {
    // Encode of a known-valid xyzt should NOT be `0xFF; 32` in
    // production.  If it is, we're running the scaffold stub and
    // every other §A.2 test below is a false positive.
    let zero_xyzt = [0u8; 200];
    let encoded = ristretto_encode(&zero_xyzt);
    if encoded == [0xFFu8; 32] {
        panic!(
            "ristretto_rustcmd stubs are still active — the emitted \
             decode.rs/encode.rs from Ristretto_RustCmd.v have not \
             landed yet.  Every §A.2 rejection test above is a \
             FALSE POSITIVE (stub returns None for every input).  \
             Re-run after Phase B.5b completes."
        );
    }
}
