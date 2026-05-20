//! Track F — constant-time verification of
//! `safegcd25519::fe25519_invert_divstep_sat` via valgrind memcheck +
//! client requests (the methodology used by libsecp256k1, BoringSSL's
//! `constant_time_test`, and blst).
//!
//! Strategy.  We mark the 32-byte secret input as **uninitialised**
//! using the `VALGRIND_MAKE_MEM_UNDEFINED` client request, then call
//! the Bernstein–Yang divstep inversion.  Valgrind tracks the
//! definedness bit through every arithmetic op; if at any point the
//! inversion *branches on*, *uses as an address*, or *passes to a
//! syscall* a value that depends on the secret, valgrind raises a
//! `Conditional jump or move depends on uninitialised value(s)` error
//! and exits with the code given by `--error-exitcode`.
//!
//! The valgrind client request is implemented inline (a four-`rol` +
//! `xchg` "no-op" magic sequence that valgrind recognises in its JIT)
//! so this test has zero extra Rust dependencies — outside valgrind
//! the sequence is a literal no-op on the bare CPU.
//!
//! Recipe (with a user-local valgrind install at /tmp/valgrind_root,
//! which is what we use because the host doesn't have valgrind
//! preinstalled and we don't have sudo):
//!
//! ```sh
//! JASMINC=$HOME/.opam/rocq-9/bin/jasminc \
//! cargo test --release --features ed25519_rustcmd \
//!     --test valgrind_ct --no-run
//!
//! VALGRIND_LIB=/tmp/valgrind_root/usr/libexec/valgrind \
//! /tmp/valgrind_root/usr/bin/valgrind \
//!     --tool=memcheck --error-exitcode=99 -q \
//!     target/release/deps/valgrind_ct-<hash>
//! ```

use curve25519_jasmin::safegcd25519::fe25519_invert_divstep_sat;

// ---------- inline valgrind client requests (amd64-linux) ----------

// Request codes from `valgrind/memcheck.h`:
//   VG_USERREQ_TOOL_BASE('M','C') = ('M' << 24) | ('C' << 16) = 0x4D43_0000
//   VG_USERREQ__MAKE_MEM_NOACCESS  = 0x4D43_0000
//   VG_USERREQ__MAKE_MEM_UNDEFINED = 0x4D43_0001
//   VG_USERREQ__MAKE_MEM_DEFINED   = 0x4D43_0002
const VG_USERREQ_MAKE_MEM_UNDEFINED: u64 = 0x4D43_0001;
const VG_USERREQ_MAKE_MEM_DEFINED: u64 = 0x4D43_0002;

/// Issue a valgrind client request.  Outside valgrind the magic
/// instruction sequence (`rol rdi, 3 / 13 / 61 / 51 ; xchg rbx, rbx`)
/// is a literal no-op on real x86-64 hardware, so the call is free.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[inline(always)]
fn vg_client_request(request: u64, arg1: u64, arg2: u64) -> u64 {
    let args: [u64; 6] = [request, arg1, arg2, 0, 0, 0];
    let result: u64;
    let default: u64 = 0;
    unsafe {
        // %rax = &args[0], %rdx = default-in, %rdx = result-out.
        // The magic preamble is what valgrind's JIT spots.
        std::arch::asm!(
            "rol rdi, 3",
            "rol rdi, 13",
            "rol rdi, 61",
            "rol rdi, 51",
            "xchg rbx, rbx",
            in("rax") &args as *const u64,
            inout("rdx") default => result,
            // Clobbers: rdi is rotated (recoverable but mark it clobbered
            // by listing as inout to a throwaway), memory because
            // valgrind may read/write the args array.
            inout("rdi") 0u64 => _,
            options(nostack, preserves_flags),
        );
    }
    result
}

#[cfg(not(all(target_arch = "x86_64", target_os = "linux")))]
#[inline(always)]
fn vg_client_request(_request: u64, _arg1: u64, _arg2: u64) -> u64 {
    0
}

/// Mark `buf` as uninitialised to memcheck.
fn poison(buf: &[u8]) {
    vg_client_request(
        VG_USERREQ_MAKE_MEM_UNDEFINED,
        buf.as_ptr() as u64,
        buf.len() as u64,
    );
}

/// Re-mark `buf` as initialised — used to suppress downstream
/// "result depends on secret" warnings once we have validated that the
/// inversion itself was CT.  Callers that branch on the output (e.g.
/// to write it to stdout, run assertions, etc.) are by construction
/// *outside* the function under test.
fn unpoison(buf: &[u8]) {
    vg_client_request(
        VG_USERREQ_MAKE_MEM_DEFINED,
        buf.as_ptr() as u64,
        buf.len() as u64,
    );
}

fn pack_u8x32_to_u64x4(bytes: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for i in 0..4 {
        out[i] = u64::from_le_bytes([
            bytes[8 * i],
            bytes[8 * i + 1],
            bytes[8 * i + 2],
            bytes[8 * i + 3],
            bytes[8 * i + 4],
            bytes[8 * i + 5],
            bytes[8 * i + 6],
            bytes[8 * i + 7],
        ]);
    }
    out
}

#[test]
fn fe25519_invert_divstep_sat_is_constant_time() {
    let mut x_bytes = [0u8; 32];
    for (i, b) in x_bytes.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(37).wrapping_add(11);
    }
    x_bytes[31] &= 0x7f;

    poison(&x_bytes);

    // Pack to [u64; 4] using `from_le_bytes`.  This is part of the
    // function under test's interface contract.
    let x = pack_u8x32_to_u64x4(&x_bytes);

    let mut y = [0u64; 4];
    // === The function under test. ===
    // Any conditional jump / memory address / syscall arg derived
    // from `x` will cause valgrind to emit an error here.
    fe25519_invert_divstep_sat(&mut y, &x);

    // Unpoison the output so the post-call assertion does not itself
    // trip memcheck.
    let y_bytes = unsafe {
        std::slice::from_raw_parts(y.as_ptr() as *const u8, std::mem::size_of_val(&y))
    };
    unpoison(y_bytes);

    // Trivial use of the result so the optimiser does not delete the
    // call.  This branch is on *defined* (unpoisoned) data.
    assert!(y[0] != u64::MAX || y[1] != u64::MAX || y[2] != u64::MAX || y[3] != u64::MAX);
}

#[test]
fn fe25519_invert_divstep_sat_many_inputs_are_constant_time() {
    for k in 1u8..6 {
        let mut x_bytes = [0u8; 32];
        for (i, b) in x_bytes.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(k.wrapping_add(1)).wrapping_add(k);
        }
        x_bytes[31] &= 0x7f;

        poison(&x_bytes);

        let x = pack_u8x32_to_u64x4(&x_bytes);
        let mut y = [0u64; 4];
        fe25519_invert_divstep_sat(&mut y, &x);

        let y_bytes = unsafe {
            std::slice::from_raw_parts(y.as_ptr() as *const u8, std::mem::size_of_val(&y))
        };
        unpoison(y_bytes);

        std::hint::black_box(&y);
    }
}
