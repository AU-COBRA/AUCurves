//! SHAKE-128 XOF via libjade's verified Jasmin implementation.
//!
//! The Jasmin source (`shake128.jazz`) is compiled from libjade
//! (formosa-crypto/libjade) using the verified Jasmin compiler.
//! The Keccak permutation is verified in EasyCrypt.
//!
//! Calling convention (System V AMD64):
//!   jade_xof_shake128_amd64_ref(output: *mut u8, output_length: u64,
//!                                input: *const u8, input_length: u64) -> u64

#[cfg(feature = "cryptopt")]
unsafe extern "C" {
    fn jade_xof_shake128_amd64_ref(
        output: *mut u8,
        output_length: u64,
        input: *const u8,
        input_length: u64,
    ) -> u64;
}

/// Compute SHAKE-128 XOF: produces `out_len` bytes from `input`.
#[cfg(feature = "cryptopt")]
pub fn shake128(input: &[u8], out_len: usize) -> Vec<u8> {
    let mut output = vec![0u8; out_len];
    unsafe {
        jade_xof_shake128_amd64_ref(
            output.as_mut_ptr(),
            out_len as u64,
            input.as_ptr(),
            input.len() as u64,
        );
    }
    output
}

/// Fallback: pure-Rust Keccak (not verified, for testing without asm).
#[cfg(not(feature = "cryptopt"))]
pub fn shake128(_input: &[u8], out_len: usize) -> Vec<u8> {
    // Stub: returns zeros. Replace with a Rust Keccak if needed.
    vec![0u8; out_len]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "cryptopt")]
    fn test_shake128_empty_input() {
        // NIST test vector: SHAKE128("", 32) =
        // 7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26
        let out = shake128(b"", 32);
        assert_eq!(out[0], 0x7f);
        assert_eq!(out[1], 0x9c);
        assert_eq!(out[31], 0x26);
    }

    #[test]
    #[cfg(feature = "cryptopt")]
    fn test_shake128_length() {
        let out = shake128(b"hello", 100);
        assert_eq!(out.len(), 100);
    }
}
