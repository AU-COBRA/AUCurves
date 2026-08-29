# Map the safe-tower's extern names to the actual symbol providers.
#
# mul    comes from CryptOpt (SMT-validated against fiat-crypto Montgomery).
# square ALSO comes from CryptOpt now -- see below.
# add and sub are NOT redirected here: Jasmin's auto-spilled add/sub
# are slower than the Rust CIOS-style stubs (measured ~1.25x slowdown
# on the full pairing).  The stubs in src/stubs.rs cover them.
#
# Each line is one jmp -- the cost of the indirection is one extra
# branch per leaf call, which the LTO pass eliminates by inlining.
.text

.global _bn254_mul
_bn254_mul: jmp fiat_bn254_mul

# square used to jump to Jasmin's `bn254_square`, which suffers exactly the
# auto-spill problem that kept Jasmin's add and sub out of this file: it
# copies both operands to the stack and reloads them.  Measured on Zen 4
# as a serial dependency chain, that cost 694.7 cycles against 88.9 for
# CryptOpt's multiply -- a squaring 7.8x more expensive than a general
# multiply of the same width, which is never a real property of the
# arithmetic, since squaring can always fall back to multiplying.
#
# So route it to the multiply instead.  System V: square is
# (out = rdi, x = rsi) and mul is (out = rdi, x = rsi, y = rdx), so
# duplicating rsi into rdx turns square(out, x) into mul(out, x, x).
# This computes exactly the same function -- the Rust reference
# `stubs.rs::_bn254_square` is itself `mont_mul(xv, xv)` -- and
# `examples/sqr_probe.rs` asserts the two agree.
#
# A dedicated CryptOpt square would be better still (fiat's own square
# saves one operand load, ~8%), but CryptOpt ships no BN254 square seed
# in this tree; only `bn254_mul_cryptopt.asm` was generated.  Generating
# one is the obvious follow-up.
.global _bn254_square
_bn254_square:
	mov %rsi, %rdx
	jmp fiat_bn254_mul
