# Map the safe-tower's extern names to the actual symbol providers.
#
# mul    comes from CryptOpt (SMT-validated against fiat-crypto Montgomery).
# square comes from Jasmin (verified register allocation).
# add and sub are NOT redirected here: Jasmin's auto-spilled add/sub
# are slower than the Rust CIOS-style stubs (measured ~1.25x slowdown
# on the full pairing).  The stubs in src/stubs.rs cover them.
#
# Each line is one jmp -- the cost of the indirection is one extra
# branch per leaf call, which the LTO pass eliminates by inlining.
.text

.global _bn254_mul
_bn254_mul: jmp fiat_bn254_mul

.global _bn254_square
_bn254_square: jmp bn254_square
