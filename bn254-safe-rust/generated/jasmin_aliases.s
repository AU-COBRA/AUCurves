# Map the safe-tower's extern names to the actual symbol providers.
#
# add/sub/square come from Jasmin (verified register allocation).
# mul comes from CryptOpt (SMT-validated against fiat-crypto Montgomery).
#
# Each line is one jmp — the cost of the indirection is one extra
# branch per leaf call, which the LTO pass eliminates by inlining.
.text

.global _bn254_add
_bn254_add: jmp bn254_add

.global _bn254_sub
_bn254_sub: jmp bn254_sub

.global _bn254_mul
_bn254_mul: jmp fiat_bn254_mul

.global _bn254_square
_bn254_square: jmp bn254_square
