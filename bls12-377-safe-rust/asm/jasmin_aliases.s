# Map the safe-tower's extern `_bls377_*` C-ABI names onto the
# Jasmin-emitted unprefixed symbols.  This mirrors the pattern in
# bls12-381-safe-rust/generated/jasmin_aliases.s — the Jasmin
# extraction emits `bls377_add` etc., but the safe tower extern
# block declares `_bls377_add` with a leading underscore.  Each
# line is a single jmp; LTO inlines it away.

.text

.global _bls377_add
_bls377_add: jmp bls377_add

.global _bls377_sub
_bls377_sub: jmp bls377_sub

.global _bls377_select_znz
_bls377_select_znz: jmp bls377_select_znz
