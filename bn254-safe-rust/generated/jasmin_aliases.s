# Thin wrappers: redirect _bn254_* calls to Jasmin-exported bn254_* symbols
.text

.global _bn254_add
_bn254_add: jmp bn254_add

.global _bn254_sub
_bn254_sub: jmp bn254_sub

.global _bn254_mul
_bn254_mul: jmp bn254_mul

.global _bn254_square
_bn254_square: jmp bn254_square

.global _bn254_felem_copy
_bn254_felem_copy: jmp bn254_felem_copy

.global _bn254_select_znz
_bn254_select_znz: jmp bn254_select_znz
