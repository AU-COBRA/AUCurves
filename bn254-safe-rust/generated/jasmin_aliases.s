# Redirect _bn254_* to Jasmin-exported bn254_* (add/sub/mul/square only)
.text
.global _bn254_add
_bn254_add: jmp bn254_add
.global _bn254_sub
_bn254_sub: jmp bn254_sub
.global _bn254_mul
_bn254_mul: jmp bn254_mul
.global _bn254_square
_bn254_square: jmp bn254_square
