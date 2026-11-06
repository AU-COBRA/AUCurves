# Map the extern names of the safe-Rust tower, and the one external call of the
# Jasmin module, to the code that provides them.  Hand-written, trusted.
#
# mul and square come from CryptOpt (SMT-validated against fiat-crypto's
# Montgomery multiply / square for p = BLS12-381; generated/bls12_*_cryptopt.asm,
# copied from spitters/bls12-jasmin-rs cryptopt/fiat_bls12_381_p_{mul,square}.asm).
# add and sub stay Rust on the safe-Rust path (src/stubs.rs), as in bn254-safe-rust.
	.text

	.globl	_bls12_mul
_bls12_mul:
	jmp	fiat_bls12_381_p_mul

	.globl	_bls12_square
_bls12_square:
	jmp	fiat_bls12_381_p_square

# The Jasmin module (generated/bls12_*_regptr.jazz, printed by
# src/Bedrock/Jasmin/RegPtrSized.v) reaches its three leaves bls12_mul,
# bls12_square and bls12_inv through Jasmin's one external call,
# `buf = #randombytes(buf)`: rdi = buf, rsi = its length in bytes, result
# rax = buf, every caller-saved register killed (jasminc Arch.syscall_kill),
# callee-saved registers preserved, stack 16-aligned at the call.  The buffer
# holds the output followed by the inputs, 48 bytes each:
#
#   144 bytes  [out | x | y]      out = x * y        fiat_bls12_381_p_mul
#    96 bytes  [out | x]          out = x^2          fiat_bls12_381_p_square
#   104 bytes  [out | x | pad]    out = x^-1 (0->0)  _bls12_inv (safegcd, src/stubs.rs)
#    56 bytes  [out | w]          out = w R mod p    _bls12_from_word (src/stubs.rs)
#   112 bytes  [out | x | pad]    out = -x           _bls12_opp (src/stubs.rs)
#
# Any other length is a bug in the printer: ud2.  For Jasmin the call is an
# oracle that may write any bytes into buf, so the compiled module is correct
# for whatever this routine returns; that it returns the field operation is
# the trusted part.
	.globl	__jasmin_syscall_randombytes__
	.type	__jasmin_syscall_randombytes__, @function
__jasmin_syscall_randombytes__:
	pushq	%rbx
	movq	%rdi, %rbx
	cmpq	$144, %rsi
	je	.Lrb_mul
	cmpq	$96, %rsi
	je	.Lrb_square
	cmpq	$104, %rsi
	je	.Lrb_inv
	cmpq	$56, %rsi
	je	.Lrb_from_word
	cmpq	$112, %rsi
	je	.Lrb_opp
	ud2
.Lrb_mul:
	leaq	96(%rdi), %rdx
	leaq	48(%rdi), %rsi
	call	fiat_bls12_381_p_mul
	jmp	.Lrb_done
.Lrb_square:
	leaq	48(%rdi), %rsi
	call	fiat_bls12_381_p_square
	jmp	.Lrb_done
.Lrb_inv:
	leaq	48(%rdi), %rsi
	call	_bls12_inv
	jmp	.Lrb_done
.Lrb_from_word:
	movq	48(%rdi), %rsi
	call	_bls12_from_word
	jmp	.Lrb_done
.Lrb_opp:
	leaq	48(%rdi), %rsi
	call	_bls12_opp
.Lrb_done:
	movq	%rbx, %rax
	popq	%rbx
	ret
	.size	__jasmin_syscall_randombytes__, .-__jasmin_syscall_randombytes__

	.section	.note.GNU-stack,"",@progbits
