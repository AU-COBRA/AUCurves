# Map the extern names of the safe-Rust tower, and the one external call of the
# Jasmin module, to the code that provides them.  Hand-written, trusted.
#
# Two configurations, chosen by build.sh (BLS12_JASMIN_LEAVES):
#
#   default             mul and square from CryptOpt (SMT-validated against
#                       fiat-crypto's Montgomery multiply / square for
#                       p = BLS12-381; generated/bls12_*_cryptopt.asm, copied
#                       from spitters/bls12-jasmin-rs
#                       cryptopt/fiat_bls12_381_p_{mul,square}.asm);
#   JASMIN_LEAVES=1     (as --defsym JASMIN_LEAVES=1) mul and square from the
#                       bedrock2 -> Jasmin leaves of
#                       src/Bedrock/Jasmin/ExtractBLS12LeavesLive.v
#                       (generated/bls12_leaves_live.jazz: polish_func_adc,
#                       liveness-chosen #[spill] hints, compiled by
#                       jasminc -auto-spill; export fn bls12_mul / bls12_square),
#                       and no CryptOpt object is linked.
#
# add and sub stay Rust on the safe-Rust path (src/stubs.rs), as in bn254-safe-rust.
	.text

.ifdef JASMIN_LEAVES
	.set	MUL_IMPL, bls12_mul
	.set	SQUARE_IMPL, bls12_square
.else
	.set	MUL_IMPL, fiat_bls12_381_p_mul
	.set	SQUARE_IMPL, fiat_bls12_381_p_square
.endif

	.globl	_bls12_mul
_bls12_mul:
	jmp	MUL_IMPL

	.globl	_bls12_square
_bls12_square:
	jmp	SQUARE_IMPL

# The Jasmin modules (generated/bls12_*_regptr.jazz, printed by
# src/Bedrock/Jasmin/RegPtrSized.v) reach their leaves bls12_mul,
# bls12_square and bls12_inv through Jasmin's one external call,
# `buf = #randombytes(buf)`: rdi = buf, rsi = its length in bytes, result
# rax = buf, every caller-saved register killed (jasminc Arch.syscall_kill),
# callee-saved registers preserved, stack 16-aligned at the call.  The buffer
# holds the output followed by the inputs, 48 bytes each:
#
#   144 bytes  [out | x | y]      out = x * y        MUL_IMPL
#    96 bytes  [out | x]          out = x^2          SQUARE_IMPL
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
	call	MUL_IMPL
	jmp	.Lrb_done
.Lrb_square:
	leaq	48(%rdi), %rsi
	call	SQUARE_IMPL
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
