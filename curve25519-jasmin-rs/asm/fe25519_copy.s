	.att_syntax
	.text
	.p2align	5
	.global	fe25519_copy
	.type	fe25519_copy, %function
fe25519_copy:
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %rdx
	movq	24(%rsi), %r8
	movq	32(%rsi), %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%r8, 24(%rdi)
	movq	%rsi, 32(%rdi)
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
