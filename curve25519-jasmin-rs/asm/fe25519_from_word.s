	.att_syntax
	.text
	.p2align	5
	.global	fe25519_from_word
	.type	fe25519_from_word, %function
fe25519_from_word:
	movq	%rsi, %rax
	movq	$2251799813685247, %rcx
	andq	%rcx, %rax
	shrq	$51, %rsi
	movq	$0, %rcx
	movq	$0, %rdx
	movq	$0, %r8
	movq	%rax, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movq	%rdx, 24(%rdi)
	movq	%r8, 32(%rdi)
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
