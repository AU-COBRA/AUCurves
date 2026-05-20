	.att_syntax
	.text
	.p2align	5
	.global	clamp_64
	.type	clamp_64, %function
clamp_64:
	movq	(%rdi), %rax
	movq	$-8, %rcx
	andq	%rcx, %rax
	movq	%rax, (%rdi)
	movq	24(%rdi), %rax
	movq	$9223372036854775807, %rcx
	andq	%rcx, %rax
	movq	$4611686018427387904, %rcx
	orq 	%rcx, %rax
	movq	%rax, 24(%rdi)
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
