	.att_syntax
	.text
	.p2align	5
	.global	fe25519_square
	.type	fe25519_square, %function
fe25519_square:
	movq	(%rsi), %rax
	imulq	(%rsi), %rax
	movq	8(%rsi), %rcx
	imulq	32(%rsi), %rcx
	movq	$38, %rdx
	imulq	%rcx, %rdx
	movq	16(%rsi), %rcx
	imulq	24(%rsi), %rcx
	movq	$38, %r8
	imulq	%rcx, %r8
	leaq	(%rdx,%r8), %rdx
	leaq	(%rax,%rdx), %rax
	movq	%rax, (%rdi)
	movq	(%rsi), %rax
	imulq	8(%rsi), %rax
	movq	$2, %rcx
	imulq	%rax, %rcx
	movq	16(%rsi), %rdx
	imulq	32(%rsi), %rdx
	movq	$38, %rax
	imulq	%rdx, %rax
	movq	24(%rsi), %r8
	imulq	24(%rsi), %r8
	movq	$19, %rdx
	imulq	%r8, %rdx
	leaq	(%rax,%rdx), %rax
	leaq	(%rcx,%rax), %rcx
	movq	%rcx, 8(%rdi)
	movq	(%rsi), %rax
	imulq	16(%rsi), %rax
	movq	$2, %rcx
	imulq	%rax, %rcx
	movq	8(%rsi), %rdx
	imulq	8(%rsi), %rdx
	movq	24(%rsi), %rax
	imulq	32(%rsi), %rax
	movq	$38, %r8
	imulq	%rax, %r8
	leaq	(%rdx,%r8), %rdx
	leaq	(%rcx,%rdx), %rax
	movq	%rax, 16(%rdi)
	movq	(%rsi), %rax
	imulq	24(%rsi), %rax
	movq	$2, %rcx
	imulq	%rax, %rcx
	movq	8(%rsi), %rdx
	imulq	16(%rsi), %rdx
	movq	$2, %rax
	imulq	%rdx, %rax
	movq	32(%rsi), %r8
	imulq	32(%rsi), %r8
	movq	$19, %rdx
	imulq	%r8, %rdx
	leaq	(%rax,%rdx), %rax
	leaq	(%rcx,%rax), %rcx
	movq	%rcx, 24(%rdi)
	movq	(%rsi), %rax
	imulq	32(%rsi), %rax
	movq	$2, %rcx
	imulq	%rax, %rcx
	movq	8(%rsi), %rdx
	imulq	24(%rsi), %rdx
	movq	$2, %rax
	imulq	%rdx, %rax
	movq	16(%rsi), %r8
	imulq	16(%rsi), %r8
	leaq	(%rax,%r8), %rax
	leaq	(%rcx,%rax), %rax
	movq	%rax, 32(%rdi)
	ret
	.ident	"Jasmin Compiler 2026.03.1"
	.section	".note.GNU-stack", "", %progbits
