	.att_syntax
	.text
	.p2align	5
	.global	fe25519_add
	.type	fe25519_add, %function
fe25519_add:
	movq	%rsp, %rax
	leaq	-24(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%rax, 16(%rsp)
	movq	%rdx, %r9
	movq	(%rsi), %r10
	movq	8(%rsi), %r11
	movq	16(%rsi), %rax
	movq	24(%rsi), %rcx
	movq	32(%rsi), %rdx
	movq	(%r9), %rbx
	movq	8(%r9), %rbp
	movq	16(%r9), %rsi
	movq	24(%r9), %r8
	movq	32(%r9), %r9
	leaq	(%r10,%rbx), %r10
	leaq	(%r11,%rbp), %r11
	leaq	(%rax,%rsi), %rax
	leaq	(%rcx,%r8), %rcx
	leaq	(%rdx,%r9), %rdx
	movq	%r10, (%rdi)
	movq	%r11, 8(%rdi)
	movq	%rax, 16(%rdi)
	movq	%rcx, 24(%rdi)
	movq	%rdx, 32(%rdi)
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
