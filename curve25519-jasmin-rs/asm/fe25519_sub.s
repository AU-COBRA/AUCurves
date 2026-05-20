	.att_syntax
	.text
	.p2align	5
	.global	fe25519_sub
	.type	fe25519_sub, %function
fe25519_sub:
	movq	%rsp, %rax
	leaq	-32(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rsi, %r8
	movq	%rdx, %rbp
	movq	(%r8), %rax
	movq	8(%r8), %rcx
	movq	16(%r8), %rdx
	movq	24(%r8), %rsi
	movq	32(%r8), %r8
	movq	(%rbp), %r9
	movq	8(%rbp), %r10
	movq	16(%rbp), %r11
	movq	24(%rbp), %rbx
	movq	32(%rbp), %rbp
	movq	$4503599627370458, %r12
	leaq	(%r12,%rax), %rax
	subq	%r9, %rax
	movq	$4503599627370494, %r12
	leaq	(%r12,%rcx), %rcx
	subq	%r10, %rcx
	movq	$4503599627370494, %r12
	leaq	(%r12,%rdx), %rdx
	subq	%r11, %rdx
	movq	$4503599627370494, %r12
	leaq	(%r12,%rsi), %rsi
	subq	%rbx, %rsi
	movq	$4503599627370494, %r12
	leaq	(%r12,%r8), %r12
	subq	%rbp, %r12
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	movq	%r12, 32(%rdi)
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
