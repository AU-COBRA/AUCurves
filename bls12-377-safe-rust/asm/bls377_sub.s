	.att_syntax
	.text
	.p2align	5
	.global	bls377_sub
	.type	bls377_sub, %function
bls377_sub:
	movq	%rsp, %rax
	leaq	-48(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	movq	(%rsi), %r13
	movq	8(%rsi), %r8
	movq	16(%rsi), %r9
	movq	24(%rsi), %r10
	movq	32(%rsi), %r11
	movq	40(%rsi), %rax
	movq	(%rdx), %r14
	movq	8(%rdx), %rbx
	movq	16(%rdx), %rbp
	movq	24(%rdx), %r12
	movq	32(%rdx), %rcx
	movq	40(%rdx), %rdx
	movq	%r13, %rsi
	subq	%r14, %rsi
	sbbq	%rbx, %r8
	sbbq	%rbp, %r9
	sbbq	%r12, %r10
	sbbq	%rcx, %r11
	sbbq	%rdx, %rax
	movq	$0, %r12
	jnb 	Lbls377_sub$1
	movq	$0, %r12
	leaq	-1(%r12), %r12
Lbls377_sub$1:
	movq	%r12, %r13
	movq	$-8860621160618917887, %rcx
	andq	%rcx, %r13
	movq	%r12, %rcx
	movq	$1660523435060625408, %rdx
	andq	%rdx, %rcx
	movq	%r12, %rdx
	movq	$2230234197602682880, %rbx
	andq	%rbx, %rdx
	movq	%r12, %rbx
	movq	$1883307231910630287, %rbp
	andq	%rbp, %rbx
	movq	%r12, %rbp
	movq	$-4162727106559522501, %r14
	andq	%r14, %rbp
	movq	$121098312706494698, %r14
	andq	%r14, %r12
	addq	%r13, %rsi
	adcq	%rcx, %r8
	adcq	%rdx, %r9
	adcq	%rbx, %r10
	adcq	%rbp, %r11
	adcq	%r12, %rax
	movq	%rsi, (%rdi)
	movq	%r8, 8(%rdi)
	movq	%r9, 16(%rdi)
	movq	%r10, 24(%rdi)
	movq	%r11, 32(%rdi)
	movq	%rax, 40(%rdi)
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.1"
	.section	".note.GNU-stack", "", %progbits
