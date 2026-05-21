	.att_syntax
	.text
	.p2align	5
	.global	bls377_select_znz
	.type	bls377_select_znz, %function
bls377_select_znz:
	movq	%rsp, %rax
	leaq	-48(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%rax, 40(%rsp)
	movq	%rcx, %r10
	movq	(%rdx), %r11
	movq	8(%rdx), %rbx
	movq	16(%rdx), %rbp
	movq	24(%rdx), %rax
	movq	32(%rdx), %rcx
	movq	40(%rdx), %rdx
	movq	(%r10), %r14
	movq	8(%r10), %r12
	movq	16(%r10), %r13
	movq	24(%r10), %r8
	movq	32(%r10), %r9
	movq	40(%r10), %r10
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$6
	movq	%r14, %r11
Lbls377_select_znz$6:
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$5
	movq	%r12, %rbx
Lbls377_select_znz$5:
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$4
	movq	%r13, %rbp
Lbls377_select_znz$4:
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$3
	movq	%r8, %rax
Lbls377_select_znz$3:
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$2
	movq	%r9, %rcx
Lbls377_select_znz$2:
	cmpq	$0, %rsi
	je  	Lbls377_select_znz$1
	movq	%r10, %rdx
Lbls377_select_znz$1:
	movq	%r11, (%rdi)
	movq	%rbx, 8(%rdi)
	movq	%rbp, 16(%rdi)
	movq	%rax, 24(%rdi)
	movq	%rcx, 32(%rdi)
	movq	%rdx, 40(%rdi)
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.1"
	.section	".note.GNU-stack", "", %progbits
