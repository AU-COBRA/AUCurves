	.att_syntax
	.text
	.p2align	5
	.global	bls377_add
	.type	bls377_add, %function
bls377_add:
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
	addq	%r14, %rsi
	adcq	%rbx, %r8
	adcq	%rbp, %r9
	adcq	%r12, %r10
	adcq	%rcx, %r11
	adcq	%rdx, %rax
	jb  	Lbls377_add$9
Lbls377_add$9:
	movq	%rsi, %r13
	movq	$-8860621160618917887, %rcx
	subq	%rcx, %r13
	movq	%r8, %r14
	movq	$1660523435060625408, %rcx
	sbbq	%rcx, %r14
	movq	%r9, %rcx
	movq	$2230234197602682880, %rdx
	sbbq	%rdx, %rcx
	movq	%r10, %rdx
	movq	$1883307231910630287, %rbx
	sbbq	%rbx, %rdx
	movq	%r11, %rbx
	movq	$-4162727106559522501, %rbp
	sbbq	%rbp, %rbx
	movq	%rax, %rbp
	movq	$121098312706494698, %r12
	sbbq	%r12, %rbp
	movq	$0, %r12
	jnb 	Lbls377_add$8
	movq	$1, %r12
Lbls377_add$8:
	cmpq	$0, %r12
	jne 	Lbls377_add$7
	movq	%r13, %rsi
Lbls377_add$7:
	cmpq	$0, %r12
	jne 	Lbls377_add$6
	movq	%r14, %r8
Lbls377_add$6:
	cmpq	$0, %r12
	je  	Lbls377_add$5
	movq	%r9, %rcx
Lbls377_add$5:
	cmpq	$0, %r12
	je  	Lbls377_add$4
	movq	%r10, %rdx
Lbls377_add$4:
	cmpq	$0, %r12
	je  	Lbls377_add$2
	movq	%r11, %r9
	jmp 	Lbls377_add$3
Lbls377_add$2:
	movq	%rbx, %r9
Lbls377_add$3:
	cmpq	$0, %r12
	jne 	Lbls377_add$1
	movq	%rbp, %rax
Lbls377_add$1:
	movq	%rsi, (%rdi)
	movq	%r8, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movq	%rdx, 24(%rdi)
	movq	%r9, 32(%rdi)
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
