	.att_syntax
	.text
	.p2align	5
	.global	felem_cswap
	.type	felem_cswap, %function
felem_cswap:
	movq	%rsp, %rax
	leaq	-16(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, (%rsp)
	movq	%rax, 8(%rsp)
	movq	$0, %rax
	subq	%rdi, %rax
	movq	%rax, %rdi
	movq	$-1, %rcx
	xorq	%rcx, %rdi
	movq	$0, %rcx
	movq	$5, %r8
Lfelem_cswap$1:
	movq	(%rsi,%rcx,8), %r9
	movq	(%rdx,%rcx,8), %r10
	movq	%rdi, %r11
	andq	%r9, %r11
	movq	%rax, %rbx
	andq	%r10, %rbx
	orq 	%rbx, %r11
	movq	%rdi, %rbx
	andq	%r10, %rbx
	movq	%rax, %r10
	andq	%r9, %r10
	orq 	%r10, %rbx
	movq	%r11, (%rsi,%rcx,8)
	movq	%rbx, (%rdx,%rcx,8)
	leaq	1(%rcx), %rcx
	cmpq	%r8, %rcx
	jb  	Lfelem_cswap$1
	movq	(%rsp), %rbx
	movq	8(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
