	.att_syntax
	.text
	.p2align	5
	.global	fe25519_scmula24
	.type	fe25519_scmula24, %function
fe25519_scmula24:
	movq	%rsp, %rax
	leaq	-40(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 8(%rsp)
	movq	%rbp, 16(%rsp)
	movq	%r12, 24(%rsp)
	movq	%rax, 32(%rsp)
	movq	(%rsi), %r10
	movq	8(%rsi), %rbx
	movq	16(%rsi), %r9
	movq	24(%rsi), %r8
	movq	32(%rsi), %rax
	movq	$121665, %rdx
	mulxq	%rax, %rax, %rcx
	movq	$121665, %rdx
	mulxq	%r8, %rsi, %r8
	movq	$121665, %rdx
	mulxq	%r9, %r11, %r9
	movq	$121665, %rdx
	mulxq	%rbx, %rbx, %rbp
	movq	$121665, %rdx
	mulxq	%r10, %rdx, %r12
	movq	%rdx, %r10
	shrq	$51, %r10
	shlq	$13, %r12
	orq 	%r12, %r10
	movq	$2251799813685247, %r12
	andq	%r12, %rdx
	addq	%rbx, %r10
	movq	$0, %rbx
	jnb 	Lfe25519_scmula24$4
	movq	$1, %rbx
Lfe25519_scmula24$4:
	leaq	(%rbx,%rbp), %rbx
	movq	%r10, %rbp
	shrq	$51, %rbp
	shlq	$13, %rbx
	orq 	%rbx, %rbp
	movq	%r10, %rbx
	movq	$2251799813685247, %r12
	andq	%r12, %rbx
	movq	%rbp, %r10
	addq	%r11, %r10
	movq	$0, %r11
	jnb 	Lfe25519_scmula24$3
	movq	$1, %r11
Lfe25519_scmula24$3:
	movq	%rdi, (%rsp)
	movq	(%rsp), %rdi
	movq	%rbx, (%rsp)
	movq	(%rsp), %rbx
	movq	%rdx, (%rsp)
	movq	(%rsp), %rdx
	movq	%rcx, (%rsp)
	movq	(%rsp), %rcx
	movq	%rax, (%rsp)
	movq	(%rsp), %rax
	movq	%r8, (%rsp)
	movq	(%rsp), %r8
	movq	%rsi, (%rsp)
	movq	(%rsp), %rsi
	movq	%r10, (%rsp)
	movq	(%rsp), %r10
	movq	%r11, (%rsp)
	movq	(%rsp), %r11
	movq	%r9, (%rsp)
	movq	(%rsp), %r9
	leaq	(%r11,%r9), %r11
	movq	%r10, %r9
	shrq	$51, %r9
	shlq	$13, %r11
	orq 	%r11, %r9
	movq	$2251799813685247, %r12
	andq	%r12, %r10
	addq	%rsi, %r9
	movq	$0, %rsi
	jnb 	Lfe25519_scmula24$2
	movq	$1, %rsi
Lfe25519_scmula24$2:
	leaq	(%rsi,%r8), %rsi
	movq	%r9, %r8
	shrq	$51, %r8
	shlq	$13, %rsi
	orq 	%rsi, %r8
	movq	%r9, %rsi
	movq	$2251799813685247, %r12
	andq	%r12, %rsi
	addq	%rax, %r8
	movq	$0, %rax
	jnb 	Lfe25519_scmula24$1
	movq	$1, %rax
Lfe25519_scmula24$1:
	leaq	(%rax,%rcx), %rax
	movq	%r8, %rcx
	shrq	$51, %rcx
	shlq	$13, %rax
	orq 	%rax, %rcx
	movq	$2251799813685247, %r12
	andq	%r12, %r8
	imulq	$19, %rcx, %rcx
	movq	%rdi, (%rsp)
	movq	(%rsp), %rdi
	movq	%r8, (%rsp)
	movq	(%rsp), %rax
	movq	%rsi, (%rsp)
	movq	(%rsp), %rsi
	movq	%r10, (%rsp)
	movq	(%rsp), %r10
	movq	%rbx, (%rsp)
	movq	(%rsp), %rbx
	movq	%rdx, (%rsp)
	movq	(%rsp), %rdx
	movq	%rcx, (%rsp)
	movq	(%rsp), %rcx
	leaq	(%rdx,%rcx), %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	movq	$2251799813685247, %r12
	andq	%r12, %rcx
	leaq	(%rdx,%rbx), %rdx
	movq	%rdx, %r8
	shrq	$51, %r8
	movq	$2251799813685247, %r12
	andq	%r12, %rdx
	leaq	(%r8,%r10), %r8
	movq	%rcx, (%rdi)
	movq	%rdx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	movq	%rax, 32(%rdi)
	movq	8(%rsp), %rbx
	movq	16(%rsp), %rbp
	movq	24(%rsp), %r12
	movq	32(%rsp), %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.0"
	.section	".note.GNU-stack", "", %progbits
