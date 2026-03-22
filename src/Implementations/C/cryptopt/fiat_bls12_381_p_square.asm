SECTION .text
	GLOBAL fiat_bls12_381_p_square
fiat_bls12_381_p_square:
SECTION .text
	GLOBAL fiat_bls12_381_p_square
fiat_bls12_381_p_square:
sub rsp, 984
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r8
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r9
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rcx
mulx rcx, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r12
mulx r12, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r12
mulx r12, rcx, rdx
mov rdx, 0x89f3fffcfffcfffd 
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], rcx
mulx rcx, r12, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r11
mulx r11, rcx, rdx
mov rdx, 0x64774b84f38512bf 
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r9
mulx r9, r11, r12
mov rdx, 0x1a0111ea397fe69a 
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], r11
mulx r11, r9, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r9
mulx r9, r11, [ rsi + 0x28 ]
mov rdx, 0x4b1ba7b6434bacd7 
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], r11
mulx r11, r9, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r9
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, 0x6730d2a0f6b0f624 
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r8
mulx r8, r11, r12
test al, al
adox rdi, r9
adox rax, r13
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], rax
mulx rax, r13, [ rsi + 0x20 ]
adcx rbx, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r11
mulx r11, r8, [ rsi + 0x0 ]
adcx r8, rbp
setc dl
clc
adcx r15, r9
mov bpl, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r15
mulx r15, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], r8
mov [ rsp + 0xe0 ], r15
mulx r15, r8, [ rsi + 0x20 ]
adcx r13, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r13
mulx r13, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
adcx r8, rax
adox r9, r10
adcx rcx, r15
seto dl
mov r10, -0x2 
inc r10
adox r13, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x40 ]
mov al, dl
mov rdx, [ rsi + 0x0 ]
mulx r10, r15, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x100 ], rbx
mov rbx, 0x0 
dec rbx
movzx rbp, bpl
adox rbp, rbx
adox r11, r15
mov rbp, 0x1eabfffeb153ffff 
xchg rdx, rbp
mulx rbx, r15, r12
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x108 ], bpl
mov [ rsp + 0x110 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, 0xb9feffffffffaaab 
mov [ rsp + 0x118 ], rdi
mov [ rsp + 0x120 ], r13
mulx r13, rdi, r12
adox r10, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r8
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], rbp
mov [ rsp + 0x138 ], r8
mulx r8, rbp, [ rsi + 0x8 ]
setc dl
clc
adcx r15, r13
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r9
mov [ rsp + 0x148 ], r10
mulx r10, r9, [ rsi + 0x18 ]
seto dl
mov byte [ rsp + 0x150 ], r13b
mov r13, -0x2 
inc r13
adox rdi, r14
adox r15, [ rsp + 0xf8 ]
setc dil
clc
movzx rdx, dl
adcx rdx, r13
adcx r12, [ rsp - 0x10 ]
setc r14b
clc
adcx rbp, rcx
adcx r9, r8
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
seto dl
inc r13
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox rbx, [ rsp + 0xc8 ]
mov rdi, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0x60 ]
mov r13, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x18 ]
mov [ rsp + 0x158 ], r13
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], r10
mov [ rsp + 0x168 ], r9
mulx r9, r10, [ rsi + 0x20 ]
setc dl
clc
adcx rcx, [ rsp + 0x28 ]
mov byte [ rsp + 0x170 ], dl
seto dl
mov [ rsp + 0x178 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rax, al
adox rax, rbp
adox r10, [ rsp + 0xe0 ]
seto al
inc rbp
adox r15, [ rsp + 0x98 ]
mov rbp, 0x89f3fffcfffcfffd 
xchg rdx, r15
mov byte [ rsp + 0x180 ], r14b
mov [ rsp + 0x188 ], rcx
mulx rcx, r14, rbp
mov rcx, 0x1eabfffeb153ffff 
xchg rdx, r14
mov [ rsp + 0x190 ], r10
mulx r10, rbp, rcx
adcx r8, [ rsp + 0x38 ]
mov rcx, 0xb9feffffffffaaab 
mov [ rsp + 0x198 ], r8
mov [ rsp + 0x1a0 ], r10
mulx r10, r8, rcx
seto cl
mov [ rsp + 0x1a8 ], r12
mov r12, -0x2 
inc r12
adox rbp, r10
mov r10, [ rsp + 0x90 ]
setc r12b
clc
mov [ rsp + 0x1b0 ], rdi
mov rdi, -0x1 
movzx r15, r15b
adcx r15, rdi
adcx r10, [ rsp + 0x58 ]
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x1b8 ], r12b
mulx r12, rdi, [ rsi + 0x20 ]
setc dl
clc
mov [ rsp + 0x1c0 ], r12
mov r12, -0x1 
movzx r13, r13b
adcx r13, r12
adcx rbx, [ rsp + 0xd8 ]
seto r13b
inc r12
mov r12, -0x1 
movzx rax, al
adox rax, r12
adox r9, [ rsp + 0x8 ]
mov rax, [ rsp + 0x0 ]
mov r12, 0x0 
adox rax, r12
dec r12
movzx rcx, cl
adox rcx, r12
adox rbx, [ rsp + 0xb8 ]
seto cl
inc r12
adox r8, r14
adox rbp, rbx
mov r8, [ rsp + 0x88 ]
setc r14b
clc
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx r8, [ rsp + 0x70 ]
seto dl
dec r12
movzx r14, r14b
adox r14, r12
adox r11, [ rsp + 0x1b0 ]
adox r10, [ rsp + 0x148 ]
setc bl
clc
movzx rcx, cl
adcx rcx, r12
adcx r11, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0x140 ]
adox r8, [ rsp + 0x1a8 ]
movzx r14, bl
mov rcx, [ rsp + 0x68 ]
lea r14, [ r14 + rcx ]
adcx r8, [ rsp + 0x190 ]
mov rcx, 0x6730d2a0f6b0f624 
xchg rdx, rcx
mulx r12, rbx, r15
seto dl
mov [ rsp + 0x1c8 ], r8
movzx r8, byte [ rsp + 0x150 ]
mov [ rsp + 0x1d0 ], rax
mov rax, 0x0 
dec rax
adox r8, rax
adox rdi, [ rsp + 0x48 ]
setc r8b
clc
movzx r13, r13b
adcx r13, rax
adcx rbx, [ rsp + 0x1a0 ]
seto r13b
inc rax
adox rbp, [ rsp + 0x20 ]
mov rax, 0x89f3fffcfffcfffd 
xchg rdx, rax
mov [ rsp + 0x1d8 ], rdi
mov [ rsp + 0x1e0 ], r9
mulx r9, rdi, rbp
mov r9, 0x64774b84f38512bf 
mov rdx, r9
mov byte [ rsp + 0x1e8 ], r8b
mulx r8, r9, rdi
movzx rdx, r13b
mov [ rsp + 0x1f0 ], r8
mov r8, [ rsp + 0x1c0 ]
lea rdx, [ rdx + r8 ]
mov r8, 0x1eabfffeb153ffff 
xchg rdx, rdi
mov [ rsp + 0x1f8 ], rdi
mulx rdi, r13, r8
mov r8, 0x64774b84f38512bf 
xchg rdx, r8
mov [ rsp + 0x200 ], r9
mov [ rsp + 0x208 ], rdi
mulx rdi, r9, r15
adcx r9, r12
seto r12b
mov rdx, 0x0 
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r11, rbx
adox r9, r10
mov rcx, 0xb9feffffffffaaab 
mov rdx, rcx
mulx r10, rcx, r8
seto bl
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox r11, [ rsp + 0x188 ]
mov r12, 0x1a0111ea397fe69a 
mov rdx, r15
mov [ rsp + 0x210 ], r9
mulx r9, r15, r12
mov r12, 0x4b1ba7b6434bacd7 
mov [ rsp + 0x218 ], r9
mov [ rsp + 0x220 ], r11
mulx r11, r9, r12
movzx rdx, byte [ rsp + 0x180 ]
mov r12, [ rsp + 0x138 ]
lea rdx, [ rdx + r12 ]
adcx r9, rdi
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x228 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
adcx r15, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x230 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x238 ], r13
movzx r13, byte [ rsp + 0x1b8 ]
mov [ rsp + 0x240 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r13, r10
adox r11, [ rsp + 0x30 ]
setc r13b
clc
movzx rax, al
adcx rax, r10
adcx r12, r14
adox rdi, rcx
setc al
movzx r14, byte [ rsp + 0x1e8 ]
clc
adcx r14, r10
adcx r12, [ rsp + 0x1e0 ]
movzx rax, al
movzx r14, al
adcx r14, [ rsp + 0x1d0 ]
setc cl
clc
movzx rbx, bl
adcx rbx, r10
adcx r9, [ rsp + 0x1c8 ]
adcx r15, r12
mov rbx, [ rsp + 0x238 ]
setc al
clc
adcx rbx, [ rsp + 0x240 ]
mov r12, 0x4b1ba7b6434bacd7 
xchg rdx, r8
mov [ rsp + 0x248 ], rdi
mulx rdi, r10, r12
mov r12, 0x6730d2a0f6b0f624 
mov [ rsp + 0x250 ], rdi
mov [ rsp + 0x258 ], r15
mulx r15, rdi, r12
adcx rdi, [ rsp + 0x208 ]
adcx r15, [ rsp + 0x200 ]
adcx r10, [ rsp + 0x1f0 ]
seto r12b
mov [ rsp + 0x260 ], r10
mov r10, -0x2 
inc r10
adox rbp, [ rsp + 0x228 ]
adox rbx, [ rsp + 0x220 ]
movzx rbp, r13b
mov r10, [ rsp + 0x218 ]
lea rbp, [ rbp + r10 ]
seto r10b
mov r13, 0x0 
dec r13
movzx rax, al
adox rax, r13
adox r14, rbp
setc al
clc
adcx rbx, [ rsp + 0x130 ]
mov rbp, [ rsp + 0x210 ]
seto r13b
mov byte [ rsp + 0x268 ], al
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx r8, r8b
adox r8, rax
adox rbp, [ rsp + 0x198 ]
movzx r8, r13b
movzx rcx, cl
lea r8, [ r8 + rcx ]
adox r11, r9
seto cl
inc rax
mov r9, -0x1 
movzx r10, r10b
adox r10, r9
adox rbp, rdi
mov rdi, 0x89f3fffcfffcfffd 
xchg rdx, rdi
mulx r13, r10, rbx
adcx rbp, [ rsp + 0x178 ]
mov r13, 0x1eabfffeb153ffff 
mov rdx, r13
mulx rax, r13, r10
mov r9, [ rsp + 0x18 ]
setc dl
clc
mov [ rsp + 0x270 ], r8
mov r8, -0x1 
movzx r12, r12b
adcx r12, r8
adcx r9, [ rsp + 0x230 ]
mov r12, 0xb9feffffffffaaab 
xchg rdx, r12
mov [ rsp + 0x278 ], rax
mulx rax, r8, r10
mov rdx, [ rsp + 0x248 ]
mov [ rsp + 0x280 ], rbp
seto bpl
mov byte [ rsp + 0x288 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox rdx, [ rsp + 0x258 ]
setc cl
clc
movzx rbp, bpl
adcx rbp, r12
adcx r11, r15
movzx r15, cl
mov rbp, [ rsp + 0x10 ]
lea r15, [ r15 + rbp ]
mov rbp, 0x1a0111ea397fe69a 
xchg rdx, rbp
mulx r12, rcx, rdi
adox r9, r14
setc dil
movzx r14, byte [ rsp + 0x268 ]
clc
mov rdx, -0x1 
adcx r14, rdx
adcx rcx, [ rsp + 0x250 ]
setc r14b
clc
movzx rdi, dil
adcx rdi, rdx
adcx rbp, [ rsp + 0x260 ]
seto dil
inc rdx
adox r8, rbx
adcx rcx, r9
setc r8b
clc
adcx r13, rax
setc bl
movzx rax, byte [ rsp + 0x288 ]
clc
mov r9, -0x1 
adcx rax, r9
adcx r11, [ rsp + 0x168 ]
adox r13, [ rsp + 0x280 ]
mov rax, 0x6730d2a0f6b0f624 
mov rdx, rax
mulx r9, rax, r10
adcx rbp, [ rsp + 0x160 ]
mov rdx, 0x64774b84f38512bf 
mov [ rsp + 0x290 ], rbp
mov [ rsp + 0x298 ], r11
mulx r11, rbp, r10
seto dl
mov [ rsp + 0x2a0 ], rcx
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox rax, [ rsp + 0x278 ]
seto bl
inc rcx
adox r13, [ rsp + 0xa8 ]
setc cl
clc
mov [ rsp + 0x2a8 ], rax
mov rax, -0x1 
movzx rdi, dil
adcx rdi, rax
adcx r15, [ rsp + 0x270 ]
seto dil
inc rax
mov rax, -0x1 
movzx rbx, bl
adox rbx, rax
adox r9, rbp
movzx rbp, r14b
lea rbp, [ rbp + r12 ]
mov r12, 0x89f3fffcfffcfffd 
xchg rdx, r13
mulx rbx, r14, r12
mov rbx, 0xb9feffffffffaaab 
xchg rdx, rbx
mulx r12, rax, r14
mov rdx, 0x64774b84f38512bf 
mov [ rsp + 0x2b0 ], r12
mov byte [ rsp + 0x2b8 ], dil
mulx rdi, r12, r14
mov rdx, 0x4b1ba7b6434bacd7 
mov [ rsp + 0x2c0 ], rdi
mov [ rsp + 0x2c8 ], r12
mulx r12, rdi, r10
setc dl
clc
adcx rax, rbx
adox rdi, r11
setc al
clc
mov r11, -0x1 
movzx r8, r8b
adcx r8, r11
adcx r15, rbp
mov r8, 0x1a0111ea397fe69a 
xchg rdx, r8
mulx rbp, rbx, r10
movzx r10, r8b
mov r11, 0x0 
adcx r10, r11
mov r8, [ rsp - 0x20 ]
movzx r11, byte [ rsp + 0x170 ]
clc
mov rdx, -0x1 
adcx r11, rdx
adcx r8, [ rsp + 0x80 ]
adox rbx, r12
mov r11, [ rsp + 0x78 ]
mov r12, 0x0 
adcx r11, r12
mov r12, [ rsp + 0x2a0 ]
clc
movzx rcx, cl
adcx rcx, rdx
adcx r12, [ rsp + 0x158 ]
mov rcx, [ rsp + 0x298 ]
seto dl
mov [ rsp + 0x2d0 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox rcx, [ rsp + 0x2a8 ]
adcx r8, r15
movzx r13, dl
lea r13, [ r13 + rbp ]
adox r9, [ rsp + 0x290 ]
adcx r11, r10
adox rdi, r12
seto r15b
movzx rbp, byte [ rsp + 0x2b8 ]
inc rbx
mov r10, -0x1 
adox rbp, r10
adox rcx, [ rsp + 0xd0 ]
adox r9, [ rsp + 0xe8 ]
mov rbp, 0x1eabfffeb153ffff 
mov rdx, rbp
mulx r12, rbp, r14
setc r10b
clc
adcx rbp, [ rsp + 0x2b0 ]
adox rdi, [ rsp + 0x128 ]
mov rbx, 0x6730d2a0f6b0f624 
mov rdx, r14
mov byte [ rsp + 0x2d8 ], r10b
mulx r10, r14, rbx
setc bl
clc
mov [ rsp + 0x2e0 ], r13
mov r13, -0x1 
movzx rax, al
adcx rax, r13
adcx rcx, rbp
mov rax, 0x1a0111ea397fe69a 
mulx r13, rbp, rax
setc al
clc
mov [ rsp + 0x2e8 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r12, r14
adcx r10, [ rsp + 0x2c8 ]
mov rbx, 0x4b1ba7b6434bacd7 
mulx r11, r14, rbx
adcx r14, [ rsp + 0x2c0 ]
adcx rbp, r11
setc dl
clc
adcx rcx, [ rsp + 0xf0 ]
mov r11, 0x89f3fffcfffcfffd 
xchg rdx, r11
mov [ rsp + 0x2f0 ], rbp
mulx rbp, rbx, rcx
setc bpl
clc
mov rdx, -0x1 
movzx rax, al
adcx rax, rdx
adcx r9, r12
seto al
inc rdx
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r9, [ rsp + 0x120 ]
adcx r10, rdi
movzx rdi, r11b
lea rdi, [ rdi + r13 ]
mov r13, 0x1eabfffeb153ffff 
mov rdx, r13
mulx r11, r13, rbx
adox r10, [ rsp + 0x118 ]
mov rbp, 0x4b1ba7b6434bacd7 
mov rdx, rbx
mulx r12, rbx, rbp
seto bpl
mov [ rsp + 0x2f8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r15, r15b
adox r15, r12
adox r8, [ rsp + 0x2d0 ]
mov r15, [ rsp + 0x2e8 ]
adox r15, [ rsp + 0x2e0 ]
movzx r12, byte [ rsp + 0x2d8 ]
mov [ rsp + 0x300 ], rdi
mov rdi, 0x0 
adox r12, rdi
dec rdi
movzx rax, al
adox rax, rdi
adox r8, [ rsp + 0x110 ]
adox r15, [ rsp + 0x1d8 ]
mov rax, 0xb9feffffffffaaab 
mov [ rsp + 0x308 ], r15
mulx r15, rdi, rax
adox r12, [ rsp + 0x1f8 ]
setc al
clc
adcx rdi, rcx
setc dil
clc
adcx r13, r15
mov rcx, 0x6730d2a0f6b0f624 
mov [ rsp + 0x310 ], r12
mulx r12, r15, rcx
adcx r15, r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x318 ], bpl
mulx rbp, rcx, rdx
mov rdx, 0x64774b84f38512bf 
mov [ rsp + 0x320 ], rbp
mov [ rsp + 0x328 ], r14
mulx r14, rbp, r11
setc dl
clc
mov [ rsp + 0x330 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx r9, r13
seto dil
inc r8
mov r13, -0x1 
movzx rdx, dl
adox rdx, r13
adox r12, rbp
adox rbx, r14
adcx r15, r10
mov r10, [ rsp - 0x40 ]
setc dl
movzx rbp, byte [ rsp + 0x108 ]
clc
adcx rbp, r13
adcx r10, [ rsp - 0x38 ]
adcx rcx, [ rsp - 0x48 ]
mov rbp, [ rsp + 0x330 ]
seto r14b
dec r8
movzx rax, al
adox rax, r8
adox rbp, [ rsp + 0x328 ]
setc r13b
movzx rax, byte [ rsp + 0x318 ]
clc
adcx rax, r8
adcx rbp, [ rsp + 0x100 ]
mov rax, [ rsp + 0x308 ]
adox rax, [ rsp + 0x2f0 ]
movzx r8, r13b
mov byte [ rsp + 0x338 ], r14b
mov r14, [ rsp + 0x320 ]
lea r8, [ r8 + r14 ]
adcx r10, rax
seto r14b
setc r13b
mov rax, 0xb9feffffffffaaab 
mov [ rsp + 0x340 ], r8
mov r8, r9
sub r8, rax
mov rax, [ rsp + 0x310 ]
mov [ rsp + 0x348 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rax, [ rsp + 0x300 ]
seto r14b
inc r8
mov r8, -0x1 
movzx rdx, dl
adox rdx, r8
adox rbp, r12
seto r12b
mov rdx, 0x1eabfffeb153ffff 
mov r8, r15
sbb r8, rdx
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox r10, rbx
seto bl
mov r12, 0x6730d2a0f6b0f624 
mov rdx, rbp
sbb rdx, r12
movzx r12, r14b
movzx rdi, dil
lea r12, [ r12 + rdi ]
mov rdi, 0x1a0111ea397fe69a 
xchg rdx, r11
mov [ rsp + 0x350 ], r11
mulx r11, r14, rdi
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox rax, rcx
setc cl
movzx r13, byte [ rsp + 0x338 ]
clc
adcx r13, rdx
adcx r14, [ rsp + 0x2f8 ]
mov r13, 0x0 
adcx r11, r13
clc
movzx rbx, bl
adcx rbx, rdx
adcx rax, r14
adox r12, [ rsp + 0x340 ]
adcx r11, r12
seto bl
setc r14b
add dl, cl
mov rdx, 0x64774b84f38512bf 
mov r12, r10
sbb r12, rdx
movzx rcx, r14b
movzx rbx, bl
lea rcx, [ rcx + rbx ]
mov rbx, 0x4b1ba7b6434bacd7 
mov r14, rax
sbb r14, rbx
mov r13, r11
sbb r13, rdi
mov rbx, 0x0 
sbb rcx, rbx
cmovc r14, rax
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x20 ], r14
cmovc r8, r15
mov [ rcx + 0x8 ], r8
cmovc r12, r10
mov [ rcx + 0x18 ], r12
mov r15, [ rsp + 0x350 ]
cmovc r15, rbp
mov rbp, [ rsp + 0x348 ]
cmovc rbp, r9
mov [ rcx + 0x0 ], rbp
cmovc r13, r11
mov [ rcx + 0x28 ], r13
mov [ rcx + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 984
ret















ret
