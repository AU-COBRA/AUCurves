SECTION .text
	GLOBAL fiat_bls12_381_p_mul
fiat_bls12_381_p_mul:
SECTION .text
	GLOBAL fiat_bls12_381_p_mul
fiat_bls12_381_p_mul:
sub rsp, 1232
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0x89f3fffcfffcfffd 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rdi
mulx rdi, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], rcx
mulx rcx, rdi, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, 0x6730d2a0f6b0f624 
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r12
mulx r12, rbp, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], rbx
mulx rbx, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r9
mulx r9, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], rdi
mulx rdi, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x50 ], rdi
mov [ rsp + 0x58 ], rbp
mulx rbp, rdi, [ rsi + 0x18 ]
test al, al
adox rdi, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], rdi
mulx rdi, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r8
mulx r8, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], rcx
mulx rcx, rbp, [ rax + 0x18 ]
mov rdx, 0xb9feffffffffaaab 
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rbp
mulx rbp, rcx, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
adcx rbp, r14
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa8 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
adcx r10, rcx
setc dl
clc
adcx r12, rbx
mov bl, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb0 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
setc dl
clc
adcx rdi, rbp
adcx rcx, r8
mov r8b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb8 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], r12
mulx r12, rdi, [ rax + 0x0 ]
setc dl
clc
adcx r9, r12
mov r12b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
seto dl
mov byte [ rsp + 0xe0 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox r11, r9
mov rbx, [ rsp + 0x80 ]
adcx rbx, [ rsp + 0x48 ]
setc r9b
clc
movzx r8, r8b
adcx r8, r12
adcx rbp, [ rsp + 0x40 ]
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xe8 ], rbx
mulx rbx, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], rbp
mulx rbp, rbx, [ rax + 0x20 ]
adox rbx, rdi
mov rdx, 0x1eabfffeb153ffff 
mov [ rsp + 0x100 ], rbp
mulx rbp, rdi, r15
adcx rcx, [ rsp + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
adcx r12, [ rsp + 0x18 ]
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x118 ], r12
seto r12b
mov byte [ rsp + 0x120 ], r8b
mov r8, 0x0 
dec r8
movzx r9, r9b
adox r9, r8
adox rdx, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x30 ]
seto r9b
inc r8
adox r13, [ rsp + 0xa0 ]
setc r13b
clc
adcx rdi, [ rsp + 0x98 ]
adox rdi, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0x8 ]
mov [ rsp + 0x128 ], rcx
setc cl
clc
adcx r14, rdi
mov rdi, 0x64774b84f38512bf 
xchg rdx, r15
mov [ rsp + 0x130 ], r15
mulx r15, r8, rdi
setc dil
clc
mov byte [ rsp + 0x138 ], r13b
mov r13, -0x1 
movzx rcx, cl
adcx rcx, r13
adcx r8, [ rsp + 0x0 ]
mov rcx, 0x4b1ba7b6434bacd7 
mov byte [ rsp + 0x140 ], dil
mulx rdi, r13, rcx
adox rbp, r10
adcx r13, r15
adox r8, r11
setc r10b
clc
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx rbx, [ rsp - 0x18 ]
mov r9, [ rsp + 0x78 ]
setc r15b
movzx r11, byte [ rsp + 0x120 ]
clc
mov rcx, -0x1 
adcx r11, rcx
adcx r9, [ rsp - 0x8 ]
mov r11, 0x89f3fffcfffcfffd 
xchg rdx, r14
mov [ rsp + 0x148 ], rbx
mulx rbx, rcx, r11
movzx rbx, r15b
mov r11, [ rsp - 0x20 ]
lea rbx, [ rbx + r11 ]
mov r11, 0x1a0111ea397fe69a 
xchg rdx, rcx
mov [ rsp + 0x150 ], rbx
mulx rbx, r15, r11
mov r11, 0xb9feffffffffaaab 
mov [ rsp + 0x158 ], r9
mov [ rsp + 0x160 ], rbx
mulx rbx, r9, r11
mov r11, 0x6730d2a0f6b0f624 
mov [ rsp + 0x168 ], r15
mov [ rsp + 0x170 ], r8
mulx r8, r15, r11
mov r11, 0x1a0111ea397fe69a 
xchg rdx, r14
mov [ rsp + 0x178 ], r8
mov [ rsp + 0x180 ], r9
mulx r9, r8, r11
setc dl
clc
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rdi, r8
mov r10, 0x1eabfffeb153ffff 
xchg rdx, r14
mulx r11, r8, r10
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x188 ], r14b
mov [ rsp + 0x190 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x198 ], r11
mov [ rsp + 0x1a0 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
adox r13, [ rsp + 0x110 ]
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx r14, [ rsp + 0x100 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1a8 ], r13
mulx r13, r12, [ rsi + 0x8 ]
setc dl
mov [ rsp + 0x1b0 ], r13
movzx r13, byte [ rsp + 0xe0 ]
clc
mov [ rsp + 0x1b8 ], r8
mov r8, -0x1 
adcx r13, r8
adcx r11, [ rsp + 0xc8 ]
adcx rbp, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x40 ]
mov r13b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], r12
mulx r12, r8, [ rax + 0x8 ]
adox rdi, r14
movzx rdx, r13b
lea rdx, [ rdx + r15 ]
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r14, [ rax + 0x0 ]
adox r9, r15
seto dl
mov r15, -0x2 
inc r15
adox rbx, [ rsp + 0x1b8 ]
mov r15, [ rsp + 0x1a0 ]
mov [ rsp + 0x1c8 ], r14
setc r14b
mov byte [ rsp + 0x1d0 ], dl
movzx rdx, byte [ rsp + 0x140 ]
clc
mov [ rsp + 0x1d8 ], r9
mov r9, -0x1 
adcx rdx, r9
adcx r15, [ rsp + 0xc0 ]
mov rdx, [ rsp + 0x198 ]
adox rdx, [ rsp + 0x190 ]
seto r9b
mov [ rsp + 0x1e0 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, [ rsp + 0x180 ]
seto cl
inc rbp
adox r8, r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1e8 ], r8
mulx r8, rbp, [ rax + 0x10 ]
adox rbp, r12
adox r8, [ rsp + 0x70 ]
mov rdx, [ rsp + 0x170 ]
adcx rdx, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0x1a8 ]
setc r12b
clc
mov [ rsp + 0x1f0 ], r8
mov r8, -0x1 
movzx rcx, cl
adcx rcx, r8
adcx r15, rbx
adcx r13, rdx
setc bl
clc
adcx r15, [ rsp + 0x20 ]
mov rcx, 0x89f3fffcfffcfffd 
mov rdx, r15
mulx r8, r15, rcx
mov r8, 0x64774b84f38512bf 
xchg rdx, r8
mov [ rsp + 0x1f8 ], rbp
mulx rbp, rcx, r15
mov rdx, 0xb9feffffffffaaab 
mov [ rsp + 0x200 ], rbp
mov [ rsp + 0x208 ], rcx
mulx rcx, rbp, r15
mov rdx, [ rsp - 0x28 ]
adox rdx, [ rsp + 0x68 ]
adcx r13, [ rsp + 0xb0 ]
mov [ rsp + 0x210 ], rdx
mov rdx, 0x6730d2a0f6b0f624 
mov [ rsp + 0x218 ], r11
mov byte [ rsp + 0x220 ], bl
mulx rbx, r11, r15
mov rdx, 0x1eabfffeb153ffff 
mov [ rsp + 0x228 ], rbx
mov [ rsp + 0x230 ], r11
mulx r11, rbx, r15
movzx rdx, r14b
mov [ rsp + 0x238 ], r11
mov r11, [ rsp + 0x1b0 ]
lea rdx, [ rdx + r11 ]
setc r11b
clc
mov r14, -0x1 
movzx r12, r12b
adcx r12, r14
adcx rdi, [ rsp + 0x1e0 ]
mov r12, [ rsp + 0x1d8 ]
adcx r12, [ rsp + 0x1c0 ]
mov r14, 0x1a0111ea397fe69a 
xchg rdx, r15
mov [ rsp + 0x240 ], r12
mov byte [ rsp + 0x248 ], r11b
mulx r11, r12, r14
mov r14, 0x64774b84f38512bf 
xchg rdx, r14
mov [ rsp + 0x250 ], r11
mov [ rsp + 0x258 ], r12
mulx r12, r11, r10
movzx rdx, byte [ rsp + 0x1d0 ]
adcx rdx, r15
setc r15b
clc
mov [ rsp + 0x260 ], rdx
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx r11, [ rsp + 0x178 ]
mov r9, 0x4b1ba7b6434bacd7 
mov rdx, r10
mov byte [ rsp + 0x268 ], r15b
mulx r15, r10, r9
adcx r10, r12
mov rdx, [ rsi + 0x10 ]
mulx r9, r12, [ rax + 0x28 ]
mov rdx, [ rsp - 0x30 ]
adox rdx, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x168 ]
mov [ rsp + 0x270 ], rdx
seto dl
mov [ rsp + 0x278 ], r9
mov r9, -0x2 
inc r9
adox rbp, r8
seto bpl
inc r9
adox rbx, rcx
seto r8b
dec r9
movzx rbp, bpl
adox rbp, r9
adox r13, rbx
mov rcx, [ rsp + 0x238 ]
seto bpl
inc r9
mov rbx, -0x1 
movzx r8, r8b
adox r8, rbx
adox rcx, [ rsp + 0x230 ]
setc r8b
clc
adcx r13, [ rsp - 0x48 ]
mov r9, 0x89f3fffcfffcfffd 
xchg rdx, r13
mov byte [ rsp + 0x280 ], r13b
mulx r13, rbx, r9
setc r13b
movzx r9, byte [ rsp + 0x220 ]
clc
mov byte [ rsp + 0x288 ], r8b
mov r8, -0x1 
adcx r9, r8
adcx r11, [ rsp + 0x218 ]
adcx r10, rdi
seto r9b
movzx rdi, byte [ rsp + 0x248 ]
inc r8
mov r8, -0x1 
adox rdi, r8
adox r11, [ rsp + 0xf8 ]
adox r10, [ rsp + 0x108 ]
mov rdi, 0xb9feffffffffaaab 
xchg rdx, rbx
mov byte [ rsp + 0x290 ], r13b
mulx r13, r8, rdi
adcx r15, [ rsp + 0x240 ]
mov rdi, 0x1eabfffeb153ffff 
mov [ rsp + 0x298 ], r8
mov [ rsp + 0x2a0 ], r13
mulx r13, r8, rdi
adox r15, [ rsp + 0x118 ]
mov rdi, 0x6730d2a0f6b0f624 
mov [ rsp + 0x2a8 ], r13
mov [ rsp + 0x2b0 ], r8
mulx r8, r13, rdi
mov rdi, [ rsp + 0x208 ]
mov [ rsp + 0x2b8 ], r8
setc r8b
clc
mov [ rsp + 0x2c0 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx rdi, [ rsp + 0x228 ]
mov r9, 0x4b1ba7b6434bacd7 
xchg rdx, r14
mov byte [ rsp + 0x2c8 ], r8b
mulx r8, r13, r9
adcx r13, [ rsp + 0x200 ]
setc dl
clc
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx r11, rcx
adcx rdi, r10
adcx r13, r15
mov rbp, [ rsp - 0x10 ]
seto cl
movzx r10, byte [ rsp + 0x188 ]
inc r9
mov r15, -0x1 
adox r10, r15
adox rbp, [ rsp + 0x90 ]
setc r10b
movzx r9, byte [ rsp + 0x138 ]
clc
adcx r9, r15
adcx r12, [ rsp + 0xf0 ]
movzx r9, byte [ rsp + 0x288 ]
mov r15, [ rsp + 0x160 ]
lea r9, [ r9 + r15 ]
setc r15b
mov byte [ rsp + 0x2d0 ], r10b
movzx r10, byte [ rsp + 0x2c8 ]
clc
mov [ rsp + 0x2d8 ], r8
mov r8, -0x1 
adcx r10, r8
adcx r9, [ rsp + 0x260 ]
mov r10, 0x64774b84f38512bf 
xchg rdx, r10
mov byte [ rsp + 0x2e0 ], r10b
mulx r10, r8, r14
movzx rdx, r15b
mov [ rsp + 0x2e8 ], r10
mov r10, [ rsp + 0x278 ]
lea rdx, [ rdx + r10 ]
mov r10, [ rsp + 0x2a0 ]
seto r15b
mov [ rsp + 0x2f0 ], rdx
mov rdx, -0x2 
inc rdx
adox r10, [ rsp + 0x2b0 ]
seto dl
mov byte [ rsp + 0x2f8 ], r15b
movzx r15, byte [ rsp + 0x290 ]
mov [ rsp + 0x300 ], r8
mov r8, 0x0 
dec r8
adox r15, r8
adox r11, [ rsp + 0x60 ]
mov r15b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x308 ], r10
mulx r10, r8, [ rsi + 0x18 ]
adox rdi, [ rsp + 0x158 ]
adox rbp, r13
setc dl
clc
adcx rbx, [ rsp + 0x298 ]
seto bl
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox r9, r12
mov rcx, [ rsp + 0x2c0 ]
seto r12b
inc r13
mov r13, -0x1 
movzx r15, r15b
adox r15, r13
adox rcx, [ rsp + 0x2a8 ]
adcx r11, [ rsp + 0x308 ]
adcx rcx, rdi
seto r15b
inc r13
adox r11, [ rsp + 0xd8 ]
mov rdi, 0x89f3fffcfffcfffd 
xchg rdx, rdi
mov [ rsp + 0x310 ], r10
mulx r10, r13, r11
adox rcx, [ rsp + 0xd0 ]
mov r10, 0x4b1ba7b6434bacd7 
mov rdx, r14
mov byte [ rsp + 0x318 ], bl
mulx rbx, r14, r10
mov r10, 0x64774b84f38512bf 
xchg rdx, r13
mov [ rsp + 0x320 ], rcx
mov [ rsp + 0x328 ], r8
mulx r8, rcx, r10
mov r10, 0x1eabfffeb153ffff 
mov [ rsp + 0x330 ], r8
mov [ rsp + 0x338 ], rcx
mulx rcx, r8, r10
mov r10, [ rsp + 0x2b8 ]
mov [ rsp + 0x340 ], rcx
setc cl
clc
mov [ rsp + 0x348 ], r9
mov r9, -0x1 
movzx r15, r15b
adcx r15, r9
adcx r10, [ rsp + 0x300 ]
adcx r14, [ rsp + 0x2e8 ]
mov r15, 0xb9feffffffffaaab 
mov [ rsp + 0x350 ], r14
mulx r14, r9, r15
mov r15, 0x1a0111ea397fe69a 
xchg rdx, r15
mov [ rsp + 0x358 ], r9
mov byte [ rsp + 0x360 ], r12b
mulx r12, r9, r13
setc r13b
clc
adcx r8, r14
setc r14b
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx rbx, r9
mov r13, [ rsp + 0x2d8 ]
setc r9b
movzx rdx, byte [ rsp + 0x2e0 ]
clc
mov [ rsp + 0x368 ], r12
mov r12, -0x1 
adcx rdx, r12
adcx r13, [ rsp + 0x258 ]
mov rdx, [ rsp + 0x250 ]
mov r12, 0x0 
adcx rdx, r12
clc
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx rbp, r10
movzx rcx, dil
movzx r10, byte [ rsp + 0x268 ]
lea rcx, [ rcx + r10 ]
setc r10b
movzx rdi, byte [ rsp + 0x360 ]
clc
adcx rdi, r12
adcx rcx, [ rsp + 0x2f0 ]
setc dil
movzx r12, byte [ rsp + 0x2d0 ]
clc
mov byte [ rsp + 0x370 ], r9b
mov r9, -0x1 
adcx r12, r9
adcx r13, [ rsp + 0x348 ]
mov r12, 0x6730d2a0f6b0f624 
xchg rdx, r12
mov byte [ rsp + 0x378 ], dil
mulx rdi, r9, r15
adcx r12, rcx
setc cl
clc
adcx r11, [ rsp + 0x358 ]
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x380 ], cl
mulx rcx, r11, [ rsi + 0x18 ]
setc dl
mov [ rsp + 0x388 ], rbx
movzx rbx, byte [ rsp + 0x2f8 ]
clc
mov [ rsp + 0x390 ], rdi
mov rdi, -0x1 
adcx rbx, rdi
adcx r11, [ rsp + 0x88 ]
adcx rcx, [ rsp + 0x328 ]
setc bl
clc
movzx rdx, dl
adcx rdx, rdi
adcx r8, [ rsp + 0x320 ]
seto dl
inc rdi
adox r8, [ rsp + 0x1c8 ]
mov rdi, 0x89f3fffcfffcfffd 
xchg rdx, r8
mov byte [ rsp + 0x398 ], bl
mov [ rsp + 0x3a0 ], r9
mulx r9, rbx, rdi
mov r9, 0x4b1ba7b6434bacd7 
xchg rdx, rbx
mov byte [ rsp + 0x3a8 ], r14b
mulx r14, rdi, r9
mov r9, 0x1eabfffeb153ffff 
mov [ rsp + 0x3b0 ], r14
mov [ rsp + 0x3b8 ], rdi
mulx rdi, r14, r9
setc r9b
mov [ rsp + 0x3c0 ], rdi
movzx rdi, byte [ rsp + 0x318 ]
clc
mov [ rsp + 0x3c8 ], r14
mov r14, -0x1 
adcx rdi, r14
adcx r13, r11
seto dil
inc r14
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox rbp, [ rsp + 0xe8 ]
setc r8b
clc
movzx r10, r10b
adcx r10, r11
adcx r13, [ rsp + 0x350 ]
setc r10b
clc
movzx r8, r8b
adcx r8, r11
adcx r12, rcx
mov rcx, 0x4b1ba7b6434bacd7 
xchg rdx, rcx
mulx r14, r8, r15
mov r11, [ rsp + 0x3a0 ]
seto dl
mov byte [ rsp + 0x3d0 ], dil
movzx rdi, byte [ rsp + 0x3a8 ]
mov [ rsp + 0x3d8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rdi, r13
adox r11, [ rsp + 0x340 ]
movzx rdi, byte [ rsp + 0x398 ]
mov r13, [ rsp + 0x310 ]
lea rdi, [ rdi + r13 ]
mov r13, [ rsp + 0x390 ]
adox r13, [ rsp + 0x338 ]
adox r8, [ rsp + 0x330 ]
mov [ rsp + 0x3e0 ], r8
setc r8b
clc
mov [ rsp + 0x3e8 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx rbp, r11
mov r9, 0x64774b84f38512bf 
xchg rdx, rcx
mulx r13, r11, r9
mov r9, 0x1a0111ea397fe69a 
mov [ rsp + 0x3f0 ], rbp
mov [ rsp + 0x3f8 ], rdi
mulx rdi, rbp, r9
xchg rdx, r15
mov [ rsp + 0x400 ], rdi
mov byte [ rsp + 0x408 ], r8b
mulx r8, rdi, r9
adox rdi, r14
mov rdx, 0xb9feffffffffaaab 
mulx r9, r14, r15
setc dl
clc
adcx r14, rbx
seto r14b
mov rbx, 0x0 
dec rbx
movzx r10, r10b
adox r10, rbx
adox r12, [ rsp + 0x388 ]
seto r10b
inc rbx
adox r9, [ rsp + 0x3c8 ]
mov rbx, 0x6730d2a0f6b0f624 
xchg rdx, rbx
mov [ rsp + 0x410 ], r8
mov byte [ rsp + 0x418 ], r14b
mulx r14, r8, r15
adox r8, [ rsp + 0x3c0 ]
adox r11, r14
adox r13, [ rsp + 0x3b8 ]
mov r15, [ rsp + 0x130 ]
setc r14b
clc
mov rdx, -0x1 
movzx rcx, cl
adcx rcx, rdx
adcx r15, [ rsp + 0x3d8 ]
movzx rcx, byte [ rsp + 0x380 ]
movzx rdx, byte [ rsp + 0x378 ]
lea rcx, [ rcx + rdx ]
movzx rdx, byte [ rsp + 0x370 ]
mov [ rsp + 0x420 ], r13
mov r13, [ rsp + 0x368 ]
lea rdx, [ rdx + r13 ]
adox rbp, [ rsp + 0x3b0 ]
adcx r12, [ rsp + 0x128 ]
seto r13b
mov [ rsp + 0x428 ], rbp
movzx rbp, byte [ rsp + 0x408 ]
mov [ rsp + 0x430 ], r11
mov r11, 0x0 
dec r11
adox rbp, r11
adox rcx, [ rsp + 0x3f8 ]
seto bpl
inc r11
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox rcx, rdx
adcx rcx, [ rsp + 0x148 ]
setc r10b
clc
movzx rbx, bl
adcx rbx, r11
adcx r15, [ rsp + 0x3e8 ]
movzx rbx, r13b
mov rdx, [ rsp + 0x400 ]
lea rbx, [ rbx + rdx ]
adcx r12, [ rsp + 0x3e0 ]
adcx rdi, rcx
mov rdx, [ rsp + 0x1e8 ]
setc r13b
movzx rcx, byte [ rsp + 0x3d0 ]
clc
adcx rcx, r11
adcx rdx, [ rsp + 0x3f0 ]
adcx r15, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x1f0 ]
adcx rdi, [ rsp + 0x210 ]
movzx rcx, bpl
mov r11, 0x0 
adox rcx, r11
dec r11
movzx r14, r14b
adox r14, r11
adox rdx, r9
seto r14b
setc r9b
mov rbp, 0xb9feffffffffaaab 
mov r11, rdx
sub r11, rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox r15, r8
adox r12, [ rsp + 0x430 ]
movzx r8, byte [ rsp + 0x280 ]
mov r14, [ rsp + 0x50 ]
lea r8, [ r8 + r14 ]
adox rdi, [ rsp + 0x420 ]
seto r14b
mov rbp, 0x1eabfffeb153ffff 
mov [ rsp + 0x438 ], r11
mov r11, r15
sbb r11, rbp
mov rbp, 0x6730d2a0f6b0f624 
mov [ rsp + 0x440 ], r11
mov r11, r12
sbb r11, rbp
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox rcx, [ rsp + 0x150 ]
movzx r10, byte [ rsp + 0x418 ]
mov rbp, [ rsp + 0x410 ]
lea r10, [ r10 + rbp ]
seto bpl
mov [ rsp + 0x448 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rcx, r10
seto r13b
inc r11
mov r10, -0x1 
movzx r9, r9b
adox r9, r10
adox rcx, [ rsp + 0x270 ]
movzx r9, r13b
movzx rbp, bpl
lea r9, [ r9 + rbp ]
seto bpl
mov r13, 0x64774b84f38512bf 
mov r11, rdi
sbb r11, r13
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox r9, r8
seto r8b
inc r10
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox rcx, [ rsp + 0x428 ]
adox rbx, r9
movzx r14, r8b
adox r14, r10
mov r9, 0x4b1ba7b6434bacd7 
mov r8, rcx
sbb r8, r9
mov r10, 0x1a0111ea397fe69a 
mov rbp, rbx
sbb rbp, r10
mov r10, 0x0 
sbb r14, r10
mov r14, [ rsp + 0x438 ]
cmovc r14, rdx
mov rdx, [ rsp + 0x448 ]
cmovc rdx, r12
mov r12, [ rsp + 0x440 ]
cmovc r12, r15
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r12
cmovc rbp, rbx
cmovc r11, rdi
mov [ r15 + 0x0 ], r14
cmovc r8, rcx
mov [ r15 + 0x20 ], r8
mov [ r15 + 0x28 ], rbp
mov [ r15 + 0x18 ], r11
mov [ r15 + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1232
ret















ret
