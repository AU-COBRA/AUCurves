SECTION .text
	GLOBAL fiat_bls12_381_p_mul
fiat_bls12_381_p_mul:
sub rsp, 1232
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, r10, [ rax + 0x10 ]; hix14, lox13<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x0 ]; hix234, lox233<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rsi + 0x10 ]; hix151, lox150<- arg1[2] * arg2[3]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x20 ]; hix301, lox300<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rax + 0x0 ]; hix18, lox17<- arg1[0] * arg2[0]
mov rdx, 0x89f3fffcfffcfffd ; moving imm to reg
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, r13; hi_, lox30<- x17 * 0x89f3fffcfffcfffd
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x48 ], rcx; spilling x233 to mem
mulx rcx, rdi, [ rax + 0x20 ]; hix72, lox71<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp - 0x40 ], rcx; spilling x72 to mem
mov [ rsp - 0x38 ], rdi; spilling x71 to mem
mulx rdi, rcx, [ rax + 0x20 ]; hix380, lox379<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x30 ], rdi; spilling x380 to mem
mov [ rsp - 0x28 ], rcx; spilling x379 to mem
mulx rcx, rdi, [ rsi + 0x20 ]; hix307, lox306<- arg1[4] * arg2[2]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x20 ], r12; spilling x301 to mem
mov [ rsp - 0x18 ], rbp; spilling x300 to mem
mulx rbp, r12, [ rsi + 0x18 ]; hix230, lox229<- arg1[3] * arg2[2]
mov rdx, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp - 0x10 ], rbp; spilling x230 to mem
mov [ rsp - 0x8 ], r12; spilling x229 to mem
mulx r12, rbp, r15; hix39, lox38<- x30 * 0x6730d2a0f6b0f624
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x0 ], r12; spilling x39 to mem
mov [ rsp + 0x8 ], rbp; spilling x38 to mem
mulx rbp, r12, [ rax + 0x8 ]; hix155, lox154<- arg1[2] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x10 ], rcx; spilling x307 to mem
mov [ rsp + 0x18 ], rbx; spilling x151 to mem
mulx rbx, rcx, [ rax + 0x0 ]; hix157, lox156<- arg1[2] * arg2[0]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x20 ], rcx; spilling x156 to mem
mov [ rsp + 0x28 ], r9; spilling x150 to mem
mulx r9, rcx, [ rsi + 0x20 ]; hix305, lox304<- arg1[4] * arg2[3]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x30 ], r9; spilling x305 to mem
mov [ rsp + 0x38 ], rcx; spilling x304 to mem
mulx rcx, r9, [ rsi + 0x20 ]; hix309, lox308<- arg1[4] * arg2[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x40 ], rbp; spilling x155 to mem
mov [ rsp + 0x48 ], rdi; spilling x306 to mem
mulx rdi, rbp, [ rax + 0x28 ]; hix378, lox377<- arg1[5] * arg2[5]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x50 ], rdi; spilling x378 to mem
mov [ rsp + 0x58 ], rbp; spilling x377 to mem
mulx rbp, rdi, [ rsi + 0x18 ]; hix232, lox231<- arg1[3] * arg2[1]
test al, al
adox rdi, r8
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x60 ], rdi; spilling x235 to mem
mulx rdi, r8, [ rax + 0x18 ]; hix382, lox381<- arg1[5] * arg2[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x68 ], rdi; spilling x382 to mem
mov [ rsp + 0x70 ], r8; spilling x381 to mem
mulx r8, rdi, [ rax + 0x8 ]; hix78, lox77<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x78 ], rbp; spilling x232 to mem
mov [ rsp + 0x80 ], rcx; spilling x309 to mem
mulx rcx, rbp, [ rax + 0x18 ]; hix228, lox227<- arg1[3] * arg2[3]
mov rdx, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x88 ], rcx; spilling x228 to mem
mov [ rsp + 0x90 ], rbp; spilling x227 to mem
mulx rbp, rcx, r15; hix43, lox42<- x30 * 0xb9feffffffffaaab
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x98 ], rbp; spilling x43 to mem
mov [ rsp + 0xa0 ], rcx; spilling x42 to mem
mulx rcx, rbp, [ rsi + 0x0 ]; hix16, lox15<- arg1[0] * arg2[1]
adcx rbp, r14
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0xa8 ], rbp; spilling x19 to mem
mulx rbp, r14, [ rsi + 0x8 ]; hix80, lox79<- arg1[1] * arg2[0]
adcx r10, rcx
setc dl;
clc;
adcx r12, rbx
mov bl, dl; preserving value of x22 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0xb0 ], r12; spilling x158 to mem
mulx r12, rcx, [ rsi + 0x8 ]; hix76, lox75<- arg1[1] * arg2[2]
setc dl;
clc;
adcx rdi, rbp
adcx rcx, r8
mov r8b, dl; preserving value of x159 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0xb8 ], rcx; spilling x83 to mem
mulx rcx, rbp, [ rsi + 0x10 ]; hix153, lox152<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xc0 ], rdi; spilling x81 to mem
mov [ rsp + 0xc8 ], r12; spilling x76 to mem
mulx r12, rdi, [ rax + 0x0 ]; hix311, lox310<- arg1[4] * arg2[0]
setc dl;
clc;
adcx r9, r12
mov r12b, dl; preserving value of x84 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0xd0 ], r9; spilling x312 to mem
mov [ rsp + 0xd8 ], rdi; spilling x310 to mem
mulx rdi, r9, [ rsi + 0x0 ]; hix12, lox11<- arg1[0] * arg2[3]
seto dl;
mov byte [ rsp + 0xe0 ], r12b; spilling byte x84 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r12; loading flag
adox r11, r9
mov rbx, [ rsp + 0x80 ]; load m64 x309 to register64
adcx rbx, [ rsp + 0x48 ]
setc r9b;
clc;
movzx r8, r8b
adcx r8, r12; loading flag
adcx rbp, [ rsp + 0x40 ]
mov r8b, dl; preserving value of x236 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0xe8 ], rbx; spilling x314 to mem
mulx rbx, r12, [ rsi + 0x10 ]; hix149, lox148<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xf0 ], rbx; spilling x149 to mem
mov [ rsp + 0xf8 ], rbp; spilling x160 to mem
mulx rbp, rbx, [ rax + 0x20 ]; hix10, lox9<- arg1[0] * arg2[4]
adox rbx, rdi
mov rdx, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x100 ], rbp; spilling x10 to mem
mulx rbp, rdi, r15; hix41, lox40<- x30 * 0x1eabfffeb153ffff
adcx rcx, [ rsp + 0x28 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x108 ], rcx; spilling x162 to mem
mov [ rsp + 0x110 ], rbx; spilling x25 to mem
mulx rbx, rcx, [ rsi + 0x20 ]; hix303, lox302<- arg1[4] * arg2[4]
adcx r12, [ rsp + 0x18 ]
mov rdx, [ rsp + 0x38 ]; load m64 x304 to register64
mov [ rsp + 0x118 ], r12; spilling x164 to mem
seto r12b;
mov byte [ rsp + 0x120 ], r8b; spilling byte x236 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, r8; loading flag
adox rdx, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x30 ]
seto r9b;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, [ rsp + 0xa0 ]
setc r13b;
clc;
adcx rdi, [ rsp + 0x98 ]
adox rdi, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0x8 ]
mov [ rsp + 0x128 ], rcx; spilling x318 to mem
setc cl;
clc;
adcx r14, rdi
mov rdi, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r15; x30, swapping with x316, which is currently in rdx
mov [ rsp + 0x130 ], r15; spilling x316 to mem
mulx r15, r8, rdi; hix37, lox36<- x30 * 0x64774b84f38512bf
setc dil;
clc;
mov byte [ rsp + 0x138 ], r13b; spilling byte x165 to mem
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r8, [ rsp + 0x0 ]
mov rcx, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov byte [ rsp + 0x140 ], dil; spilling byte x93 to mem
mulx rdi, r13, rcx; hix35, lox34<- x30 * 0x4b1ba7b6434bacd7
adox rbp, r10
adcx r13, r15
adox r8, r11
setc r10b;
clc;
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r11; loading flag
adcx rbx, [ rsp - 0x18 ]
mov r9, [ rsp + 0x78 ]; load m64 x232 to register64
setc r15b;
movzx r11, byte [ rsp + 0x120 ]; load byte memx236 to register64
clc;
mov rcx, -0x1 ; moving imm to reg
adcx r11, rcx; loading flag
adcx r9, [ rsp - 0x8 ]
mov r11, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r14; x92, swapping with x30, which is currently in rdx
mov [ rsp + 0x148 ], rbx; spilling x320 to mem
mulx rbx, rcx, r11; hi_, lox106<- x92 * 0x89f3fffcfffcfffd
movzx rbx, r15b;
mov r11, [ rsp - 0x20 ]; load m64 x301 to register64
lea rbx, [ rbx + r11 ]; r8/64 + m8
mov r11, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, rcx; x106, swapping with x92, which is currently in rdx
mov [ rsp + 0x150 ], rbx; spilling x322 to mem
mulx rbx, r15, r11; hix109, lox108<- x106 * 0x1a0111ea397fe69a
mov r11, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x158 ], r9; spilling x237 to mem
mov [ rsp + 0x160 ], rbx; spilling x109 to mem
mulx rbx, r9, r11; hix119, lox118<- x106 * 0xb9feffffffffaaab
mov r11, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x168 ], r15; spilling x108 to mem
mov [ rsp + 0x170 ], r8; spilling x61 to mem
mulx r8, r15, r11; hix115, lox114<- x106 * 0x6730d2a0f6b0f624
mov r11, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, r14; x30, swapping with x106, which is currently in rdx
mov [ rsp + 0x178 ], r8; spilling x115 to mem
mov [ rsp + 0x180 ], r9; spilling x118 to mem
mulx r9, r8, r11; hix33, lox32<- x30 * 0x1a0111ea397fe69a
setc dl;
clc;
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r11; loading flag
adcx rdi, r8
mov r10, 0x1eabfffeb153ffff ; moving imm to reg
xchg rdx, r14; x106, swapping with x238, which is currently in rdx
mulx r11, r8, r10; hix117, lox116<- x106 * 0x1eabfffeb153ffff
mov r10, rdx; preserving value of x106 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov byte [ rsp + 0x188 ], r14b; spilling byte x238 to mem
mov [ rsp + 0x190 ], r15; spilling x114 to mem
mulx r15, r14, [ rsi + 0x0 ]; hix8, lox7<- arg1[0] * arg2[5]
mov rdx, 0x0 ; moving imm to reg
adcx r9, rdx
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x198 ], r11; spilling x117 to mem
mov [ rsp + 0x1a0 ], rbp; spilling x59 to mem
mulx rbp, r11, [ rsi + 0x8 ]; hix74, lox73<- arg1[1] * arg2[3]
adox r13, [ rsp + 0x110 ]
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rdx; loading flag
adcx r14, [ rsp + 0x100 ]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x1a8 ], r13; spilling x63 to mem
mulx r13, r12, [ rsi + 0x8 ]; hix70, lox69<- arg1[1] * arg2[5]
setc dl;
mov [ rsp + 0x1b0 ], r13; spilling x70 to mem
movzx r13, byte [ rsp + 0xe0 ]; load byte memx84 to register64
clc;
mov [ rsp + 0x1b8 ], r8; spilling x116 to mem
mov r8, -0x1 ; moving imm to reg
adcx r13, r8; loading flag
adcx r11, [ rsp + 0xc8 ]
adcx rbp, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x40 ]
mov r13b, dl; preserving value of x28 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x1c0 ], r12; spilling x89 to mem
mulx r12, r8, [ rax + 0x8 ]; hix386, lox385<- arg1[5] * arg2[1]
adox rdi, r14
movzx rdx, r13b;
lea rdx, [ rdx + r15 ]
mov r15, rdx; preserving value of x29 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r13, r14, [ rax + 0x0 ]; hix388, lox387<- arg1[5] * arg2[0]
adox r9, r15
seto dl;
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x1b8 ]
mov r15, [ rsp + 0x1a0 ]; load m64 x59 to register64
mov [ rsp + 0x1c8 ], r14; spilling x387 to mem
setc r14b;
mov byte [ rsp + 0x1d0 ], dl; spilling byte x68 to mem
movzx rdx, byte [ rsp + 0x140 ]; load byte memx93 to register64
clc;
mov [ rsp + 0x1d8 ], r9; spilling x67 to mem
mov r9, -0x1 ; moving imm to reg
adcx rdx, r9; loading flag
adcx r15, [ rsp + 0xc0 ]
mov rdx, [ rsp + 0x198 ]; load m64 x117 to register64
adox rdx, [ rsp + 0x190 ]
seto r9b;
mov [ rsp + 0x1e0 ], rbp; spilling x87 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x180 ]
seto cl;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, r13
mov r13, rdx; preserving value of x122 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x1e8 ], r8; spilling x389 to mem
mulx r8, rbp, [ rax + 0x10 ]; hix384, lox383<- arg1[5] * arg2[2]
adox rbp, r12
adox r8, [ rsp + 0x70 ]
mov rdx, [ rsp + 0x170 ]; load m64 x61 to register64
adcx rdx, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0x1a8 ]
setc r12b;
clc;
mov [ rsp + 0x1f0 ], r8; spilling x393 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r15, rbx
adcx r13, rdx
setc bl;
clc;
adcx r15, [ rsp + 0x20 ]
mov rcx, 0x89f3fffcfffcfffd ; moving imm to reg
mov rdx, r15; x169 to rdx
mulx r8, r15, rcx; hi_, lox183<- x169 * 0x89f3fffcfffcfffd
mov r8, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r8; 0x64774b84f38512bf, swapping with x169, which is currently in rdx
mov [ rsp + 0x1f8 ], rbp; spilling x391 to mem
mulx rbp, rcx, r15; hix190, lox189<- x183 * 0x64774b84f38512bf
mov rdx, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x200 ], rbp; spilling x190 to mem
mov [ rsp + 0x208 ], rcx; spilling x189 to mem
mulx rcx, rbp, r15; hix196, lox195<- x183 * 0xb9feffffffffaaab
mov rdx, [ rsp - 0x28 ]; load m64 x379 to register64
adox rdx, [ rsp + 0x68 ]
adcx r13, [ rsp + 0xb0 ]
mov [ rsp + 0x210 ], rdx; spilling x395 to mem
mov rdx, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x218 ], r11; spilling x98 to mem
mov byte [ rsp + 0x220 ], bl; spilling byte x136 to mem
mulx rbx, r11, r15; hix192, lox191<- x183 * 0x6730d2a0f6b0f624
mov rdx, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x228 ], rbx; spilling x192 to mem
mov [ rsp + 0x230 ], r11; spilling x191 to mem
mulx r11, rbx, r15; hix194, lox193<- x183 * 0x1eabfffeb153ffff
movzx rdx, r14b;
mov [ rsp + 0x238 ], r11; spilling x194 to mem
mov r11, [ rsp + 0x1b0 ]; load m64 x70 to register64
lea rdx, [ rdx + r11 ]; r8/64 + m8
setc r11b;
clc;
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r14; loading flag
adcx rdi, [ rsp + 0x1e0 ]
mov r12, [ rsp + 0x1d8 ]; load m64 x67 to register64
adcx r12, [ rsp + 0x1c0 ]
mov r14, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, r15; x183, swapping with x91, which is currently in rdx
mov [ rsp + 0x240 ], r12; spilling x102 to mem
mov byte [ rsp + 0x248 ], r11b; spilling byte x172 to mem
mulx r11, r12, r14; hix186, lox185<- x183 * 0x1a0111ea397fe69a
mov r14, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r14; 0x64774b84f38512bf, swapping with x183, which is currently in rdx
mov [ rsp + 0x250 ], r11; spilling x186 to mem
mov [ rsp + 0x258 ], r12; spilling x185 to mem
mulx r12, r11, r10; hix113, lox112<- x106 * 0x64774b84f38512bf
movzx rdx, byte [ rsp + 0x1d0 ];
adcx rdx, r15
setc r15b;
clc;
mov [ rsp + 0x260 ], rdx; spilling x104 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rdx; loading flag
adcx r11, [ rsp + 0x178 ]
mov r9, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov rdx, r10; x106 to rdx
mov byte [ rsp + 0x268 ], r15b; spilling byte x105 to mem
mulx r15, r10, r9; hix111, lox110<- x106 * 0x4b1ba7b6434bacd7
adcx r10, r12
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r12, [ rax + 0x28 ]; hix147, lox146<- arg1[2] * arg2[5]
mov rdx, [ rsp - 0x30 ]; load m64 x380 to register64
adox rdx, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x168 ]
mov [ rsp + 0x270 ], rdx; spilling x397 to mem
seto dl;
mov [ rsp + 0x278 ], r9; spilling x147 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r8
seto bpl;
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, rcx
seto r8b;
dec r9; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, r9; loading flag
adox r13, rbx
mov rcx, [ rsp + 0x238 ]; load m64 x194 to register64
seto bpl;
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rbx; loading flag
adox rcx, [ rsp + 0x230 ]
setc r8b;
clc;
adcx r13, [ rsp - 0x48 ]
mov r9, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r13; x246, swapping with x398, which is currently in rdx
mov byte [ rsp + 0x280 ], r13b; spilling byte x398 to mem
mulx r13, rbx, r9; hi_, lox260<- x246 * 0x89f3fffcfffcfffd
setc r13b;
movzx r9, byte [ rsp + 0x220 ]; load byte memx136 to register64
clc;
mov byte [ rsp + 0x288 ], r8b; spilling byte x129 to mem
mov r8, -0x1 ; moving imm to reg
adcx r9, r8; loading flag
adcx r11, [ rsp + 0x218 ]
adcx r10, rdi
seto r9b;
movzx rdi, byte [ rsp + 0x248 ]; load byte memx172 to register64
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox rdi, r8; loading flag
adox r11, [ rsp + 0xf8 ]
adox r10, [ rsp + 0x108 ]
mov rdi, 0xb9feffffffffaaab ; moving imm to reg
xchg rdx, rbx; x260, swapping with x246, which is currently in rdx
mov byte [ rsp + 0x290 ], r13b; spilling byte x247 to mem
mulx r13, r8, rdi; hix273, lox272<- x260 * 0xb9feffffffffaaab
adcx r15, [ rsp + 0x240 ]
mov rdi, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x298 ], r8; spilling x272 to mem
mov [ rsp + 0x2a0 ], r13; spilling x273 to mem
mulx r13, r8, rdi; hix271, lox270<- x260 * 0x1eabfffeb153ffff
adox r15, [ rsp + 0x118 ]
mov rdi, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x2a8 ], r13; spilling x271 to mem
mov [ rsp + 0x2b0 ], r8; spilling x270 to mem
mulx r8, r13, rdi; hix269, lox268<- x260 * 0x6730d2a0f6b0f624
mov rdi, [ rsp + 0x208 ]; load m64 x189 to register64
mov [ rsp + 0x2b8 ], r8; spilling x269 to mem
setc r8b;
clc;
mov [ rsp + 0x2c0 ], r13; spilling x268 to mem
mov r13, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r13; loading flag
adcx rdi, [ rsp + 0x228 ]
mov r9, 0x4b1ba7b6434bacd7 ; moving imm to reg
xchg rdx, r14; x183, swapping with x260, which is currently in rdx
mov byte [ rsp + 0x2c8 ], r8b; spilling byte x142 to mem
mulx r8, r13, r9; hix188, lox187<- x183 * 0x4b1ba7b6434bacd7
adcx r13, [ rsp + 0x200 ]
setc dl;
clc;
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r11, rcx
adcx rdi, r10
adcx r13, r15
mov rbp, [ rsp - 0x10 ]; load m64 x230 to register64
seto cl;
movzx r10, byte [ rsp + 0x188 ]; load byte memx238 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
adox r10, r15; loading flag
adox rbp, [ rsp + 0x90 ]
setc r10b;
movzx r9, byte [ rsp + 0x138 ]; load byte memx165 to register64
clc;
adcx r9, r15; loading flag
adcx r12, [ rsp + 0xf0 ]
movzx r9, byte [ rsp + 0x288 ];
mov r15, [ rsp + 0x160 ]; load m64 x109 to register64
lea r9, [ r9 + r15 ]; r8/64 + m8
setc r15b;
mov byte [ rsp + 0x2d0 ], r10b; spilling byte x217 to mem
movzx r10, byte [ rsp + 0x2c8 ]; load byte memx142 to register64
clc;
mov [ rsp + 0x2d8 ], r8; spilling x188 to mem
mov r8, -0x1 ; moving imm to reg
adcx r10, r8; loading flag
adcx r9, [ rsp + 0x260 ]
mov r10, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r10; 0x64774b84f38512bf, swapping with x204, which is currently in rdx
mov byte [ rsp + 0x2e0 ], r10b; spilling byte x204 to mem
mulx r10, r8, r14; hix267, lox266<- x260 * 0x64774b84f38512bf
movzx rdx, r15b;
mov [ rsp + 0x2e8 ], r10; spilling x267 to mem
mov r10, [ rsp + 0x278 ]; load m64 x147 to register64
lea rdx, [ rdx + r10 ]; r8/64 + m8
mov r10, [ rsp + 0x2a0 ]; load m64 x273 to register64
seto r15b;
mov [ rsp + 0x2f0 ], rdx; spilling x168 to mem
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x2b0 ]
seto dl;
mov byte [ rsp + 0x2f8 ], r15b; spilling byte x240 to mem
movzx r15, byte [ rsp + 0x290 ]; load byte memx247 to register64
mov [ rsp + 0x300 ], r8; spilling x266 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r8; loading flag
adox r11, [ rsp + 0x60 ]
mov r15b, dl; preserving value of x275 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x308 ], r10; spilling x274 to mem
mulx r10, r8, [ rsi + 0x18 ]; hix224, lox223<- arg1[3] * arg2[5]
adox rdi, [ rsp + 0x158 ]
adox rbp, r13
setc dl;
clc;
adcx rbx, [ rsp + 0x298 ]
seto bl;
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r13; loading flag
adox r9, r12
mov rcx, [ rsp + 0x2c0 ]; load m64 x268 to register64
seto r12b;
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r13; loading flag
adox rcx, [ rsp + 0x2a8 ]
adcx r11, [ rsp + 0x308 ]
adcx rcx, rdi
seto r15b;
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0xd8 ]
mov rdi, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, rdi; 0x89f3fffcfffcfffd, swapping with x144, which is currently in rdx
mov [ rsp + 0x310 ], r10; spilling x224 to mem
mulx r10, r13, r11; hi_, lox337<- x323 * 0x89f3fffcfffcfffd
adox rcx, [ rsp + 0xd0 ]
mov r10, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov rdx, r14; x260 to rdx
mov byte [ rsp + 0x318 ], bl; spilling byte x253 to mem
mulx rbx, r14, r10; hix265, lox264<- x260 * 0x4b1ba7b6434bacd7
mov r10, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r13; x337, swapping with x260, which is currently in rdx
mov [ rsp + 0x320 ], rcx; spilling x325 to mem
mov [ rsp + 0x328 ], r8; spilling x223 to mem
mulx r8, rcx, r10; hix344, lox343<- x337 * 0x64774b84f38512bf
mov r10, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x330 ], r8; spilling x344 to mem
mov [ rsp + 0x338 ], rcx; spilling x343 to mem
mulx rcx, r8, r10; hix348, lox347<- x337 * 0x1eabfffeb153ffff
mov r10, [ rsp + 0x2b8 ]; load m64 x269 to register64
mov [ rsp + 0x340 ], rcx; spilling x348 to mem
setc cl;
clc;
mov [ rsp + 0x348 ], r9; spilling x179 to mem
mov r9, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r9; loading flag
adcx r10, [ rsp + 0x300 ]
adcx r14, [ rsp + 0x2e8 ]
mov r15, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x350 ], r14; spilling x280 to mem
mulx r14, r9, r15; hix350, lox349<- x337 * 0xb9feffffffffaaab
mov r15, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, r15; 0x1a0111ea397fe69a, swapping with x337, which is currently in rdx
mov [ rsp + 0x358 ], r9; spilling x349 to mem
mov byte [ rsp + 0x360 ], r12b; spilling byte x180 to mem
mulx r12, r9, r13; hix263, lox262<- x260 * 0x1a0111ea397fe69a
setc r13b;
clc;
adcx r8, r14
setc r14b;
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx rbx, r9
mov r13, [ rsp + 0x2d8 ]; load m64 x188 to register64
setc r9b;
movzx rdx, byte [ rsp + 0x2e0 ]; load byte memx204 to register64
clc;
mov [ rsp + 0x368 ], r12; spilling x263 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdx, r12; loading flag
adcx r13, [ rsp + 0x258 ]
mov rdx, [ rsp + 0x250 ];
mov r12, 0x0 ; moving imm to reg
adcx rdx, r12
clc;
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rbp, r10
movzx rcx, dil;
movzx r10, byte [ rsp + 0x268 ]; load byte memx105 to register64
lea rcx, [ rcx + r10 ]; r64+m8
setc r10b;
movzx rdi, byte [ rsp + 0x360 ]; load byte memx180 to register64
clc;
adcx rdi, r12; loading flag
adcx rcx, [ rsp + 0x2f0 ]
setc dil;
movzx r12, byte [ rsp + 0x2d0 ]; load byte memx217 to register64
clc;
mov byte [ rsp + 0x370 ], r9b; spilling byte x283 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx r13, [ rsp + 0x348 ]
mov r12, 0x6730d2a0f6b0f624 ; moving imm to reg
xchg rdx, r12; 0x6730d2a0f6b0f624, swapping with x207, which is currently in rdx
mov byte [ rsp + 0x378 ], dil; spilling byte x182 to mem
mulx rdi, r9, r15; hix346, lox345<- x337 * 0x6730d2a0f6b0f624
adcx r12, rcx
setc cl;
clc;
adcx r11, [ rsp + 0x358 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov byte [ rsp + 0x380 ], cl; spilling byte x221 to mem
mulx rcx, r11, [ rsi + 0x18 ]; hix226, lox225<- arg1[3] * arg2[4]
setc dl;
mov [ rsp + 0x388 ], rbx; spilling x282 to mem
movzx rbx, byte [ rsp + 0x2f8 ]; load byte memx240 to register64
clc;
mov [ rsp + 0x390 ], rdi; spilling x346 to mem
mov rdi, -0x1 ; moving imm to reg
adcx rbx, rdi; loading flag
adcx r11, [ rsp + 0x88 ]
adcx rcx, [ rsp + 0x328 ]
setc bl;
clc;
movzx rdx, dl
adcx rdx, rdi; loading flag
adcx r8, [ rsp + 0x320 ]
seto dl;
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x1c8 ]
mov rdi, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r8; x400, swapping with x326, which is currently in rdx
mov byte [ rsp + 0x398 ], bl; spilling byte x244 to mem
mov [ rsp + 0x3a0 ], r9; spilling x345 to mem
mulx r9, rbx, rdi; hi_, lox414<- x400 * 0x89f3fffcfffcfffd
mov r9, 0x4b1ba7b6434bacd7 ; moving imm to reg
xchg rdx, rbx; x414, swapping with x400, which is currently in rdx
mov byte [ rsp + 0x3a8 ], r14b; spilling byte x352 to mem
mulx r14, rdi, r9; hix419, lox418<- x414 * 0x4b1ba7b6434bacd7
mov r9, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x3b0 ], r14; spilling x419 to mem
mov [ rsp + 0x3b8 ], rdi; spilling x418 to mem
mulx rdi, r14, r9; hix425, lox424<- x414 * 0x1eabfffeb153ffff
setc r9b;
mov [ rsp + 0x3c0 ], rdi; spilling x425 to mem
movzx rdi, byte [ rsp + 0x318 ]; load byte memx253 to register64
clc;
mov [ rsp + 0x3c8 ], r14; spilling x424 to mem
mov r14, -0x1 ; moving imm to reg
adcx rdi, r14; loading flag
adcx r13, r11
seto dil;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r11; loading flag
adox rbp, [ rsp + 0xe8 ]
setc r8b;
clc;
movzx r10, r10b
adcx r10, r11; loading flag
adcx r13, [ rsp + 0x350 ]
setc r10b;
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx r12, rcx
mov rcx, 0x4b1ba7b6434bacd7 ; moving imm to reg
xchg rdx, rcx; 0x4b1ba7b6434bacd7, swapping with x414, which is currently in rdx
mulx r14, r8, r15; hix342, lox341<- x337 * 0x4b1ba7b6434bacd7
mov r11, [ rsp + 0x3a0 ]; load m64 x345 to register64
seto dl;
mov byte [ rsp + 0x3d0 ], dil; spilling byte x401 to mem
movzx rdi, byte [ rsp + 0x3a8 ]; load byte memx352 to register64
mov [ rsp + 0x3d8 ], r13; spilling x293 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rdi, r13; loading flag
adox r11, [ rsp + 0x340 ]
movzx rdi, byte [ rsp + 0x398 ];
mov r13, [ rsp + 0x310 ]; load m64 x224 to register64
lea rdi, [ rdi + r13 ]; r8/64 + m8
mov r13, [ rsp + 0x390 ]; load m64 x346 to register64
adox r13, [ rsp + 0x338 ]
adox r8, [ rsp + 0x330 ]
mov [ rsp + 0x3e0 ], r8; spilling x357 to mem
setc r8b;
clc;
mov [ rsp + 0x3e8 ], r13; spilling x355 to mem
mov r13, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r13; loading flag
adcx rbp, r11
mov r9, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, rcx; x414, swapping with x328, which is currently in rdx
mulx r13, r11, r9; hix421, lox420<- x414 * 0x64774b84f38512bf
mov r9, 0x1a0111ea397fe69a ; moving imm to reg
mov [ rsp + 0x3f0 ], rbp; spilling x366 to mem
mov [ rsp + 0x3f8 ], rdi; spilling x245 to mem
mulx rdi, rbp, r9; hix417, lox416<- x414 * 0x1a0111ea397fe69a
xchg rdx, r15; x337, swapping with x414, which is currently in rdx
mov [ rsp + 0x400 ], rdi; spilling x417 to mem
mov byte [ rsp + 0x408 ], r8b; spilling byte x257 to mem
mulx r8, rdi, r9; hix340, lox339<- x337 * 0x1a0111ea397fe69a
adox rdi, r14
mov rdx, 0xb9feffffffffaaab ; moving imm to reg
mulx r9, r14, r15; hix427, lox426<- x414 * 0xb9feffffffffaaab
setc dl;
clc;
adcx r14, rbx
seto r14b;
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rbx; loading flag
adox r12, [ rsp + 0x388 ]
seto r10b;
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x3c8 ]
mov rbx, 0x6730d2a0f6b0f624 ; moving imm to reg
xchg rdx, rbx; 0x6730d2a0f6b0f624, swapping with x367, which is currently in rdx
mov [ rsp + 0x410 ], r8; spilling x340 to mem
mov byte [ rsp + 0x418 ], r14b; spilling byte x360 to mem
mulx r14, r8, r15; hix423, lox422<- x414 * 0x6730d2a0f6b0f624
adox r8, [ rsp + 0x3c0 ]
adox r11, r14
adox r13, [ rsp + 0x3b8 ]
mov r15, [ rsp + 0x130 ]; load m64 x316 to register64
setc r14b;
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r15, [ rsp + 0x3d8 ]
movzx rcx, byte [ rsp + 0x380 ];
movzx rdx, byte [ rsp + 0x378 ]; load byte memx182 to register64
lea rcx, [ rcx + rdx ]; r64+m8
movzx rdx, byte [ rsp + 0x370 ];
mov [ rsp + 0x420 ], r13; spilling x434 to mem
mov r13, [ rsp + 0x368 ]; load m64 x263 to register64
lea rdx, [ rdx + r13 ]; r8/64 + m8
adox rbp, [ rsp + 0x3b0 ]
adcx r12, [ rsp + 0x128 ]
seto r13b;
mov [ rsp + 0x428 ], rbp; spilling x436 to mem
movzx rbp, byte [ rsp + 0x408 ]; load byte memx257 to register64
mov [ rsp + 0x430 ], r11; spilling x432 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbp, r11; loading flag
adox rcx, [ rsp + 0x3f8 ]
seto bpl;
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r11; loading flag
adox rcx, rdx
adcx rcx, [ rsp + 0x148 ]
setc r10b;
clc;
movzx rbx, bl
adcx rbx, r11; loading flag
adcx r15, [ rsp + 0x3e8 ]
movzx rbx, r13b;
mov rdx, [ rsp + 0x400 ]; load m64 x417 to register64
lea rbx, [ rbx + rdx ]; r8/64 + m8
adcx r12, [ rsp + 0x3e0 ]
adcx rdi, rcx
mov rdx, [ rsp + 0x1e8 ]; load m64 x389 to register64
setc r13b;
movzx rcx, byte [ rsp + 0x3d0 ]; load byte memx401 to register64
clc;
adcx rcx, r11; loading flag
adcx rdx, [ rsp + 0x3f0 ]
adcx r15, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x1f0 ]
adcx rdi, [ rsp + 0x210 ]
movzx rcx, bpl;
mov r11, 0x0 ; moving imm to reg
adox rcx, r11
dec r11; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, r11; loading flag
adox rdx, r9
seto r14b;
setc r9b;
mov rbp, 0xb9feffffffffaaab ; moving imm to reg
mov r11, rdx;
sub r11, rbp
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox r15, r8
adox r12, [ rsp + 0x430 ]
movzx r8, byte [ rsp + 0x280 ];
mov r14, [ rsp + 0x50 ]; load m64 x378 to register64
lea r8, [ r8 + r14 ]; r8/64 + m8
adox rdi, [ rsp + 0x420 ]
seto r14b;
mov rbp, 0x1eabfffeb153ffff ; moving imm to reg
mov [ rsp + 0x438 ], r11; spilling x454 to mem
mov r11, r15;
sbb r11, rbp
mov rbp, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x440 ], r11; spilling x456 to mem
mov r11, r12;
sbb r11, rbp
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rbp; loading flag
adox rcx, [ rsp + 0x150 ]
movzx r10, byte [ rsp + 0x418 ];
mov rbp, [ rsp + 0x410 ]; load m64 x340 to register64
lea r10, [ r10 + rbp ]; r8/64 + m8
seto bpl;
mov [ rsp + 0x448 ], r11; spilling x458 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r11; loading flag
adox rcx, r10
seto r13b;
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox rcx, [ rsp + 0x270 ]
movzx r9, r13b;
movzx rbp, bpl
lea r9, [ r9 + rbp ]
seto bpl;
mov r13, 0x64774b84f38512bf ; moving imm to reg
mov r11, rdi;
sbb r11, r13
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r10; loading flag
adox r9, r8
seto r8b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox rcx, [ rsp + 0x428 ]
adox rbx, r9
movzx r14, r8b;
adox r14, r10
mov r9, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov r8, rcx;
sbb r8, r9
mov r10, 0x1a0111ea397fe69a ; moving imm to reg
mov rbp, rbx;
sbb rbp, r10
mov r10, 0x0 ; moving imm to reg
sbb r14, r10
mov r14, [ rsp + 0x438 ];
cmovc r14, rdx; if CF, x468<- x441 (nzVar)
mov rdx, [ rsp + 0x448 ];
cmovc rdx, r12; if CF, x470<- x445 (nzVar)
mov r12, [ rsp + 0x440 ];
cmovc r12, r15; if CF, x469<- x443 (nzVar)
mov r15, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r15 + 0x8 ], r12; out1[1] = x469
cmovc rbp, rbx; if CF, x473<- x451 (nzVar)
cmovc r11, rdi; if CF, x471<- x447 (nzVar)
mov [ r15 + 0x0 ], r14; out1[0] = x468
cmovc r8, rcx; if CF, x472<- x449 (nzVar)
mov [ r15 + 0x20 ], r8; out1[4] = x472
mov [ r15 + 0x28 ], rbp; out1[5] = x473
mov [ r15 + 0x18 ], r11; out1[3] = x471
mov [ r15 + 0x10 ], rdx; out1[2] = x470
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 1232
ret
; cpu AMD Ryzen 7 PRO 7840U w/ Radeon 780M Graphics
; ratio 1.6010
; seed 0001774118158107 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; cyclegoal; 10000
; using counter; RDTSCP
; framePointer omit
; memoryConstraints none
; time needed: 324999 ms on 10000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 9077 ms
; number of used evaluations: 10000
; Ratio (time for assembling + measure)/(total runtime for 10000 evals): 0.027929316705589863
; number reverted permutation / tried permutation: 3415 / 4989 =68.451%
; number reverted decision / tried decision: 3175 / 5010 =63.373%
; validated in 38.156s
