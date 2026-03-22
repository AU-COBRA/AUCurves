SECTION .text
	GLOBAL fiat_bls12_381_p_square
fiat_bls12_381_p_square:
sub rsp, 984
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, rax, [ rsi + 0x10 ]; hix76, lox75<- arg1[1] * arg1[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r11, [ rsi + 0x28 ]; hix382, lox381<- arg1[5] * arg1[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r8, rdx; hix228, lox227<- arg1[3]^2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, [ rsi + 0x0 ]; hix16, lox15<- arg1[0] * arg1[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r12, [ rsi + 0x20 ]; hix380, lox379<- arg1[5] * arg1[4]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, rdx; hix18, lox17<- arg1[0]^2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], r13; spilling x380 to mem
mulx r13, rdi, rdx; hix78, lox77<- arg1[1]^2
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x40 ], r12; spilling x379 to mem
mov [ rsp - 0x38 ], rcx; spilling x382 to mem
mulx rcx, r12, [ rsi + 0x0 ]; hix10, lox9<- arg1[0] * arg1[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x30 ], r9; spilling x228 to mem
mov [ rsp - 0x28 ], r8; spilling x227 to mem
mulx r8, r9, [ rsi + 0x18 ]; hix226, lox225<- arg1[3] * arg1[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp - 0x20 ], r8; spilling x226 to mem
mov [ rsp - 0x18 ], r9; spilling x225 to mem
mulx r9, r8, [ rsi + 0x8 ]; hix386, lox385<- arg1[5] * arg1[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp - 0x10 ], rcx; spilling x10 to mem
mov [ rsp - 0x8 ], r12; spilling x9 to mem
mulx r12, rcx, [ rsi + 0x8 ]; hix70, lox69<- arg1[1] * arg1[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x0 ], r12; spilling x70 to mem
mov [ rsp + 0x8 ], rcx; spilling x69 to mem
mulx rcx, r12, [ rsi + 0x10 ]; hix147, lox146<- arg1[2] * arg1[5]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x10 ], rcx; spilling x147 to mem
mov [ rsp + 0x18 ], r12; spilling x146 to mem
mulx r12, rcx, [ rsi + 0x0 ]; hix157, lox156<- arg1[2] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x20 ], rcx; spilling x156 to mem
mov [ rsp + 0x28 ], r12; spilling x157 to mem
mulx r12, rcx, rdx; hix153, lox152<- arg1[2]^2
mov rdx, 0x89f3fffcfffcfffd ; moving imm to reg
mov [ rsp + 0x30 ], r12; spilling x153 to mem
mov [ rsp + 0x38 ], rcx; spilling x152 to mem
mulx rcx, r12, r14; hi_, lox30<- x17 * 0x89f3fffcfffcfffd
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x40 ], r11; spilling x381 to mem
mulx r11, rcx, rdx; hix303, lox302<- arg1[4]^2
mov rdx, 0x64774b84f38512bf ; moving imm to reg
mov [ rsp + 0x48 ], r11; spilling x303 to mem
mov [ rsp + 0x50 ], r9; spilling x386 to mem
mulx r9, r11, r12; hix37, lox36<- x30 * 0x64774b84f38512bf
mov rdx, 0x1a0111ea397fe69a ; moving imm to reg
mov [ rsp + 0x58 ], r9; spilling x37 to mem
mov [ rsp + 0x60 ], r11; spilling x36 to mem
mulx r11, r9, r12; hix33, lox32<- x30 * 0x1a0111ea397fe69a
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x68 ], r11; spilling x33 to mem
mov [ rsp + 0x70 ], r9; spilling x32 to mem
mulx r9, r11, [ rsi + 0x28 ]; hix224, lox223<- arg1[3] * arg1[5]
mov rdx, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov [ rsp + 0x78 ], r9; spilling x224 to mem
mov [ rsp + 0x80 ], r11; spilling x223 to mem
mulx r11, r9, r12; hix35, lox34<- x30 * 0x4b1ba7b6434bacd7
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x88 ], r11; spilling x35 to mem
mov [ rsp + 0x90 ], r9; spilling x34 to mem
mulx r9, r11, [ rsi + 0x8 ]; hix80, lox79<- arg1[1] * arg1[0]
mov rdx, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x98 ], r11; spilling x79 to mem
mov [ rsp + 0xa0 ], r8; spilling x385 to mem
mulx r8, r11, r12; hix39, lox38<- x30 * 0x6730d2a0f6b0f624
test al, al
adox rdi, r9
adox rax, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r9, r13, [ rsi + 0x0 ]; hix311, lox310<- arg1[4] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xa8 ], r13; spilling x310 to mem
mov [ rsp + 0xb0 ], rax; spilling x83 to mem
mulx rax, r13, [ rsi + 0x20 ]; hix307, lox306<- arg1[4] * arg1[2]
adcx rbx, r15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0xb8 ], rdi; spilling x81 to mem
mulx rdi, r15, [ rsi + 0x20 ]; hix309, lox308<- arg1[4] * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xc0 ], r8; spilling x39 to mem
mov [ rsp + 0xc8 ], r11; spilling x38 to mem
mulx r11, r8, [ rsi + 0x0 ]; hix14, lox13<- arg1[0] * arg1[2]
adcx r8, rbp
setc dl;
clc;
adcx r15, r9
mov bpl, dl; preserving value of x22 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xd0 ], r15; spilling x312 to mem
mulx r15, r9, [ rsi + 0x8 ]; hix74, lox73<- arg1[1] * arg1[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xd8 ], r8; spilling x21 to mem
mov [ rsp + 0xe0 ], r15; spilling x74 to mem
mulx r15, r8, [ rsi + 0x20 ]; hix305, lox304<- arg1[4] * arg1[3]
adcx r13, rdi
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xe8 ], r13; spilling x314 to mem
mulx r13, rdi, [ rsi + 0x28 ]; hix388, lox387<- arg1[5] * arg1[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xf0 ], rdi; spilling x387 to mem
mov [ rsp + 0xf8 ], rbx; spilling x19 to mem
mulx rbx, rdi, [ rsi + 0x10 ]; hix384, lox383<- arg1[5] * arg1[2]
adcx r8, rax
adox r9, r10
adcx rcx, r15
seto dl;
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x40 ]
mov al, dl; preserving value of x86 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r15, [ rsi + 0x18 ]; hix12, lox11<- arg1[0] * arg1[3]
seto dl;
mov [ rsp + 0x100 ], rbx; spilling x393 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r11, r15
mov rbp, 0x1eabfffeb153ffff ; moving imm to reg
xchg rdx, rbp; 0x1eabfffeb153ffff, swapping with x394, which is currently in rdx
mulx rbx, r15, r12; hix41, lox40<- x30 * 0x1eabfffeb153ffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov byte [ rsp + 0x108 ], bpl; spilling byte x394 to mem
mov [ rsp + 0x110 ], rcx; spilling x318 to mem
mulx rcx, rbp, [ rsi + 0x18 ]; hix234, lox233<- arg1[3] * arg1[0]
mov rdx, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x118 ], rdi; spilling x391 to mem
mov [ rsp + 0x120 ], r13; spilling x389 to mem
mulx r13, rdi, r12; hix43, lox42<- x30 * 0xb9feffffffffaaab
adox r10, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x128 ], r8; spilling x316 to mem
mulx r8, r12, [ rsi + 0x0 ]; hix8, lox7<- arg1[0] * arg1[5]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x130 ], rbp; spilling x233 to mem
mov [ rsp + 0x138 ], r8; spilling x8 to mem
mulx r8, rbp, [ rsi + 0x8 ]; hix232, lox231<- arg1[3] * arg1[1]
setc dl;
clc;
adcx r15, r13
mov r13b, dl; preserving value of x319 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x140 ], r9; spilling x85 to mem
mov [ rsp + 0x148 ], r10; spilling x25 to mem
mulx r10, r9, [ rsi + 0x18 ]; hix230, lox229<- arg1[3] * arg1[2]
seto dl;
mov byte [ rsp + 0x150 ], r13b; spilling byte x319 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r14
adox r15, [ rsp + 0xf8 ]
setc dil;
clc;
movzx rdx, dl
adcx rdx, r13; loading flag
adcx r12, [ rsp - 0x10 ]
setc r14b;
clc;
adcx rbp, rcx
adcx r9, r8
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rcx, [ rsi + 0x8 ]; hix155, lox154<- arg1[2] * arg1[1]
seto dl;
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r13; loading flag
adox rbx, [ rsp + 0xc8 ]
mov rdi, [ rsp + 0xc0 ]; load m64 x39 to register64
adox rdi, [ rsp + 0x60 ]
mov r13, [ rsp - 0x30 ]; load m64 x228 to register64
adcx r13, [ rsp - 0x18 ]
mov [ rsp + 0x158 ], r13; spilling x241 to mem
mov r13b, dl; preserving value of x58 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x160 ], r10; spilling x239 to mem
mov [ rsp + 0x168 ], r9; spilling x237 to mem
mulx r9, r10, [ rsi + 0x20 ]; hix72, lox71<- arg1[1] * arg1[4]
setc dl;
clc;
adcx rcx, [ rsp + 0x28 ]
mov byte [ rsp + 0x170 ], dl; spilling byte x242 to mem
seto dl;
mov [ rsp + 0x178 ], rbp; spilling x235 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbp; loading flag
adox r10, [ rsp + 0xe0 ]
seto al;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x98 ]
mov rbp, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r15; x92, swapping with x49, which is currently in rdx
mov byte [ rsp + 0x180 ], r14b; spilling byte x28 to mem
mov [ rsp + 0x188 ], rcx; spilling x158 to mem
mulx rcx, r14, rbp; hi_, lox106<- x92 * 0x89f3fffcfffcfffd
mov rcx, 0x1eabfffeb153ffff ; moving imm to reg
xchg rdx, r14; x106, swapping with x92, which is currently in rdx
mov [ rsp + 0x190 ], r10; spilling x87 to mem
mulx r10, rbp, rcx; hix117, lox116<- x106 * 0x1eabfffeb153ffff
adcx r8, [ rsp + 0x38 ]
mov rcx, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x198 ], r8; spilling x160 to mem
mov [ rsp + 0x1a0 ], r10; spilling x117 to mem
mulx r10, r8, rcx; hix119, lox118<- x106 * 0xb9feffffffffaaab
seto cl;
mov [ rsp + 0x1a8 ], r12; spilling x27 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r10
mov r10, [ rsp + 0x90 ]; load m64 x34 to register64
setc r12b;
clc;
mov [ rsp + 0x1b0 ], rdi; spilling x48 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdi; loading flag
adcx r10, [ rsp + 0x58 ]
mov r15, rdx; preserving value of x106 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x1b8 ], r12b; spilling byte x161 to mem
mulx r12, rdi, [ rsi + 0x20 ]; hix301, lox300<- arg1[4] * arg1[5]
setc dl;
clc;
mov [ rsp + 0x1c0 ], r12; spilling x301 to mem
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r12; loading flag
adcx rbx, [ rsp + 0xd8 ]
seto r13b;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r12; loading flag
adox r9, [ rsp + 0x8 ]
mov rax, [ rsp + 0x0 ];
mov r12, 0x0 ; moving imm to reg
adox rax, r12
dec r12; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rcx, cl
adox rcx, r12; loading flag
adox rbx, [ rsp + 0xb8 ]
seto cl;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, r14
adox rbp, rbx
mov r8, [ rsp + 0x88 ]; load m64 x35 to register64
setc r14b;
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, rbx; loading flag
adcx r8, [ rsp + 0x70 ]
seto dl;
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, r12; loading flag
adox r11, [ rsp + 0x1b0 ]
adox r10, [ rsp + 0x148 ]
setc bl;
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx r11, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0x140 ]
adox r8, [ rsp + 0x1a8 ]
movzx r14, bl;
mov rcx, [ rsp + 0x68 ]; load m64 x33 to register64
lea r14, [ r14 + rcx ]; r8/64 + m8
adcx r8, [ rsp + 0x190 ]
mov rcx, 0x6730d2a0f6b0f624 ; moving imm to reg
xchg rdx, rcx; 0x6730d2a0f6b0f624, swapping with x134, which is currently in rdx
mulx r12, rbx, r15; hix115, lox114<- x106 * 0x6730d2a0f6b0f624
seto dl;
mov [ rsp + 0x1c8 ], r8; spilling x100 to mem
movzx r8, byte [ rsp + 0x150 ]; load byte memx319 to register64
mov [ rsp + 0x1d0 ], rax; spilling x91 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r8, rax; loading flag
adox rdi, [ rsp + 0x48 ]
setc r8b;
clc;
movzx r13, r13b
adcx r13, rax; loading flag
adcx rbx, [ rsp + 0x1a0 ]
seto r13b;
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, [ rsp + 0x20 ]
mov rax, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, rax; 0x89f3fffcfffcfffd, swapping with x66, which is currently in rdx
mov [ rsp + 0x1d8 ], rdi; spilling x320 to mem
mov [ rsp + 0x1e0 ], r9; spilling x89 to mem
mulx r9, rdi, rbp; hi_, lox183<- x169 * 0x89f3fffcfffcfffd
mov r9, 0x64774b84f38512bf ; moving imm to reg
mov rdx, r9; 0x64774b84f38512bf to rdx
mov byte [ rsp + 0x1e8 ], r8b; spilling byte x101 to mem
mulx r8, r9, rdi; hix190, lox189<- x183 * 0x64774b84f38512bf
movzx rdx, r13b;
mov [ rsp + 0x1f0 ], r8; spilling x190 to mem
mov r8, [ rsp + 0x1c0 ]; load m64 x301 to register64
lea rdx, [ rdx + r8 ]; r8/64 + m8
mov r8, 0x1eabfffeb153ffff ; moving imm to reg
xchg rdx, rdi; x183, swapping with x322, which is currently in rdx
mov [ rsp + 0x1f8 ], rdi; spilling x322 to mem
mulx rdi, r13, r8; hix194, lox193<- x183 * 0x1eabfffeb153ffff
mov r8, 0x64774b84f38512bf ; moving imm to reg
xchg rdx, r8; 0x64774b84f38512bf, swapping with x183, which is currently in rdx
mov [ rsp + 0x200 ], r9; spilling x189 to mem
mov [ rsp + 0x208 ], rdi; spilling x194 to mem
mulx rdi, r9, r15; hix113, lox112<- x106 * 0x64774b84f38512bf
adcx r9, r12
seto r12b;
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdx; loading flag
adox r11, rbx
adox r9, r10
mov rcx, 0xb9feffffffffaaab ; moving imm to reg
mov rdx, rcx; 0xb9feffffffffaaab to rdx
mulx r10, rcx, r8; hix196, lox195<- x183 * 0xb9feffffffffaaab
seto bl;
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdx; loading flag
adox r11, [ rsp + 0x188 ]
mov r12, 0x1a0111ea397fe69a ; moving imm to reg
mov rdx, r15; x106 to rdx
mov [ rsp + 0x210 ], r9; spilling x137 to mem
mulx r9, r15, r12; hix109, lox108<- x106 * 0x1a0111ea397fe69a
mov r12, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov [ rsp + 0x218 ], r9; spilling x109 to mem
mov [ rsp + 0x220 ], r11; spilling x171 to mem
mulx r11, r9, r12; hix111, lox110<- x106 * 0x4b1ba7b6434bacd7
movzx rdx, byte [ rsp + 0x180 ];
mov r12, [ rsp + 0x138 ]; load m64 x8 to register64
lea rdx, [ rdx + r12 ]; r8/64 + m8
adcx r9, rdi
mov r12, rdx; preserving value of x29 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x228 ], rcx; spilling x195 to mem
mulx rcx, rdi, [ rsi + 0x10 ]; hix149, lox148<- arg1[2] * arg1[4]
adcx r15, r11
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x230 ], rcx; spilling x149 to mem
mulx rcx, r11, [ rsi + 0x10 ]; hix151, lox150<- arg1[2] * arg1[3]
seto dl;
mov [ rsp + 0x238 ], r13; spilling x193 to mem
movzx r13, byte [ rsp + 0x1b8 ]; load byte memx161 to register64
mov [ rsp + 0x240 ], r10; spilling x196 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r13, r10; loading flag
adox r11, [ rsp + 0x30 ]
setc r13b;
clc;
movzx rax, al
adcx rax, r10; loading flag
adcx r12, r14
adox rdi, rcx
setc al;
movzx r14, byte [ rsp + 0x1e8 ]; load byte memx101 to register64
clc;
adcx r14, r10; loading flag
adcx r12, [ rsp + 0x1e0 ]
movzx rax, al
movzx r14, al;
adcx r14, [ rsp + 0x1d0 ]
setc cl;
clc;
movzx rbx, bl
adcx rbx, r10; loading flag
adcx r9, [ rsp + 0x1c8 ]
adcx r15, r12
mov rbx, [ rsp + 0x238 ]; load m64 x193 to register64
setc al;
clc;
adcx rbx, [ rsp + 0x240 ]
mov r12, 0x4b1ba7b6434bacd7 ; moving imm to reg
xchg rdx, r8; x183, swapping with x172, which is currently in rdx
mov [ rsp + 0x248 ], rdi; spilling x164 to mem
mulx rdi, r10, r12; hix188, lox187<- x183 * 0x4b1ba7b6434bacd7
mov r12, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x250 ], rdi; spilling x188 to mem
mov [ rsp + 0x258 ], r15; spilling x141 to mem
mulx r15, rdi, r12; hix192, lox191<- x183 * 0x6730d2a0f6b0f624
adcx rdi, [ rsp + 0x208 ]
adcx r15, [ rsp + 0x200 ]
adcx r10, [ rsp + 0x1f0 ]
seto r12b;
mov [ rsp + 0x260 ], r10; spilling x203 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x228 ]
adox rbx, [ rsp + 0x220 ]
movzx rbp, r13b;
mov r10, [ rsp + 0x218 ]; load m64 x109 to register64
lea rbp, [ rbp + r10 ]; r8/64 + m8
seto r10b;
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r13; loading flag
adox r14, rbp
setc al;
clc;
adcx rbx, [ rsp + 0x130 ]
mov rbp, [ rsp + 0x210 ]; load m64 x137 to register64
seto r13b;
mov byte [ rsp + 0x268 ], al; spilling byte x204 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rax; loading flag
adox rbp, [ rsp + 0x198 ]
movzx r8, r13b;
movzx rcx, cl
lea r8, [ r8 + rcx ]
adox r11, r9
seto cl;
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r9; loading flag
adox rbp, rdi
mov rdi, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, rdi; 0x89f3fffcfffcfffd, swapping with x183, which is currently in rdx
mulx r13, r10, rbx; hi_, lox260<- x246 * 0x89f3fffcfffcfffd
adcx rbp, [ rsp + 0x178 ]
mov r13, 0x1eabfffeb153ffff ; moving imm to reg
mov rdx, r13; 0x1eabfffeb153ffff to rdx
mulx rax, r13, r10; hix271, lox270<- x260 * 0x1eabfffeb153ffff
mov r9, [ rsp + 0x18 ]; load m64 x146 to register64
setc dl;
clc;
mov [ rsp + 0x270 ], r8; spilling x145 to mem
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r8; loading flag
adcx r9, [ rsp + 0x230 ]
mov r12, 0xb9feffffffffaaab ; moving imm to reg
xchg rdx, r12; 0xb9feffffffffaaab, swapping with x249, which is currently in rdx
mov [ rsp + 0x278 ], rax; spilling x271 to mem
mulx rax, r8, r10; hix273, lox272<- x260 * 0xb9feffffffffaaab
mov rdx, [ rsp + 0x248 ]; load m64 x164 to register64
mov [ rsp + 0x280 ], rbp; spilling x248 to mem
seto bpl;
mov byte [ rsp + 0x288 ], r12b; spilling byte x249 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r12; loading flag
adox rdx, [ rsp + 0x258 ]
setc cl;
clc;
movzx rbp, bpl
adcx rbp, r12; loading flag
adcx r11, r15
movzx r15, cl;
mov rbp, [ rsp + 0x10 ]; load m64 x147 to register64
lea r15, [ r15 + rbp ]; r8/64 + m8
mov rbp, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, rbp; 0x1a0111ea397fe69a, swapping with x177, which is currently in rdx
mulx r12, rcx, rdi; hix186, lox185<- x183 * 0x1a0111ea397fe69a
adox r9, r14
setc dil;
movzx r14, byte [ rsp + 0x268 ]; load byte memx204 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r14, rdx; loading flag
adcx rcx, [ rsp + 0x250 ]
setc r14b;
clc;
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx rbp, [ rsp + 0x260 ]
seto dil;
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rbx
adcx rcx, r9
setc r8b;
clc;
adcx r13, rax
setc bl;
movzx rax, byte [ rsp + 0x288 ]; load byte memx249 to register64
clc;
mov r9, -0x1 ; moving imm to reg
adcx rax, r9; loading flag
adcx r11, [ rsp + 0x168 ]
adox r13, [ rsp + 0x280 ]
mov rax, 0x6730d2a0f6b0f624 ; moving imm to reg
mov rdx, rax; 0x6730d2a0f6b0f624 to rdx
mulx r9, rax, r10; hix269, lox268<- x260 * 0x6730d2a0f6b0f624
adcx rbp, [ rsp + 0x160 ]
mov rdx, 0x64774b84f38512bf ; moving imm to reg
mov [ rsp + 0x290 ], rbp; spilling x252 to mem
mov [ rsp + 0x298 ], r11; spilling x250 to mem
mulx r11, rbp, r10; hix267, lox266<- x260 * 0x64774b84f38512bf
seto dl;
mov [ rsp + 0x2a0 ], rcx; spilling x218 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox rax, [ rsp + 0x278 ]
seto bl;
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, [ rsp + 0xa8 ]
setc cl;
clc;
mov [ rsp + 0x2a8 ], rax; spilling x276 to mem
mov rax, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rax; loading flag
adcx r15, [ rsp + 0x270 ]
seto dil;
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rax; loading flag
adox r9, rbp
movzx rbp, r14b;
lea rbp, [ rbp + r12 ]
mov r12, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r13; x323, swapping with x288, which is currently in rdx
mulx rbx, r14, r12; hi_, lox337<- x323 * 0x89f3fffcfffcfffd
mov rbx, 0xb9feffffffffaaab ; moving imm to reg
xchg rdx, rbx; 0xb9feffffffffaaab, swapping with x323, which is currently in rdx
mulx r12, rax, r14; hix350, lox349<- x337 * 0xb9feffffffffaaab
mov rdx, 0x64774b84f38512bf ; moving imm to reg
mov [ rsp + 0x2b0 ], r12; spilling x350 to mem
mov byte [ rsp + 0x2b8 ], dil; spilling byte x324 to mem
mulx rdi, r12, r14; hix344, lox343<- x337 * 0x64774b84f38512bf
mov rdx, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov [ rsp + 0x2c0 ], rdi; spilling x344 to mem
mov [ rsp + 0x2c8 ], r12; spilling x343 to mem
mulx r12, rdi, r10; hix265, lox264<- x260 * 0x4b1ba7b6434bacd7
setc dl;
clc;
adcx rax, rbx
adox rdi, r11
setc al;
clc;
mov r11, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r11; loading flag
adcx r15, rbp
mov r8, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, r8; 0x1a0111ea397fe69a, swapping with x182, which is currently in rdx
mulx rbp, rbx, r10; hix263, lox262<- x260 * 0x1a0111ea397fe69a
movzx r10, r8b;
mov r11, 0x0 ; moving imm to reg
adcx r10, r11
mov r8, [ rsp - 0x20 ]; load m64 x226 to register64
movzx r11, byte [ rsp + 0x170 ]; load byte memx242 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r11, rdx; loading flag
adcx r8, [ rsp + 0x80 ]
adox rbx, r12
mov r11, [ rsp + 0x78 ];
mov r12, 0x0 ; moving imm to reg
adcx r11, r12
mov r12, [ rsp + 0x2a0 ]; load m64 x218 to register64
clc;
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r12, [ rsp + 0x158 ]
mov rcx, [ rsp + 0x298 ]; load m64 x250 to register64
seto dl;
mov [ rsp + 0x2d0 ], rbx; spilling x282 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rbx; loading flag
adox rcx, [ rsp + 0x2a8 ]
adcx r8, r15
movzx r13, dl;
lea r13, [ r13 + rbp ]
adox r9, [ rsp + 0x290 ]
adcx r11, r10
adox rdi, r12
seto r15b;
movzx rbp, byte [ rsp + 0x2b8 ]; load byte memx324 to register64
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
adox rbp, r10; loading flag
adox rcx, [ rsp + 0xd0 ]
adox r9, [ rsp + 0xe8 ]
mov rbp, 0x1eabfffeb153ffff ; moving imm to reg
mov rdx, rbp; 0x1eabfffeb153ffff to rdx
mulx r12, rbp, r14; hix348, lox347<- x337 * 0x1eabfffeb153ffff
setc r10b;
clc;
adcx rbp, [ rsp + 0x2b0 ]
adox rdi, [ rsp + 0x128 ]
mov rbx, 0x6730d2a0f6b0f624 ; moving imm to reg
mov rdx, r14; x337 to rdx
mov byte [ rsp + 0x2d8 ], r10b; spilling byte x259 to mem
mulx r10, r14, rbx; hix346, lox345<- x337 * 0x6730d2a0f6b0f624
setc bl;
clc;
mov [ rsp + 0x2e0 ], r13; spilling x284 to mem
mov r13, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r13; loading flag
adcx rcx, rbp
mov rax, 0x1a0111ea397fe69a ; moving imm to reg
mulx r13, rbp, rax; hix340, lox339<- x337 * 0x1a0111ea397fe69a
setc al;
clc;
mov [ rsp + 0x2e8 ], r11; spilling x258 to mem
mov r11, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r11; loading flag
adcx r12, r14
adcx r10, [ rsp + 0x2c8 ]
mov rbx, 0x4b1ba7b6434bacd7 ; moving imm to reg
mulx r11, r14, rbx; hix342, lox341<- x337 * 0x4b1ba7b6434bacd7
adcx r14, [ rsp + 0x2c0 ]
adcx rbp, r11
setc dl;
clc;
adcx rcx, [ rsp + 0xf0 ]
mov r11, 0x89f3fffcfffcfffd ; moving imm to reg
xchg rdx, r11; 0x89f3fffcfffcfffd, swapping with x360, which is currently in rdx
mov [ rsp + 0x2f0 ], rbp; spilling x359 to mem
mulx rbp, rbx, rcx; hi_, lox414<- x400 * 0x89f3fffcfffcfffd
setc bpl;
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx r9, r12
seto al;
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r12; loading flag
adox r9, [ rsp + 0x120 ]
adcx r10, rdi
movzx rdi, r11b;
lea rdi, [ rdi + r13 ]
mov r13, 0x1eabfffeb153ffff ; moving imm to reg
mov rdx, r13; 0x1eabfffeb153ffff to rdx
mulx r11, r13, rbx; hix425, lox424<- x414 * 0x1eabfffeb153ffff
adox r10, [ rsp + 0x118 ]
mov rbp, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov rdx, rbx; x414 to rdx
mulx r12, rbx, rbp; hix419, lox418<- x414 * 0x4b1ba7b6434bacd7
seto bpl;
mov [ rsp + 0x2f8 ], r12; spilling x419 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, r12; loading flag
adox r8, [ rsp + 0x2d0 ]
mov r15, [ rsp + 0x2e8 ]; load m64 x258 to register64
adox r15, [ rsp + 0x2e0 ]
movzx r12, byte [ rsp + 0x2d8 ];
mov [ rsp + 0x300 ], rdi; spilling x361 to mem
mov rdi, 0x0 ; moving imm to reg
adox r12, rdi
dec rdi; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rax, al
adox rax, rdi; loading flag
adox r8, [ rsp + 0x110 ]
adox r15, [ rsp + 0x1d8 ]
mov rax, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x308 ], r15; spilling x333 to mem
mulx r15, rdi, rax; hix427, lox426<- x414 * 0xb9feffffffffaaab
adox r12, [ rsp + 0x1f8 ]
setc al;
clc;
adcx rdi, rcx
setc dil;
clc;
adcx r13, r15
mov rcx, 0x6730d2a0f6b0f624 ; moving imm to reg
mov [ rsp + 0x310 ], r12; spilling x335 to mem
mulx r12, r15, rcx; hix423, lox422<- x414 * 0x6730d2a0f6b0f624
adcx r15, r11
mov r11, rdx; preserving value of x414 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x318 ], bpl; spilling byte x405 to mem
mulx rbp, rcx, rdx; hix378, lox377<- arg1[5]^2
mov rdx, 0x64774b84f38512bf ; moving imm to reg
mov [ rsp + 0x320 ], rbp; spilling x378 to mem
mov [ rsp + 0x328 ], r14; spilling x357 to mem
mulx r14, rbp, r11; hix421, lox420<- x414 * 0x64774b84f38512bf
setc dl;
clc;
mov [ rsp + 0x330 ], r8; spilling x331 to mem
mov r8, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r8; loading flag
adcx r9, r13
seto dil;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r13; loading flag
adox r12, rbp
adox rbx, r14
adcx r15, r10
mov r10, [ rsp - 0x40 ]; load m64 x379 to register64
setc dl;
movzx rbp, byte [ rsp + 0x108 ]; load byte memx394 to register64
clc;
adcx rbp, r13; loading flag
adcx r10, [ rsp - 0x38 ]
adcx rcx, [ rsp - 0x48 ]
mov rbp, [ rsp + 0x330 ]; load m64 x331 to register64
seto r14b;
dec r8; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rax, al
adox rax, r8; loading flag
adox rbp, [ rsp + 0x328 ]
setc r13b;
movzx rax, byte [ rsp + 0x318 ]; load byte memx405 to register64
clc;
adcx rax, r8; loading flag
adcx rbp, [ rsp + 0x100 ]
mov rax, [ rsp + 0x308 ]; load m64 x333 to register64
adox rax, [ rsp + 0x2f0 ]
movzx r8, r13b;
mov byte [ rsp + 0x338 ], r14b; spilling byte x435 to mem
mov r14, [ rsp + 0x320 ]; load m64 x378 to register64
lea r8, [ r8 + r14 ]; r8/64 + m8
adcx r10, rax
seto r14b;
setc r13b;
mov rax, 0xb9feffffffffaaab ; moving imm to reg
mov [ rsp + 0x340 ], r8; spilling x399 to mem
mov r8, r9;
sub r8, rax
mov rax, [ rsp + 0x310 ]; load m64 x335 to register64
mov [ rsp + 0x348 ], r8; spilling x454 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r8; loading flag
adox rax, [ rsp + 0x300 ]
seto r14b;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r8; loading flag
adox rbp, r12
seto r12b;
mov rdx, 0x1eabfffeb153ffff ; moving imm to reg
mov r8, r15;
sbb r8, rdx
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdx; loading flag
adox r10, rbx
seto bl;
mov r12, 0x6730d2a0f6b0f624 ; moving imm to reg
mov rdx, rbp;
sbb rdx, r12
movzx r12, r14b;
movzx rdi, dil
lea r12, [ r12 + rdi ]
mov rdi, 0x1a0111ea397fe69a ; moving imm to reg
xchg rdx, r11; x414, swapping with x458, which is currently in rdx
mov [ rsp + 0x350 ], r11; spilling x458 to mem
mulx r11, r14, rdi; hix417, lox416<- x414 * 0x1a0111ea397fe69a
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox rax, rcx
setc cl;
movzx r13, byte [ rsp + 0x338 ]; load byte memx435 to register64
clc;
adcx r13, rdx; loading flag
adcx r14, [ rsp + 0x2f8 ]
mov r13, 0x0 ; moving imm to reg
adcx r11, r13
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx rax, r14
adox r12, [ rsp + 0x340 ]
adcx r11, r12
seto bl;
setc r14b;
add dl, cl; load to CF<-x459
mov rdx, 0x64774b84f38512bf ; moving imm to reg
mov r12, r10;
sbb r12, rdx
movzx rcx, r14b;
movzx rbx, bl
lea rcx, [ rcx + rbx ]
mov rbx, 0x4b1ba7b6434bacd7 ; moving imm to reg
mov r14, rax;
sbb r14, rbx
mov r13, r11;
sbb r13, rdi
mov rbx, 0x0 ; moving imm to reg
sbb rcx, rbx
cmovc r14, rax; if CF, x472<- x449 (nzVar)
mov rcx, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rcx + 0x20 ], r14; out1[4] = x472
cmovc r8, r15; if CF, x469<- x443 (nzVar)
mov [ rcx + 0x8 ], r8; out1[1] = x469
cmovc r12, r10; if CF, x471<- x447 (nzVar)
mov [ rcx + 0x18 ], r12; out1[3] = x471
mov r15, [ rsp + 0x350 ];
cmovc r15, rbp; if CF, x470<- x445 (nzVar)
mov rbp, [ rsp + 0x348 ];
cmovc rbp, r9; if CF, x468<- x441 (nzVar)
mov [ rcx + 0x0 ], rbp; out1[0] = x468
cmovc r13, r11; if CF, x473<- x451 (nzVar)
mov [ rcx + 0x28 ], r13; out1[5] = x473
mov [ rcx + 0x10 ], r15; out1[2] = x470
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 984
ret
; cpu AMD Ryzen 7 PRO 7840U w/ Radeon 780M Graphics
; ratio 1.5812
; seed 0001774118538926 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; cyclegoal; 10000
; using counter; RDTSCP
; framePointer omit
; memoryConstraints none
; time needed: 357512 ms on 10000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 10455 ms
; number of used evaluations: 10000
; Ratio (time for assembling + measure)/(total runtime for 10000 evals): 0.029243773635570274
; number reverted permutation / tried permutation: 3006 / 4990 =60.240%
; number reverted decision / tried decision: 2605 / 5009 =52.006%
; validated in 32.439s
