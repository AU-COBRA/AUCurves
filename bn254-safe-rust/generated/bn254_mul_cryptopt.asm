SECTION .text
	GLOBAL fiat_bn254_mul
fiat_bn254_mul:
sub rsp, 264
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x18 ]; saving arg2[3] in rdx.
mulx r11, r10, [ rsi + 0x0 ]; hix6, lox5<- arg1[0] * arg2[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rcx, [ rax + 0x0 ]; hix12, lox11<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rax + 0x18 ]; hix101, lox100<- arg1[2] * arg2[3]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rsi + 0x8 ]; hix52, lox51<- arg1[1] * arg2[1]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rsi + 0x0 ]; hix8, lox7<- arg1[0] * arg2[2]
mov rdx, 0x87d20782e4866389 ; moving imm to reg
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, rcx; hi_, lox20<- x11 * 0x87d20782e4866389
mov rdi, 0x97816a916871ca8d ; moving imm to reg
mov rdx, r15; x20 to rdx
mov [ rsp - 0x48 ], rbx; spilling x101 to mem
mulx rbx, r15, rdi; hix27, lox26<- x20 * 0x97816a916871ca8d
mov rdi, 0x3c208c16d87cfd47 ; moving imm to reg
mov [ rsp - 0x40 ], r12; spilling x52 to mem
mov [ rsp - 0x38 ], r9; spilling x100 to mem
mulx r9, r12, rdi; hix29, lox28<- x20 * 0x3c208c16d87cfd47
mov rdi, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp - 0x30 ], rbp; spilling x51 to mem
mov [ rsp - 0x28 ], rbx; spilling x27 to mem
mulx rbx, rbp, [ rax + 0x10 ]; hix50, lox49<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x20 ], rbx; spilling x50 to mem
mov [ rsp - 0x18 ], rbp; spilling x49 to mem
mulx rbp, rbx, [ rsi + 0x18 ]; hix158, lox157<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x10 ], r15; spilling x26 to mem
mov [ rsp - 0x8 ], r9; spilling x29 to mem
mulx r9, r15, [ rax + 0x0 ]; hix160, lox159<- arg1[3] * arg2[0]
test al, al
adox r12, rcx
adcx rbx, r9
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx rcx, r12, [ rsi + 0x18 ]; hix156, lox155<- arg1[3] * arg2[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x0 ], rbx; spilling x161 to mem
mulx rbx, r9, [ rax + 0x8 ]; hix10, lox9<- arg1[0] * arg2[1]
adcx r12, rbp
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x8 ], r12; spilling x163 to mem
mulx r12, rbp, [ rax + 0x18 ]; hix154, lox153<- arg1[3] * arg2[3]
seto dl;
mov [ rsp + 0x10 ], r15; spilling x159 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r8
adox r13, rbx
adox r10, r14
adcx rbp, rcx
mov r8, 0x0 ; moving imm to reg
adox r11, r8
adc r12, 0x0; add CF to r0's alloc
mov r14, [ rsp - 0x10 ]; load m64 x26 to register64
xor rcx, rcx
adox r14, [ rsp - 0x8 ]
mov r8, 0xb85045b68181585d ; moving imm to reg
xchg rdx, rdi; x20, swapping with x38, which is currently in rdx
mulx rcx, rbx, r8; hix25, lox24<- x20 * 0xb85045b68181585d
adox rbx, [ rsp - 0x28 ]
mov r15, rdx; preserving value of x20 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x18 ], r12; spilling x167 to mem
mulx r12, r8, [ rsi + 0x10 ]; hix107, lox106<- arg1[2] * arg2[0]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x20 ], rbp; spilling x165 to mem
mov [ rsp + 0x28 ], r8; spilling x106 to mem
mulx r8, rbp, [ rsi + 0x10 ]; hix105, lox104<- arg1[2] * arg2[1]
mov rdx, 0x30644e72e131a029 ; moving imm to reg
mov [ rsp + 0x30 ], r11; spilling x19 to mem
mov [ rsp + 0x38 ], r10; spilling x17 to mem
mulx r10, r11, r15; hix23, lox22<- x20 * 0x30644e72e131a029
adox r11, rcx
adcx rbp, r12
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rcx, r15, [ rsi + 0x8 ]; hix54, lox53<- arg1[1] * arg2[0]
seto dl;
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp - 0x30 ]
mov r12b, dl; preserving value of x35 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x40 ], rbp; spilling x108 to mem
mov [ rsp + 0x48 ], rcx; spilling x55 to mem
mulx rcx, rbp, [ rax + 0x10 ]; hix103, lox102<- arg1[2] * arg2[2]
adcx rbp, r8
adcx rcx, [ rsp - 0x38 ]
movzx rdx, r12b;
lea rdx, [ rdx + r10 ]
mov r8, [ rsp - 0x18 ]; load m64 x49 to register64
adox r8, [ rsp - 0x40 ]
mov r10, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x50 ], rcx; spilling x112 to mem
mulx rcx, r12, [ rax + 0x18 ]; hix48, lox47<- arg1[1] * arg2[3]
adox r12, [ rsp - 0x20 ]
setc dl;
clc;
mov [ rsp + 0x58 ], rbp; spilling x110 to mem
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rbp; loading flag
adcx r9, r14
adcx rbx, r13
adcx r11, [ rsp + 0x38 ]
mov rdi, 0x0 ; moving imm to reg
adox rcx, rdi
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, r9
adox rbx, [ rsp + 0x48 ]
mov r14, 0x87d20782e4866389 ; moving imm to reg
xchg rdx, r14; 0x87d20782e4866389, swapping with x113, which is currently in rdx
mulx rdi, r9, r15; hi_, lox72<- x62 * 0x87d20782e4866389
adox r8, r11
adcx r10, [ rsp + 0x30 ]
adox r12, r10
mov rdi, 0xb85045b68181585d ; moving imm to reg
mov rdx, rdi; 0xb85045b68181585d to rdx
mulx r11, rdi, r9; hix77, lox76<- x72 * 0xb85045b68181585d
mov r10, 0x3c208c16d87cfd47 ; moving imm to reg
mov rdx, r9; x72 to rdx
mulx r13, r9, r10; hix81, lox80<- x72 * 0x3c208c16d87cfd47
setc bpl;
movzx rbp, bpl; spilling a flag to reg cause it has deps 
adox rbp, rcx; OF should have been spilled if it had deps, CF should have been spilled into rbp and into another reg, if it has had other deps than this one.
mov rcx, 0x97816a916871ca8d ; moving imm to reg
mov byte [ rsp + 0x60 ], r14b; spilling byte x113 to mem
mulx r14, r10, rcx; hix79, lox78<- x72 * 0x97816a916871ca8d
clc;
adcx r10, r13
mov r13, 0x30644e72e131a029 ; moving imm to reg
mov [ rsp + 0x68 ], rbp; spilling x70 to mem
mulx rbp, rcx, r13; hix75, lox74<- x72 * 0x30644e72e131a029
adcx rdi, r14
seto dl;
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r15
adox r10, rbx
adox rdi, r8
adcx rcx, r11
setc r9b;
clc;
adcx r10, [ rsp + 0x28 ]
adcx rdi, [ rsp + 0x40 ]
mov r15, 0x87d20782e4866389 ; moving imm to reg
xchg rdx, r15; 0x87d20782e4866389, swapping with x71, which is currently in rdx
mulx r8, rbx, r10; hi_, lox125<- x115 * 0x87d20782e4866389
mov r8, 0x3c208c16d87cfd47 ; moving imm to reg
mov rdx, rbx; x125 to rdx
mulx r11, rbx, r8; hix134, lox133<- x125 * 0x3c208c16d87cfd47
movzx r14, r9b;
lea r14, [ r14 + rbp ]
mov rbp, 0x97816a916871ca8d ; moving imm to reg
mulx r8, r9, rbp; hix132, lox131<- x125 * 0x97816a916871ca8d
mov rbp, 0xb85045b68181585d ; moving imm to reg
mov byte [ rsp + 0x70 ], r15b; spilling byte x71 to mem
mulx r15, r13, rbp; hix130, lox129<- x125 * 0xb85045b68181585d
adox rcx, r12
adcx rcx, [ rsp + 0x58 ]
adox r14, [ rsp + 0x68 ]
seto r12b;
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r11
adcx r14, [ rsp + 0x50 ]
movzx r11, byte [ rsp + 0x60 ];
mov rbp, [ rsp - 0x48 ]; load m64 x101 to register64
lea r11, [ r11 + rbp ]; r8/64 + m8
adox r13, r8
seto bpl;
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r10
adox r9, rdi
movzx rbx, r12b;
movzx r10, byte [ rsp + 0x70 ]; load byte memx71 to register64
lea rbx, [ rbx + r10 ]; r64+m8
mov r10, 0x30644e72e131a029 ; moving imm to reg
mulx r12, rdi, r10; hix128, lox127<- x125 * 0x30644e72e131a029
adcx r11, rbx
adox r13, rcx
setc dl;
clc;
movzx rbp, bpl
adcx rbp, r8; loading flag
adcx r15, rdi
mov rcx, 0x0 ; moving imm to reg
adcx r12, rcx
adox r15, r14
adox r12, r11
movzx r14, dl;
adox r14, rcx
xor rbp, rbp
adox r9, [ rsp + 0x10 ]
mov rcx, 0x87d20782e4866389 ; moving imm to reg
mov rdx, r9; x168 to rdx
mulx rbx, r9, rcx; hi_, lox178<- x168 * 0x87d20782e4866389
mov rbx, 0x3c208c16d87cfd47 ; moving imm to reg
xchg rdx, r9; x178, swapping with x168, which is currently in rdx
mulx r11, rdi, rbx; hix187, lox186<- x178 * 0x3c208c16d87cfd47
mov rbp, 0xb85045b68181585d ; moving imm to reg
mulx rbx, r8, rbp; hix183, lox182<- x178 * 0xb85045b68181585d
adox r13, [ rsp + 0x0 ]
adox r15, [ rsp + 0x8 ]
mulx rbp, rcx, r10; hix181, lox180<- x178 * 0x30644e72e131a029
mov r10, 0x97816a916871ca8d ; moving imm to reg
mov [ rsp + 0x78 ], r14; spilling x152 to mem
mov [ rsp + 0x80 ], r15; spilling x172 to mem
mulx r15, r14, r10; hix185, lox184<- x178 * 0x97816a916871ca8d
adcx r14, r11
adox r12, [ rsp + 0x20 ]
adcx r8, r15
adcx rcx, rbx
mov rdx, 0x0 ; moving imm to reg
adcx rbp, rdx
clc;
adcx rdi, r9
adcx r14, r13
adcx r8, [ rsp + 0x80 ]
mov rdi, [ rsp + 0x78 ]; load m64 x152 to register64
adox rdi, [ rsp + 0x18 ]
adcx rcx, r12
adcx rbp, rdi
seto r9b;
setc r11b;
mov rbx, 0x3c208c16d87cfd47 ; moving imm to reg
mov r13, r14;
sub r13, rbx
movzx r15, r11b;
movzx r9, r9b
lea r15, [ r15 + r9 ]
mov r12, r8;
sbb r12, r10
mov r9, 0xb85045b68181585d ; moving imm to reg
mov rdi, rcx;
sbb rdi, r9
mov r11, 0x30644e72e131a029 ; moving imm to reg
mov rdx, rbp;
sbb rdx, r11
mov r10, 0x0 ; moving imm to reg
sbb r15, r10
cmovc r13, r14; if CF, x216<- x197 (nzVar)
cmovc rdi, rcx; if CF, x218<- x201 (nzVar)
mov r15, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r15 + 0x0 ], r13; out1[0] = x216
cmovc rdx, rbp; if CF, x219<- x203 (nzVar)
mov [ r15 + 0x18 ], rdx; out1[3] = x219
cmovc r12, r8; if CF, x217<- x199 (nzVar)
mov [ r15 + 0x8 ], r12; out1[1] = x217
mov [ r15 + 0x10 ], rdi; out1[2] = x218
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 264
ret
; cpu AMD Ryzen 7 PRO 7840U w/ Radeon 780M Graphics
; ratio 1.9226
; seed 0001775728131548 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; cyclegoal; 10000
; using counter; RDTSCP
; framePointer omit
; memoryConstraints none
; time needed: 37482 ms on 5000 evaluations.
; Time spent for assembling and measuring (initial batch_size=94, initial num_batches=31): 2880 ms
; number of used evaluations: 5000
; Ratio (time for assembling + measure)/(total runtime for 5000 evals): 0.07683688170321755
; number reverted permutation / tried permutation: 1751 / 2450 =71.469%
; number reverted decision / tried decision: 1382 / 2549 =54.217%
; validated in 2.862s
