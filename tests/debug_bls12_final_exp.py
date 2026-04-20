#!/usr/bin/env python3
"""Debug BLS12-381 bls12_final_exp_hard_dsd.

KEY FACTS (from BLS12_Pairing.v):
  - bls12_final_exp_hard_dsd computes f^{3*h3} where h3=(p^4-p^2+1)/r
  - 3*h3 = 3 + (|u|^2-1+p^2)*(|u|+1)^2*(p-|u|)  [proved in FinalExpEquiv.v]
  - lit1=|u|/2=0x6900800000008000, lit2=|u|=0xd201000000010000

THE BUG (confirmed below):
  dsd_inline_exp_x_half initialises result=base (not ONE).
  Since bit63(lit1)=0, the loop gives (f^2)^{2^63+|u|/2} not (f^2)^{|u|/2}.
  Fix: initialise result=ONE before the loop.
"""
import hashlib

p   = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
r   = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
abs_u = 0xd201000000010000
h3  = (p**4-p**2+1)//r
order = p**4-p**2+1
assert (p**4-p**2+1)%r==0
assert (3*h3)%order == (3+(abs_u**2-1+p**2)*(abs_u+1)**2*(p-abs_u))%order

lit1 = abs_u//2   # 0x6900800000008000, bit63=0 <- problematic
lit2 = abs_u      # 0xd201000000010000, bit63=1 <- ok

def fp(a): return a%p
def fp2_add(a,b): return (fp(a[0]+b[0]),fp(a[1]+b[1]))
def fp2_sub(a,b): return (fp(a[0]-b[0]),fp(a[1]-b[1]))
def fp2_neg(a):   return (fp(-a[0]),fp(-a[1]))
def fp2_mul(a,b): return (fp(a[0]*b[0]-a[1]*b[1]),fp(a[0]*b[1]+a[1]*b[0]))
def fp2_sq(a):    return fp2_mul(a,a)
def fp2_conj(a):  return (a[0],fp(-a[1]))
def fp2_inv(a):
    n=pow(fp(a[0]*a[0]+a[1]*a[1]),p-2,p)
    return (fp(a[0]*n),fp(-a[1]*n))
def fp2_mul_xi(a): return (fp(a[0]-a[1]),fp(a[0]+a[1]))
FP2_0,FP2_1=(0,0),(1,0)
xi=(1,1)
def fp2_pow(a,n):
    if n==0: return FP2_1
    if n<0: return fp2_pow(fp2_inv(a),-n)
    rr,b=FP2_1,a
    while n:
        if n&1: rr=fp2_mul(rr,b)
        b=fp2_sq(b); n>>=1
    return rr

def fp6_mul(a,b):
    t0,t1,t2=fp2_mul(a[0],b[0]),fp2_mul(a[1],b[1]),fp2_mul(a[2],b[2])
    c0=fp2_add(t0,fp2_mul_xi(fp2_sub(fp2_mul(fp2_add(a[1],a[2]),fp2_add(b[1],b[2])),fp2_add(t1,t2))))
    c1=fp2_add(fp2_sub(fp2_mul(fp2_add(a[0],a[1]),fp2_add(b[0],b[1])),fp2_add(t0,t1)),fp2_mul_xi(t2))
    c2=fp2_add(fp2_sub(fp2_mul(fp2_add(a[0],a[2]),fp2_add(b[0],b[2])),fp2_add(t0,t2)),t1)
    return (c0,c1,c2)
def fp6_sq(a): return fp6_mul(a,a)
def fp6_mul_v(a): return (fp2_mul_xi(a[2]),a[0],a[1])
def fp6_neg(a): return tuple(fp2_neg(x) for x in a)
def fp6_add(a,b): return tuple(fp2_add(a[i],b[i]) for i in range(3))
def fp6_sub(a,b): return tuple(fp2_sub(a[i],b[i]) for i in range(3))
FP6_0,FP6_1=(FP2_0,FP2_0,FP2_0),(FP2_1,FP2_0,FP2_0)
def fp6_inv(a):
    t0=fp2_sub(fp2_mul(a[0],a[0]),fp2_mul_xi(fp2_mul(a[1],a[2])))
    t1=fp2_sub(fp2_mul_xi(fp2_mul(a[2],a[2])),fp2_mul(a[0],a[1]))
    t2=fp2_sub(fp2_mul(a[1],a[1]),fp2_mul(a[0],a[2]))
    f=fp2_inv(fp2_add(fp2_mul(a[0],t0),fp2_mul_xi(fp2_add(fp2_mul(a[2],t1),fp2_mul(a[1],t2)))))
    return (fp2_mul(t0,f),fp2_mul(t1,f),fp2_mul(t2,f))

def fp12_mul(a,b):
    t0,t1=fp6_mul(a[0],b[0]),fp6_mul(a[1],b[1])
    return (fp6_add(t0,fp6_mul_v(t1)),fp6_sub(fp6_sub(fp6_mul(fp6_add(a[0],a[1]),fp6_add(b[0],b[1])),t0),t1))
def fp12_sq(a):
    t0=fp6_mul(a[0],a[1])
    t1=fp6_mul(fp6_add(a[0],fp6_mul_v(a[1])),fp6_add(a[1],a[0]))
    return (fp6_sub(t1,fp6_add(t0,fp6_mul_v(t0))),fp6_add(t0,t0))
def fp12_conj(a): return (a[0],fp6_neg(a[1]))
def fp12_inv(a):
    t=fp6_inv(fp6_sub(fp6_sq(a[0]),fp6_mul_v(fp6_sq(a[1]))))
    return (fp6_mul(a[0],t),fp6_neg(fp6_mul(a[1],t)))
FP12_1=(FP6_1,FP6_0)
def fp12_pow(a,n):
    if n==0: return FP12_1
    if n<0: return fp12_pow(fp12_inv(a),-n)
    rr,b=FP12_1,a
    while n:
        if n&1: rr=fp12_mul(rr,b)
        b=fp12_sq(b); n>>=1
    return rr
def fp12_eq(a,b): return all(a[i][j][k]==b[i][j][k] for i in range(2) for j in range(3) for k in range(2))
def fp12_fp(a): return f"0x{a[0][0][0]:x}..."[:20]

# Frobenius
g1=fp2_pow(xi,(p-1)//6); g2=fp2_pow(xi,(p-1)//3); g3=fp2_pow(xi,2*(p-1)//3)
g2p2=fp2_pow(xi,(p**2-1)//6); g22=fp2_pow(xi,(p**2-1)//3); g24=fp2_pow(xi,2*(p**2-1)//3)

def fp6_frob(a): return (fp2_conj(a[0]),fp2_mul(fp2_conj(a[1]),g2),fp2_mul(fp2_conj(a[2]),g3))
def fp12_frob(a):
    fc0=fp6_frob(a[0]); fc1=tuple(fp2_mul(c,g1) for c in fp6_frob(a[1]))
    return (fc0,fc1)
def fp6_frob_p2(a): return (a[0],fp2_mul(a[1],g22),fp2_mul(a[2],g24))
def fp12_frob_p2(a):
    fc0=fp6_frob_p2(a[0]); fc1=tuple(fp2_mul(c,g2p2) for c in fp6_frob_p2(a[1]))
    return (fc0,fc1)

# pow loops
def pow_loop_base(base, c):
    """result=base, 63 steps using bits 62..0 of c. Effective exp: 2^63|c if bit63(c)=0."""
    result=base
    for i in range(62,-1,-1):
        result=fp12_sq(result)
        if (c>>i)&1: result=fp12_mul(result,base)
    return result

def pow_loop_one(base, c):
    """FIXED: result=ONE, 63 steps using bits 62..0 of c. Gives base^(bits62..0 of c)."""
    result=FP12_1
    for i in range(62,-1,-1):
        result=fp12_sq(result)
        if (c>>i)&1: result=fp12_mul(result,base)
    return result

# dsd helpers
def exp_x(base):      return fp12_conj(pow_loop_base(base, lit2))  # base^{-|u|}, correct (bit63=1)
def exp_x_half_bug(b): return fp12_conj(pow_loop_base(b, lit1))    # BUGGY: b^{-(2^63+|u|/2)}
def exp_x_half_fix(b): return fp12_conj(pow_loop_one(b, lit1))     # FIXED: b^{-|u|/2}

# build cyclotomic test element
def make_f():
    cs=[]
    for i in range(12):
        h=hashlib.sha256(b"bls12test"+i.to_bytes(1,'big')).digest()
        cs.append(int.from_bytes(h,'big')%p)
    raw=(((cs[0],cs[1]),(cs[2],cs[3]),(cs[4],cs[5])),
         ((cs[6],cs[7]),(cs[8],cs[9]),(cs[10],cs[11])))
    s1=fp12_mul(fp12_conj(raw),fp12_inv(raw))
    return fp12_mul(fp12_frob_p2(s1),s1)

print("Setting up...")
f=make_f()
assert fp12_eq(fp12_mul(f,fp12_conj(f)),FP12_1)
assert fp12_eq(fp12_frob(f),fp12_pow(f,p)),   "frob_p wrong"
assert fp12_eq(fp12_frob_p2(f),fp12_pow(f,p**2)), "frob_p2 wrong"
print("  frob_p and frob_p2 verified correct")

target = fp12_pow(f, 3*h3)
print(f"  target f^(3*h3) = {fp12_fp(target)}")
print()

# ---- BUGGY sim (exact Rust code) ----
def sim_buggy(f):
    t0=fp12_sq(f)                       # f^2
    t1=exp_x_half_bug(t0)               # (f^2)^{-(2^63+|u|/2)} WRONG
    t2=fp12_conj(f)
    t1=fp12_mul(t1,t2)
    result=pow_loop_base(t1,lit2); t2=fp12_conj(result)
    t1=fp12_mul(fp12_conj(t1),t2)
    result=pow_loop_base(t1,lit2); t2=fp12_conj(result)
    t1=fp12_mul(fp12_frob(t1),t2)
    t3=fp12_mul(f,t0)
    result=pow_loop_base(t1,lit2); t0=fp12_conj(result)
    result=pow_loop_base(t0,lit2); t2=fp12_conj(result)
    t0f=fp12_frob_p2(t1)
    t1c=fp12_mul(fp12_mul(fp12_conj(t1),t2),t0f)
    return fp12_mul(t3,t1c)

# ---- FIXED sim (result=ONE for half-exp) ----
def sim_fixed(f):
    t0=fp12_sq(f)                       # f^2
    t1=exp_x_half_fix(t0)               # (f^2)^{-|u|/2} = f^{-|u|} CORRECT
    t2=fp12_conj(f)
    t1=fp12_mul(t1,t2)                  # f^{-|u|-1}
    result=pow_loop_base(t1,lit2); t2=fp12_conj(result)
    t1=fp12_mul(fp12_conj(t1),t2)      # f^{(|u|+1)^2}
    result=pow_loop_base(t1,lit2); t2=fp12_conj(result)
    t1=fp12_mul(fp12_frob(t1),t2)      # f^{(p-|u|)(|u|+1)^2}
    t3=fp12_mul(f,t0)                   # f^3
    result=pow_loop_base(t1,lit2); t0=fp12_conj(result)  # f^{-|u|(p-|u|)(|u|+1)^2}
    result=pow_loop_base(t0,lit2); t2=fp12_conj(result)  # f^{|u|^2(p-|u|)(|u|+1)^2}
    t0f=fp12_frob_p2(t1)               # f^{p^2(p-|u|)(|u|+1)^2}
    t1c=fp12_mul(fp12_mul(fp12_conj(t1),t2),t0f)  # f^{(|u|^2-1+p^2)(p-|u|)(|u|+1)^2}
    return fp12_mul(t3,t1c)             # f^{3*h3}

print("Running simulations (each takes ~2 min)...")
buggy=sim_buggy(f)
print(f"  buggy done:  {fp12_fp(buggy)}")
fixed=sim_fixed(f)
print(f"  fixed done:  {fp12_fp(fixed)}")
print()

print("="*70)
print("RESULTS")
print("="*70)
print(f"  target (f^(3*h3)):  {fp12_fp(target)}")
print(f"  buggy output:       {fp12_fp(buggy)}")
print(f"  fixed output:       {fp12_fp(fixed)}")
print()
print(f"  buggy == target: {fp12_eq(buggy,target)}")
print(f"  fixed == target: {fp12_eq(fixed,target)}")
print()

# verify the individual loop step
t0=fp12_sq(f)
bl=pow_loop_base(t0,lit1)
fl=pow_loop_one(t0,lit1)
fu=fp12_pow(f,abs_u)
print("="*70)
print("BLOCK 1 DIVERGENCE PROOF")
print("="*70)
print(f"  t0 = f^2")
print(f"  pow_loop_base(t0,lit1) [buggy]:  {fp12_fp(bl)}")
print(f"  pow_loop_one (t0,lit1) [fixed]:  {fp12_fp(fl)}")
print(f"  f^|u|                  [direct]: {fp12_fp(fu)}")
print(f"  buggy == f^|u|: {fp12_eq(bl,fu)}  (should be False)")
print(f"  fixed == f^|u|: {fp12_eq(fl,fu)}  (should be True)")
print()
print("="*70)
print("BUG REPORT")
print("="*70)
print()
print("LOCATION: BLS12_Pairing.v, dsd_inline_exp_x_half (lines ~1117-1124)")
print("          bls12_safe_tower.rs Block 1 (lines 629-645)")
print()
print("BUG: The half-exponent pow loop (using lit1 = |u|/2 = 0x6900800000008000)")
print("     initialises 'result = base_var' (= f^2).")
print("     Since bit63(lit1) = 0, the loop adds a spurious implicit 2^63,")
print("     giving (f^2)^{2^63 + |u|/2} = f^{2^64 + |u|}  [WRONG]")
print("     instead of (f^2)^{|u|/2} = f^{|u|}            [CORRECT]")
print()
print("FIX: In dsd_inline_exp_x_half, remove the line:")
print("       cmd.call [] fp12_copy_name [expr.var \"result\"; expr.var base_var]")
print("     (or replace it with initialization to the identity element).")
print("     This makes result=ONE before the loop, so the loop computes")
print("     base^{bits_62..0_of_lit1} = (f^2)^{|u|/2} = f^{|u|} correctly.")
print()
print("     In the Rust (bls12_safe_tower.rs, line 630):")
print("       bls12_Fp12_felem_copy(&mut result, &t0);  // REMOVE THIS LINE")
print("     Instead, result should be initialized to the identity element.")
