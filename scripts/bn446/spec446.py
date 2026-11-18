# Python model of AUCurves' Gallina BN446 pairing spec:
#   PairingSpec.optimal_ate bn446_zmod_ops (zfp12_conj p) (zfp12_inv p xi) (zfp12_frob_p2 p xi)
#     (zfp12_pow p xi) (zfp2_conj p) (zfp2_mul_const p) bn446_params gamma1 gamma_y gamma1_p2
# at the FrobConstants gammas (gamma1_val, gamma_y_val, gamma1_p2_val bn446_params), i.e.
#   * Affine.affine_miller_aux over loop_abs: double_step, then add_step when Z.testbit n i,
#     with ZModTower.dtwist_make_line (c0.c0 = (Py,0), c1.c0 = -lam Px, c1.c1 = lam Tx - Ty);
#   * PairingSpecDefs.apply_corrections over optimal_ate_extras: pi_power 1 -> frobenius_Q
#     (conj(Qx) gamma1, conj(Qy) gamma_y), pi_power 2 -> frobenius2_Q (Qx gamma1_p2, Qy),
#     then the negate flag, then apply_correction (chord line, T update);
#   * conj if loop_neg; final_exp = final_exp_hard (final_exp_easy f) with
#     final_exp_easy f = frob_p2(t) t, t = conj(f) inv(f), inv = pow(p^12 - 2), frob_p2 = pow(p^2),
#     final_exp_hard = pow((p^4 - p^2 + 1) / r).
# Every parameter is read from the Rocq sources (AUCURVES, default: this checkout
#   Curves/BN446_params.v (curve_b, xi_re, xi_im, loop_abs, loop_neg, the optimal_ate_extras flags)
#   Examples/bn446_prime_certif.v (the seed u and the p, r polynomials).
import os, re
A = os.environ.get('AUCURVES', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
_P = open(os.path.join(A, 'src/Bedrock/Field/PairingTheory/Curves/BN446_params.v')).read()
_P = _P[_P.index('Definition bn446_params'):]   # the record, not the header comment
_P = re.sub(r'\(\*.*?\*\)', '', _P, flags=re.S)        # and no comments
_C = open(os.path.join(A, 'src/Bedrock/Field/Synthesis/Examples/bn446_prime_certif.v')).read()
def _field(name):
    m = re.search(r'\b' + name + r'\s*:=\s*([^;]+);', _P); assert m, name
    v = m.group(1).strip().rstrip('%Z')
    return v
CURVE_B = int(_field('curve_b')); XI = (int(_field('xi_re')), int(_field('xi_im')))
LOOP = int(_field('loop_abs'), 0); LOOP_NEG = _field('loop_neg') == 'true'
EXTRAS = [(int(a), b == 'true') for a, b in re.findall(r'pi_power\s*:=\s*(\d+)\s*;\s*negate\s*:=\s*(true|false)', _P)]
U = int(re.search(r'Definition bn446_u : Z := (0x[0-9a-fA-F]+)%Z', _C).group(1), 16)
assert '36 * u^4 + 36 * u^3 + 24 * u^2 + 6 * u + 1' in _C and '36 * bn446_u^4 + 36 * bn446_u^3 + 18 * bn446_u^2 + 6 * bn446_u + 1' in _C
p = 36*U**4 + 36*U**3 + 24*U**2 + 6*U + 1
r = 36*U**4 + 36*U**3 + 18*U**2 + 6*U + 1
Z2 = (0, 0)
def f2add(a, b): return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def f2sub(a, b): return ((a[0]-b[0]) % p, (a[1]-b[1]) % p)
def f2neg(a): return ((p-a[0]) % p, (p-a[1]) % p)
def f2mul(a, b): return ((a[0]*b[0] - a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
def f2sqr(a): return f2mul(a, a)
def f2inv(a):   # zfp2_inv: conj / norm, norm^-1 by Fermat
    n = (a[0]*a[0] + a[1]*a[1]) % p; ni = pow(n, p-2, p)
    return (a[0]*ni % p, (p - a[1]) % p * ni % p)
def f2mulfp(a, s): return (a[0]*s % p, a[1]*s % p)
def f2conj(a): return (a[0], (p - a[1]) % p)
def mulxi(a): return f2mul(a, XI)
def f6add(a, b): return tuple(f2add(x, y) for x, y in zip(a, b))
def f6sub(a, b): return tuple(f2sub(x, y) for x, y in zip(a, b))
def f6neg(a): return tuple(f2neg(x) for x in a)
def f6mul(a, b):   # ZModTower.zfp6_mul (Karatsuba, v^3 = xi)
    a0, a1, a2 = a; b0, b1, b2 = b
    t0, t1, t2 = f2mul(a0, b0), f2mul(a1, b1), f2mul(a2, b2)
    c0 = f2add(t0, mulxi(f2sub(f2sub(f2mul(f2add(a1, a2), f2add(b1, b2)), t1), t2)))
    c1 = f2add(f2sub(f2sub(f2mul(f2add(a0, a1), f2add(b0, b1)), t0), t1), mulxi(t2))
    c2 = f2sub(f2add(f2sub(f2mul(f2add(a0, a2), f2add(b0, b2)), t0), t1), t2)
    return (c0, c1, c2)
def f6mulv(a): return (mulxi(a[2]), a[0], a[1])
def f12mul(a, b):  # w^2 = v
    t0 = f6mul(a[0], b[0]); t1 = f6mul(a[1], b[1])
    return (f6add(t0, f6mulv(t1)), f6sub(f6sub(f6mul(f6add(a[0], a[1]), f6add(b[0], b[1])), t0), t1))
ONE12 = (((1, 0), Z2, Z2), (Z2, Z2, Z2))
def f12pow(a, e):  # zfp12_pow: square-and-multiply, LSB first
    acc = ONE12
    while e > 0:
        if e & 1: acc = f12mul(acc, a)
        a = f12mul(a, a); e >>= 1
    return acc
def f12conj(a): return (a[0], f6neg(a[1]))
def f2pow(a, e):   # FrobConstants.zfp2_pow_Z
    acc = (1, 0)
    while e > 0:
        if e & 1: acc = f2mul(acc, a)
        a = f2mul(a, a); e >>= 1
    return acc
GAMMA1 = f2pow(XI, (p - 1)//3); GAMMA_Y = f2pow(XI, (p - 1)//2); GAMMA1_P2 = f2pow(XI, (p*p - 1)//3)
def make_line(lam, Tx, Ty, Px, Py):   # ZModTower.dtwist_make_line
    return (((Py % p, 0), Z2, Z2), (f2neg(f2mulfp(lam, Px)), f2sub(f2mul(lam, Tx), Ty), Z2))
def dbl_slope(Tx, Ty):
    t = f2sqr(Tx); return f2mul(f2add(f2add(t, t), t), f2inv(f2add(Ty, Ty)))
def chord(Tx, Ty, Qx, Qy): return f2mul(f2sub(Qy, Ty), f2inv(f2sub(Qx, Tx)))
def double_step(f, Tx, Ty, Px, Py):
    lam = dbl_slope(Tx, Ty); f2_ = f12mul(f12mul(f, f), make_line(lam, Tx, Ty, Px, Py))
    nx = f2sub(f2sub(f2sqr(lam), Tx), Tx); return f2_, nx, f2sub(f2mul(lam, f2sub(Tx, nx)), Ty)
def add_step(f, Tx, Ty, Qx, Qy, Px, Py):
    lam = chord(Tx, Ty, Qx, Qy); f2_ = f12mul(f, make_line(lam, Tx, Ty, Px, Py))
    nx = f2sub(f2sub(f2sqr(lam), Tx), Qx); return f2_, nx, f2sub(f2mul(lam, f2sub(Tx, nx)), Ty)
def miller_aux(Px, Py, Qx, Qy):
    f, Tx, Ty = ONE12, Qx, Qy
    for i in range(LOOP.bit_length() - 2, -1, -1):   # Z.to_nat (Z.log2 n) iterations, i' = log2 n - 1 .. 0
        f, Tx, Ty = double_step(f, Tx, Ty, Px, Py)
        if (LOOP >> i) & 1: f, Tx, Ty = add_step(f, Tx, Ty, Qx, Qy, Px, Py)
    return f, Tx, Ty
def apply_corrections(f, Tx, Ty, Px, Py, Qx, Qy):
    for k, neg in EXTRAS:
        if k == 1: cx, cy = f2mul(f2conj(Qx), GAMMA1), f2mul(f2conj(Qy), GAMMA_Y)
        elif k == 2: cx, cy = f2mul(Qx, GAMMA1_P2), Qy
        else: cx, cy = Qx, Qy
        if neg: cy = f2neg(cy)
        f, Tx, Ty = add_step(f, Tx, Ty, cx, cy, Px, Py)   # apply_correction = add_step with corrected Q
    return f
def miller(P, Q):
    (Px, Py), (Qx, Qy) = P, Q
    f, Tx, Ty = miller_aux(Px, Py, Qx, Qy)
    f = apply_corrections(f, Tx, Ty, Px, Py, Qx, Qy)
    return f12conj(f) if LOOP_NEG else f
def final_exp(f):
    t = f12mul(f12conj(f), f12pow(f, p**12 - 2))
    t = f12mul(f12pow(t, p*p), t)
    return f12pow(t, (p**4 - p*p + 1)//r)
def optimal_ate(P, Q): return final_exp(miller(P, Q))
