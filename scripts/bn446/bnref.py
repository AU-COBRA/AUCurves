# Generic BN-curve reference (Python; with the 'bn446_fixed' entry and a per-curve b) for AUCurves' BN254/BN256/BN446 executable pairings:
# curve parameters from the seed u and xi, G1/G2 points, and the optimal-ate pairing with the
# D-twist line in AUCurves' tower basis (Fp2 = Fp[u]/(u^2+1), Fp6 = Fp2[v]/(v^3-xi),
# Fp12 = Fp6[w]/(w^2-v)), corrections through Q1 = pi(Q) and -Q2 = -pi^2(Q) = (Qx g1p2, Qy), and the
# exact final exponent (p^12-1)/r.  For BN254 this equals py_ecc's bn128 pairing (checked by
# check_bn254_vs_py_ecc below).  Also models AUCurves' executable variants:
#   miller(..., line='corrected')  : bn254_make_line_corrected layout (the right D-twist line)
#   miller(..., line='plain')      : <curve>_make_line layout of BN256/BN446 (and the stale BN254 one)
#   corrections in {None, 'optimal', 'spec'}  ('spec' = PairingSpec as written: -(-pi^2 Q))
import random
CURVES = {
    'bn254': dict(u=4965661367192848881, xi=(9, 1)),
    'bn256': dict(u=0x5A76AE9AEC588301, xi=(3, 1)),
    'bn446': dict(u=0x4000000000000000001000000001, xi=(2, 3)),
    # bn446 (this session's fix): b = 257 (Aranha et al. BN-446), xi = 1+9u, D-twist y^2 = x^3 + 257/xi
    'bn446_fixed': dict(u=0x4000000000000000001000000001, xi=(1, 9), b=257),
}
class BN:
    def set_curve(self, b, twist):
        # y^2 = x^3 + b, twist 'D' (b/xi) or 'M' (b xi)
        self.b = b
        self.b2 = self.f2mul((b, 0), self.f2inv(self.xi) if twist == 'D' else self.xi)
    def __init__(self, name):
        c = CURVES[name]; u = c['u']; self.name = name; self.u = u
        self.p = p = 36*u**4 + 36*u**3 + 24*u**2 + 6*u + 1
        self.r = 36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1
        self.xi = c['xi']; self.loop = 6*u + 2
        self.b = c.get('b', 3)
        self.b2 = self.f2mul((self.b, 0), self.f2inv(self.xi))   # D-twist: y^2 = x^3 + b/xi
        self.g1 = self.f2pow(self.xi, (p-1)//3); self.gy = self.f2pow(self.xi, (p-1)//2)
        self.g1p2 = self.f2pow(self.xi, (p*p-1)//3)
        self.ONE12 = (((1, 0), (0, 0), (0, 0)), ((0, 0), (0, 0), (0, 0)))
    # Fp2
    def f2add(s, a, b): return ((a[0]+b[0]) % s.p, (a[1]+b[1]) % s.p)
    def f2sub(s, a, b): return ((a[0]-b[0]) % s.p, (a[1]-b[1]) % s.p)
    def f2neg(s, a): return ((-a[0]) % s.p, (-a[1]) % s.p)
    def f2mul(s, a, b): return ((a[0]*b[0]-a[1]*b[1]) % s.p, (a[0]*b[1]+a[1]*b[0]) % s.p)
    def f2mulfp(s, a, k): return (a[0]*k % s.p, a[1]*k % s.p)
    def f2conj(s, a): return (a[0], (-a[1]) % s.p)
    def f2inv(s, a):
        n = pow((a[0]*a[0] + a[1]*a[1]) % s.p, -1, s.p); return (a[0]*n % s.p, (-a[1])*n % s.p)
    def f2pow(s, a, e):
        acc = (1, 0)
        while e:
            if e & 1: acc = s.f2mul(acc, a)
            a = s.f2mul(a, a); e >>= 1
        return acc
    def mulxi(s, a): return s.f2mul(a, s.xi)
    # Fp6, Fp12
    def f6add(s, a, b): return tuple(s.f2add(x, y) for x, y in zip(a, b))
    def f6sub(s, a, b): return tuple(s.f2sub(x, y) for x, y in zip(a, b))
    def f6neg(s, a): return tuple(s.f2neg(x) for x in a)
    def f6mul(s, a, b):
        a0, a1, a2 = a; b0, b1, b2 = b; m = s.f2mul
        t0, t1, t2 = m(a0, b0), m(a1, b1), m(a2, b2)
        c0 = s.f2add(t0, s.mulxi(s.f2sub(s.f2sub(m(s.f2add(a1, a2), s.f2add(b1, b2)), t1), t2)))
        c1 = s.f2add(s.f2sub(s.f2sub(m(s.f2add(a0, a1), s.f2add(b0, b1)), t0), t1), s.mulxi(t2))
        c2 = s.f2sub(s.f2add(s.f2sub(m(s.f2add(a0, a2), s.f2add(b0, b2)), t0), t1), t2)
        return (c0, c1, c2)
    def f6mulv(s, a): return (s.mulxi(a[2]), a[0], a[1])
    def f12mul(s, a, b):
        t0 = s.f6mul(a[0], b[0]); t1 = s.f6mul(a[1], b[1])
        return (s.f6add(t0, s.f6mulv(t1)), s.f6sub(s.f6sub(s.f6mul(s.f6add(a[0], a[1]), s.f6add(b[0], b[1])), t0), t1))
    def f12pow(s, a, e):
        acc = s.ONE12
        for i in range(e.bit_length() - 1, -1, -1):
            acc = s.f12mul(acc, acc)
            if (e >> i) & 1: acc = s.f12mul(acc, a)
        return acc
    def f12conj(s, a): return (a[0], s.f6neg(a[1]))
    # lines
    def line(s, kind, lam, Tx, Ty, Px, Py):
        Z = (0, 0); c = s.f2sub(s.f2mul(lam, Tx), Ty); m = s.f2neg(s.f2mulfp(lam, Px))
        if kind == 'corrected':   # Py + (-lam Px) w + (lam Tx - Ty) v w
            return (((Py, 0), Z, Z), (m, c, Z))
        if kind == 'plain':       # (lam Tx - Ty) + (-lam Px) v + Py v w
            return ((c, m, Z), (Z, (Py, 0), Z))
        raise ValueError(kind)
    def dbl_slope(s, Tx, Ty):
        t = s.f2mul(Tx, Tx); return s.f2mul(s.f2add(s.f2add(t, t), t), s.f2inv(s.f2add(Ty, Ty)))
    def chord(s, Tx, Ty, Qx, Qy): return s.f2mul(s.f2sub(Qy, Ty), s.f2inv(s.f2sub(Qx, Tx)))
    def add_line(s, kind, f, Tx, Ty, Px, Py, Qx, Qy):
        lam = s.chord(Tx, Ty, Qx, Qy); f = s.f12mul(f, s.line(kind, lam, Tx, Ty, Px, Py))
        nx = s.f2sub(s.f2sub(s.f2mul(lam, lam), Tx), Qx)
        return f, nx, s.f2sub(s.f2mul(lam, s.f2sub(Tx, nx)), Ty)
    def miller(s, P, Q, kind='corrected', corrections='optimal'):
        (Px, Py), (Qx, Qy) = P, Q
        f = s.ONE12; Tx, Ty = Qx, Qy
        for i in range(s.loop.bit_length() - 2, -1, -1):
            lam = s.dbl_slope(Tx, Ty)
            f = s.f12mul(s.f12mul(f, f), s.line(kind, lam, Tx, Ty, Px, Py))
            nx = s.f2sub(s.f2sub(s.f2mul(lam, lam), Tx), Tx)
            Tx, Ty = nx, s.f2sub(s.f2mul(lam, s.f2sub(Tx, nx)), Ty)
            if (s.loop >> i) & 1:
                f, Tx, Ty = s.add_line(kind, f, Tx, Ty, Px, Py, Qx, Qy)
        if corrections is None: return f
        Q1 = (s.f2mul(s.f2conj(Qx), s.g1), s.f2mul(s.f2conj(Qy), s.gy))
        f, Tx, Ty = s.add_line(kind, f, Tx, Ty, Px, Py, *Q1)
        Q2x, Q2y = s.f2mul(Qx, s.g1p2), Qy            # = -pi^2(Q)
        if corrections == 'spec': Q2y = s.f2neg(Q2y)  # PairingSpec: negate true on top
        f, _, _ = s.add_line(kind, f, Tx, Ty, Px, Py, Q2x, Q2y)
        return f
    def final_exp(s, f): return s.f12pow(f, (s.p**12 - 1) // s.r)
    def pairing(s, P, Q, **kw): return s.final_exp(s.miller(P, Q, **kw))
    # groups
    def fsqrt(s, a):
        assert s.p % 4 == 3
        x = pow(a, (s.p + 1)//4, s.p); return x if x*x % s.p == a % s.p else None
    def f2sqrt(s, a):
        # p = 3 mod 4: Adj-Rodriguez-Henriquez Algorithm 9
        p = s.p; a1 = s.f2pow(a, (p - 3)//4); alpha = s.f2mul(a1, s.f2mul(a1, a)); a0 = s.f2mul(s.f2conj(alpha), alpha)
        if a0 == (p - 1, 0): return None
        x0 = s.f2mul(a1, a)
        if alpha == (p - 1, 0): x = s.f2mul((0, 1), x0)
        else: x = s.f2mul(s.f2pow(s.f2add((1, 0), alpha), (p - 1)//2), x0)
        return x if s.f2mul(x, x) == a else None
    def g1_add(s, A, B):
        if A is None: return B
        if B is None: return A
        p = s.p; (x1, y1), (x2, y2) = A, B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            l = 3*x1*x1 * pow(2*y1, -1, p) % p
        else: l = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (l*l - x1 - x2) % p; return (x3, (l*(x1 - x3) - y1) % p)
    def g2_add(s, A, B):
        if A is None: return B
        if B is None: return A
        (x1, y1), (x2, y2) = A, B
        if x1 == x2:
            if s.f2add(y1, y2) == (0, 0): return None
            l = s.dbl_slope(x1, y1)
        else: l = s.chord(x1, y1, x2, y2)
        x3 = s.f2sub(s.f2sub(s.f2mul(l, l), x1), x2); return (x3, s.f2sub(s.f2mul(l, s.f2sub(x1, x3)), y1))
    def mul(s, add, P, k):
        R = None
        for i in range(k.bit_length() - 1, -1, -1):
            R = add(R, R)
            if (k >> i) & 1: R = add(R, P)
        return R
    def g1_gen(s):
        x = 1
        while True:
            y = s.fsqrt((x**3 + s.b) % s.p)
            if y is not None: return (x, min(y, s.p - y))
            x += 1
    def g2_gen(s):
        k = 1
        while True:
            x = (k, 1); y = s.f2sqrt(s.f2add(s.f2mul(x, s.f2mul(x, x)), s.b2))
            if y is not None:
                Q = s.mul(s.g2_add, (x, y), 2*s.p - s.r)   # #E'(Fp2) = r (2p - r)
                if Q is not None and s.mul(s.g2_add, Q, s.r) is None: return Q
            k += 1
    def g1_neg(s, P): return (P[0], (-P[1]) % s.p)

def to_c12(f): return [x for six in f for two in six for x in two]
def from_c12(c):
    t = [(c[2*i], c[2*i+1]) for i in range(6)]
    return ((t[0], t[1], t[2]), (t[3], t[4], t[5]))

def check_bn254_vs_py_ecc(n=3):
    from py_ecc.bn128 import bn128_pairing as bp, bn128_curve as bc
    import vs_py_ecc as m
    s = BN('bn254'); ok = 0
    for k in range(n):
        a, b = k + 1, 2*k + 3
        P = (int(bc.multiply(bc.G1, a)[0]), int(bc.multiply(bc.G1, a)[1]))
        Q2 = bc.multiply(bc.G2, b); Q = (tuple(int(c) for c in Q2[0].coeffs), tuple(int(c) for c in Q2[1].coeffs))
        ok += m.to_poly(to_c12(s.pairing(P, Q))) == [int(x) % s.p for x in bp.pairing(Q2, bc.multiply(bc.G1, a)).coeffs]
    return ok, n
