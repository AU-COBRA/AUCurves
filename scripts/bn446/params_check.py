# Step (2): BN446 parameter checks for b = 257, xi = 1+9u (D-twist), seed u, p, r unchanged.
#  * p, r prime (Miller-Rabin, 40 rounds; Rocq has the certificates), p mod 4, #E(Fp) = r
#  * xi neither a square nor a cube in Fp2 (so v^3 - xi and w^6 - xi are irreducible)
#  * every small xi = a+bu (0 <= a, b <= 12): irreducible? b = 257 a D-twist?  (why 1+9u)
#  * G1 = (-1, 16) on y^2 = x^3 + 257, r G1 = O;  G2 on the D-twist y^2 = x^3 + 257/xi, r G2 = O
#  * the FrobConstants gammas at xi = 1+9u, their relations, psi(G2) = [p] G2 (so they belong to this twist)
#  * Montgomery limbs (R = 2^448) for the loaders; the old loaders decode to the old xi's powers (encoding check)
# usage: python3 params_check.py
import random, sys
from bnref import BN
def is_prime(n, k=40):
    if n < 2: return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29):
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    rnd = random.Random(n)
    for _ in range(k):
        a = rnd.randrange(2, n - 1); x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
s = BN('bn446_fixed'); p, r, u = s.p, s.r, s.u; t = p + 1 - r
print(f'u = {hex(u)}  (= 2^110 + 2^36 + 1: {u == 2**110 + 2**36 + 1})')
print(f'p = {p}\n  {p.bit_length()} bits, prime {is_prime(p)}, p mod 4 = {p % 4}, p mod 3 = {p % 3}, p mod 8 = {p % 8}')
print(f'r = {r}\n  {r.bit_length()} bits, prime {is_prime(r)};  t = 6u^2+1: {t == 6*u*u + 1};  6u+2 = {hex(6*u+2)}')
print(f'BN446_params.prime_p, scalar_r: see the Rocq check (Eval vm_compute) for equality with these')
xi = s.xi
sq = s.f2pow(xi, (p*p - 1)//2); cu = s.f2pow(xi, (p*p - 1)//3)
print(f'xi = {xi[0]}+{xi[1]}u: xi^((p^2-1)/2) = {"-1" if sq == (p-1, 0) else sq}  -> non-square {sq != (1, 0)}; '
      f'xi^((p^2-1)/3) != 1 -> non-cube {cu != (1, 0)}')
# Which small xi are irreducible and make b = 257 a D-twist?  The twist y^2 = x^3 + 257 c has r | #E'(Fp2) for a unique
# class of c in Fp2*/(Fp2*)^6.  Find it from xi = 1+9u by points (below), then compare classes: c ~ c'  <=>  (c/c')^((p^2-1)/6) = 1.
def sixth(z): return s.f2pow(z, (p*p - 1)//6) == (1, 0)
good = []
rows = []
for a in range(0, 13):
    for b in range(0, 13):
        if (a, b) == (0, 0): continue
        z = (a, b)
        irr = s.f2pow(z, (p*p-1)//2) != (1, 0) and s.f2pow(z, (p*p-1)//3) != (1, 0)
        dtw = sixth(s.f2mul(z, s.f2inv(xi)))   # 1/z ~ 1/xi  (xi = 1+9u, the D-twist class, checked by points below)
        mtw = sixth(s.f2mul(z, xi))            # z ~ 1/xi: b = 257 would be an M-twist over z
        rows.append((a, b, irr, dtw, mtw))
        if irr and dtw: good.append(f'{a}+{b}u')
print('small xi = a+bu (0<=a,b<=12) irreducible (non-square, non-cube) with b = 257 a D-twist over it:', ', '.join(good))
for a, b in [(1, 1), (9, 1), (2, 1), (3, 1), (1, 2), (2, 3), (1, 9)]:
    row = [x for x in rows if x[:2] == (a, b)][0]
    print(f'  xi = {a}+{b}u: irreducible {row[2]}, b=257 D-twist {row[3]}, b=257 M-twist {row[4]}')
# G1
G1 = (p - 1, 16)
assert (G1[1]**2 - G1[0]**3 - 257) % p == 0
print(f'G1 = (-1, 16): on y^2 = x^3 + 257 {(G1[1]**2 - G1[0]**3 - 257) % p == 0}; r G1 = O {s.mul(s.g1_add, G1, r) is None}; '
      f'#E(Fp) = p+1-t = r {p + 1 - t == r}')
# G2: first x = k + u (k = 1, 2, ...) with x^3 + 257/xi a square, times the cofactor 2p - r
G2 = s.g2_gen()
(x0, x1), (y0, y1) = G2
on = s.f2sub(s.f2mul(G2[1], G2[1]), s.f2add(s.f2mul(G2[0], s.f2mul(G2[0], G2[0])), s.b2)) == (0, 0)
print(f'b\' = 257/xi = ({s.b2[0]}, {s.b2[1]})')
print(f'G2 = ((x0, x1), (y0, y1)) =\n  x0 = {x0}\n  x1 = {x1}\n  y0 = {y0}\n  y1 = {y1}')
print(f'  on D-twist y^2 = x^3 + 257/xi {on}; r G2 = O {s.mul(s.g2_add, G2, r) is None}; G2 != O {G2 is not None}')
# M-twist control: same search on y^2 = x^3 + 257 xi
sM = BN('bn446_fixed'); sM.set_curve(257, 'M'); k = 1
while True:
    X = (k, 1); Y = sM.f2sqrt(sM.f2add(sM.f2mul(X, sM.f2mul(X, X)), sM.b2))
    if Y is not None: break
    k += 1
print(f'control: M-twist y^2 = x^3 + 257 xi: [r(2p-r)] Q = O for a point Q: {sM.mul(sM.g2_add, (X, Y), r*(2*p - r)) is None} (expected False)')
# gammas (FrobConstants)
G = dict(gamma1=(p-1)//3, gamma2=2*(p-1)//3, w_frob_c1=(p-1)//6, gamma1_p2=(p*p-1)//3, gamma2_p2=2*(p*p-1)//3,
         w_frob_p2_c1=(p*p-1)//6, gamma_y=(p-1)//2)
V = {k: s.f2pow(xi, e) for k, e in G.items()}
for k, v in V.items(): print(f'{k} = xi^{G[k]} = ({v[0]}, {v[1]})')
print('relations: gamma1 = w_frob_c1^2', V['gamma1'] == s.f2pow(V['w_frob_c1'], 2), '; gamma2 = gamma1^2', V['gamma2'] == s.f2pow(V['gamma1'], 2),
      '; gamma_y = w_frob_c1^3', V['gamma_y'] == s.f2pow(V['w_frob_c1'], 3),
      '; p^2 constants real', all(V[k][1] == 0 for k in ('gamma1_p2', 'gamma2_p2', 'w_frob_p2_c1')),
      '; xi^((p^2-1)/2) = -1', sq == (p-1, 0))
psi = (s.f2mul(s.f2conj(G2[0]), V['gamma1']), s.f2mul(s.f2conj(G2[1]), V['gamma_y']))
print('psi(G2) = (conj(x) gamma1, conj(y) gamma_y) = [p] G2:', psi == s.mul(s.g2_add, G2, p % r))
f2 = (s.f2mul(G2[0], V['gamma1_p2']), G2[1])
print('frobenius2_Q(G2) = (x gamma1_p2, y) = -[p^2] G2:', f2 == s.mul(s.g2_add, G2, (-p*p) % r))
# Montgomery limbs
R = 2**448
def limbs(z): m = z * R % p; return [(m >> (64*i)) & (2**64 - 1) for i in range(7)]
for k, v in V.items():
    print(f'{k} Montgomery limbs: re ' + ' '.join(f'0x{x:016X}' for x in limbs(v[0])) + ' | im ' + ' '.join(f'0x{x:016X}' for x in limbs(v[1])))
# encoding check against the current (xi = 2+3u) loaders of BN446_Pairing.v
old = BN('bn446'); oldg1p2 = old.f2pow(old.xi, (p*p-1)//3)
print('encoding check: old gamma1_p2 (xi = 2+3u) limbs[0] = 0x%016X (BN446_Pairing.v: 0x5557523555553909)' % limbs(oldg1p2[0])[0])
oldg1 = old.f2pow(old.xi, (p-1)//3)
print('encoding check: old gamma1 (xi = 2+3u) re limbs[0] = 0x%016X (BN446_Pairing.v: 0xA9707F06A2911FE5)' % limbs(oldg1[0])[0])
# pairing smoke test (the 60-case test is step 5)
e0 = s.pairing(G1, G2, kind='corrected', corrections='optimal')
a, c = 5, 7
e1 = s.pairing(s.mul(s.g1_add, G1, a), s.mul(s.g2_add, G2, c), kind='corrected', corrections='optimal')
print(f'reference pairing (D-twist line, corrections pi(Q), -pi^2(Q), exact final exponent): e(G1,G2) != 1 {e0 != s.ONE12}; '
      f'e^r = 1 {s.f12pow(e0, r) == s.ONE12}; e(5G1,7G2) = e^35 {e1 == s.f12pow(e0, 35)}')
