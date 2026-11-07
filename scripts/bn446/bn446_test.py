# BN446 bilinearity test, at b = 257, xi = 1+9u (AUCurves Curves/BN446_params.v).
#   * Python generates N cases: P = s G1, Q = t G2 (s = 1 or random, t = 1 or random), random a, b;
#     G1 = (-1, 16), G2 = the generator of BN446ParamsCheck.v.
#   * The Rust test bn446/rust/bilinear_dump.rs (copied to bn446-safe-rust/tests/) evaluates the crate's
#     `pairing` (tower::bn446_pairing_dsd_optimal), `miller_loop` (bn446_miller_loop_optimal) and the
#     control `pairing_dsd_uncorrected` (tower::bn446_pairing_dsd) on (P,Q), (aP,bQ), (aP,Q), (P,bQ), (-P,Q).
#   * Python checks, for the executable and for the spec model (spec446.py: PairingSpec.optimal_ate on
#     bn446_zmod_ops at the FrobConstants gammas, parameters read from the Rocq source):
#       e(aP,bQ) = e(P,Q)^(ab), e(aP,Q) = e^a, e(P,bQ) = e^b, e(P,Q) e(-P,Q) = 1, e != 1, e^r = 1,
#       and equality with the reference (bnref.py, 'bn446_fixed').
# usage: python3 bn446_test.py AUCURVES_DIR [N] [TMPDIR]
import os, sys, random, subprocess, time
from multiprocessing import Pool
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
A = sys.argv[1]; os.environ['AUCURVES'] = A
N = int(sys.argv[2]) if len(sys.argv) > 2 else 60
tmp = sys.argv[3] if len(sys.argv) > 3 else '/tmp'
from bnref import BN, from_c12
import spec446 as S
s = BN('bn446_fixed'); p, r = s.p, s.r
assert (S.p, S.r, S.XI, S.CURVE_B) == (p, r, s.xi, s.b) == (p, r, (1, 9), 257), 'spec model params != reference params'
R = 2**448
G1 = (p - 1, 16); G2 = s.g2_gen()
def m(x): return '%x' % (x * R % p)
def line(lab, P, Q): return '%s %s %s %s %s %s %s' % (lab, m(P[0]), m(P[1]), m(Q[0][0]), m(Q[0][1]), m(Q[1][0]), m(Q[1][1]))
rnd = random.Random(0xb446)
cases, lines = [], []
for i in range(N):
    sc = 1 if i % 3 == 0 else rnd.randrange(1, r); tc = 1 if i % 2 == 0 else rnd.randrange(1, r)
    a, bb = rnd.randrange(1, r), rnd.randrange(1, r)
    P = s.mul(s.g1_add, G1, sc); Q = s.mul(s.g2_add, G2, tc)
    aP = s.mul(s.g1_add, P, a); bQ = s.mul(s.g2_add, Q, bb)
    cases.append((P, Q, a, bb, aP, bQ))
    lines += [line('%d:e' % i, P, Q), line('%d:ab' % i, aP, bQ), line('%d:a' % i, aP, Q),
              line('%d:b' % i, P, bQ), line('%d:n' % i, s.g1_neg(P), Q)]
fin, fout = os.path.join(tmp, 'bn446-in.txt'), os.path.join(tmp, 'bn446-out.txt')
open(fin, 'w').write('\n'.join(lines) + '\n')
crate = os.path.join(A, 'bn446-safe-rust')
open(os.path.join(crate, 'tests', 'bilinear_dump.rs'), 'w').write(open(os.path.join(here, '..', 'rust', 'bilinear_dump.rs')).read())
t = time.time()
res = subprocess.run(['cargo', 'test', '--release', '-j2', '--test', 'bilinear_dump'], cwd=crate,
                     env=dict(os.environ, BN446_IN=fin, BN446_OUT=fout), capture_output=True, text=True)
assert res.returncode == 0, res.stderr[-3000:]
out = {}
for l in open(fout):
    w = l.split(); k = w.index('ml'); ku = w.index('u') if 'u' in w else len(w)
    out[w[0]] = (from_c12([int(x, 16) for x in w[2:k]]), from_c12([int(x, 16) for x in w[k+1:ku]]),
                 from_c12([int(x, 16) for x in w[ku+1:]]) if ku < len(w) else None)
print('bn446-safe-rust (b=257, xi=1+9u, D-twist): %d cases, %d executable evaluations in %.1fs' % (N, len(out), time.time() - t), flush=True)
def checks(e, eab, ea, eb, en, a, bb):
    return dict(ab=eab == s.f12pow(e, a * bb % r), a=ea == s.f12pow(e, a), b=eb == s.f12pow(e, bb),
                n=s.f12mul(e, en) == s.ONE12, nd=e != s.ONE12, ordr=s.f12pow(e, r) == s.ONE12)
def tally(rows):
    keys = ['ab', 'a', 'b', 'n', 'nd', 'ordr']; return {k: sum(x[k] for x in rows) for k in keys}
def show(name, c, n):
    print('BILINEARITY %s: e(aP,bQ)=e^(ab) %d/%d  e(aP,Q)=e^a %d/%d  e(P,bQ)=e^b %d/%d  e(P,Q)e(-P,Q)=1 %d/%d' % (
        name, c['ab'], n, c['a'], n, c['b'], n, c['n'], n))
    print('NONDEGENERATE %s: e(P,Q) != 1 %d/%d  e(P,Q)^r = 1 %d/%d' % (name, c['nd'], n, c['ordr'], n), flush=True)
# executable
rows = []
for i, (P, Q, a, bb, aP, bQ) in enumerate(cases):
    g = lambda k: out['%d:%s' % (i, k)][0]
    rows.append(checks(g('e'), g('ab'), g('a'), g('b'), g('n'), a, bb))
show('bn446-safe-rust pairing (tower::bn446_pairing_dsd_optimal)', tally(rows), N)
# control: the emitted uncorrected pairing
uc = sum(out['%d:ab' % i][2] == s.f12pow(out['%d:e' % i][2], a * bb % r) for i, (_, _, a, bb, _, _) in enumerate(cases))
print('CONTROL tower::bn446_pairing_dsd (uncorrected): e(aP,bQ)=e^(ab) %d/%d' % (uc, N), flush=True)
# spec model and reference (parallel)
def model(i):
    P, Q, a, bb, aP, bQ = cases[i]
    es = S.optimal_ate(P, Q); esab = S.optimal_ate(aP, bQ); er = s.pairing(P, Q)
    ms = S.miller(P, Q)
    return i, es, esab, er, ms
t = time.time()
with Pool(int(os.environ.get("BN446_PROCS", "4"))) as pool:
    res = pool.map(model, range(N))
print('spec model and reference: %d + %d + %d Python pairings in %.1fs' % (N, N, N, time.time() - t), flush=True)
srows, eq_ref, eq_spec, spec_ref, ml_eq = [], 0, 0, 0, 0
for i, es, esab, er, ms in res:
    P, Q, a, bb, aP, bQ = cases[i]
    e, ml, _ = out['%d:e' % i]
    srows.append(dict(ab=esab == s.f12pow(es, a * bb % r), a=True, b=True, n=True, nd=es != s.ONE12, ordr=s.f12pow(es, r) == s.ONE12))
    eq_ref += e == er; eq_spec += e == es; spec_ref += es == er; ml_eq += ml == ms
c = tally(srows)
print('BILINEARITY spec model (PairingSpec.optimal_ate, bn446_zmod_ops, FrobConstants): e(aP,bQ)=e^(ab) %d/%d' % (c['ab'], N))
print('NONDEGENERATE spec model: e(P,Q) != 1 %d/%d  e(P,Q)^r = 1 %d/%d' % (c['nd'], N, c['ordr'], N))
print('REFERENCE spec model = reference (bnref.py) %d/%d' % (spec_ref, N))
print('REFERENCE bn446-safe-rust pairing = reference %d/%d, = spec model %d/%d' % (eq_ref, N, eq_spec, N))
print('MODEL bn446-safe-rust miller_loop = spec model Miller loop + corrections (before final exp) %d/%d' % (ml_eq, N))
