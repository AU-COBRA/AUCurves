#!/usr/bin/env python3
"""Big-integer reference check of `test_leaves dump N` output (Python ints).
add: a+b mod p, sub: a-b mod p, mul: a*b*R^-1 mod p, square: a*a*R^-1 mod p, R = 2^384.
Every line is "op impl a b out" with 384-bit hex numbers (a, b < p are checked too)."""
import sys
p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
R = 2 ** 384
Rinv = pow(R, -1, p)
assert R % p == 0x15f65ec3fa80e4935c071a97a256ec6d77ce5853705257455f48985753c758baebf4000bc40c0002760900000002fffd
ref = {
    'add': lambda a, b: (a + b) % p,
    'sub': lambda a, b: (a - b) % p,
    'mul': lambda a, b: a * b * Rinv % p,
    'square': lambda a, b: a * a * Rinv % p,
}
cnt = {}; bad = 0
for line in sys.stdin:
    op, impl, a, b, out = line.split()
    a, b, out = int(a, 16), int(b, 16), int(out, 16)
    assert a < p and b < p, line
    k = (op, impl); cnt[k] = cnt.get(k, 0) + 1
    if out != ref[op](a, b):
        bad += 1
        if bad <= 10: print('WRONG', line.strip())
for (op, impl), c in sorted(cnt.items()):
    print(f'{op:7s} {impl:9s} {c} inputs checked')
print('bigint check:', 'ok' if bad == 0 else f'{bad} FAILURES')
sys.exit(bad != 0)
