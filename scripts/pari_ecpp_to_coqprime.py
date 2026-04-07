#!/usr/bin/env python3
"""Convert a PARI ECPP certificate to a coqprime Ell_certif chain.

Usage:
    1. Generate ECPP cert with PARI:
        from cypari2 import Pari
        pari = Pari()
        pari.allocatemem(1 << 30)
        pari.default('parisizemax', 1 << 32)
        cert = pari.primecert(p, 0)  # flag=0 for ECPP
        with open('cert.txt', 'w') as f:
            f.write(str(cert))

    2. Convert to coqprime:
        python3 pari_ecpp_to_coqprime.py cert.txt <name> <hex_or_dec> -o cert.v

    Example:
        python3 pari_ecpp_to_coqprime.py bw6_761.txt bw6_761 0x122e8... -o bw6_761_certif.v

PARI ECPP cert format: list of [N, t, s, A, [x, y]] entries where:
    - N is the prime being proven
    - t is the trace
    - s is a divisor of m = N+1-t (curve order)
    - A is the curve parameter (Weierstrass: y² = x³ + Ax + B)
    - [x, y] is a point on E(F_N)
    - The next prime in the chain is q = m/s

Coqprime Ell_certif format: Ell_certif N S l A B x y where:
    - N, A, x, y same as PARI
    - S = s (the cofactor)
    - l = ((q, 1)::nil) where q is the next prime
    - B = (y² - x³ - Ax) mod N (computed from the on-curve equation)

The trailing prime (small enough that PARI stopped recursing) gets a
Pocklington chain (Pock_certif) recursively until reaching builtin primes.
"""

import sys
import argparse
from math import gcd
from sympy import factorint


# ----- PARI cert parser -----

def parse_pari(s):
    """Parse PARI's nested list format into Python lists/ints."""
    s = s.strip()
    pos = [0]

    def parse_one():
        while pos[0] < len(s) and s[pos[0]] in ' ,':
            pos[0] += 1
        c = s[pos[0]]
        if c == '[':
            pos[0] += 1
            result = []
            while pos[0] < len(s) and s[pos[0]] != ']':
                result.append(parse_one())
                while pos[0] < len(s) and s[pos[0]] in ' ,':
                    pos[0] += 1
            pos[0] += 1
            return result
        else:
            start = pos[0]
            if s[pos[0]] == '-':
                pos[0] += 1
            while pos[0] < len(s) and s[pos[0]].isdigit():
                pos[0] += 1
            return int(s[start:pos[0]])

    return parse_one()


# ----- Pocklington chain for trailing small prime -----

KNOWN_BUILTIN = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}


def find_witness(p, factors_of_pm1):
    """Find a Pocklington witness a for prime p."""
    pm1 = p - 1
    for a in [2, 3, 5, 6, 7, 10, 11, 12, 13, 17, 19, 21, 23]:
        if a >= p:
            break
        if pow(a, pm1, p) != 1:
            continue
        ok = True
        for q in factors_of_pm1:
            if gcd(pow(a, pm1 // q, p) - 1, p) != 1:
                ok = False
                break
        if ok:
            return a
    raise RuntimeError(f"No Pocklington witness found for {p}")


def build_pocklington_chain(start_p):
    """Build a Pocklington chain for a small prime, recursively."""
    pock_certs = []
    visited = set()
    builtin_used = set()

    def build(p):
        if p in visited:
            return
        if p in KNOWN_BUILTIN:
            builtin_used.add(p)
            return
        visited.add(p)
        factors = factorint(p - 1)
        for q in factors:
            build(q)
        w = find_witness(p, factors.keys())
        fl = "::".join(f"({q}, {e})" for q, e in sorted(factors.items())) + "::nil"
        pock_certs.append(f"Pock_certif {p} {w} ({fl}) 1")

    build(start_p)
    pock_certs.reverse()  # parents before children in the cert list

    proof_certs = [f"Proof_certif {p} prime{p}"
                   for p in sorted(builtin_used, reverse=True)]
    return pock_certs, proof_certs


# ----- Main conversion -----

def convert(cert_path, name, hexval, output):
    with open(cert_path) as f:
        raw = f.read()

    entries = parse_pari(raw)
    print(f"Parsed {len(entries)} ECPP entries", file=sys.stderr)

    # Build Coq Ell_certif strings for each ECPP step
    coq_ell = []
    for i, entry in enumerate(entries):
        N, t, s, A, P = entry
        x, y = P
        m = N + 1 - t
        if m % s != 0:
            raise RuntimeError(f"Step {i}: s={s} does not divide m=N+1-t")
        next_p = m // s
        B = (y * y - x * x * x - A * x) % N
        # Sanity check
        assert (y * y - x * x * x - A * x - B) % N == 0
        coq_ell.append(
            f"Ell_certif {N} {s} (({next_p}, 1)::nil) ({A}) ({B}) ({x}) ({y})"
        )

    # The final next_p needs its own primality cert via Pocklington
    final_entry = entries[-1]
    final_p = (final_entry[0] + 1 - final_entry[1]) // final_entry[2]
    print(f"Trailing prime: {final_p} ({final_p.bit_length()}b)", file=sys.stderr)

    pock_certs, proof_certs = build_pocklington_chain(final_p)
    print(f"  + {len(pock_certs)} Pock_certifs, {len(proof_certs)} Proof_certifs",
          file=sys.stderr)

    # Build the main certificate (first ECPP entry)
    e0 = entries[0]
    N0, t0, s0, A0, P0 = e0
    x0, y0 = P0
    m0 = N0 + 1 - t0
    next0 = m0 // s0
    B0 = (y0 * y0 - x0 * x0 * x0 - A0 * x0) % N0

    main = (f"(Ell_certif {name}_prime_pos {s0} (({next0}, 1)::nil) "
            f"({A0}) ({B0}) ({x0}) ({y0}))")

    # All sub-certs: ECPP[1:] + Pock chain + Proof leaves
    sub_lines = coq_ell[1:] + pock_certs + proof_certs
    subs = ";\n    ".join(sub_lines)

    coq = (
        "Require Import Coq.ZArith.ZArith.\n"
        "Require Import Coq.ZArith.Znumtheory.\n"
        "From Coqprime Require Import PocklingtonRefl.\n\n"
        "Local Open Scope positive_scope.\n\n"
        f"Definition {name}_modulus : Z :=\n"
        f"  Eval vm_compute in ({hexval})%Z.\n\n"
        f"Definition {name}_prime_pos : positive :=\n"
        f"  Eval vm_compute in (Z.to_pos {hexval})%Z.\n\n"
        f"Lemma {name}_modulus_pos : {name}_modulus = Z.pos {name}_prime_pos.\n"
        "Proof. vm_compute. reflexivity. Qed.\n\n"
        f"Lemma prime_{name} : prime {name}_modulus.\n"
        "Proof.\n"
        f"  rewrite {name}_modulus_pos.\n"
        f"  apply (Pocklington_refl\n    {main}\n    [\n    {subs}\n    ] _).\n"
        "  native_cast_no_check (refl_equal true).\n"
        "Qed.\n"
    )

    if output:
        with open(output, 'w') as f:
            f.write(coq)
        print(f"Wrote {len(sub_lines)+1} cert entries, {len(coq)} bytes to {output}",
              file=sys.stderr)
    else:
        print(coq)


def main():
    parser = argparse.ArgumentParser(
        description="Convert PARI ECPP certificate to coqprime Ell_certif chain"
    )
    parser.add_argument("cert_file", help="PARI ECPP certificate file")
    parser.add_argument("name", help="Name for Coq definitions (e.g., bw6_761)")
    parser.add_argument("hex", help="Prime as Coq expression (e.g., 0x...)")
    parser.add_argument("-o", "--output", help="Output .v file")
    args = parser.parse_args()

    convert(args.cert_file, args.name, args.hex, args.output)


if __name__ == "__main__":
    main()
