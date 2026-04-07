#!/usr/bin/env python3
"""Generate Pocklington primality certificates for Coqprime.

Usage:
    python3 gen_pock_certif.py <prime_hex_or_dec> <name> [--expr EXPR] [-o OUTPUT]

Examples:
    # secp256k1
    python3 gen_pock_certif.py 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F secp256k1

    # Pallas (with expression for readability)
    python3 gen_pock_certif.py 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 pallas

    # BW6-761 (output to file)
    python3 gen_pock_certif.py <big_hex> bw6_761 -o bw6_761_prime_certif.v
"""

import sys
import argparse
from math import isqrt

# Try cypari2 first (much faster for large primes), fall back to sympy
try:
    import cypari2
    _pari = cypari2.Pari()
    _HAS_PARI = True
except ImportError:
    _HAS_PARI = False

from sympy import isprime as sympy_isprime


def _factor_pari(n):
    """Factor n using PARI/GP (fast, handles large numbers)."""
    f = _pari.factor(n)
    primes = f[0]
    exponents = f[1]
    return {int(primes[i]): int(exponents[i]) for i in range(len(primes))}


def _factor_sympy(n):
    """Factor n using sympy (slower, may struggle > 300 bits)."""
    from sympy import factorint
    return factorint(n, multiple=False)


def factor(n):
    """Factor n using the best available backend."""
    if _HAS_PARI:
        return _factor_pari(n)
    return _factor_sympy(n)


def isprime(n):
    """Primality test using best available backend."""
    if _HAS_PARI:
        return bool(_pari.isprime(n))
    return sympy_isprime(n)


# ---------------------------------------------------------------------------
# Pocklington certificate generation
# ---------------------------------------------------------------------------

def factor_for_pocklington(n):
    """Factor n, returning list of (prime, exponent) sorted descending by prime.

    For very large n, sympy may not fully factor.  We only need enough
    factors so that their product F1 satisfies the BPP bound:
        N < ((2*F1 + r + 1)*F1 + r)*F1 + 1
    which roughly requires F1 > N^(1/3).
    """
    factors = factor(n)
    # Sort descending by prime (largest first, matching Coqprime convention)
    return sorted(factors.items(), key=lambda x: -x[0])


def compute_F1(factors):
    """Compute F1 = product of p^e for each (p, e) in factors."""
    result = 1
    for p, e in factors:
        result *= p ** e
    return result


def check_bpp_bound(N, F1):
    """Check the BPP bound: N < ((2*F1 + r + 1)*F1 + r)*F1 + 1."""
    Nm1 = N - 1
    R1 = Nm1 // F1
    if Nm1 != F1 * R1:
        return False
    F1_2 = 2 * F1
    s = R1 // F1_2
    r = R1 % F1_2
    bound = ((F1_2 + r + 1) * F1 + r) * F1 + 1
    return N < bound


def compute_sqrt_param(N, F1):
    """Compute the sqrt parameter for Pock_certif."""
    Nm1 = N - 1
    R1 = Nm1 // F1
    F1_2 = 2 * F1
    s = R1 // F1_2
    r = R1 % F1_2
    if s == 0:
        return 1
    x = r * r - 8 * s
    if x <= 0:
        return 1
    sq = isqrt(x)
    # Verify: sq^2 < x < (sq+1)^2
    if sq * sq >= x:
        sq -= 1
    assert sq * sq < x < (sq + 1) * (sq + 1), \
        f"sqrt check failed: {sq}^2 = {sq*sq}, x = {x}, {(sq+1)}^2 = {(sq+1)**2}"
    return sq


def find_witness(N, factors_of_Nm1):
    """Find Pocklington witness a for prime N.

    Conditions:
        1) a^(N-1) ≡ 1 (mod N)
        2) For each prime q | F1: gcd(a^((N-1)/q) - 1, N) = 1
    """
    from math import gcd
    Nm1 = N - 1
    primes_in_F1 = [p for p, _ in factors_of_Nm1]

    for a in candidate_witnesses():
        if a >= N:
            break
        # Check a^(N-1) ≡ 1 (mod N)
        if pow(a, Nm1, N) != 1:
            continue
        # Check gcd condition for each prime factor
        ok = True
        for q in primes_in_F1:
            val = pow(a, Nm1 // q, N) - 1
            if gcd(val % N, N) != 1:
                ok = False
                break
        if ok:
            return a

    raise RuntimeError(f"No witness found for N = {N}")


def candidate_witnesses():
    """Generate candidate witnesses: 2, 3, 5, 6, 7, 10, 11, 12, 13, ..."""
    # Start with small primes and composites
    for a in [2, 3, 5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 19, 21, 23]:
        yield a
    a = 24
    while True:
        yield a
        a += 1


# ---------------------------------------------------------------------------
# Recursive certificate tree
# ---------------------------------------------------------------------------

# Primes with built-in Coqprime proofs (prime_2, prime_3, etc.)
# Conservative: only 2 and 3 are guaranteed everywhere.
# Extended set works with most Coqprime installations.
BUILTIN_PRIMES = {
    2: "prime_2", 3: "prime_3", 5: "prime_5", 7: "prime_7",
    11: "prime_11", 13: "prime_13", 17: "prime_17", 19: "prime_19",
    23: "prime_23", 29: "prime_29", 31: "prime_31", 37: "prime_37",
    41: "prime_41", 43: "prime_43", 47: "prime_47", 53: "prime_53",
    59: "prime_59", 61: "prime_61", 67: "prime_67", 71: "prime_71",
    73: "prime_73", 79: "prime_79", 83: "prime_83", 89: "prime_89",
    97: "prime_97",
}

# For larger "small" primes, we can also try prime_N naming
PROOF_CERTIF_THRESHOLD = 100  # Use Proof_certif for primes <= this


class CertNode:
    """A node in the Pocklington certificate tree."""

    def __init__(self, N, witness, factors, sqrt_param, children):
        self.N = N
        self.witness = witness
        self.factors = factors  # list of (prime, exponent)
        self.sqrt_param = sqrt_param
        self.children = children  # list of CertNode or (N, proof_name)


def build_certificate(N, depth=0, verbose=True):
    """Recursively build a Pocklington certificate for prime N."""
    if verbose:
        prefix = "  " * depth
        bits = N.bit_length()
        print(f"{prefix}Certifying {bits}-bit prime: {N if bits <= 80 else hex(N)[:20]}...")

    assert isprime(N), f"{N} is not prime"

    # Base case: small primes with built-in proofs
    if N in BUILTIN_PRIMES:
        return (N, BUILTIN_PRIMES[N])

    if N <= PROOF_CERTIF_THRESHOLD and isprime(N):
        name = f"prime{N}"
        return (N, name)

    # Factor N-1
    Nm1 = N - 1
    factors_full = factor_for_pocklington(Nm1)

    if verbose:
        print(f"{prefix}  N-1 factors: {[(p, e) for p, e in factors_full if p.bit_length() <= 64]}"
              f"{' + larger...' if any(p.bit_length() > 64 for p, _ in factors_full) else ''}")

    # Check BPP bound with all factors
    F1 = compute_F1(factors_full)
    if not check_bpp_bound(N, F1):
        raise RuntimeError(
            f"BPP bound not satisfied for {N}. "
            f"F1 = {F1}, F1^3 vs N = {F1**3} vs {4*N}. "
            f"Need more factorization of N-1."
        )

    # Find witness
    witness = find_witness(N, factors_full)
    if verbose:
        print(f"{prefix}  witness: {witness}")

    # Compute sqrt parameter
    sqrt_param = compute_sqrt_param(N, F1)

    # Recursively certify all prime factors > threshold
    children = []
    for p, e in factors_full:
        child = build_certificate(p, depth + 1, verbose)
        children.append(child)

    return CertNode(N, witness, factors_full, sqrt_param, children)


# ---------------------------------------------------------------------------
# Coq output
# ---------------------------------------------------------------------------

def format_factors(factors):
    """Format factor list as Coq dec_prime: ((p1, e1)::(p2, e2)::...::nil)"""
    parts = [f"({p}, {e})" for p, e in factors]
    return "::".join(parts) + "::nil"


def collect_subcerts(node):
    """Flatten certificate tree into list for Coqprime's Certif format.

    Coqprime expects a flat list of certificates. The order must be such that
    each prime's certificate appears before it's referenced by a parent.
    We do post-order traversal (children before parents), but skip the root
    since it's the main certificate argument.
    """
    result = []
    _collect_subcerts_impl(node, result, is_root=True)
    return result


def _collect_subcerts_impl(node, result, is_root=False):
    if isinstance(node, tuple):
        # Proof_certif leaf
        N, proof_name = node
        result.append(f"Proof_certif {N} {proof_name}")
        return

    # Process children first (post-order)
    for child in node.children:
        _collect_subcerts_impl(child, result)

    # Add this node (unless root — root goes in the main Pocklington_refl call)
    if not is_root:
        factors_str = format_factors(node.factors)
        result.append(
            f"Pock_certif {node.N} {node.witness} ({factors_str}) {node.sqrt_param}"
        )


def generate_coq(node, name, prime_expr=None):
    """Generate the full .v file content."""
    lines = []

    # Header
    lines.append("Require Import Coq.ZArith.ZArith.")
    lines.append("Require Import Coq.ZArith.Znumtheory.")
    lines.append("From Coqprime Require Import PocklingtonRefl.")
    lines.append("")
    lines.append("Local Open Scope positive_scope.")
    lines.append("")

    # Modulus definition
    if prime_expr:
        lines.append(f"Definition {name}_modulus : Z :=")
        lines.append(f"  Eval vm_compute in ({prime_expr})%Z.")
    else:
        lines.append(f"Definition {name}_modulus : Z := {node.N}%Z.")
    lines.append("")

    # Positive version
    if prime_expr:
        lines.append(f"Definition {name}_prime_pos : positive :=")
        lines.append(f"  Eval vm_compute in (Z.to_pos ({prime_expr}))%Z.")
    else:
        lines.append(f"Definition {name}_prime_pos : positive :=")
        lines.append(f"  Eval vm_compute in (Z.to_pos {node.N})%Z.")
    lines.append("")

    # Modulus_pos lemma
    lines.append(f"Lemma {name}_modulus_pos : {name}_modulus = Z.pos {name}_prime_pos.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")

    # Main primality lemma
    lines.append(f"Lemma prime_{name} : prime {name}_modulus.")
    lines.append("Proof.")
    lines.append(f"  rewrite {name}_modulus_pos.")

    # Main certificate
    main_factors = format_factors(node.factors)
    lines.append(f"  apply (Pocklington_refl")
    lines.append(f"    (Pock_certif {name}_prime_pos {node.witness}")
    lines.append(f"      ({main_factors})")
    lines.append(f"      {node.sqrt_param})")

    # Sub-certificates
    subcerts = collect_subcerts(node)
    lines.append(f"    [")
    for i, sc in enumerate(subcerts):
        sep = ";" if i < len(subcerts) - 1 else ""
        lines.append(f"    {sc}{sep}")
    lines.append(f"    ] _).")

    lines.append("  native_cast_no_check (refl_equal true).")
    lines.append("Qed.")
    lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def parse_prime(s):
    """Parse a prime from hex (0x...) or decimal string."""
    s = s.strip()
    if s.startswith("0x") or s.startswith("0X"):
        return int(s, 16)
    return int(s)


def main():
    parser = argparse.ArgumentParser(
        description="Generate Pocklington primality certificates for Coqprime"
    )
    parser.add_argument("prime", help="The prime number (hex with 0x prefix, or decimal)")
    parser.add_argument("name", help="Curve/field name (e.g., pallas, secp256k1)")
    parser.add_argument("--expr", help="Coq expression for the prime (e.g., '2^256 - 2^32 - 977')")
    parser.add_argument("-o", "--output", help="Output .v file (default: stdout)")
    parser.add_argument("-q", "--quiet", action="store_true", help="Suppress progress output")
    args = parser.parse_args()

    p = parse_prime(args.prime)
    verbose = not args.quiet

    if verbose:
        print(f"Prime: {p.bit_length()}-bit number", file=sys.stderr)
        print(f"Name: {args.name}", file=sys.stderr)

    if not isprime(p):
        print(f"ERROR: {p} is not prime!", file=sys.stderr)
        sys.exit(1)

    # Build certificate tree
    cert = build_certificate(p, verbose=verbose)

    # Generate Coq output
    coq_src = generate_coq(cert, args.name, prime_expr=args.expr)

    if args.output:
        with open(args.output, "w") as f:
            f.write(coq_src)
        if verbose:
            print(f"\nWrote {args.output}", file=sys.stderr)
    else:
        print(coq_src)


if __name__ == "__main__":
    main()
