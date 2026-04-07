#!/usr/bin/env python3
"""Convert a PARI ECPP certificate to coqprime Ell_certif format.

Usage:
    # First generate the cert with PARI:
    python3 -c "
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(1 << 30)
    pari.default('parisizemax', 1 << 32)
    q = <your_prime>
    cert = pari.primecert(q, 0)
    with open('cert.txt', 'w') as f: f.write(str(cert))
    "

    # Then convert:
    python3 ecpp_to_coq.py cert.txt <name> -o output.v

Requires: cypari2 (pip install cypari2)
"""

import sys
import argparse
import cypari2


def parse_nested_list(s):
    """Parse PARI's nested list string into Python lists."""
    s = s.strip()
    result = []
    depth = 0
    current = ""
    for c in s:
        if c == '[':
            if depth > 0:
                current += c
            depth += 1
        elif c == ']':
            depth -= 1
            if depth == 0 and current.strip():
                if '[' in current:
                    result.append(parse_nested_list(current))
                else:
                    result.append(int(current.strip()))
            elif depth > 0:
                current += c
        elif c == ',' and depth == 1:
            val = current.strip()
            if val:
                if '[' in val:
                    result.append(parse_nested_list(val))
                else:
                    result.append(int(val))
            current = ""
        else:
            current += c
    if not result and current.strip():
        for part in current.split(','):
            p = part.strip()
            if p:
                result.append(int(p))
    return result


def main():
    parser = argparse.ArgumentParser(description="Convert PARI ECPP cert to coqprime")
    parser.add_argument("cert_file", help="PARI ECPP certificate file")
    parser.add_argument("name", help="Name for Coq definitions (e.g., bw6_761)")
    parser.add_argument("-o", "--output", help="Output .v file")
    parser.add_argument("--hex", help="Hex value of the prime for Definition")
    args = parser.parse_args()

    pari = cypari2.Pari()
    pari.allocatemem(1 << 28)

    with open(args.cert_file) as f:
        raw = f.read()

    entries = parse_nested_list(raw)
    print(f"Parsed {len(entries)} ECPP steps", file=sys.stderr)

    # Build Coq Ell_certif entries
    # Key: S_i should factor as cofactor * N_{i+1}
    coq_certs = []
    for i in range(len(entries)):
        N = entries[i][0]
        A_val = entries[i][1]
        B_val = entries[i][2]
        S = entries[i][3]
        x_val = entries[i][4][0]
        y_val = entries[i][4][1]

        if S == 0 or S == 1:
            continue

        # Factor S by dividing out N_{i+1} first
        if i + 1 < len(entries) and S % entries[i + 1][0] == 0:
            N_next = entries[i + 1][0]
            cofactor = S // N_next
            cf = dict(pari.factor(pari(cofactor)))
            all_factors = sorted(list(cf.items()) + [(N_next, 1)])
        else:
            sf = pari.factor(pari(S))
            all_factors = [(int(sf[0][j]), int(sf[1][j]))
                           for j in range(len(sf[0]))]

        fl_str = "::".join(f"({p}, {e})" for p, e in all_factors) + "::nil"
        coq_certs.append(
            f"    Ell_certif {N} {S} ({fl_str}) ({A_val}) ({B_val}) ({x_val}) ({y_val})"
        )
        print(f"  Step {i}: {N.bit_length()}-bit N", file=sys.stderr)

    # Build the .v file
    hex_val = args.hex or hex(entries[0][0])
    subcerts = ";\n".join(coq_certs[1:])
    main_cert = coq_certs[0].strip()
    coq = (
        "Require Import Coq.ZArith.ZArith.\n"
        "Require Import Coq.ZArith.Znumtheory.\n"
        "From Coqprime Require Import PocklingtonRefl.\n"
        "\n"
        "Local Open Scope positive_scope.\n"
        "\n"
        f"Definition {args.name}_modulus : Z :=\n"
        f"  Eval vm_compute in ({hex_val})%Z.\n"
        "\n"
        f"Definition {args.name}_prime_pos : positive :=\n"
        f"  Eval vm_compute in (Z.to_pos {hex_val})%Z.\n"
        "\n"
        f"Lemma {args.name}_modulus_pos : {args.name}_modulus = Z.pos {args.name}_prime_pos.\n"
        "Proof. vm_compute. reflexivity. Qed.\n"
        "\n"
        f"Lemma prime_{args.name} : prime {args.name}_modulus.\n"
        "Proof.\n"
        f"  rewrite {args.name}_modulus_pos.\n"
        "  apply (Pocklington_refl\n"
        f"    {main_cert}\n"
        "    [\n"
        f"{subcerts}\n"
        "    ] _).\n"
        "  native_cast_no_check (refl_equal true).\n"
        "Qed.\n"
    )

    if args.output:
        with open(args.output, 'w') as f:
            f.write(coq)
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        print(coq)


if __name__ == "__main__":
    main()
