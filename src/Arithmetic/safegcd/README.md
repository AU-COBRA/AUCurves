# Divstep Convergence Certificates for BLS12-381

Formal proof that the Bernstein-Yang divstep algorithm converges for BLS12-381,
using O'Connor's convex hull framework from [safegcd-bounds](https://github.com/sipa/safegcd-bounds).

## Files

| File | Purpose |
|------|---------|
| `divsteps_def.v` | Divstep algorithm definition |
| `divsteps_base.v` | Convex hull certificate infrastructure |
| `divsteps_convexhull.v` | Convex hull computation |
| `divsteps_theory.v` | Parameterized convergence & inverse theorems |
| `divsteps_bls12.v` | **BLS12-381 certificate** (heavy computation) |
| `divsteps_bls12_proof.v` | Inverse correctness (zero axioms, uses certificate) |

## Building

The certificate computation (`divsteps_bls12.v`) is the expensive step.
It runs `vm_compute` on `N.iter N (processDivstep p) state0` which
iterates the convex hull algorithm N times for the 381-bit BLS12 prime.

### Finding the tight bound

The Bernstein-Yang formula gives N=1101 as an upper bound. O'Connor's
convex hull typically gives a tighter bound. To find it:

```bash
# Binary search: try values from 1070 upward
for N in 1070 1075 1080 1085 1090 1095 1100 1101; do
  echo "Trying N=$N..."
  sed "s/N.iter [0-9]*/N.iter $N/" divsteps_bls12.v > /tmp/try_$N.v
  sed -i "s/bls12_iters : N := [0-9]*/bls12_iters : N := $N/" /tmp/try_$N.v
  timeout 7200 coqc -R . '' /tmp/try_$N.v 2>&1 | tail -1
  if [ $? -eq 0 ]; then echo "SUCCESS at N=$N"; break; fi
done
```

### Build commands

```bash
# Step 1: Build the framework (fast, <1 min)
coqc -R . '' divsteps_def.v
coqc -R . '' divsteps_convexhull.v
coqc -R . '' divsteps_base.v
coqc -R . '' divsteps_theory.v

# Step 2: Build the certificate (SLOW — hours, use native_compute if available)
# Option A: vm_compute (safe, may need 8+ GB RAM)
coqc -R . '' divsteps_bls12.v

# Option B: native_compute (faster if native compiler is available)
coqc -native-compiler yes -R . '' divsteps_bls12.v

# Step 3: Build the proof (fast, <1 sec)
coqc -R . '' divsteps_bls12_proof.v
```

### Memory and time estimates

Measured on AMD Ryzen 7 PRO 7840U (container, vm_compute):
- 100 iters: 27s
- 200 iters: >5 min (quadratic scaling)
- Extrapolated 1075 iters: ~50-60 min with vm_compute

| Params | vm_compute | native_compute (est.) | RAM |
|--------|-----------|----------------------|-----|
| 256-bit, N=724 | ~minutes | ~seconds | ~2 GB |
| 381-bit, N=1075 | **~50 min** | **~1-5 min** | ~4 GB |
| 381-bit, N=1101 | ~55 min | ~1-5 min | ~4 GB |

**Strongly recommended**: use `native_compute`. It needs a Rocq built with the
native compiler enabled (`-native-compiler yes`), which the standard Rocq 9
opam switch provides:
```bash
opam switch create aucurves ocaml-base-compiler.4.14.2
eval $(opam env)
opam install coq-rocq-prover
```

## References

- O'Connor, Poelstra. "Formal Verification of the Safegcd Implementation." arXiv:2507.17956, 2025.
- Bernstein, Yang. "Fast constant-time gcd computation and modular inversion." CHES 2019.
- Hvass, Aranha, Spitters. "High-assurance field inversion." ePrint 2021/549.
- Aranha, Hvass, Tibouchi, Spitters. "Faster Constant-time Evaluation of the Kronecker Symbol." CCS 2023.
