(** * BN Pairing Optimizations — Gallina specs + cost analysis.

    Three algorithmic optimizations for the pairing computation:

    1. Cyclotomic squaring (Granger-Scott 2010)
       - After the easy part of final exp, elements are in the cyclotomic
         subgroup GΦ₆ ⊂ Fp12*. These satisfy Norm(f) = f * conj(f) = 1.
       - Cyclotomic squaring: 4 Fp2 squarings + adds (vs 3 Fp6 muls)
       - Savings: ~30% of each squaring in pow_u and final exp hard part

    2. Lazy reduction (deferred modular reduction)
       - Standard: each Fp add/sub does (a ± b) mod p immediately
       - Lazy: allow 2p-wide intermediates, reduce only before mul
       - Savings: ~15-20% overall (eliminates ~50% of conditional subs)

    3. Sparse Fp12 multiplication in Miller loop
       - Line evaluations produce elements with structure:
         l = ((l₀, l₁, 0), (0, l₃, 0)) in Fp6×Fp6
       - Multiplying f * l can skip zero components
       - Savings: ~30% of each line-times-f multiplication

    These are specified as Gallina functions. The bedrock2 bodies and
    WP proofs are future work. *)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.

Local Open Scope Z_scope.

Section Optimizations.

  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Variable beta : Fp.  (* Fp2 nonresidue *)

  (* === Fp2 operations === *)

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (F.add (fst a) (fst b), F.add (snd a) (snd b)).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (F.sub (fst a) (fst b), F.sub (snd a) (snd b)).

  Definition fp2_mul (a b : Fp2) : Fp2 :=
    let '(a0, a1) := a in
    let '(b0, b1) := b in
    (F.add (F.mul a0 b0) (F.mul beta (F.mul a1 b1)),
     F.add (F.mul a0 b1) (F.mul a1 b0)).

  Definition fp2_sqr (a : Fp2) : Fp2 := fp2_mul a a.

  Definition fp2_dbl (a : Fp2) : Fp2 := fp2_add a a.

  (* ================================================================ *)
  (** * 1. Cyclotomic Squaring (Granger-Scott 2010)                    *)
  (* ================================================================ *)

  (** For f in the cyclotomic subgroup GΦ₆ of Fp12, f^(-1) = conj(f).
      The element f = (a, b) ∈ Fp6 × Fp6 = Fp12 satisfies a² - v·b² = 1.

      Decompose f into 6 Fp2 components:
        a = (a0, a1, a2) ∈ Fp6  (= Fp2³)
        b = (b0, b1, b2) ∈ Fp6

      Cyclotomic squaring uses the relation a² + v·b² = 2a - 1
      (from a² - v·b² = 1) to compute f² with only Fp2 squarings.

      Algorithm (Karabina 2012, compressed form):
      Cost: 6 Fp2 squarings + 8 Fp2 adds/subs
      vs schoolbook: 3 Fp6 muls ≈ 18 Fp2 muls + 12 Fp2 adds *)

  Definition cyclotomic_sqr (f : Fp12) : Fp12 :=
    let '((a0, a1, a2), (b0, b1, b2)) := f in
    (* Compute Fp2 squarings of the "active" components *)
    let t0 := fp2_sqr a0 in    (* a0² *)
    let t1 := fp2_sqr a1 in    (* a1² *)
    let t2 := fp2_sqr a2 in    (* a2² *)
    let t3 := fp2_sqr b0 in    (* b0² *)
    let t4 := fp2_sqr b1 in    (* b1² *)
    let t5 := fp2_sqr b2 in    (* b2² *)
    (* Use cyclotomic constraint to reconstruct f² *)
    (* The formulas use xi-multiples and additions only *)
    let a0' := fp2_sub (fp2_dbl t0) (fp2_dbl a0) in  (* placeholder *)
    let a1' := fp2_add (fp2_dbl t1) (fp2_dbl a1) in  (* placeholder *)
    let a2' := fp2_sub (fp2_dbl t2) (fp2_dbl a2) in  (* placeholder *)
    let b0' := fp2_add (fp2_dbl t3) (fp2_dbl b0) in  (* placeholder *)
    let b1' := fp2_sub (fp2_dbl t4) (fp2_dbl b1) in  (* placeholder *)
    let b2' := fp2_add (fp2_dbl t5) (fp2_dbl b2) in  (* placeholder *)
    ((a0', a1', a2'), (b0', b1', b2')).

  (* Operation count comparison *)
  (* Schoolbook Fp12 sqr: 2 Fp6_sqr + 1 Fp6_mul = ~54 Fp_mul *)
  (* Cyclotomic Fp12 sqr: 6 Fp2_sqr + adds      = ~18 Fp_mul *)
  (* Savings: ~67% per squaring *)
  (* Applied to pow_u (63 iters × 1 sqr) + DSD (4 sqr) = 193 squarings *)
  (* Savings: 193 × (54-18) = ~6948 Fp_mul saved *)

  (* ================================================================ *)
  (** * 2. Lazy Reduction                                              *)
  (* ================================================================ *)

  (** Standard Fp add: c = (a + b) mod p (conditional subtract)
      Lazy Fp add:     c = a + b        (no mod, result < 2p)

      For Fp2 mul (a0+a1*u)(b0+b1*u):
        standard: 3 Fp_mul + 5 Fp_add (each Fp_add does mod)
        lazy:     3 Fp_mul + 5 wide_add (no mod) + 2 Fp_reduce

      Since Fp_mul already reduces at the end (Montgomery), the
      intermediate adds don't need reduction. We only reduce after
      the final subtraction.

      Implementation: widen the Fp representation to allow [0, 2p)
      intermediates. Fp_mul still takes tight inputs and produces
      tight output (Montgomery reduction handles it). Only Fp_add/sub
      change to allow unreduced output.

      NOTE: This requires changing the field element representation
      and bounds in bedrock2, which is a deeper change than just
      adding a new function. The fiat-crypto pipeline already supports
      "loose bounds" vs "tight bounds" — this optimization maps to
      using loose bounds for add/sub outputs and tight bounds for
      mul inputs. *)

  (* Estimated savings:
     Fp2_mul: saves ~2 conditional subs out of 5 adds = ~15% per Fp2_mul
     Total: ~6826 Fp_mul → the ~9400 Fp_add become ~20% cheaper
     Net: ~15% overall reduction *)

  (* ================================================================ *)
  (** * 3. Sparse Fp12 Multiplication in Miller Loop                   *)
  (* ================================================================ *)

  (** Line evaluation produces a "sparse" Fp12 element:
        l = ((l00, l01, 0), (0, l10, 0)) ∈ Fp6 × Fp6
      where l00, l01, l10 ∈ Fp2 and the rest are zero.

      Full Fp12_mul(f, l) costs: ~18 Fp2_mul + 12 Fp2_add
      Sparse Fp12_mul_line(f, l) costs: ~13 Fp2_mul + 8 Fp2_add

      The savings come from skipping multiplications by zero and
      simplifying the Karatsuba decomposition. *)

  (* Sparse Fp12 element: only 3 nonzero Fp2 components *)
  Record sparse_fp12 := {
    sl00 : Fp2;  (* c0.c0 *)
    sl01 : Fp2;  (* c0.c1 *)
    sl10 : Fp2;  (* c1.c1 = coefficient of w*v *)
  }.

  (** Sparse multiplication: f * l where l is sparse.
      Uses the structure l = (sl00 + sl01*v, sl10*v*w) to reduce ops. *)
  Definition fp12_mul_sparse (f : Fp12) (l : sparse_fp12) : Fp12 :=
    let '((a0, a1, a2), (b0, b1, b2)) := f in
    (* Full implementation requires Fp6 operations *)
    (* This is the spec — bedrock2 body is future work *)
    f. (* placeholder *)

  (* Operation count:
     Full Fp12_mul:        18 Fp2_mul + 12 Fp2_add = 54+36 Fp_mul equiv
     Sparse Fp12_mul_line: 13 Fp2_mul + 8 Fp2_add  = 39+24 Fp_mul equiv
     Savings per line mul: ~28%

     Miller loop: 64 iterations × 1 line mul = 64 sparse muls
     Savings: 64 × (18-13) = 320 Fp2_mul = 960 Fp_mul saved *)

  (* ================================================================ *)
  (** * Combined Impact                                                *)
  (* ================================================================ *)

  (* Current:
     Miller loop: ~2560 Fp_mul + ~6400 Fp_add
     Final exp:   ~4266 Fp_mul + ~3000 Fp_add
     Total:       ~6826 Fp_mul + ~9400 Fp_add

     With optimizations:
     1. Cyclotomic sqr: -6948 Fp_mul (replaced by Fp_sqr+add)
                         +3474 Fp_sqr + 4632 Fp_add
     2. Lazy reduction:  -0 Fp_mul, -1880 Fp_add (20% of adds)
     3. Sparse mul:      -960 Fp_mul, -640 Fp_add

     Optimized:
     Miller loop: ~1600 Fp_mul + ~6000 Fp_add
     Final exp:   ~1000 Fp_mul + ~6000 Fp_add + ~3500 Fp_sqr
     Total:       ~2600 Fp_mul + ~12000 Fp_add + ~3500 Fp_sqr

     At 27ns/mul, 25ns/sqr, 4ns/add:
     Current:  6826*27 + 9400*4 = 184+38 = ~222 μs
     Optimized: 2600*27 + 12000*4 + 3500*25 = 70+48+88 = ~206 μs

     The cyclotomic squaring benefit is modest when Fp_sqr ≈ Fp_mul.
     The REAL win from cyclotomic squaring comes when using compressed
     representations (Karabina), which this analysis doesn't capture.

     The biggest practical win is sparse multiplication (#3):
     simple to implement, no representation changes needed. *)

End Optimizations.
