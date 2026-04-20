# src/Theory

Mathematical foundations underlying the curve and field proofs.

## Subdirectories

### `Fields/`

| File | Contents |
|------|----------|
| `QuadraticFieldExtensions.v` | Generic Fp2 combinator (HierarchyBuilder fieldType instance) |
| `ReflectiveZmod.v` / `ReflectiveZmodTac.v` | Reflective ring/field tactic for `'F_p` (avoids `ring` timeouts on large primes) |
| `SmallZMul.v` | Lemmas for multiplication by small constants |
| `RingsUtil.v` / `FieldsUtil.v` | Utility lemmas |

### `WordByWordMontgomery/`

| File | Contents |
|------|----------|
| `MontgomeryCurveSpecs.v` | Gallina curve specs in Montgomery representation |
| `CurveSpecsEquivalence.v` | Equivalence: bedrock2 ↔ Gallina Montgomery specs |
| `MontgomeryCurveG1Equiv.v` | G1-specific equivalence chain |
| `BignumFElemBridge.v` | Bridge: bignum limb arrays ↔ field element `FElem` predicates |
| `MontgomeryRingTheory.v` | Ring-theory lemmas for Montgomery form |
| `wbw_morphisms.v` | Word-by-word morphism lemmas |

### `Util/`

Miscellaneous rewriting and automation utilities.
