# rust_cmd: Design, Gap Analysis, and Jasmin Path

## What rust_cmd is

`SafeRustSimulation.v` defines `rust_cmd`, a typed dialect of bedrock2 that targets
safe Rust via OCaml extraction (`ToSafeRustBody.v`, `ToSafeRustString.v`).

The AST constructors:

```coq
| RSkip
| RSeq (c1 c2 : rust_cmd)
| RLetZero    (x : string) (t : tower_type)       (* let x = T::ZERO *)
| RLetU64Zero (x : string)                         (* let x = 0u64    *)
| RScalarSet  (dst src : string)                   (* dst = src        *)
| RCall       (dst : string) (f : string) (args : list string)
| RCloneCall  (dst alias : string) (f : string) (args : list string)
| RIfNz       (cond : string) (body : rust_cmd)
| RWhileNz    (cond : string) (body : rust_cmd)
| RLimbStore  (arr idx : string) (val : string)    (* arr[<lit>] = val *)
```

`tower_type` is hard-coded: `TFp | TFp2 | TFp6 | TFp12` (BN254 tower).

The operational semantics (`rust_step`, `rust_exec`) define a small-step and big-step
interpreter respectively. The soundness theorem `safe_cmd_correct` proves:

```
bedrock_exec c rs1 rs2  →  rust_exec (btranslate c) rs1 rs2
```

where `btranslate : bcmd → rust_cmd` is an identity-like translation (bcmd is the
toy bedrock fragment used in `SafeRustSimulation.v`).

The full bedrock2 → rust_cmd path goes through `SafeRustBedrockBridge.v`,
which connects bedrock2 `exec` to `rust_exec` for concrete tower functions.

---

## What rust_cmd covers today

For the BN254/BN256/BN446/BLS12 tower field arithmetic:

- All 64-bit word loads/stores
- `let x = T::ZERO` and `let x = 0u64`
- Function calls (single return value)
- Clone-and-call (aliasing workaround for Rust borrow checker)
- Fixed-index limb stores: `arr[4] = val`
- If-nonzero and while-nonzero control flow

The extracted code (e.g., `bls12_rust_extracted.ml`) uses these to generate
safe Rust `#[repr(C)]` structs with no unsafe blocks.

---

## Gap analysis: rust_cmd vs libcrux/hax field arithmetic

These features appear in libcrux's `x25519`, `ristretto255`, and pairing code
but are **not** in rust_cmd:

| Missing feature | Appears in | Impact |
|---|---|---|
| **Tuple / multi-value returns** | Multiplication with carry: `let (hi, lo) = u64::widening_mul(a, b)` | Cannot represent mulx/adcx patterns directly |
| **`u128` wide integers** | Alternative carry representation: `let r: u128 = (a as u128) * (b as u128)` | No `SU128` value type |
| **Variable-index limb stores** | `arr[i] = val` where `i` is a runtime variable | Only `RLimbStore` with literal index |
| **Non-BN254 tower types** | BLS12, BLS24, Pallas, Vesta Fp2 | `tower_type` is a 4-variant enum |
| **u8 byte arrays** | Serialization / deserialization in X25519 | No byte-level type in `rust_val` |

These are **absent** from inner field loops and are **not blocking** for tower arithmetic:

- `Vec`, closures, traits, generics, `Option`, `match` patterns
- Protocol-level Rust (hax extracts these to CryptOpt separately)

---

## Would a toy rust_cmd → Jasmin translation give us anything?

**No — the direct bedrock2 → jasmin_cmd path already exists and is proved.**

`Jasmin/Core.v` provides `tr_cmd : bedrock2.cmd → jasmin_cmd` with a structural
simulation proof (`tr_cmd_correct`), further polished by `JasminBridgeReal.to_jasmin_cmd`.

The two existing paths both originate from bedrock2:

```
bedrock2 WP proof
      ↓ tr_cmd / to_jasmin_cmd  [proved]
  jasmin_cmd  ──jasminc──▶  x86-64  (formal path)

bedrock2 WP proof
      ↓ SafeRustBedrockBridge  [proved]
  rust_exec
      ↓ ToSafeRustBody  [OCaml extraction, unverified pretty-print]
  safe Rust source (.rs)  (production path)
```

A rust_cmd → jasmin_cmd translation would be a **longer detour to the same
jasmin_cmd** that bedrock2 already reaches directly. It adds no additional
verification coverage.

### When it would be non-redundant

Only if rust_cmd expressed something beyond bedrock2 — it does not. rust_cmd
is a restricted, typed variant of bedrock2 with no new semantic content.

The related goal that IS meaningful: proving `rust_exec ≅ jasmin_exec` to show
the safe Rust and Jasmin implementations are semantically equivalent. But this
is best established by transitivity through their shared bedrock2 origin
(both are proved w.r.t. bedrock2 semantics), not by a new translation.

### What it would NOT give

- Any verification not already provided by the direct bedrock2→jasmin path
- Coverage of the `rustc` step (that requires a Rust compiler correctness proof)
- Coverage of libcrux/hax code (different source, not in rust_cmd at all)

---

## Minimum extensions to rust_cmd for broader libcrux coverage

If the goal is to cover libcrux's `ristretto255_mul` and `x25519_scalarmult` entirely
(not just the tower):

| Extension | Constructor | Needed for |
|---|---|---|
| Multi-value returns | `RTuple (dsts : list string) (f : string) (args : list string)` | `u64::widening_mul` → mulx |
| Wide integers | `SU128` value type + `RWideStore` | Alternative carry form |
| Variable limb index | `RLimbStoreVar (arr idx val : string)` | Montgomery loop patterns |
| Parameterized tower | `tower_type` as an inductive parameter | BLS12, BLS24, Pallas/Vesta |

These extensions are orthogonal and can be added incrementally.

---

## Files

| File | Role |
|---|---|
| `SafeRustSimulation.v` | `rust_cmd` AST + `rust_exec` semantics + `safe_cmd_correct` |
| `ToSafeRustBody.v` | OCaml extraction pretty-printer (generates `.rs` text) |
| `SafeRustBedrockBridge.v` | Connects bedrock2 `exec` to `rust_exec` for tower functions |
| `RustComposition.v` | `rust_refines` predicate + composition lemmas |
| `Jasmin/Core.v` | `jasmin_cmd` AST + `to_jasmin_cmd : bedrock2.cmd → jasmin_cmd` |
| `Jasmin/BridgeAbstract.v` | `UCEmulates`-style bridge: jasmin_cmd semantics → `psem.sem` |
| `Jasmin/BridgeConcrete.v` | Concrete instantiation for BLS12 field ops |
