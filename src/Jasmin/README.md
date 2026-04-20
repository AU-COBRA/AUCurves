# src/Jasmin

Bridge connecting bedrock2 proofs to the Jasmin compiler's semantics.

## Files

| File | Contents |
|------|----------|
| `BridgeReal.v` | Core simulation: bedrock2 `exec` ↔ Jasmin `psem.sem` |
| `BridgeRealInstance.v` | Instantiation of the bridge for concrete Jasmin programs |
| `extractions/` | OCaml extraction of Jasmin programs from bedrock2 |
| `ocaml/` | OCaml driver code for the extraction pipeline |

## How it works

`BridgeReal.v` proves a `bridge_simulation` theorem: if a bedrock2 function
satisfies its `spec_of` postcondition, then the corresponding Jasmin function
(compiled via `psem.sem`) satisfies the same functional contract.

The extraction pipeline emits `.jazz` source from proven bedrock2 programs,
which can then be compiled by the Jasmin compiler to assembly.
