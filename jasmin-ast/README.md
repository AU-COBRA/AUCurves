# BLS12-381 Fp leaves through the verified bedrock2 -> Jasmin AST path

The four Fp leaves of fiat-crypto (add, sub, mul, square; `bls12_prime.v`) are translated in
Rocq from their bedrock2 bodies to a Jasmin program (`expr.uprog`, no `.jazz` text), extracted
to OCaml, and compiled by the Jasmin compiler of the Rocq development the theorems use.

## Theorems

| file | theorem | statement |
|---|---|---|
| `src/Bedrock/JasminAst/BLS12LeafSpecsProof.v` | `bls12_{add,sub,mul,square}_contract_proof` | fiat-crypto's `bls12_*_correct` imply the bridge propositions of `BLS12LeafSpecs.v` (the contract as a bedrock2 `exec` of the body) |
| `src/Jasmin/Ast/Sim.v` | `ccmd_correct`, `ccmd_sp_correct` | simulation: bedrock2 `exec` of a translated straight-line command implies Jasmin's execution to a related state (with spill hints) |
| `src/Jasmin/Ast/Fun.v` | `jfun_correct` | bedrock2 `exec` of a function body implies Jasmin `psem.sem_call` of the translated export function |
| `src/Jasmin/Ast/BLS12LeafThms.v` | `bls12_*_jasmin` | bridge proposition -> `psem.sem_call` of `bls12_leaves_prog` meets the contract |
| `src/Jasmin/Ast/BLS12LeafAsm.v` | `bls12_*_asm` | + `compiler_proof.compile_prog_to_asmP`: for any successful compilation, `asmsem_exportcall` of the assembly program meets the contract |

The fiat-side file and the Jasmin-side files cannot be loaded in one Rocq environment
(universe inconsistency between ITree, which Jasmin's `psem` imports, and fiat-crypto's
synthesis pipeline), so the end-to-end statement is the conjunction of the two halves over the
shared bridge propositions of `BLS12LeafSpecs.v` (which loads in both).

## Building the assembly

The Jasmin Rocq library in the Rocq 9.2 switch is jasmin-lang/jasmin main `294b46e` (not the
2026.09.0 release).  `toolchain/` rebuilds the matching OCaml compiler: a 2-line patch of Rocq
9.2's extraction plugin (an anomaly on `Declare Module ... with Definition`), the CIL extracted
from the switch's `.vo` with 294b46e's own `extraction.v`, the `jasmin.jasmin` library and the
driver `driver/jast294c.ml` (`main_compiler.ml` without the safety checker and linter, plus
`-bls12-leaves [-spill-K N]`, which compiles the extracted `bls12_leaves_prog`).
`leaves/run_all.sh` extracts the program, builds the driver, sweeps `K`, builds the reference
`.jazz` leaves (#21) and CryptOpt, runs the tests and the cycle benchmark (`leaves/leaves.md`).
The scripts read the toolchain from `$JAST_TOOLS` (default `~/tools`) and the AUCurves checkout from `$AUCURVES` (default `~/AUCurves`).
