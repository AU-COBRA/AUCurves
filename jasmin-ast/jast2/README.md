# Optimised bedrock2 -> Jasmin AST path for the BLS12-381 Fp leaves (jast2)

Rocq (theory `JasminBridge`, `src/Jasmin/Ast/`):

| file | content |
|---|---|
| `Carry.v` | `xcmd`: the optimising translation of a flattened leaf body. Rules: fiat's addcarryx / subborrowx windows (2- and 5-statement forms, first word, chain ends, `(ce+a)+b`) to `Oaddcarry`/`Osubcarry` with the carry in a boolean variable; carry naming / materialisation (`CMOV`); fiat's mask `-1+(c==0)` as `SBB r,r`; fiat's select as `MOV`+`CMOV`; `x=a*b; y=mulhuu a b` as one `MULX`; hoisting of masked operands `y & k` into available-expression holders; every other statement as `Comp.ccmd`. State: carry fact, stale variables, available expressions. A translation that would read a stale variable fails as a whole (the leaf then uses `Comp.ccmd_sp`). |
| `CarryArith.v` | carry identities: fiat's word-level carries = Jasmin's `waddcarry`/`wsubcarry`; mask and select identities |
| `CarrySim.v` | `xcmd_correct`: bedrock2 `exec` of a body -> `Trans.run` of the code to a related state (relation `RX`: non-stale locals agree, carry fact, available expressions); one lemma per rule (`rule_*_ok`), `hoist_ok`, `xchunks_ok` |
| `SpillChoice.v` | spill hints from liveness (unverified heuristic, any choice is correct): Belady greedy under a register budget |
| `BLS12Leaves2.v` | `bls12_leaves2_prog name cfn fname finfo iinfo budget` |
| `Fun2.v` | `jfun_correct2` (either translation -> `psem.sem_call`) |
| `BLS12LeafThms2.v` | `bls12_{add,sub,mul,square}_jasmin2` |
| `BLS12LeafAsm2.v` | `bls12_{add,sub,mul,square}_asm2` (+ `compile_prog_to_asmP`) |

Assembly (toolchain as `jasmin-ast/toolchain`, under `$JAST_TOOLS`):
`extract.sh` (extraction from the dune `_build`, CIL identity check), `cycle.sh` (build, extract,
driver, compile, test/bench), `bench.sh` (tests vs AUCurves main's `generated/bls12_leaves_live.jazz`
compiled by jasminc 2026.09.0 `-auto-spill`, and CryptOpt; big-integer check; objdump stats; cycles),
`ct_check.sh` + `ct_sanitize.py` (jasmin-ct 2026.09.0 on the program printed by the 294b46e compiler),
`measure_files.py` (per-file compile time / peak RSS). Driver: `jast294c -bls12-leaves -spill-K <budget>`
compiles `bls12_leaves2_prog` (`-leaves-v1`: jast's `bls12_leaves_prog`).
