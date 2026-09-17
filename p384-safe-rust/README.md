# p384-safe-rust

P-384 (secp384r1) field and group arithmetic in Rust: fiat-crypto's
word-by-word Montgomery field over `[u64; 6]` with `R = 2^384`, the
Bernstein–Yang divstep inverse from `safegcd-rs`, and a projective group
with the `a = -3` Renes–Costello–Batina complete formulas, a constant-time
4-bit variable-base window and a `W = 5` fixed-base comb over a precomputed
generator table (`src/group.rs`).

## Field configurations

`fp_mul` and `fp_square` in `src/lib.rs` are selected at build time by
`build.rs`. Every other function, including the group law and both scalar
multiplications, is the same in all configurations; they call the field
through `fp_mul` and `fp_square`, so they inherit the configuration.

| `FIELD_CONFIG`          | cfg                                            | `fp_mul`                          | `fp_square`                       |
|-------------------------|------------------------------------------------|-----------------------------------|-----------------------------------|
| `"fiat"`                | none                                           | `fiat_p384_mul`                   | `fiat_p384_square`                |
| `"cryptopt"`            | `p384_cryptopt_asm`                            | `p384_cryptopt_mul` (`generated/`)| `p384_cryptopt_square`            |
| `"s2n-bignum"`          | `p384_s2n_field`                               | `bignum_montmul_p384`             | `bignum_montsqr_p384`             |
| `"s2n-montmul-encoded"` | `p384_s2n_field`, `p384_s2n_montmul_only`      | `bignum_montmul_p384_encoded`     | `bignum_montmul_p384_encoded(x, x)` |

Precedence, highest first:

1. `P384_NO_CRYPTOPT` set, to any value: fiat. This holds even when
   `P384_S2N_FIELD` is also set; the build prints a warning.
2. `P384_S2N_FIELD=<path>` set: s2n-bignum. The file extension selects the
   form:
   * `.a`: a static archive with `bignum_montmul_p384` and
     `bignum_montsqr_p384`, such as s2n-bignum's `x86/libs2nbignum.a`;
   * `.o`: one object file with the same two symbols;
   * `.s`: an assembly file defining `bignum_montmul_p384_encoded`, assembled
     with `as --64`; this is the `s2n-montmul-encoded` row.

   A relative path is resolved against this crate's directory. The build
   fails, with the reason, if the file is missing, has another extension,
   lacks the `.s` symbol, or cannot be assembled, or if the build is not a
   native x86-64 Linux build on a host with BMI2 and ADX. It does not fall
   back to another configuration.
3. Otherwise CryptOpt, when the build is native x86-64 Linux, the host has
   BMI2 and ADX, and `nasm` assembles `generated/`; fiat when any of these
   fails.

`p384::FIELD_CONFIG` names the configuration of a binary, `p384::S2N_FIELD`
and `p384::CRYPTOPT_ASM` are the corresponding booleans, and
`fp_mul_fiat` / `fp_square_fiat` always call fiat.

A crate that depends on this one gets the configuration from the environment
of its own build:

```
P384_S2N_FIELD=/path/to/s2n-bignum/x86/libs2nbignum.a cargo build --release --offline
```

### Cargo features

A dependent crate can instead fix the configuration in its manifest. With
none of the three features below enabled, the rules above are unchanged.

| feature            | configuration         | notes |
|--------------------|-----------------------|-------|
| `fiat`             | `"fiat"`              | no CryptOpt autodetection; `P384_NO_CRYPTOPT` and `P384_S2N_FIELD` still apply as above |
| `cryptopt`         | `"cryptopt"`          | the build fails where the automatic selection would fall back to fiat |
| `catcrypt-montmul` | `"s2n-montmul-encoded"` | `fp_mul` and `fp_square` call `bignum_montmul_p384_encoded`; see below |

Under `catcrypt-montmul`, `P384_CATCRYPT_MONTMUL_S=<file.s>` names an
assembly source defining the global `bignum_montmul_p384_encoded`, which
`build.rs` assembles with `as --64` and links. Without that variable nothing
is linked, and the symbol must be supplied by another crate of the final
link; the `asm-montmul` feature of CatCrypt's `catcrypt-p384` crate does this
with its vendored copy of the framed, CatCrypt-encoded montmul. A link
without the symbol fails with `undefined symbol: bignum_montmul_p384_encoded`.

`cryptopt` together with `catcrypt-montmul` fails the build, and so does
either of them together with `P384_NO_CRYPTOPT` or `P384_S2N_FIELD`.
Enabled together with `fiat`, either of them takes precedence. Both require
a native x86-64 Linux build on a host with BMI2 and ADX and fail the build
otherwise.

```
cargo test --offline --release -p p384-safe-rust --features extracted,fiat
cargo test --offline --release -p p384-safe-rust --features extracted,cryptopt
P384_CATCRYPT_MONTMUL_S=/path/to/bignum_montmul_p384_encoded.s \
  cargo test --offline --release -p p384-safe-rust --features extracted,catcrypt-montmul
```

### What is ours and what is external under `P384_S2N_FIELD`

The group law, the variable-base window, the fixed-base comb and table, the
constant-time selection, the inverse and the field addition, subtraction,
negation and Montgomery conversions are this crate's (fiat-crypto and
`safegcd-rs` for the field operations other than multiply and square). The
field multiply and square are external:

* `.a` / `.o`: s2n-bignum's hand-written x86-64 assembly
  `x86_att/p384/bignum_montmul_p384.S` and `bignum_montsqr_p384.S`, whose
  machine code is proved in HOL Light against the specification
  `z = 2^-384 · x · y mod p_384` (theorems
  `BIGNUM_MONTMUL_P384_SUBROUTINE_CORRECT`, `BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT`
  in `x86/proofs/`).
* `.s`: s2n-bignum's montmul imported into CatCrypt's `JInstr 64` IR and
  re-encoded by CatCrypt's scalar encoder. The body bytes are covered by a
  Lean proof that they decode to the imported block and that the block
  computes the Montgomery product under CatCrypt's machine model; the
  function frame (`endbr64`, register saves and restores, `ret`) is outside
  that proof. Squaring calls the same function with both inputs equal to
  `x`, so every field multiply and square runs through the proved bytes, at
  the cost of a general multiply where s2n-bignum has a dedicated square.

### The s2n-bignum conventions

Taken from the header comments of the two `.S` files and the HOL Light
statements:

* Arguments, System V: `z` in `%rdi`, `x` in `%rsi`, `y` in `%rdx`; `z`,
  `x`, `y` are little-endian `uint64_t[6]`.
* Function: `bignum_montmul_p384` computes `(2^-384 · x · y) mod p_384`,
  `bignum_montsqr_p384` computes `(2^-384 · x^2) mod p_384`. The result is
  fully reduced (`MOD p_384` in the post-condition).
* Precondition: `x · y ≤ 2^384 · p_384` (resp. `x^2 ≤ 2^384 · p_384`), which
  holds for `x, y < p_384`, the range fiat-crypto's field operations
  return.
* Instructions: `mulx`, `adcx`, `adox` (BMI2, ADX).

This is the function fiat-crypto's `fiat_p384_mul` / `fiat_p384_square`
compute on Montgomery-domain elements, so no representation change is
needed at the call.

## Tests

```
cargo test --offline --release -p p384-safe-rust --features extracted
```

`tests/s2n_field_diff.rs` is the differential test for the s2n
configurations. It compares `fp_mul` / `fp_square` with fiat bit for bit, and
checks that results are below `p` and that `fp_square(x) = fp_mul(x, x)`,
on 441 pairs of 21 edge values (0, 1, 2, `R mod p`, `p − 1`, `p − 2`,
`2^383`, `2^383 ± 1`, values with all-ones limbs below `p`, the limb patterns
of `p`), 200 000 random pairs, 200 000 random squares, 420 000 edge × random
pairs and a 100 000-step chain feeding each output back as an input. In the
fiat and CryptOpt configurations it prints that it did not run.
`tests/cryptopt_diff.rs` performs the same comparison against whichever
leaves `fp_mul` is bound to.

Results of the full suite with `--features extracted` (unit tests in
`src/`, then `a3_diff`, `cryptopt_diff`, `extracted_diff`, `kat_vectors`,
`s2n_field_diff`, `scalar_mul_diff`):

| configuration          | unit | a3_diff | cryptopt_diff | extracted_diff | kat_vectors | s2n_field_diff | scalar_mul_diff |
|------------------------|-----:|--------:|--------------:|---------------:|------------:|---------------:|----------------:|
| fiat                   | 22   | 8       | 7             | 1              | 14          | 7 (not run)    | 6               |
| cryptopt               | 22   | 8       | 7             | 1              | 14          | 7 (not run)    | 6               |
| s2n-bignum (`.a`)      | 22   | 8       | 7             | 1              | 14          | 7              | 6               |
| s2n-montmul-encoded    | 22   | 8       | 7             | 1              | 14          | 7              | 6               |

All passed. The `.o` form (the two objects combined with `ld -r`) passed
`s2n_field_diff` as well. The feature selections `extracted,fiat`,
`extracted,cryptopt` and `extracted,catcrypt-montmul` (the last with
`P384_CATCRYPT_MONTMUL_S` naming the framed montmul vendored in
`catcrypt-p384/asm/`) pass with the counts of the `fiat`, `cryptopt` and
`s2n-montmul-encoded` rows respectively.

## Measurements

`examples/bench.rs`, one binary per configuration, each pinned to logical
CPU 6 (`taskset -c 6`) on an AMD Ryzen 7 PRO 7840U. The four binaries ran
round-robin for 14 rounds, seven in the order fiat, CryptOpt, s2n, encoded
and seven in the reverse order. Figures are nanoseconds per operation,
minimum over the 14 rounds, with the median in parentheses. The machine was
shared: the load average was between 6 and 8 throughout, and the spread
between minimum and median (10–20 %) bounds what a difference between two
columns can mean.

| operation            | fiat              | CryptOpt          | s2n-bignum        | s2n-montmul-encoded |
|----------------------|------------------:|------------------:|------------------:|--------------------:|
| `fp_mul`             | 55.5 (62.7)       | 36.1 (42.1)       | 26.5 (30.3)       | 25.6 (30.7)         |
| `fp_square`          | 50.6 (58.8)       | 37.6 (41.3)       | 21.8 (24.8)       | 24.9 (30.2)         |
| `g1_add`             | 927 (1033)        | 745 (829)         | 643 (686)         | 593 (712)           |
| `g1_double`          | 847 (946)         | 685 (773)         | 529 (606)         | 549 (616)           |
| `g1_scalar_mul`      | 426 896 (480 713) | 346 759 (360 858) | 257 412 (315 207) | 294 585 (312 356)   |
| `g1_scalar_mul_base` | 82 634 (93 255)   | 68 930 (73 300)   | 55 579 (66 558)   | 58 888 (65 592)     |

`g1_scalar_mul` is the constant-time 4-bit variable-base window,
`g1_scalar_mul_base` the constant-time `W = 5` fixed-base comb. The field
rows multiply fixed operands passed through `black_box`; the group rows are
serial chains. On `fp_mul` the two s2n columns run the same instruction
sequence, differing in the encoding of 25 `adc`/`sbb $0` instructions, and
measure the same. On `fp_square` the encoded configuration calls the general
multiply and is slower than `bignum_montsqr_p384` by 14 % at the minimum and
22 % at the median. At this noise level the group rows do not separate the
two s2n configurations.

To reproduce, build `cargo build --offline --release -p p384-safe-rust
--example bench` four times, with `P384_NO_CRYPTOPT=1`, with neither
variable set, with `P384_S2N_FIELD=<s2n-bignum>/x86/libs2nbignum.a`, and with
`P384_S2N_FIELD=<path>/bignum_montmul_p384_encoded.s`, copying
`target/release/examples/bench` aside after each build; `FIELD_CONFIG` is not
printed by `bench`, so check the build warning or `nm` for the linked
symbols.
