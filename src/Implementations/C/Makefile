CC = gcc
CFLAGS = -std=c11 -O2 -Wall -Wno-implicit-function-declaration -Wno-unused-function
CFLAGS_BENCH = -std=c11 -O3 -march=native -flto -Wall -Wno-implicit-function-declaration -Wno-unused-function
LDFLAGS = -z noexecstack

# Extracted C code from verified bedrock2 implementation.
# NOTE: bls12_pairing_all.c has been patched to use CryptOpt assembly
# for bls12_mul and bls12_square (formally verified by fiat-crypto
# equivalence checker). The unpatched baseline is in bls12_pairing_all_baseline.c.
PAIRING_SRC = bls12_pairing_all.c
TEST_SRC = test_pairing.c
BENCH_SRC = bench_pairing.c
TEST_BIN = test_pairing
BENCH_BIN = bench_pairing

NASM = nasm
NASMFLAGS = -f elf64

# CryptOpt assembly files (formally verified by fiat-crypto equivalence checker)
CRYPTOPT_MUL_ASM = cryptopt/fiat_bls12_381_p_mul.asm
CRYPTOPT_SQR_ASM = cryptopt/fiat_bls12_381_p_square.asm
CRYPTOPT_OBJS = cryptopt/fiat_bls12_381_p_mul.o cryptopt/fiat_bls12_381_p_square.o

.PHONY: all test bench clean extract

all: $(TEST_BIN) $(BENCH_BIN)

# Assemble CryptOpt-generated assembly
cryptopt/fiat_bls12_381_p_mul.o: $(CRYPTOPT_MUL_ASM)
	$(NASM) $(NASMFLAGS) -o $@ $<

cryptopt/fiat_bls12_381_p_square.o: $(CRYPTOPT_SQR_ASM)
	$(NASM) $(NASMFLAGS) -o $@ $<

# BY inversion compiled separately to avoid bloating the main TU
bls12_by_inv.o: bls12_by_inv.c
	$(CC) $(CFLAGS_BENCH) -c -o $@ $<

# Build test binary
$(TEST_BIN): $(TEST_SRC) $(PAIRING_SRC) bls12_fp2_stubs.c bls12_by_inv.o $(CRYPTOPT_OBJS)
	$(CC) $(CFLAGS) -o $@ $(TEST_SRC) bls12_by_inv.o $(CRYPTOPT_OBJS) $(LDFLAGS)

# Build benchmark binary (O3 + march=native for realistic perf)
$(BENCH_BIN): $(BENCH_SRC) $(PAIRING_SRC) bls12_fp2_stubs.c bls12_by_inv.o $(CRYPTOPT_OBJS)
	$(CC) $(CFLAGS_BENCH) -o $@ $(BENCH_SRC) bls12_by_inv.o $(CRYPTOPT_OBJS) $(LDFLAGS)

test: $(TEST_BIN)
	./$(TEST_BIN)

bench: $(BENCH_BIN)
	./$(BENCH_BIN)

# Re-extract C code from Coq (requires compiled .vo files)
# NOTE: After re-extraction, the CryptOpt patch must be re-applied.
# The patch replaces the bls12_mul/bls12_square function bodies with
# calls to the CryptOpt assembly (fiat_bls12_381_p_mul/square).
extract:
	cd ../../../fiat-crypto && \
	ROCQPATH=$OPAM_ROOT/rocq-9/lib/coq/user-contrib \
	$OPAM_ROOT/rocq-9/bin/coqc -Q src Crypto \
	src/Bedrock/Field/Synthesis/Examples/BLS12_Extract.v && \
	sed '1d;$$d' bls12_pairing_all.out | \
	sed 's/^     = "//;s/"$$//;s/\\n/\n/g;s/""/"/g' > \
	../../src/Implementations/C/bls12_pairing_all.c

clean:
	rm -f $(TEST_BIN) $(BENCH_BIN) bench_baseline bench_pairing_cryptopt test_pairing_debug *.o cryptopt/*.o
