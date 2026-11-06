# Map the safe-tower's extern names to the actual symbol providers.
#
# mul    comes from CryptOpt (SMT-validated against fiat-crypto Montgomery).
# square comes from Jasmin -- see below.
# add    comes from Jasmin (bn254_leaves_live.jazz): with the hints chosen
#        from liveness it runs at 6.6 cycles against 9.2 for the Rust stub
#        (rdtsc cycles per call on a serial chain); the all-#[spill]
#        emission runs at 14-16 cycles.
# sub is NOT redirected: Jasmin's sub (10.4 cycles) is still slower than
# the Rust stub (5.5); src/stubs.rs covers it.
#
# Each line is one jmp -- the cost of the indirection is one extra
# branch per leaf call, which the LTO pass eliminates by inlining.
.text

.global _bn254_add
_bn254_add: jmp bn254_add

.global _bn254_mul
_bn254_mul: jmp fiat_bn254_mul

# square comes from Jasmin again (bn254_leaves_live.jazz).  It used to jump to
# Jasmin's `bn254_square`, which suffered the auto-spill problem: every
# register local was #[spill], so it copied its operands to the stack and
# reloaded them (694.7 cycles against 88.9 for CryptOpt's multiply on Zen 4),
# and every carry was a data-dependent branch.  From then until now it was
# routed to CryptOpt's multiply as mul(out, x, x).
#
# The leaf now comes through AdcChain.polish_func_adc (fiat's addcarryx /
# subborrowx windows as #ADCX / #SBB chains, proved by adc_cmd_correct) with
# #[spill] hints chosen from liveness (SpillLiveness.pp_module_live, proved
# inert by pp_module_live_erases).  Measured on this tree's harness
# (rdtsc, serial chain, median of 3 x median of 11 x 10^5 calls, cloud Xeon):
# Jasmin bn254_square 54.6 cycles against 55.2 for CryptOpt mul(x, x)
# (CryptOpt mul: 52.3; Jasmin mul: 55.0, so mul stays on CryptOpt).
# System V: square is (out = rdi, x = rsi), the Jasmin export signature.
.global _bn254_square
_bn254_square: jmp bn254_square
