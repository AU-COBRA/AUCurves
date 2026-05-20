(* p25519_driver.ml — compute the tight divstep convergence bound for p25519
 *
 * Uses the same extracted [processDivstep] / [state0] from divstep_extracted.ml
 * (which is generated from divsteps_base.v with δ₀=1 in the divstep init).
 *
 * For p25519 = 2^255 - 19, this measures the smallest N such that
 *   N.iter N (processDivstep p25519) state0
 * has an empty hull, i.e. the convex-hull cert succeeds.
 *
 * Reference points from the paper §3.4 (Table 1.2.1):
 *   δ₀=1 + b=256: N = 724 (their H_{724} cert covers all 256-bit inputs)
 *   δ₀=1/2 + b=256: N = 590
 *
 * Since the existing extracted code uses δ₀=1, this driver measures the
 * δ₀=1 cert for the *specific* prime p25519 (not for all 256-bit inputs).
 * The bound for p25519 specifically may be tighter than 724.
 *
 * Usage:
 *   ocamlfind ocamlopt -package zarith -linkpkg \
 *     divstep_extracted.ml p25519_driver.ml -o p25519_driver
 *   ./p25519_driver [N_MAX] [K_STEP]
 *)

open Divstep_extracted

(* p25519 = 2^255 - 19 *)
let p25519 =
  Big_int_Z.big_int_of_string
    "57896044618658097711785492504343953926634992332820282019728792003956564819949"

let () =
  let n_max = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 730 in
  let k_step = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 50 in
  Printf.eprintf "p25519 = 2^255 - 19\n";
  Printf.eprintf "N_MAX = %d, K_STEP = %d\n%!" n_max k_step;
  let state = ref state0 in
  let step = ref 0 in
  while !step < n_max do
    let next = Stdlib.min (!step + k_step) n_max in
    let t0 = Unix.gettimeofday () in
    for _ = 1 to (next - !step) do
      state := processDivstep p25519 !state
    done;
    let t1 = Unix.gettimeofday () in
    let empty = ZMap.is_empty !state in
    Printf.eprintf "Step %d -> %d: %.2fs, empty=%b\n%!" !step next (t1 -. t0) empty;
    if empty then begin
      Printf.printf "CONVERGED for p25519 at N = %d\n" next;
      exit 0
    end;
    step := next
  done;
  Printf.printf "NOT CONVERGED after %d steps\n" n_max;
  exit 1
