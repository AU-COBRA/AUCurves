(* multi_curve_half_driver.ml — measure tight δ₀=1/2 divstep convergence bound
 * via the extracted half-framework (Wuille / EUROCRYPT 2026).
 *
 * Usage: ./multi_curve_half_driver PRIME_DEC NAME [N_MAX] [K_STEP]
 *
 * Paper expects N=590 for any 256-bit prime (Theorem 1 with b=256, δ₀=1/2).
 *)

open Divstep_extracted_half

let () =
  if Array.length Sys.argv < 3 then begin
    Printf.eprintf "Usage: %s PRIME_DEC NAME [N_MAX] [K_STEP]\n" Sys.argv.(0);
    exit 2
  end;
  let p = Big_int_Z.big_int_of_string Sys.argv.(1) in
  let name = Sys.argv.(2) in
  let n_max = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 600 in
  let k_step = if Array.length Sys.argv > 4 then int_of_string Sys.argv.(4) else 25 in
  Printf.eprintf "=== %s (δ₀=1/2) ===\n" name;
  Printf.eprintf "N_MAX = %d, K_STEP = %d\n%!" n_max k_step;
  let state = ref state0_half in
  let step = ref 0 in
  let t0_total = Unix.gettimeofday () in
  while !step < n_max do
    let next = Stdlib.min (!step + k_step) n_max in
    let t0 = Unix.gettimeofday () in
    for _ = 1 to (next - !step) do
      state := processDivstep_half p !state
    done;
    let t1 = Unix.gettimeofday () in
    let empty = ZMap.is_empty !state in
    Printf.eprintf "  %d -> %d: %.2fs empty=%b\n%!" !step next (t1 -. t0) empty;
    if empty then begin
      Printf.printf "%s: CONVERGED at N <= %d (δ₀=1/2, total %.1fs)\n%!"
        name next (Unix.gettimeofday () -. t0_total);
      exit 0
    end;
    step := next
  done;
  Printf.printf "%s: NOT CONVERGED after %d steps (δ₀=1/2)\n" name n_max;
  exit 1
