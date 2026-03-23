open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

let () =
  let n_total = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1075 in
  let k_step = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 50 in
  Printf.eprintf "N=%d K=%d\n%!" n_total k_step;
  let state = ref state0 in
  let step = ref 0 in
  while !step < n_total do
    let next = Stdlib.min (!step + k_step) n_total in
    let t0 = Unix.gettimeofday () in
    for _ = 1 to (next - !step) do
      state := processDivstep bls12_p !state
    done;
    let t1 = Unix.gettimeofday () in
    let empty = ZMap.is_empty !state in
    Printf.eprintf "Step %d->%d: %.1fs empty=%b\n%!" !step next (t1-.t0) empty;
    if empty then (Printf.printf "CONVERGED at N=%d\n" next; exit 0);
    step := next
  done;
  Printf.printf "NOT CONVERGED after %d steps\n" n_total; exit 1
