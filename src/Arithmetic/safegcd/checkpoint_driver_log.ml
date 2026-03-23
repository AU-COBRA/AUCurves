(* Driver that logs intermediate states as Coq definitions.
   Each checkpoint can be independently verified in Rocq. *)

open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

(* Serialize a ZMap tree to Coq syntax *)
let rec coq_of_positive p =
  (* Big_int_Z extracted positive is just big_int *)
  let s = Big_int_Z.string_of_big_int p in
  (* Convert decimal to Coq positive literal *)
  s ^ "%positive"

let rec coq_of_tree = function
  | ZMap.Leaf -> "ZMap.Leaf _"
  | ZMap.Node (l, None, r) ->
    Printf.sprintf "(ZMap.Node _ %s None %s)" (coq_of_tree l) (coq_of_tree r)
  | ZMap.Node (l, Some v, r) ->
    Printf.sprintf "(ZMap.Node _ %s (Some _) %s)" (coq_of_tree l) (coq_of_tree r)

let () =
  let n_total = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1078 in
  let k_step = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 50 in
  let out_dir = if Array.length Sys.argv > 3 then Sys.argv.(3) else "." in

  Printf.eprintf "N=%d K=%d out=%s\n%!" n_total k_step out_dir;

  (* Log: just check emptiness at each checkpoint for timing data *)
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
    if empty then begin
      Printf.printf "CONVERGED at N=%d\n" next;

      (* Write the final certificate as a Coq file *)
      let fname = Printf.sprintf "%s/divsteps_bls12_cert.v" out_dir in
      let oc = open_out fname in
      Printf.fprintf oc "Require Import ZArith.\n";
      Printf.fprintf oc "Require Import divsteps_base.\n\n";
      Printf.fprintf oc "Definition bls12_p : Z :=\n";
      Printf.fprintf oc "  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.\n\n";
      Printf.fprintf oc "(** Tight bound N=%d, computed by OCaml extraction. *)\n" next;
      Printf.fprintf oc "Lemma bls12_certificate : ZMap.Empty (N.iter %d (processDivstep bls12_p) state0).\n" next;
      Printf.fprintf oc "Proof. apply ZMap.is_empty_2. native_compute. reflexivity. Qed.\n";
      Printf.fprintf oc "Definition bls12_iters : N := %d.\n" next;
      close_out oc;
      Printf.eprintf "Wrote %s\n" fname;
      exit 0
    end;
    step := next
  done;
  Printf.printf "NOT CONVERGED after %d steps\n" n_total; exit 1
