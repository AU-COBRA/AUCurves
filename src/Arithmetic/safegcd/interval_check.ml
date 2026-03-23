open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string
    "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

(* Bounding box: replace convex hull with 4 corners *)
let bbox_ddset s =
  let elts = DDSet.elements s in
  match elts with
  | [] -> s
  | first :: rest ->
    let g0 = fst first and f0 = snd first in
    let gmin = ref g0 and gmax = ref g0 in
    let fmin = ref f0 and fmax = ref f0 in
    List.iter (fun p ->
      let g = fst p and f = snd p in
      if dcompare g !gmin = Lt then gmin := g;
      if dcompare g !gmax = Gt then gmax := g;
      if dcompare f !fmin = Lt then fmin := f;
      if dcompare f !fmax = Gt then fmax := f
    ) rest;
    dDSet_fromList [(!gmin, !fmin); (!gmin, !fmax);
                    (!gmax, !fmin); (!gmax, !fmax)]

(* processDivstep with bbox instead of convexHull *)
let process_interval m s =
  let f kv = [even_map kv; odd_map kv] in
  let s1 = state_fromList (List.concat_map f (ZMap.elements s)) in
  let g kv =
    let k = fst kv and v = snd kv in
    if narrow m v then []
    else [(k, bbox_ddset v)]
  in
  state_fromList (List.concat_map g (ZMap.elements s1))

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 1078 in

  (* Exact *)
  Printf.eprintf "Exact N=%d...\n%!" n;
  let se = ref state0 in
  let t0 = Unix.gettimeofday () in
  for _ = 1 to n do se := processDivstep bls12_p !se done;
  let t1 = Unix.gettimeofday () in
  Printf.eprintf "Exact: %.1fs empty=%b\n%!" (t1-.t0) (ZMap.is_empty !se);

  (* Interval *)
  Printf.eprintf "Interval N=%d...\n%!" n;
  let si = ref state0 in
  let t2 = Unix.gettimeofday () in
  for i = 1 to n do
    si := process_interval bls12_p !si;
    if i mod 200 = 0 || i >= n-5 then
      let nk = List.length (ZMap.elements !si) in
      Printf.eprintf "  step %d: keys=%d empty=%b\n%!" i nk (ZMap.is_empty !si)
  done;
  let t3 = Unix.gettimeofday () in
  Printf.eprintf "Interval: %.1fs empty=%b\n%!" (t3-.t2) (ZMap.is_empty !si);

  Printf.printf "exact_empty=%b interval_empty=%b\n" (ZMap.is_empty !se) (ZMap.is_empty !si)
