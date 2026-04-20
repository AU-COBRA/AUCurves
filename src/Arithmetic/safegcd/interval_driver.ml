(* Measure exact state dimensions at each checkpoint *)

open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string
    "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

let () =
  let state = ref state0 in
  for i = 1 to 1078 do
    state := processDivstep bls12_p !state;
    if i mod 50 = 0 || i >= 1070 then begin
      let elts = ZMap.elements !state in
      let nkeys = List.length elts in
      let total_pts = List.fold_left (fun acc (_, s) ->
        acc + List.length (DDSet.elements s)
      ) 0 elts in
      let max_pts = List.fold_left (fun acc (_, s) ->
        Stdlib.max acc (List.length (DDSet.elements s))
      ) 0 elts in
      Printf.printf "Step %4d: keys=%3d total_pts=%6d max_pts=%4d empty=%b\n%!"
        i nkeys total_pts max_pts (ZMap.is_empty !state)
    end
  done
