open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

let () =
  let state = ref state0 in
  let gc0 = Gc.stat () in
  for i = 1 to 1078 do
    state := processDivstep bls12_p !state;
    if i mod 50 = 0 || i = 1078 then begin
      let gc = Gc.stat () in
      let heap_mb = (gc.Gc.heap_words * 8) / (1024*1024) in
      Printf.printf "Step %4d: empty=%b heap=%dMB live_words=%d\n%!"
        i (ZMap.is_empty !state) heap_mb gc.Gc.live_words
    end
  done;
  ignore gc0
