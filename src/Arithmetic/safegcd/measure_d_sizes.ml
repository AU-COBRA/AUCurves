open Divstep_extracted

let bls12_p =
  Big_int_Z.big_int_of_string
    "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

let max_d_bits state =
  let max_m = ref 0 and max_e = ref 0 in
  List.iter (fun (_, s) ->
    List.iter (fun (g, f) ->
      let gm = Big_int_Z.num_digits_big_int g.dmantissa in
      let ge = Big_int_Z.num_digits_big_int g.dexponent in
      let fm = Big_int_Z.num_digits_big_int f.dmantissa in
      let fe = Big_int_Z.num_digits_big_int f.dexponent in
      max_m := Stdlib.max !max_m (Stdlib.max gm fm);
      max_e := Stdlib.max !max_e (Stdlib.max ge fe)
    ) (DDSet.elements s)
  ) (ZMap.elements state);
  (!max_m, !max_e)

let () =
  let state = ref state0 in
  for i = 1 to 1078 do
    state := processDivstep bls12_p !state;
    if i mod 100 = 0 || i = 1078 then begin
      let (mb, eb) = max_d_bits !state in
      Printf.printf "Step %4d: max_mantissa_bits=%d max_exponent_bits=%d\n%!" i mb eb
    end
  done
