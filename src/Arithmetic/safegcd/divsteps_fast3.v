(** * Fast processDivstep v3: Uint63 packed D + merge-only sort + hull-before-union.

    Three optimizations over v1:
    1. D packed into single Uint63: mantissa in bits [0..47], exponent in bits [48..62]
    2. No re-sorting after transforms — use merge for union, sort only for hull
    3. ConvexHull applied per-transform BEFORE union (30 vertices, not 500)

    Mantissa range: ≤ 38 bits (signed). Exponent range: ≤ 12 bits.
    Both verified by OCaml extraction measurement. *)

From Stdlib Require Import ZArith Uint63 List Bool.
Import ListNotations.
Local Open Scope Z_scope.

(** *** Packed D: mantissa (bits 0-47) + exponent (bits 48-62) in one Uint63 *)

(** Layout: value = mantissa_biased + exponent_biased * 2^48
    mantissa_biased = mantissa + 2^47  (bias to make non-negative)
    exponent_biased = exponent + 2^14  (bias to make non-negative) *)

Local Open Scope uint63_scope.

Definition mant_bits : int := 48.
Definition mant_bias : int := 140737488355328. (* 2^47 *)
Definition mant_mask : int := 281474976710655. (* 2^48 - 1 *)
Definition exp_bias : int := 16384. (* 2^14 *)

Definition D_pack (mantissa exponent : int) : int :=
  Uint63.lor (mantissa + mant_bias) (Uint63.lsl (exponent + exp_bias) mant_bits).

Definition D_mantissa (d : int) : int := Uint63.sub (Uint63.land d mant_mask) mant_bias.
Definition D_exponent (d : int) : int := Uint63.sub (Uint63.lsr d mant_bits) exp_bias.

Definition D_zero : int := D_pack 0 0.
Definition D_one : int := D_pack 1 0.
Definition D_neg1 : int := D_pack (0 - 1) 0.

(** Normalization: strip trailing zero bits from mantissa *)
(** We use a loop that checks the LSB and shifts right *)
Fixpoint Dred_fuel (fuel : nat) (m e : int) : int :=
  match fuel with
  | O => D_pack m e
  | S n =>
    if m =? 0 then D_zero
    else if Uint63.eqb (Uint63.land m 1) 0 then Dred_fuel n (asr m 1) (e + 1)
    else D_pack m e
  end.

Definition Dred (d : int) : int :=
  Dred_fuel 48 (D_mantissa d) (D_exponent d).

(** Alignment: shift mantissas to common exponent *)
Definition Dalign_cmp (a b : int) : int * int :=
  let ea := D_exponent a in
  let eb := D_exponent b in
  let ma := D_mantissa a in
  let mb := D_mantissa b in
  if ea <? eb then (ma, Uint63.lsl mb (Uint63.sub eb ea))
  else if eb <? ea then (Uint63.lsl ma (Uint63.sub ea eb), mb)
  else (ma, mb).

Definition Dadd (a b : int) : int :=
  let ea := D_exponent a in
  let eb := D_exponent b in
  let ma := D_mantissa a in
  let mb := D_mantissa b in
  if ea <? eb then Dred_fuel 48 (ma + (Uint63.lsl mb (Uint63.sub eb ea))) ea
  else if eb <? ea then Dred_fuel 48 ((Uint63.lsl ma (Uint63.sub ea eb)) + mb) eb
  else Dred_fuel 48 (ma + mb) ea.

Definition Dsub (a b : int) : int :=
  let ea := D_exponent a in
  let eb := D_exponent b in
  let ma := D_mantissa a in
  let mb := D_mantissa b in
  if ea <? eb then Dred_fuel 48 (ma - (Uint63.lsl mb (Uint63.sub eb ea))) ea
  else if eb <? ea then Dred_fuel 48 ((Uint63.lsl ma (Uint63.sub ea eb)) - mb) eb
  else Dred_fuel 48 (ma - mb) ea.

Definition Dmult (a b : int) : int :=
  Dred_fuel 48 (D_mantissa a * D_mantissa b) (D_exponent a + D_exponent b).

Definition Dhalf (d : int) : int :=
  Dred_fuel 48 (D_mantissa d) (D_exponent d - 1).

(** Comparison after alignment *)
Definition Dcompare (a b : int) : comparison :=
  let '(ma, mb) := Dalign_cmp a b in
  if ma <? mb then Lt
  else if mb <? ma then Gt
  else Eq.

Definition Dltb (a b : int) : bool :=
  let '(ma, mb) := Dalign_cmp a b in
  ma <? mb.

Local Close Scope uint63_scope.

(** *** DD: pair of packed D values *)
Definition DD := (int * int)%type.

Definition DD_compare (a b : DD) : comparison :=
  match Dcompare (fst a) (fst b) with Eq => Dcompare (snd a) (snd b) | c => c end.

Definition DD_leb (a b : DD) : bool :=
  match DD_compare a b with Gt => false | _ => true end.

(** *** Sorted list operations using MERGE (not insertion sort) *)

(** Merge two sorted lists with dedup — O(n+m) *)
Fixpoint sl_merge (l1 l2 : list DD) (fuel : nat) : list DD :=
  match fuel with O => [] | S n =>
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 =>
    match DD_compare h1 h2 with
    | Lt => h1 :: sl_merge t1 l2 n
    | Eq => h1 :: sl_merge t1 t2 n
    | Gt => h2 :: sl_merge l1 t2 n
    end
  end end.

Definition sl_union (a b : list DD) : list DD :=
  sl_merge a b (length a + length b).

(** Map + sort: transform each element, then merge-sort the result.
    Top-down merge sort using fuel = length. *)
(** Merge sort with explicit fuel (= log2(length) + 1) *)
Fixpoint msort_pass (pairs : list (list DD)) (fuel : nat) : list DD :=
  match fuel with O => concat pairs | S n =>
  match pairs with
  | [] => []
  | [l] => l
  | l1 :: l2 :: rest =>
    msort_pass (sl_merge l1 l2 (length l1 + length l2) :: rest) n
  end end.

Definition sl_sort (l : list DD) : list DD :=
  msort_pass (map (fun x => [x]) l) (length l).


Definition sl_map_sort (f : DD -> DD) (s : list DD) : list DD :=
  sl_sort (map f s).

Definition sl_min (s : list DD) := match s with [] => None | h :: _ => Some h end.
Definition sl_max (s : list DD) := match s with [] => None | _ => Some (last s (D_zero, D_zero)) end.

(** *** Convex hull — applied to small sets (hull vertices only) *)

Definition cross_sign (a b p : DD) : bool :=
  (* Returns true if cross product (b-a) × (p-a) ≤ 0 *)
  let '(ma1, ma2) := Dalign_cmp (fst b) (fst a) in
  let '(mb1, mb2) := Dalign_cmp (snd b) (snd a) in
  let '(mc1, mc2) := Dalign_cmp (fst p) (fst a) in
  let '(md1, md2) := Dalign_cmp (snd p) (snd a) in
  let dx1 := Uint63.sub ma1 ma2 in
  let dy1 := Uint63.sub mb1 mb2 in
  let dx2 := Uint63.sub mc1 mc2 in
  let dy2 := Uint63.sub md1 md2 in
  Uint63.leb (Uint63.sub (Uint63.mul dx1 dy2) (Uint63.mul dy1 dx2)) 0%uint63.

Definition cross_sign_neg (a b p : DD) : bool :=
  let '(ma1, ma2) := Dalign_cmp (fst b) (fst a) in
  let '(mb1, mb2) := Dalign_cmp (snd b) (snd a) in
  let '(mc1, mc2) := Dalign_cmp (fst p) (fst a) in
  let '(md1, md2) := Dalign_cmp (snd p) (snd a) in
  let dx1 := Uint63.sub ma1 ma2 in
  let dy1 := Uint63.sub mb1 mb2 in
  let dx2 := Uint63.sub mc1 mc2 in
  let dy2 := Uint63.sub md1 md2 in
  Uint63.leb 0%uint63 (Uint63.sub (Uint63.mul dx1 dy2) (Uint63.mul dy1 dx2)).

Fixpoint addUpperPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if cross_sign a b p then addUpperPoint p rest
    else p :: hull
  end.

Fixpoint addLowerPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if cross_sign_neg a b p then addLowerPoint p rest
    else p :: hull
  end.

Definition convexHull (s : list DD) : list DD :=
  sl_sort
    (fold_left (fun acc p => addUpperPoint p acc) s []
     ++ fold_left (fun acc p => addLowerPoint p acc) s []).

(** *** Narrow check — uses Z for M*mantissa (M is 381-bit, doesn't fit Uint63) *)

Definition D_to_Z (d : int) : Z :=
  let m := Uint63.to_Z (D_mantissa d) in
  let e := Uint63.to_Z (D_exponent d) in
  (* Interpret as signed: if m >= 2^47, subtract 2^48 *)
  let ms := if (m >? 140737488355327)%Z then (m - 281474976710656)%Z else m in
  let es := if (e >? 16383)%Z then (e - 32768)%Z else e in
  if (es >=? 0)%Z then (ms * Z.shiftl 1 es)%Z
  else ms. (* for negative exponent, the rational is ms * 2^es < ms *)

Definition narrow (M : Z) (s : list DD) : bool :=
  match sl_min s, sl_max s with
  | Some p1, Some p2 =>
    let lg := fst p1 in
    let hg := fst p2 in
    let lz := D_to_Z lg in
    let hz := D_to_Z hg in
    ((-1 <? M * lz) && (M * hz <? 1))%Z
  | _, _ => true
  end.

(** *** Transforms *)
Definition even_trans (p : DD) : DD :=
  let '(g, f) := p in (Dhalf g, f).
Definition odd_pos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dsub g f)), g).
Definition odd_nonpos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dadd g f)), f).

(** *** State: sorted assoc list keyed by Z (keys are small: -400..+400) *)
Definition State := list (Z * list DD).

Fixpoint State_join (k : Z) (v : list DD) (m : State) : State :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    match Z.compare k k' with
    | Lt => (k, v) :: m
    | Eq => (k', sl_union v v') :: rest
    | Gt => (k', v') :: State_join k v rest
    end
  end.

Definition State_fromList (l : list (Z * list DD)) : State :=
  fold_left (fun s kv => State_join (fst kv) (snd kv) s) l [].

Definition State_is_empty (s : State) : bool :=
  match s with [] => true | _ => false end.

(** *** processDivstep with hull-before-union (optimization 3) *)

Definition even_map_hull (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in (1 + k, convexHull (sl_map_sort even_trans v)).

Definition odd_map_hull (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in
  if (0 <? k)%Z
  then (1 - k, convexHull (sl_map_sort odd_pos_trans v))
  else (1 + k, convexHull (sl_map_sort odd_nonpos_trans v)).

Definition processDivstep (M : Z) (s : State) : State :=
  let f kv := [even_map_hull kv; odd_map_hull kv] in
  let s1 := State_fromList (flat_map f s) in
  let g kv :=
    let '(k, v) := kv in
    if narrow M v then [] else [(k, convexHull v)]
  in State_fromList (flat_map g s1).

(** *** Initial state + certificate *)

Definition set0 : list DD := sl_sort [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1%Z, set0)].

Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
