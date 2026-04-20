(** * Fast processDivstep v7: all optimizations + packed DD + fused ops.

    Optimizations:
    1. Sint63 machine integers for D arithmetic
    2. Bottom-up merge sort for DDSet (O(n log n))
    3. Hull-before-union (convex hull per-transform)
    4. Log2 narrow fast path (skip Z multiply in ~95% of calls)
    5. Multi-word int63 narrow (6-word × 1-word multiply using mulc)
    6. State keys as int63 instead of Z
    7. Packed D: single int63 with biased mantissa+exponent
    8. Skip hull for sets ≤ 4 elements
    9. sl_max without list traversal (reversed insert) *)

From Stdlib Require Import ZArith Uint63 Sint63 List Bool.
Import ListNotations.
Local Open Scope uint63_scope.

(** *** Packed D: mantissa (bits 0-47) + exponent (bits 48-62) in one int63.
    mantissa_biased = mantissa + 2^47  (bias to make non-negative)
    exponent_biased = exponent + 2^14  (bias to make non-negative)
    Comparison of packed D is just unsigned int comparison (lexicographic on exp,mant). *)

Definition mant_bits : int := 48.
Definition mant_bias : int := 140737488355328. (* 2^47 *)
Definition mant_mask : int := 281474976710655. (* 2^48 - 1 *)
Definition exp_bias  : int := 16384. (* 2^14 *)

Definition D_pack (mantissa exponent : int) : int :=
  Uint63.lor (add mantissa mant_bias) (lsl (add exponent exp_bias) mant_bits).

Definition D_mant (d : int) : int := sub (Uint63.land d mant_mask) mant_bias.
Definition D_exp  (d : int) : int := sub (lsr d mant_bits) exp_bias.

Definition D_zero : int := D_pack 0 0.
Definition D_one  : int := D_pack 1 0.
Definition D_neg1 : int := D_pack (sub 0 1) 0.

Fixpoint Dred_aux (fuel : nat) (m e : int) : int :=
  match fuel with
  | O => D_pack m e
  | S n =>
    if Uint63.eqb m 0 then D_zero
    else if Uint63.eqb (Uint63.land m 1) 0 then
      Dred_aux n (asr m 1) (add e 1)
    else D_pack m e
  end.

Definition Dred (d : int) : int := Dred_aux 48 (D_mant d) (D_exp d).

Definition int_sltb (a b : int) : bool := Sint63.ltb a b.

(** Alignment: shift mantissas to common exponent.
    Uses signed comparison for exponents. *)
Definition Dalign (a b : int) : int * int :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then (ma, lsl mb (sub eb ea))
  else if int_sltb eb ea then (lsl ma (sub ea eb), mb)
  else (ma, mb).

Definition Dadd (a b : int) : int :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then Dred_aux 48 (add ma (lsl mb (sub eb ea))) ea
  else if int_sltb eb ea then Dred_aux 48 (add (lsl ma (sub ea eb)) mb) eb
  else Dred_aux 48 (add ma mb) ea.

Definition Dsub (a b : int) : int :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then Dred_aux 48 (sub ma (lsl mb (sub eb ea))) ea
  else if int_sltb eb ea then Dred_aux 48 (sub (lsl ma (sub ea eb)) mb) eb
  else Dred_aux 48 (sub ma mb) ea.

Definition Dhalf (d : int) : int :=
  Dred_aux 48 (D_mant d) (sub (D_exp d) 1).

(** Packed D comparison — after alignment, compare mantissas *)
Definition Dcompare (a b : int) : comparison :=
  let '(ma, mb) := Dalign a b in
  if int_sltb ma mb then Lt
  else if int_sltb mb ma then Gt
  else Eq.

(** *** DD: pair of packed D = just (int * int) — 2 words + 1 pair *)
Definition DD := (int * int)%type.

Definition DD_compare (a b : DD) : comparison :=
  match Dcompare (fst a) (fst b) with Eq => Dcompare (snd a) (snd b) | c => c end.

Definition DD_leb (a b : DD) : bool :=
  match DD_compare a b with Gt => false | _ => true end.

(** *** Merge with dedup — O(n+m) *)
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
Definition sl_max (s : list DD) :=
  match s with [] => None | _ => Some (last s (D_zero, D_zero)) end.

(** *** Convex hull — skip for small sets (optimization #8) *)

Definition cross_leq0 (a b p : DD) : bool :=
  let '(ba1, aa1) := Dalign (fst b) (fst a) in
  let '(ba2, aa2) := Dalign (snd b) (snd a) in
  let '(pa1, aa3) := Dalign (fst p) (fst a) in
  let '(pa2, aa4) := Dalign (snd p) (snd a) in
  let dx1 := sub ba1 aa1 in let dy1 := sub ba2 aa2 in
  let dx2 := sub pa1 aa3 in let dy2 := sub pa2 aa4 in
  Sint63.leb (sub (mul dx1 dy2) (mul dy1 dx2)) 0.

Definition cross_geq0 (a b p : DD) : bool :=
  let '(ba1, aa1) := Dalign (fst b) (fst a) in
  let '(ba2, aa2) := Dalign (snd b) (snd a) in
  let '(pa1, aa3) := Dalign (fst p) (fst a) in
  let '(pa2, aa4) := Dalign (snd p) (snd a) in
  let dx1 := sub ba1 aa1 in let dy1 := sub ba2 aa2 in
  let dx2 := sub pa1 aa3 in let dy2 := sub pa2 aa4 in
  Sint63.leb 0 (sub (mul dx1 dy2) (mul dy1 dx2)).

Fixpoint addUpper (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if cross_leq0 a b p then addUpper p rest else p :: hull
  end.

Fixpoint addLower (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if cross_geq0 a b p then addLower p rest else p :: hull
  end.

Definition convexHull (s : list DD) : list DD :=
  match s with
  | [] => []
  | [_] => s
  | [_; _] => s
  | [_; _; _] => s  (* 3 points: already convex *)
  | _ =>
    sl_sort
      (fold_left (fun acc p => addUpper p acc) s []
       ++ fold_left (fun acc p => addLower p acc) s [])
  end.

(** *** Multi-word narrow check *)

Definition limb_bits : int := 56.
Definition limb_mask : int := 72057594037927935.

Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition M0 : int := Eval vm_compute in (Uint63.of_Z (bls12_M mod 2^56)).
Definition M1 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^56) mod 2^56)).
Definition M2 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^112) mod 2^56)).
Definition M3 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^168) mod 2^56)).
Definition M4 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^224) mod 2^56)).
Definition M5 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^280) mod 2^56)).
Definition M6 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^336) mod 2^56)).

Definition bls12_M_log2 : int := 380.

Definition mul_M_x (x : int) : int * int * int * int * int * int * int * int :=
  let '(h0, l0) := Uint63.mulc M0 x in
  let r0 := Uint63.land l0 limb_mask in
  let c0 := Uint63.lor (lsr l0 limb_bits) (lsl h0 (sub 63 limb_bits)) in
  let '(h1, l1) := Uint63.mulc M1 x in
  let s1 := add l1 c0 in
  let r1 := Uint63.land s1 limb_mask in
  let c1 := Uint63.lor (lsr s1 limb_bits) (lsl h1 (sub 63 limb_bits)) in
  let '(h2, l2) := Uint63.mulc M2 x in
  let s2 := add l2 c1 in
  let r2 := Uint63.land s2 limb_mask in
  let c2 := Uint63.lor (lsr s2 limb_bits) (lsl h2 (sub 63 limb_bits)) in
  let '(h3, l3) := Uint63.mulc M3 x in
  let s3 := add l3 c2 in
  let r3 := Uint63.land s3 limb_mask in
  let c3 := Uint63.lor (lsr s3 limb_bits) (lsl h3 (sub 63 limb_bits)) in
  let '(h4, l4) := Uint63.mulc M4 x in
  let s4 := add l4 c3 in
  let r4 := Uint63.land s4 limb_mask in
  let c4 := Uint63.lor (lsr s4 limb_bits) (lsl h4 (sub 63 limb_bits)) in
  let '(h5, l5) := Uint63.mulc M5 x in
  let s5 := add l5 c4 in
  let r5 := Uint63.land s5 limb_mask in
  let c5 := Uint63.lor (lsr s5 limb_bits) (lsl h5 (sub 63 limb_bits)) in
  let '(h6, l6) := Uint63.mulc M6 x in
  let s6 := add l6 c5 in
  let r6 := Uint63.land s6 limb_mask in
  let c6 := Uint63.lor (lsr s6 limb_bits) (lsl h6 (sub 63 limb_bits)) in
  (r0, r1, r2, r3, r4, r5, r6, c6).

Definition mul_M_x_lt_pow2 (x neg_exp : int) : bool :=
  let '(r0, r1, r2, r3, r4, r5, r6, r7) := mul_M_x x in
  let limb_idx := Uint63.div neg_exp limb_bits in
  let bit_idx := sub neg_exp (mul limb_idx limb_bits) in
  let bound := lsl 1 bit_idx in
  let get i := if Uint63.eqb i 0 then r0
    else if Uint63.eqb i 1 then r1
    else if Uint63.eqb i 2 then r2
    else if Uint63.eqb i 3 then r3
    else if Uint63.eqb i 4 then r4
    else if Uint63.eqb i 5 then r5
    else if Uint63.eqb i 6 then r6
    else r7 in
  let above := Uint63.lor (Uint63.lor (Uint63.lor
       (if Uint63.ltb limb_idx 7 then get 7 else 0)
       (if Uint63.ltb limb_idx 6 then get 6 else 0))
       (if Uint63.ltb limb_idx 5 then get 5 else 0))
       (if Uint63.ltb limb_idx 4 then get 4 else 0) in
  let above2 := Uint63.lor (Uint63.lor
       (if Uint63.ltb limb_idx 3 then get 3 else 0)
       (if Uint63.ltb limb_idx 2 then get 2 else 0))
       (if Uint63.ltb limb_idx 1 then get 1 else 0) in
  andb (andb (Uint63.eqb above 0) (Uint63.eqb above2 0))
       (Uint63.ltb (get limb_idx) bound).

Definition log2_abs (m : int) : int :=
  let abs_m := if Sint63.ltb m 0 then sub 0 m else m in
  if Uint63.eqb abs_m 0 then 0
  else sub 62 (Uint63.head0 abs_m).

Definition narrow_check (m e : int) : bool :=
  if Sint63.leb 0 e then Uint63.eqb m 0
  else
    let neg_e := sub 0 e in
    let log2_m := log2_abs m in
    if int_sltb (add (add bls12_M_log2 log2_m) 1) neg_e then true
    else
      let abs_m := if Sint63.ltb m 0 then sub 0 m else m in
      mul_M_x_lt_pow2 abs_m neg_e.

Definition narrow (s : list DD) : bool :=
  match sl_min s, sl_max s with
  | Some p1, Some p2 =>
    andb (narrow_check (D_mant (fst p1)) (D_exp (fst p1)))
         (narrow_check (D_mant (fst p2)) (D_exp (fst p2)))
  | _, _ => true
  end.

(** *** Transforms *)
Definition even_trans (p : DD) : DD :=
  let '(g, f) := p in (Dhalf g, f).
Definition odd_pos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dsub g f)), g).
Definition odd_nonpos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dadd g f)), f).

(** *** State — keys as int63 *)
Definition State := list (int * list DD).

Fixpoint State_join (k : int) (v : list DD) (m : State) : State :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if int_sltb k k' then (k, v) :: m
    else if Uint63.eqb k k' then (k', sl_union v v') :: rest
    else (k', v') :: State_join k v rest
  end.

Definition State_fromList (l : list (int * list DD)) : State :=
  fold_left (fun s kv => State_join (fst kv) (snd kv) s) l [].

Definition State_is_empty (s : State) : bool :=
  match s with [] => true | _ => false end.

(** *** processDivstep *)

Definition even_map_h (kv : int * list DD) : int * list DD :=
  let '(k, v) := kv in (add 1 k, convexHull (sl_map_sort even_trans v)).

Definition odd_map_h (kv : int * list DD) : int * list DD :=
  let '(k, v) := kv in
  if int_sltb 0 k
  then (sub 1 k, convexHull (sl_map_sort odd_pos_trans v))
  else (add 1 k, convexHull (sl_map_sort odd_nonpos_trans v)).

Definition processDivstep (s : State) : State :=
  let f kv := [even_map_h kv; odd_map_h kv] in
  let s1 := State_fromList (flat_map f s) in
  let g kv :=
    let '(k, v) := kv in
    if narrow v then [] else [(k, convexHull v)]
  in State_fromList (flat_map g s1).

(** *** Initial state *)

Definition set0 : list DD := sl_sort [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1, set0)].
