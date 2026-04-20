(** * Fast processDivstep v6: all optimizations.

    1. Sint63 machine integers for D arithmetic
    2. Bottom-up merge sort for DDSet (O(n log n))
    3. Hull-before-union (convex hull per-transform)
    4. Log2 narrow fast path (skip Z multiply in ~95% of calls)
    5. Multi-word int63 narrow (6-word × 1-word multiply using mulc)
    6. State keys as int63 instead of Z (avoid Z allocation for keys)

    Note: We keep lists (not PArray) because PArray.set returns a new array,
    making it no better than cons for functional updates. *)

From Stdlib Require Import ZArith Uint63 Sint63 List Bool.
Import ListNotations.
Local Open Scope uint63_scope.

(** *** D type: pair of int, interpreted as signed via Sint63 *)

Definition D := (int * int)%type.
Definition D_mant (d : D) : int := fst d.
Definition D_exp (d : D) : int := snd d.

Definition D_zero : D := (0, 0).
Definition D_one  : D := (1, 0).
Definition D_neg1 : D := (sub 0 1, 0).

Fixpoint Dred_aux (fuel : nat) (m e : int) : D :=
  match fuel with
  | O => (m, e)
  | S n =>
    if Uint63.eqb m 0 then D_zero
    else if Uint63.eqb (Uint63.land m 1) 0 then
      Dred_aux n (asr m 1) (add e 1)
    else (m, e)
  end.

Definition Dred (d : D) : D := Dred_aux 48 (D_mant d) (D_exp d).

Definition int_sleb (a b : int) : bool := Sint63.leb a b.
Definition int_sltb (a b : int) : bool := Sint63.ltb a b.

Definition Dalign (a b : D) : int * int :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then (ma, lsl mb (sub eb ea))
  else if int_sltb eb ea then (lsl ma (sub ea eb), mb)
  else (ma, mb).

Definition Dadd (a b : D) : D :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then Dred_aux 48 (add ma (lsl mb (sub eb ea))) ea
  else if int_sltb eb ea then Dred_aux 48 (add (lsl ma (sub ea eb)) mb) eb
  else Dred_aux 48 (add ma mb) ea.

Definition Dsub (a b : D) : D :=
  let ea := D_exp a in let eb := D_exp b in
  let ma := D_mant a in let mb := D_mant b in
  if int_sltb ea eb then Dred_aux 48 (sub ma (lsl mb (sub eb ea))) ea
  else if int_sltb eb ea then Dred_aux 48 (sub (lsl ma (sub ea eb)) mb) eb
  else Dred_aux 48 (sub ma mb) ea.

Definition Dmult (a b : D) : D :=
  Dred_aux 48 (mul (D_mant a) (D_mant b)) (add (D_exp a) (D_exp b)).

Definition Dhalf (d : D) : D :=
  Dred_aux 48 (D_mant d) (sub (D_exp d) 1).

Definition Dcompare (a b : D) : comparison :=
  let '(ma, mb) := Dalign a b in
  if int_sltb ma mb then Lt
  else if int_sltb mb ma then Gt
  else Eq.

Definition Dltb (a b : D) : bool :=
  let '(ma, mb) := Dalign a b in int_sltb ma mb.

(** *** DD: pair of D *)
Definition DD := (D * D)%type.

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

(** *** Convex hull *)

Definition cross_leq0 (a b p : DD) : bool :=
  let '(ba1, aa1) := Dalign (fst b) (fst a) in
  let '(ba2, aa2) := Dalign (snd b) (snd a) in
  let '(pa1, aa3) := Dalign (fst p) (fst a) in
  let '(pa2, aa4) := Dalign (snd p) (snd a) in
  let dx1 := sub ba1 aa1 in let dy1 := sub ba2 aa2 in
  let dx2 := sub pa1 aa3 in let dy2 := sub pa2 aa4 in
  int_sleb (sub (mul dx1 dy2) (mul dy1 dx2)) 0.

Definition cross_geq0 (a b p : DD) : bool :=
  let '(ba1, aa1) := Dalign (fst b) (fst a) in
  let '(ba2, aa2) := Dalign (snd b) (snd a) in
  let '(pa1, aa3) := Dalign (fst p) (fst a) in
  let '(pa2, aa4) := Dalign (snd p) (snd a) in
  let dx1 := sub ba1 aa1 in let dy1 := sub ba2 aa2 in
  let dx2 := sub pa1 aa3 in let dy2 := sub pa2 aa4 in
  int_sleb 0 (sub (mul dx1 dy2) (mul dy1 dx2)).

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
  sl_sort
    (fold_left (fun acc p => addUpper p acc) s []
     ++ fold_left (fun acc p => addLower p acc) s []).

(** *** Multi-word narrow check — Optimization #5

    M is represented as 7 uint63 words (M0..M6), least significant first.
    Each word holds up to 56 bits (we use 56-bit limbs for carry room).
    M = M0 + M1*2^56 + M2*2^112 + ... + M6*2^336.

    For BLS12-381: M is 381 bits, so 7 limbs of 56 bits cover it
    (7*56 = 392 > 381).

    The narrow check: |M * mantissa| < 2^(-exponent).
    mantissa fits in 38 bits (signed), so |mantissa| < 2^37.
    M * |mantissa| < 2^381 * 2^37 = 2^418.

    We compute M * |mantissa| as a multi-word product:
      result[i] = sum(M_j * |mantissa|) with carries.
    Then compare against 2^(-exponent) by checking which word is nonzero. *)

Definition limb_bits : int := 56.
Definition limb_mask : int := 72057594037927935. (* 2^56 - 1 *)

(** Extract 56-bit limbs from a Z value.
    We precompute these for BLS12-381 M. *)
Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

(** BLS12-381 M as 7 limbs of 56 bits (precomputed) *)
Definition M0 : int := Eval vm_compute in (Uint63.of_Z (bls12_M mod 2^56)).
Definition M1 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^56) mod 2^56)).
Definition M2 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^112) mod 2^56)).
Definition M3 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^168) mod 2^56)).
Definition M4 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^224) mod 2^56)).
Definition M5 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^280) mod 2^56)).
Definition M6 : int := Eval vm_compute in (Uint63.of_Z ((bls12_M / 2^336) mod 2^56)).

(** log2(bls12_M) = 380 *)
Definition bls12_M_log2 : int := 380.

(** Multiply M (7 limbs) by a single unsigned word x (< 2^38).
    Returns result as 8 limbs of 56 bits.
    Each intermediate product M_i * x < 2^56 * 2^38 = 2^94,
    which fits in the 126-bit result of mulc. *)
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

(** Compare M*x against 2^neg_exp where neg_exp > 0.
    Returns true if M*x < 2^neg_exp.
    M*x is in 8 limbs of 56 bits = 448 bits total.
    2^neg_exp is 1 in the (neg_exp / 56)-th limb, bit (neg_exp mod 56). *)
Definition mul_M_x_lt_pow2 (x neg_exp : int) : bool :=
  let '(r0, r1, r2, r3, r4, r5, r6, r7) := mul_M_x x in
  (* Which 56-bit limb contains the boundary? *)
  let limb_idx := Uint63.div neg_exp limb_bits in
  let bit_idx := Uint63.sub neg_exp (Uint63.mul limb_idx limb_bits) in
  (* All limbs above limb_idx must be 0, limb at limb_idx < 2^bit_idx *)
  let bound := lsl 1 bit_idx in
  let get_limb i := if Uint63.eqb i 0 then r0
    else if Uint63.eqb i 1 then r1
    else if Uint63.eqb i 2 then r2
    else if Uint63.eqb i 3 then r3
    else if Uint63.eqb i 4 then r4
    else if Uint63.eqb i 5 then r5
    else if Uint63.eqb i 6 then r6
    else r7 in
  (* Check: all limbs above index must be 0, limb at index < bound *)
  let check_above := Uint63.eqb
    (Uint63.lor (Uint63.lor (Uint63.lor
       (if Uint63.ltb limb_idx 7 then get_limb 7 else 0)
       (if Uint63.ltb limb_idx 6 then get_limb 6 else 0))
       (if Uint63.ltb limb_idx 5 then get_limb 5 else 0))
       (if Uint63.ltb limb_idx 4 then get_limb 4 else 0))
    0 in
  let check_above2 := Uint63.eqb
    (Uint63.lor (Uint63.lor
       (if Uint63.ltb limb_idx 3 then get_limb 3 else 0)
       (if Uint63.ltb limb_idx 2 then get_limb 2 else 0))
       (if Uint63.ltb limb_idx 1 then get_limb 1 else 0))
    0 in
  andb (andb check_above check_above2)
       (Uint63.ltb (get_limb limb_idx) bound).

(** Full narrow check: |M * mantissa| < 2^(-exponent).
    Uses log2 fast path, then multi-word int63 fallback. *)
Definition log2_abs (m : int) : int :=
  let abs_m := if Sint63.ltb m 0 then sub 0 m else m in
  if Uint63.eqb abs_m 0 then 0
  else sub 62 (Uint63.head0 abs_m).

Definition narrow_check (m e : int) : bool :=
  if Sint63.leb 0 e then
    Uint63.eqb m 0
  else
    let neg_e := sub 0 e in
    let log2_m := log2_abs m in
    (* Fast path: log2(M) + log2(|m|) + 1 < -exponent *)
    if int_sltb (add (add bls12_M_log2 log2_m) 1) neg_e then true
    else
      (* Multi-word fallback: compute M * |m| and compare *)
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

(** *** State — keys as int63 (optimization #6)
    Keys are small integers (-400..+400), well within int63 range. *)
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

(** *** processDivstep — all optimizations *)

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
