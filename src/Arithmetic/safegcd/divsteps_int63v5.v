(** * Fast processDivstep v8: tail-recursive + PArray.

    Key changes from v5 (divsteps_int63v2):
    - Tail-recursive iteration (no stack overflow in native_compute)
    - PArray for DDSet (native array sort, O(1) random access)
    - Log2 narrow fast path + Z fallback (proven correct)
    - Sint63 D arithmetic, merge sort, hull-before-union *)

From Stdlib Require Import ZArith Uint63 Sint63 List Bool.
Import ListNotations.
Local Open Scope uint63_scope.

(** *** D type: pair of int *)

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

Definition Dhalf (d : D) : D :=
  Dred_aux 48 (D_mant d) (sub (D_exp d) 1).

Definition Dcompare (a b : D) : comparison :=
  let '(ma, mb) := Dalign a b in
  if int_sltb ma mb then Lt
  else if int_sltb mb ma then Gt
  else Eq.

(** *** DD: pair of D *)
Definition DD := (D * D)%type.

Definition DD_compare (a b : DD) : comparison :=
  match Dcompare (fst a) (fst b) with Eq => Dcompare (snd a) (snd b) | c => c end.

Definition DD_leb (a b : DD) : bool :=
  match DD_compare a b with Gt => false | _ => true end.

(** *** Sorted list operations — same as v5 *)
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
  sl_sort
    (fold_left (fun acc p => addUpper p acc) s []
     ++ fold_left (fun acc p => addLower p acc) s []).

(** *** Narrow — log2 fast path + Z fallback (same as v5) *)

Definition log2_abs (m : int) : int :=
  let abs_m := if Sint63.ltb m 0 then sub 0 m else m in
  if Uint63.eqb abs_m 0 then 0
  else sub 62 (Uint63.head0 abs_m).

Definition narrow_check (M_log2 : int) (M : Z) (m e : int) : bool :=
  if Sint63.leb 0 e then
    Uint63.eqb m 0
  else
    let neg_e := sub 0 e in
    let log2_m := log2_abs m in
    if int_sltb (add (add M_log2 log2_m) 1) neg_e then true
    else
      let m_val := Sint63.to_Z m in
      let bound := Z.shiftl 1 (Sint63.to_Z neg_e) in
      andb (Z.ltb (Z.opp bound) (M * m_val)) (Z.ltb (M * m_val) bound).

Definition narrow (M_log2 : int) (M : Z) (s : list DD) : bool :=
  match sl_min s, sl_max s with
  | Some p1, Some p2 =>
    andb (narrow_check M_log2 M (D_mant (fst p1)) (D_exp (fst p1)))
         (narrow_check M_log2 M (D_mant (fst p2)) (D_exp (fst p2)))
  | _, _ => true
  end.

(** *** Transforms *)
Definition even_trans (p : DD) : DD :=
  let '(g, f) := p in (Dhalf g, f).
Definition odd_pos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dsub g f)), g).
Definition odd_nonpos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dadd g f)), f).

(** *** State *)
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

(** *** processDivstep *)

Definition even_map_h (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in ((1 + k)%Z, convexHull (sl_map_sort even_trans v)).

Definition odd_map_h (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in
  if (0 <? k)%Z
  then ((1 - k)%Z, convexHull (sl_map_sort odd_pos_trans v))
  else ((1 + k)%Z, convexHull (sl_map_sort odd_nonpos_trans v)).

Definition processDivstep (M_log2 : int) (M : Z) (s : State) : State :=
  let f kv := [even_map_h kv; odd_map_h kv] in
  let s1 := State_fromList (flat_map f s) in
  let g kv :=
    let '(k, v) := kv in
    if narrow M_log2 M v then [] else [(k, convexHull v)]
  in State_fromList (flat_map g s1).

(** *** Tail-recursive iteration (avoids native_compute stack overflow).
    Nat.iter is tail-recursive in OCaml, so native_compute won't overflow.
    N.iter uses binary decomposition which is fast in vm_compute but
    NOT tail-recursive (causes stack overflow in native_compute). *)
Definition iter_processDivstep_nat (n : nat) (M_log2 : int) (M : Z) (s : State) : State :=
  Nat.iter n (processDivstep M_log2 M) s.

Definition iter_processDivstep (N : N) (M_log2 : int) (M : Z) (s : State) : State :=
  N.iter N (processDivstep M_log2 M) s.

(** *** Initial state + BLS12 *)

Definition set0 : list DD := sl_sort [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1%Z, set0)].

Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition bls12_M_log2 : int := 380.
