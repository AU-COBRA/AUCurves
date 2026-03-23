(** * Fast processDivstep v2: merge sort instead of insertion sort.

    Same as divsteps_fast.v but replaces O(n²) insertion sort with
    O(n log n) merge sort for DDSet construction. This is the main
    bottleneck identified in profiling. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* === D type: same as divsteps_fast === *)
Record D := Dmake { Dmantissa : Z; Dexponent : Z }.
Definition D_zero := Dmake 0 0.
Definition D_one := Dmake 1 0.
Definition D_from_Z (z : Z) := Dmake z 0.
Fixpoint DredH (p : positive) (z : Z) : positive * Z :=
  match p with xO x => DredH x (Z.succ z) | _ => (p, z) end.
Definition Dred (a : D) : D :=
  match Dmantissa a with
  | Z0 => D_from_Z 0
  | Zpos p => let '(p', e') := DredH p (Dexponent a) in Dmake (Zpos p') e'
  | Zneg p => let '(p', e') := DredH p (Dexponent a) in Dmake (Zneg p') e'
  end.
Definition Dalign (a b : D) : Z * Z * Z :=
  match Dexponent a - Dexponent b with
  | Zpos d => (Z.shiftl (Dmantissa a) (Zpos d), Dmantissa b, Dexponent b)
  | Z0 => (Dmantissa a, Dmantissa b, Dexponent b)
  | Zneg d => (Dmantissa a, Z.shiftl (Dmantissa b) (Zpos d), Dexponent a)
  end.
Definition Dadd (a b : D) := let '(ma, mb, e) := Dalign a b in Dred (Dmake (ma + mb) e).
Definition Dsub (a b : D) := let '(ma, mb, e) := Dalign a b in Dred (Dmake (ma - mb) e).
Definition Dmult (a b : D) := Dred (Dmake (Dmantissa a * Dmantissa b) (Dexponent a + Dexponent b)).
Definition Dhalf (d : D) := Dred (Dmake (Dmantissa d) (Dexponent d - 1)).
Definition Dcompare (a b : D) := let '(ma, mb, _) := Dalign a b in Z.compare ma mb.
Definition Dltb (a b : D) := match Dcompare a b with Lt => true | _ => false end.

(* === DD type === *)
Definition DD := (D * D)%type.
Definition DD_compare (a b : DD) :=
  match Dcompare (fst a) (fst b) with Eq => Dcompare (snd a) (snd b) | c => c end.
Definition DD_leb (a b : DD) := match DD_compare a b with Gt => false | _ => true end.

(* === Merge with dedup (fuel = total length bound) === *)
Fixpoint merge (l1 l2 : list DD) (fuel : nat) : list DD :=
  match fuel with O => [] | S n =>
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 =>
    match DD_compare h1 h2 with
    | Lt => h1 :: merge t1 l2 n
    | Eq => h1 :: merge t1 t2 n
    | Gt => h2 :: merge l1 t2 n
    end
  end end.

(* === Top-down merge sort (fuel = length for termination) === *)
Fixpoint merge_sort_aux (l : list DD) (len : nat) : list DD :=
  match len with
  | O => []
  | S O => match l with [] => [] | h :: _ => [h] end
  | _ =>
    let half := Nat.div len 2 in
    let l1 := firstn half l in
    let l2 := skipn half l in
    merge (merge_sort_aux l1 half) (merge_sort_aux l2 (len - half)) len
  end.

Definition merge_sort (l : list DD) : list DD :=
  merge_sort_aux l (length l).

(* === Set operations using merge sort === *)
Definition sl_fromList (l : list DD) : list DD := merge_sort l.
Definition sl_map (f : DD -> DD) (s : list DD) : list DD := merge_sort (map f s).
Definition sl_union (a b : list DD) : list DD := merge a b (length a + length b).
Definition sl_min (s : list DD) := match s with [] => None | h :: _ => Some h end.
Definition sl_max (s : list DD) := match s with [] => None | _ => Some (last s (D_zero, D_zero)) end.

(* === Convex hull === *)
Fixpoint addUpperPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    let '(oa, ob, _) := Dalign (fst b) (fst a) in
    let '(oc, od, _) := Dalign (snd b) (snd a) in
    let '(oe, of_, _) := Dalign (fst p) (fst a) in
    let '(og, oh, _) := Dalign (snd p) (snd a) in
    if Z.leb ((oa - ob) * (og - oh) - (oc - od) * (oe - of_)) 0
    then addUpperPoint p rest
    else p :: hull
  end.

Fixpoint addLowerPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if DD_leb h p then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    let '(oa, ob, _) := Dalign (fst b) (fst a) in
    let '(oc, od, _) := Dalign (snd b) (snd a) in
    let '(oe, of_, _) := Dalign (fst p) (fst a) in
    let '(og, oh, _) := Dalign (snd p) (snd a) in
    if Z.leb 0 ((oa - ob) * (og - oh) - (oc - od) * (oe - of_))
    then addLowerPoint p rest
    else p :: hull
  end.

Definition convexHull (s : list DD) : list DD :=
  sl_fromList
    (fold_left (fun acc p => addUpperPoint p acc) s []
     ++ fold_left (fun acc p => addLowerPoint p acc) s []).

(* === Narrow === *)
Definition narrow (M : Z) (s : list DD) : bool :=
  match sl_min s, sl_max s with
  | Some (l, _), Some (h, _) =>
    let ml := Dmult (D_from_Z M) l in
    let mh := Dmult (D_from_Z M) h in
    Dltb (Dmake (-1) 0) ml && Dltb mh (Dmake 1 0)
  | _, _ => true
  end.

(* === Transforms === *)
Definition even_trans (p : DD) : DD :=
  let '(g, f) := p in (Dhalf g, f).
Definition odd_pos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dsub g f)), g).
Definition odd_nonpos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dadd g f)), f).

(* === State === *)
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

(* === processDivstep === *)
Definition even_map (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in (1 + k, sl_map even_trans v).
Definition odd_map (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in
  if (0 <? k)%Z
  then (1 - k, sl_map odd_pos_trans v)
  else (1 + k, sl_map odd_nonpos_trans v).

Definition processDivstep (M : Z) (s : State) : State :=
  let f kv := [even_map kv; odd_map kv] in
  let s1 := State_fromList (flat_map f s) in
  let g kv :=
    let '(k, v) := kv in
    if narrow M v then [] else [(k, convexHull v)]
  in State_fromList (flat_map g s1).

(* === Certificate === *)
Definition set0 : list DD := sl_fromList [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1, set0)].
Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
