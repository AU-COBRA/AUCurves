(** * Fast processDivstep using sorted lists instead of MSets/FMaps.

    Reimplements the O'Connor divstep convergence checker with:
    - D (dyadic rationals): same Z × Z representation (small values, fast in vm)
    - DDSet: sorted list instead of MSet balanced tree
    - State: sorted association list instead of FMapAVL

    This eliminates tree rebalancing overhead. For the ~500-element sets
    in this computation, sorted lists are competitive with balanced trees
    in vm_compute due to lower per-element overhead. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.

(** *** D type: dyadic rational (same as original) *)

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

(** *** DD: pair of D, with lexicographic comparison *)

Definition DD := (D * D)%type.

Definition DD_compare (a b : DD) :=
  match Dcompare (fst a) (fst b) with Eq => Dcompare (snd a) (snd b) | c => c end.

(** *** Sorted list as set *)

Fixpoint sl_insert (x : DD) (l : list DD) : list DD :=
  match l with
  | [] => [x]
  | h :: t => match DD_compare x h with
    | Lt => x :: l | Eq => l | Gt => h :: sl_insert x t end
  end.

Definition sl_fromList (l : list DD) : list DD :=
  fold_left (fun acc x => sl_insert x acc) l [].

Definition sl_map (f : DD -> DD) (s : list DD) : list DD :=
  sl_fromList (map f s).

Definition sl_union (a b : list DD) : list DD :=
  fold_left (fun acc x => sl_insert x acc) b a.

Definition sl_min (s : list DD) := match s with [] => None | h :: _ => Some h end.
Definition sl_max (s : list DD) := match s with [] => None | _ => Some (last s (D_zero, D_zero)) end.

Definition sl_fold {A} (f : A -> DD -> A) (s : list DD) (a : A) : A :=
  fold_left f s a.

Definition sl_elements (s : list DD) : list DD := s.

(** *** Convex hull *)

Definition crossD (o a b : DD) : Z :=
  let '(oa, ob, _) := Dalign (fst a) (fst o) in
  let '(oc, od, _) := Dalign (snd a) (snd o) in
  let '(oe, of_, _) := Dalign (fst b) (fst o) in
  let '(og, oh, _) := Dalign (snd b) (snd o) in
  (oa - ob) * (og - oh) - (oc - od) * (oe - of_).

Fixpoint addUpperPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if match DD_compare h p with Lt | Eq => true | Gt => false end
           then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if Z.leb (crossD a b p) 0 then addUpperPoint p rest
    else p :: hull
  end.

Fixpoint addLowerPoint (p : DD) (hull : list DD) : list DD :=
  match hull with
  | [] => [p]
  | [h] => if match DD_compare h p with Lt | Eq => true | Gt => false end
           then [h; p] else [p; h]
  | a :: ((b :: _) as rest) =>
    if Z.leb 0 (crossD a b p) then addLowerPoint p rest
    else p :: hull
  end.

Definition convexHull (s : list DD) : list DD :=
  sl_fromList
    (sl_fold (fun acc p => addUpperPoint p acc) s []
     ++ sl_fold (fun acc p => addLowerPoint p acc) s []).

(** *** Narrow check *)

(** narrow M s: check if all g-coordinates of s satisfy |M*g| < 1.
    M*g = M * mantissa * 2^exponent. Since exponent can be negative,
    we compare M * mantissa against 2^(-exponent) instead. *)
Definition narrow (M : Z) (s : list DD) : bool :=
  match sl_min s, sl_max s with
  | Some (l, _), Some (h, _) =>
    let ml := Dmult (D_from_Z M) l in
    let mh := Dmult (D_from_Z M) h in
    Dltb (Dmake (-1) 0) ml && Dltb mh (Dmake 1 0)
  | _, _ => true
  end.

(** *** Transforms *)

Definition even_trans (p : DD) : DD :=
  let '(g, f) := p in (Dhalf g, f).
Definition odd_pos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dsub g f)), g).
Definition odd_nonpos_trans (p : DD) : DD :=
  let '(g, f) := p in (Dred (Dhalf (Dadd g f)), f).

(** *** State: sorted assoc list *)

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

Definition INC : Z := 1.

Definition even_map (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in (INC + k, sl_map even_trans v).

Definition odd_map (kv : Z * list DD) : Z * list DD :=
  let '(k, v) := kv in
  if (0 <? k)%Z
  then (INC - k, sl_map odd_pos_trans v)
  else (INC + k, sl_map odd_nonpos_trans v).

Definition processDivstep (M : Z) (s : State) : State :=
  let f kv := [even_map kv; odd_map kv] in
  let s1 := State_fromList (flat_map f s) in
  let g kv :=
    let '(k, v) := kv in
    if narrow M v then [] else [(k, convexHull v)]
  in State_fromList (flat_map g s1).

(** *** Initial state and certificate *)

Definition set0 : list DD := sl_fromList [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1, set0)].

Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

(** Tight bound certificate: N=1078 *)
Lemma bls12_fast_certificate :
  State_is_empty (N.iter 1078 (processDivstep bls12_M) state0) = true.
Proof. vm_compute. reflexivity. Qed.
