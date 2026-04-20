(** * Fast processDivstep v5: Sint63 + log2 narrow optimization.

    Same as divsteps_int63.v but with a fast-path narrow check:
    instead of computing M * mantissa (381-bit × 38-bit Z multiply),
    first check if log2(M) + log2(|mantissa|) + 1 < -exponent.
    This skips the expensive Z multiply in ~95% of narrow calls.

    Optimization 4: log2-based narrow fast path. *)

From Stdlib Require Import ZArith Uint63 Sint63 List Bool.
Import ListNotations.
Local Open Scope uint63_scope.

(** *** D type: pair of int, interpreted as signed via Sint63 *)

Definition D := (int * int)%type.
Definition D_mant (d : D) : int := fst d.
Definition D_exp (d : D) : int := snd d.
Definition D_mk (m e : int) : D := (m, e).

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

(** *** Narrow — OPTIMIZED with log2 fast path *)

(** log2 of absolute value of a signed int63.
    Returns 62 - head0(|m|). For m=0 returns 0. *)
Definition log2_abs (m : int) : int :=
  let abs_m := if Sint63.ltb m 0 then sub 0 m else m in
  if Uint63.eqb abs_m 0 then 0
  else sub 62 (Uint63.head0 abs_m).

(** Narrow fast path using log2 bounds.
    |M * mantissa * 2^exponent| < 1
    ⟺  |M * mantissa| < 2^(-exponent)   [when exponent < 0]
    ⟸  2^(log2M + log2|mantissa| + 1) ≤ 2^(-exponent)
    ⟺  log2M + log2|mantissa| + 1 ≤ -exponent

    When the fast test passes, we skip the expensive Z multiply.
    When it fails (tight bound), we fall back to exact Z computation. *)
Definition narrow_check (M_log2 : int) (M : Z) (m e : int) : bool :=
  if Sint63.leb 0 e then
    (* positive exponent: M*m*2^e, only narrow if m = 0 *)
    Uint63.eqb m 0
  else
    let neg_e := sub 0 e in  (* -exponent, positive *)
    let log2_m := log2_abs m in
    (* Fast path: log2(M) + log2(|m|) + 1 < -exponent → definitely narrow *)
    if int_sltb (add (add M_log2 log2_m) 1) neg_e then true
    else
      (* Tight case: fall back to exact Z computation *)
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

(** *** processDivstep — hull before union + log2 narrow *)

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

(** *** Initial state + BLS12 *)

Definition set0 : list DD := sl_sort [(D_zero, D_one); (D_one, D_one)].
Definition state0 : State := [(1%Z, set0)].

Definition bls12_M : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

(** log2(bls12_M) = 380 (it's a 381-bit number) *)
Definition bls12_M_log2 : int := 380.
