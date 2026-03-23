
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

module type EqLtLe =
 sig
  type t
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedTypeFull' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module OTF_to_TTLB =
 functor (O:OrderedTypeFull') ->
 struct
  (** val leb : O.t -> O.t -> bool **)

  let leb x y =
    match O.compare x y with
    | Gt -> false
    | _ -> true

  type t = O.t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module Pos =
 struct
  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> Big_int_Z.mult_int_big_int 2 (succ p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p)
      (fun _ -> Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
      x

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (add p q))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.mult_int_big_int 2 (succ q))
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        q)
        (fun _ -> Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)
        y)
      x

  (** val add_carry :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add_carry p q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.mult_int_big_int 2 (add_carry p q))
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (add p q))
        (fun _ -> Big_int_Z.mult_int_big_int 2 (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        (succ q))
        (fun q -> Big_int_Z.mult_int_big_int 2 (succ q))
        (fun _ ->
        (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
        Big_int_Z.unit_big_int)
        y)
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (Big_int_Z.mult_int_big_int 2 p))
      (fun p ->
      (fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      (pred_double p))
      (fun _ -> Big_int_Z.unit_big_int)
      x

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p -> add y (Big_int_Z.mult_int_big_int 2 (mul p y)))
      (fun p -> Big_int_Z.mult_int_big_int 2 (mul p y))
      (fun _ -> y)
      x

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Big_int_Z.big_int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> Big_int_Z.unit_big_int)
      p

  (** val div2_up : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> Big_int_Z.unit_big_int)
      p

  (** val compare_cont :
      comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

module Coq_Pos =
 struct
  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module Z =
 struct
  (** val double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p -> (Big_int_Z.mult_int_big_int 2 p))
      (fun p -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2 p))
      x

  (** val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.unit_big_int)
      (fun p ->
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      p))
      (fun p -> Big_int_Z.minus_big_int (Pos.pred_double p))
      x

  (** val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred_double x =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.minus_big_int Big_int_Z.unit_big_int)
      (fun p -> (Pos.pred_double p))
      (fun p -> Big_int_Z.minus_big_int
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) p))
      x

  (** val pos_sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> (Big_int_Z.mult_int_big_int 2 p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun q -> Big_int_Z.minus_big_int (Big_int_Z.mult_int_big_int 2
        q))
        (fun q -> Big_int_Z.minus_big_int (Pos.pred_double q))
        (fun _ -> Big_int_Z.zero_big_int)
        y)
      x

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add = Big_int_Z.add_big_int

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp = Big_int_Z.minus_big_int

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub = Big_int_Z.sub_big_int

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul = Big_int_Z.mult_big_int

  (** val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison **)

  let compare = (fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb = Big_int_Z.eq_big_int

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let max = Big_int_Z.max_big_int

  (** val div2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let div2 z0 =
    (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
      (fun _ -> Big_int_Z.zero_big_int)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
        (fun _ -> (Pos.div2 p))
        (fun _ -> (Pos.div2 p))
        (fun _ -> Big_int_Z.zero_big_int)
        p)
      (fun p -> Big_int_Z.minus_big_int (Pos.div2_up p))
      z0

  (** val shiftl :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let shiftl = Big_int_Z.(fun x y ->
  let y = int_of_big_int y in
  if y < 0 then shift_right_big_int x (-y)
  else shift_left_big_int x y)

  (** val succ : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let succ = Big_int_Z.succ_big_int

  (** val pred : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let pred = Big_int_Z.pred_big_int

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec = Big_int_Z.eq_big_int
 end

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

module PairOrderedType =
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 struct
  type t = O1.t * O2.t

  (** val eq_dec : (O1.t * O2.t) -> (O1.t * O2.t) -> bool **)

  let eq_dec x y =
    let (t0, t1) = x in
    let (t2, t3) = y in
    let s = O1.eq_dec t0 t2 in if s then O2.eq_dec t1 t3 else false

  (** val compare : (O1.t * O2.t) -> (O1.t * O2.t) -> comparison **)

  let compare x y =
    match O1.compare (fst x) (fst y) with
    | Eq -> O2.compare (snd x) (snd y)
    | x0 -> x0
 end

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module Coq_OrderedTypeFacts =
 functor (O:Coq_OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:Coq_OrderedType) ->
 struct
  module MO = Coq_OrderedTypeFacts(O)
 end

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OT_from_Alt =
 functor (O:OrderedTypeAlt) ->
 struct
  type t = O.t

  (** val compare : O.t -> O.t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Z_as_OT =
 struct
  type t = Big_int_Z.big_int

  (** val compare :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int compare0 **)

  let compare x y =
    match Z.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec =
    Z.eq_dec
 end

module type Int =
 sig
  type t

  val i2z : t -> Big_int_Z.big_int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = Big_int_Z.big_int

  (** val _0 : Big_int_Z.big_int **)

  let _0 =
    Big_int_Z.zero_big_int

  (** val _1 : Big_int_Z.big_int **)

  let _1 =
    Big_int_Z.unit_big_int

  (** val _2 : Big_int_Z.big_int **)

  let _2 =
    (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)

  (** val _3 : Big_int_Z.big_int **)

  let _3 =
    ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))
      Big_int_Z.unit_big_int)

  (** val add :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let add =
    Z.add

  (** val opp : Big_int_Z.big_int -> Big_int_Z.big_int **)

  let opp =
    Z.opp

  (** val sub :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let sub =
    Z.sub

  (** val mul :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let mul =
    Z.mul

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let max =
    Z.max

  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> Big_int_Z.big_int **)

  let i2z n =
    n
 end

module MakeRaw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type elt = X.t

  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val is_empty : tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _) -> false

  (** val mem : X.t -> tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (_, l, k, r) ->
    (match X.compare x k with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)

  (** val min_elt : tree -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (_, l, x, _) ->
    (match l with
     | Leaf -> Some x
     | Node (_, _, _, _) -> min_elt l)

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (_, _, _, _) -> max_elt r)

  (** val choose : tree -> elt option **)

  let choose =
    min_elt

  (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

  let rec fold f t0 base =
    match t0 with
    | Leaf -> base
    | Node (_, l, x, r) -> fold f r (f x (fold f l base))

  (** val elements_aux : X.t list -> tree -> X.t list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

  (** val elements : tree -> X.t list **)

  let elements =
    elements_aux []

  (** val rev_elements_aux : X.t list -> tree -> X.t list **)

  let rec rev_elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

  (** val rev_elements : tree -> X.t list **)

  let rev_elements =
    rev_elements_aux []

  (** val cardinal : tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

  (** val maxdepth : tree -> nat **)

  let rec maxdepth = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

  (** val mindepth : tree -> nat **)

  let rec mindepth = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

  (** val for_all : (elt -> bool) -> tree -> bool **)

  let rec for_all f = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    if if f x then for_all f l else false then for_all f r else false

  (** val exists_ : (elt -> bool) -> tree -> bool **)

  let rec exists_ f = function
  | Leaf -> false
  | Node (_, l, x, r) ->
    if if f x then true else exists_ f l then true else exists_ f r

  type enumeration =
  | End
  | More of elt * tree * enumeration

  (** val cons : tree -> enumeration -> enumeration **)

  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (_, l, x, r) -> cons l (More (x, r, e))

  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)

  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)

  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (_, l1, x1, r1) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

  (** val compare_end : enumeration -> comparison **)

  let compare_end = function
  | End -> Eq
  | More (_, _, _) -> Lt

  (** val compare : tree -> tree -> comparison **)

  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)

  (** val equal : tree -> tree -> bool **)

  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false

  (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)

  (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)

  (** val subset : tree -> tree -> bool **)

  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> false
       | Node (_, l2, x2, r2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

  type t = tree

  (** val height : t -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (h, _, _, _) -> h

  (** val singleton : X.t -> tree **)

  let singleton x =
    Node (I._1, Leaf, x, Leaf)

  (** val create : t -> X.t -> t -> tree **)

  let create l x r =
    Node ((I.add (I.max (height l) (height r)) I._1), l, x, r)

  (** val assert_false : t -> X.t -> t -> tree **)

  let assert_false =
    create

  (** val bal : t -> X.t -> t -> tree **)

  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.ltb (I.add hr I._2) hl
    then (match l with
          | Leaf -> assert_false l x r
          | Node (_, ll, lx, lr) ->
            if I.leb (height lr) (height ll)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (_, lrl, lrx, lrr) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.ltb (I.add hl I._2) hr
         then (match r with
               | Leaf -> assert_false l x r
               | Node (_, rl, rx, rr) ->
                 if I.leb (height rl) (height rr)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (_, rll, rlx, rlr) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r

  (** val add : X.t -> tree -> tree **)

  let rec add x = function
  | Leaf -> Node (I._1, Leaf, x, Leaf)
  | Node (h, l, y, r) ->
    (match X.compare x y with
     | Eq -> Node (h, l, y, r)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))

  (** val join : tree -> elt -> t -> t **)

  let rec join l = match l with
  | Leaf -> add
  | Node (lh, ll, lx, lr) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rh, rl, rx, rr) ->
        if I.ltb (I.add rh I._2) lh
        then bal ll lx (join lr x r)
        else if I.ltb (I.add lh I._2) rh
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)

  (** val remove_min : tree -> elt -> t -> t * elt **)

  let rec remove_min l x r =
    match l with
    | Leaf -> (r, x)
    | Node (_, ll, lx, lr) ->
      let (l', m) = remove_min ll lx lr in ((bal l' x r), m)

  (** val merge : tree -> tree -> tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

  (** val remove : X.t -> tree -> tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))

  (** val concat : tree -> tree -> tree **)

  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

  type triple = { t_left : t; t_in : bool; t_right : t }

  (** val t_left : triple -> t **)

  let t_left t0 =
    t0.t_left

  (** val t_in : triple -> bool **)

  let t_in t0 =
    t0.t_in

  (** val t_right : triple -> t **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> tree -> triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b; t_right = rr })

  (** val inter : tree -> tree -> tree **)

  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))

  (** val diff : tree -> tree -> tree **)

  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))

  (** val union : tree -> tree -> tree **)

  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))

  (** val filter : (elt -> bool) -> tree -> tree **)

  let rec filter f = function
  | Leaf -> Leaf
  | Node (_, l, x, r) ->
    let l' = filter f l in
    let r' = filter f r in if f x then join l' x r' else concat l' r'

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | Leaf -> (Leaf, Leaf)
  | Node (_, l, x, r) ->
    let (l1, l2) = partition f l in
    let (r1, r2) = partition f r in
    if f x
    then ((join l1 x r1), (concat l2 r2))
    else ((concat l1 r1), (join l2 x r2))

  (** val ltb_tree : X.t -> tree -> bool **)

  let rec ltb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
     | _ -> false)

  (** val gtb_tree : X.t -> tree -> bool **)

  let rec gtb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
     | _ -> false)

  (** val isok : tree -> bool **)

  let rec isok = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

  module MX = OrderedTypeFacts(X)

  module L = MakeListOrdering(X)

  (** val flatten_e : enumeration -> elt list **)

  let rec flatten_e = function
  | End -> []
  | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(I)(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem =
    Raw.mem

  (** val add : elt -> t -> t **)

  let add =
    Raw.add

  (** val remove : elt -> t -> t **)

  let remove =
    Raw.remove

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union =
    Raw.union

  (** val inter : t -> t -> t **)

  let inter =
    Raw.inter

  (** val diff : t -> t -> t **)

  let diff =
    Raw.diff

  (** val equal : t -> t -> bool **)

  let equal =
    Raw.equal

  (** val subset : t -> t -> bool **)

  let subset =
    Raw.subset

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val elements : t -> elt list **)

  let elements =
    Raw.elements

  (** val choose : t -> elt option **)

  let choose =
    Raw.choose

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    Raw.fold

  (** val cardinal : t -> nat **)

  let cardinal =
    Raw.cardinal

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    Raw.filter

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    Raw.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    Raw.exists_

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f s in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare =
    Raw.compare

  (** val min_elt : t -> elt option **)

  let min_elt =
    Raw.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    Raw.max_elt
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module Raw =
 functor (X:Coq_OrderedType) ->
 struct
  module MX = Coq_OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d0, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d0
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d0 r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d0 r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d0 r)
            else (match lr with
                  | Leaf -> assert_false l x d0 r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d0 r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d0 r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d0 rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d0 r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d0 rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d0 r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d0 = function
  | Leaf -> Node (Leaf, x, d0, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d0 l) y d' r
     | EQ -> Node (l, y, d0, r, h)
     | GT -> bal l y d' (add x d0 r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d0 r =
    match l with
    | Leaf -> (r, (x, d0))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d0 r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d0) = p in bal s1 x d0 s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d0, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d0 r
     | EQ -> merge l r
     | GT -> bal l y d0 (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d0 ->
      let rec join_aux r = match r with
      | Leaf -> add x d0 l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d0 r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d0 r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d0, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d0 r) }
     | EQ -> { t_left = l; t_opt = (Some d0); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d0 rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d0, r, _) -> elements_aux ((x, d0) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d0, r, _) -> fold f r (f x d0 (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d0, r, _) -> cons l (More (x, d0, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d0, r, h) -> Node ((map f l), x, (f d0), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d0, r, h) -> Node ((mapi f l), x, (f x d0), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d0, r, _) ->
    (match f x d0 with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d0 o -> f (Some d0) o)
      (map_option (fun _ d0 -> f (Some d0) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = Coq_OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module Coq_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    Raw.add

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    Raw.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    Raw.mem

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    Raw.find

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    Raw.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    Raw.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    Raw.map2

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements =
    Raw.elements

  (** val cardinal : 'a1 t -> nat **)

  let cardinal =
    Raw.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    Raw.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    Raw.equal
 end

module Coq_Make =
 functor (X:Coq_OrderedType) ->
 Coq_IntMake(Z_as_Int)(X)

(** val iNC : Big_int_Z.big_int **)

let iNC =
  Big_int_Z.unit_big_int

type d = { dmantissa : Big_int_Z.big_int; dexponent : Big_int_Z.big_int }

(** val d_from_Z : Big_int_Z.big_int -> d **)

let d_from_Z a =
  { dmantissa = a; dexponent = Big_int_Z.zero_big_int }

(** val dredH :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * Big_int_Z.big_int **)

let rec dredH p z0 =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun _ -> (p, z0))
    (fun x -> dredH x (Z.succ z0))
    (fun _ -> (p, z0))
    p

(** val dred : d -> d **)

let dred a =
  let { dmantissa = m; dexponent = e } = a in
  ((fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
     (fun _ -> d_from_Z Big_int_Z.zero_big_int)
     (fun p ->
     let (p', e') = dredH p e in { dmantissa = p'; dexponent = e' })
     (fun p ->
     let (p', e') = dredH p e in
     { dmantissa = (Big_int_Z.minus_big_int p'); dexponent = e' })
     m)

(** val dalign :
    d -> d -> (Big_int_Z.big_int * Big_int_Z.big_int) * Big_int_Z.big_int **)

let dalign a b =
  (fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))
    (fun _ -> ((a.dmantissa, b.dmantissa), b.dexponent))
    (fun d0 -> (((Z.shiftl a.dmantissa d0), b.dmantissa),
    b.dexponent))
    (fun d0 -> ((a.dmantissa, (Z.shiftl b.dmantissa d0)),
    a.dexponent))
    (Z.sub a.dexponent b.dexponent)

(** val dadd : d -> d -> d **)

let dadd a b =
  let (p, e') = dalign a b in
  let (a', b') = p in { dmantissa = (Z.add a' b'); dexponent = e' }

(** val dsub : d -> d -> d **)

let dsub a b =
  let (p, e') = dalign a b in
  let (a', b') = p in { dmantissa = (Z.sub a' b'); dexponent = e' }

(** val dmult : d -> d -> d **)

let dmult a b =
  { dmantissa = (Z.mul a.dmantissa b.dmantissa); dexponent =
    (Z.add a.dexponent b.dexponent) }

(** val dhalf : d -> d **)

let dhalf a =
  { dmantissa = a.dmantissa; dexponent = (Z.pred a.dexponent) }

(** val dcompare : d -> d -> comparison **)

let dcompare a b =
  let (p, _) = dalign a b in let (a', b') = p in Z.compare a' b'

module D_as_OrderedTypeAlt =
 struct
  type t = d

  (** val compare : d -> d -> comparison **)

  let compare =
    dcompare
 end

module D_as_OT = OT_from_Alt(D_as_OrderedTypeAlt)

module D_as_OTF = OT_to_Full(D_as_OT)

module D_as_TTLT = OTF_to_TTLB(D_as_OTF)

(** val dltb : d -> d -> bool **)

let dltb a b =
  negb (D_as_TTLT.leb b a)

module DDOrder = PairOrderedType(D_as_OT)(D_as_OT)

type dD = DDOrder.t

(** val orientation : dD -> dD -> dD -> comparison **)

let orientation p1 p2 p3 =
  let (x1, y1) = p1 in
  let (x2, y2) = p2 in
  let (x3, y3) = p3 in
  dcompare (dmult (dsub x1 x3) (dsub y2 y3)) (dmult (dsub y1 y3) (dsub x2 x3))

(** val addLowerPoint : dD -> dD list -> dD list **)

let rec addLowerPoint p l = match l with
| [] -> p :: []
| q :: l0 ->
  (match l0 with
   | [] ->
     (match DDOrder.compare p q with
      | Eq -> p :: []
      | _ -> p :: (q :: []))
   | r :: _ ->
     (match orientation p q r with
      | Lt -> p :: l
      | _ -> addLowerPoint p l0))

(** val addUpperPoint : dD -> dD list -> dD list **)

let rec addUpperPoint p l = match l with
| [] -> p :: []
| q :: l0 ->
  (match l0 with
   | [] ->
     (match DDOrder.compare p q with
      | Eq -> p :: []
      | _ -> p :: (q :: []))
   | r :: _ ->
     (match orientation p q r with
      | Gt -> p :: l
      | _ -> addUpperPoint p l0))

module DDSet = Make(DDOrder)

(** val dDSet_fromList : dD list -> DDSet.t **)

let dDSet_fromList l =
  fold_left (fun s a -> DDSet.add a s) l DDSet.empty

(** val dDSet_map : (dD -> dD) -> DDSet.t -> DDSet.t **)

let dDSet_map f s =
  DDSet.fold (fun a s0 -> DDSet.add (f a) s0) s DDSet.empty

(** val convexHull : DDSet.t -> DDSet.t **)

let convexHull s =
  dDSet_fromList
    (app (DDSet.fold addUpperPoint s []) (DDSet.fold addLowerPoint s []))

(** val narrow : Big_int_Z.big_int -> DDSet.t -> bool **)

let narrow m s =
  let o = DDSet.min_elt s in
  let o0 = DDSet.max_elt s in
  (match o with
   | Some e ->
     let (l, _) = e in
     (match o0 with
      | Some e0 ->
        let (h, _) = e0 in
        (&&)
          (dltb (d_from_Z (Big_int_Z.minus_big_int Big_int_Z.unit_big_int))
            (dmult (d_from_Z m) l))
          (dltb (dmult (d_from_Z m) h) (d_from_Z Big_int_Z.unit_big_int))
      | None -> true)
   | None -> true)

(** val odd_pos_trans : dD -> dD **)

let odd_pos_trans = function
| (g, f) -> ((dred (dhalf (dsub g f))), g)

(** val odd_nonpos_trans : dD -> dD **)

let odd_nonpos_trans = function
| (g, f) -> ((dred (dhalf (dadd g f))), f)

(** val even_trans : dD -> dD **)

let even_trans = function
| (g, f) -> ((dhalf g), f)

(** val even_map :
    (Big_int_Z.big_int * DDSet.t) -> Big_int_Z.big_int * DDSet.t **)

let even_map = function
| (k, v) -> ((Z.add iNC k), (dDSet_map even_trans v))

(** val odd_map :
    (Big_int_Z.big_int * DDSet.t) -> Big_int_Z.big_int * DDSet.t **)

let odd_map = function
| (k, v) ->
  if Z.ltb Big_int_Z.zero_big_int k
  then ((Z.sub iNC k), (dDSet_map odd_pos_trans v))
  else ((Z.add iNC k), (dDSet_map odd_nonpos_trans v))

module ZMap = Coq_Make(Z_as_OT)

type state = DDSet.t ZMap.t

(** val empty0 : state **)

let empty0 =
  ZMap.empty

(** val state_join : Big_int_Z.big_int -> DDSet.t -> state -> state **)

let state_join k v m =
  ZMap.add k
    (match ZMap.find k m with
     | Some v0 -> DDSet.union v v0
     | None -> v)
    m

(** val state_fromList : (Big_int_Z.big_int * DDSet.t) list -> state **)

let state_fromList l =
  fold_left (fun s kv -> state_join (fst kv) (snd kv) s) l empty0

(** val processDivstep : Big_int_Z.big_int -> state -> state **)

let processDivstep m s =
  let f = fun kv -> (even_map kv) :: ((odd_map kv) :: []) in
  let s1 = state_fromList (flat_map f (ZMap.elements s)) in
  let g = fun kv ->
    let (k, v) = kv in if narrow m v then [] else (k, (convexHull v)) :: []
  in
  state_fromList (flat_map g (ZMap.elements s1))

(** val set0 : DDSet.t **)

let set0 =
  dDSet_fromList (((d_from_Z Big_int_Z.zero_big_int),
    (d_from_Z Big_int_Z.unit_big_int)) :: (((d_from_Z Big_int_Z.unit_big_int),
    (d_from_Z Big_int_Z.unit_big_int)) :: []))

(** val state0 : state **)

let state0 =
  ZMap.add Big_int_Z.unit_big_int set0 empty0
