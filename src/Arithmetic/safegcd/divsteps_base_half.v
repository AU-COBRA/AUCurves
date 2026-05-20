(** * Convex-hull divstep framework for δ₀ = 1/2 (Wuille / EUROCRYPT 2026).

    This is a δ₀ = 1/2 variant of [divsteps_base.v].

    Encoding: write [δ_paper = (δ_int + 1) / 2] so that
    - [δ_paper = 1/2] ↔ [δ_int = 0]
    - [δ_paper ↦ δ_paper + 1]  becomes  [δ_int ↦ δ_int + 2]   (INC = 2)
    - test "[δ_paper > 0]"     becomes  "[δ_int ≥ 0]"          (0 <=? δ_int)

    Mathematically, the [δ_paper] sequence ranges over half-integers
    {±1/2, ±3/2, …}; encoded as [δ_int] it ranges over even integers
    {0, ±2, ±4, …}.  The convex-hull algorithm is geometric and δ₀-
    independent in form — only [INC], [state0], and the strict/loose
    inequality test change.

    For [b = 256] the EUROCRYPT 2026 paper (Theorem 1, §3.4) shows
    convergence at [N = 590] divsteps, vs [N = 724] for δ₀ = 1.
*)

Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Require Import divsteps_base.   (* reuse all of D, DD, DDSet, ZMap, narrow, … *)
Import ListNotations.

(** ** Transitions on convex-hull keys (Wuille zeta-encoded).

    With [zeta := -(δ + 1/2)] (integer), the three branches update zeta as:
    - even g:               zeta ↦ zeta - 1
    - g odd, zeta < 0:      zeta ↦ -zeta - 2     (swap branch)
    - g odd, zeta ≥ 0:      zeta ↦ zeta - 1

    The point transitions [even_trans / odd_pos_trans / odd_nonpos_trans]
    are reused verbatim from [divsteps_base.v] (the (g, f) → (g', f')
    geometry is identical; only the bookkeeping on [delta] differs). *)

Definition even_map_half (kv : Z * DDSet.t) : Z * DDSet.t :=
  let (k, v) := kv in ((k - 1)%Z, DDSet_map even_trans v).

Definition odd_map_half (kv : Z * DDSet.t) : Z * DDSet.t :=
  let (k, v) := kv in
  if (k <? 0)%Z
   then ((- k - 2)%Z, DDSet_map odd_pos_trans v)
   else ((k - 1)%Z, DDSet_map odd_nonpos_trans v).

Definition processDivstep_half (M : Z) (s : State) : State :=
 let f kv := [even_map_half kv; odd_map_half kv] in
 let s1 := (State_fromList (flat_map f (ZMap.elements s))) in
 let g kv := let (k, v) := kv : Z * DDSet.t in
             if narrow M v then [] else [(k, convexHull v)]
 in State_fromList (flat_map g (ZMap.elements s1)).

(** Initial state at [zeta_0 = -1] (which represents [δ_0 = 1/2]). *)
Definition state0_half : State := ZMap.add (-1)%Z set0 empty.
