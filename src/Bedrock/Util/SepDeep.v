(** * SepDeep — vm_compute-friendly variant of [reflective_ecancel].

    Companion to [SepReflectiveAC.v].  The shallow [reflective_ecancel]
    permutes the [seps] list via [seps_pick_iff1] and then uses
    [cbn [List.nth List.firstn List.skipn List.app]] to reduce the
    permuted list to a concrete cons-of-atoms.  When the surrounding
    proof has many open let-bindings (as in
    [Scalarmult_Impl_64.ed25519_scalarmult_base_correct]), the [cbn]
    leaves the result in a shape that the kernel re-traverses on [Qed]
    in time exponential in the let-binding count.

    [deep_ecancel] swaps the two slow steps for [vm_compute]:

      1. The index-bound proof [n < length l] is replaced by a
         [Nat.ltb n (length l) = true] obligation discharged by
         [vm_compute; reflexivity].
      2. The cons-list reduction is done via [vm_compute in H] instead
         of [cbn].

    The Qed-sealed lemma [seps_pick_iff1_decb] reuses [seps_pick_iff1]
    from [SepReflectiveAC.v] under the hood; the only new content is
    the boolean wrapper. *)

From Stdlib Require Import List ZArith Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import Bedrock.Util.SepReflectiveAC.
Import ListNotations.

Section SepDeep.
  Context {key value : Type}
          {key_eqb : key -> key -> bool}
          {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}
          {map : map.map key value} {map_ok : map.ok map}.

  Local Notation iff1 := Lift1Prop.iff1.
  Local Notation pred := (map -> Prop).

  (** Boolean variant of [seps_pick_iff1].  The bound is expressed as
      [Nat.ltb n (length l) = true] so callers can discharge it via
      [vm_compute; reflexivity] (or [eq_refl] when the lengths are
      ground). *)
  Lemma seps_pick_iff1_decb : forall (l : list pred) (n : nat),
    Nat.ltb n (Datatypes.length l) = true ->
    iff1 (seps l)
         (seps (List.nth n l (emp True)
                :: List.firstn n l ++ List.skipn (S n) l)).
  Proof.
    intros l n Hb.
    apply Nat.ltb_lt in Hb.
    apply seps_pick_iff1; exact Hb.
  Qed.

End SepDeep.

(** [deep_ecancel H] — drop-in replacement for [reflective_ecancel] from
    [SepReflectiveAC.v] that uses [vm_compute] instead of [cbn] for the
    list-reduction step.

    Pipeline:
      1. [flatten_seps_in_strict H]   → [H : seps Hin m]
      2. find index [i] of [target] in [Hin] via [find_index_of_atom]
      3. apply [seps_pick_iff1_decb Hin i (eq_refl : Nat.ltb i _ = true)]
         to permute [Hin] so [target] sits at position 0.  The
         [Nat.ltb] obligation is decidable and is discharged by
         [vm_compute; reflexivity] inline.
      4. [vm_compute in H] — reduces [List.nth/firstn/skipn/app] to a
         concrete cons-of-atoms WITHOUT unfolding any [pred] atoms
         (they're abstract under the [seps] head, so [vm_compute]
         leaves them alone).
      5. convert [seps (target :: rest) m] back to
         [(target ⋆ seps rest) m] via [seps_cons]; [exact H] unifies
         the goal's residual evar with [seps rest]. *)
Ltac deep_ecancel H :=
  flatten_seps_in_strict H;
  lazymatch goal with
  | |- (?target ⋆ _)%sep ?m =>
      lazymatch type of H with
      | seps ?Hin _ =>
          let i := find_index_of_atom target Hin in
          apply (proj1 (seps_pick_iff1_decb Hin i
                          (eq_refl : Nat.ltb i (Datatypes.length Hin) = true)
                          m)) in H;
          vm_compute List.nth in H;
          vm_compute List.firstn in H;
          vm_compute List.skipn in H;
          vm_compute List.app in H;
          lazymatch type of H with
          | seps (?t :: ?rest) ?m' =>
              apply (proj1 (SeparationLogic.seps_cons t rest m')) in H
          end;
          exact H
      end
  end.

(** ** Test / demo for [deep_ecancel].

    Synthetic 5-atom sep state — exercises the full pipeline (flatten,
    permute via boolean lemma, vm_compute reduce, convert back) on a
    cancellation goal.  Mirrors the shape used in
    [Scalarmult_Impl_64.v] (eexists-sep with a residual evar). *)
Section DeepEcancelTest.
  Context {key value : Type}
          {key_eqb : key -> key -> bool}
          {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}
          {map : map.map key value} {map_ok : map.ok map}.

  Local Notation pred := (map -> Prop).

  Lemma deep_ecancel_test :
    forall (P0 P1 P2 P3 P4 : pred) (m : map),
      (P0 ⋆ (P1 ⋆ P2 ⋆ P3 ⋆ P4))%sep m ->
      exists R, (P3 ⋆ R)%sep m.
  Proof.
    intros P0 P1 P2 P3 P4 m Hsep.
    eexists.
    deep_ecancel Hsep.
  Qed.

End DeepEcancelTest.
