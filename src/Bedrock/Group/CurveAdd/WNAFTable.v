(** * wNAF precomputation table and lookup.

    For window w=4: table = [[1]P, [3]P, [5]P, [7]P] (4 Jacobian points).
    Digit d maps to table[|d|/2] with conditional negation for d < 0. *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Table specifications *)

Section TableSpec.
  Context {F : Type} {Fzero Fone : F} {Fopp : F -> F}.
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  Fixpoint scmul (n : nat) (P : F * F * F) : F * F * F :=
    match n with
    | O => (Fzero, Fone, Fzero)
    | S m => curve_add P (scmul m P)
    end.

  Definition curve_negate (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in (X, Fopp Y, Z).

  (** Table entry i holds [2*i+1]P *)
  Definition table_entry (i : nat) (P : F * F * F) : F * F * F :=
    scmul (2 * i + 1) P.

  (** For w=4: 4 entries (indices 0..3 → multiples 1,3,5,7) *)
  Definition table_size (w : nat) : nat := Nat.pow 2 (w - 2).

  (** Table lookup: index → entry *)
  Definition table_lookup (table : list (F * F * F)) (i : nat) : F * F * F :=
    nth i table (Fzero, Fone, Fzero).

  (** wNAF digit → table index + sign.
      For d > 0: idx = (d-1)/2, negate = false.
      For d < 0: idx = (-d-1)/2, negate = true. *)
  Definition wnaf_to_index (d : Z) : nat * bool :=
    if d >? 0 then (Z.to_nat ((d - 1) / 2), false)
    else if d <? 0 then (Z.to_nat ((-d - 1) / 2), true)
    else (0%nat, false).

  (** Select from table and conditionally negate *)
  Definition table_select (table : list (F * F * F)) (d : Z) : F * F * F :=
    let '(idx, neg) := wnaf_to_index d in
    let P := table_lookup table idx in
    if neg then curve_negate P else P.

End TableSpec.

(** ** Precomputation for w=4 *)

Section Precompute.
  Context {F : Type}.
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  (** Build [1]P, [3]P, [5]P, [7]P from P and double(P).
      Cost: 1 doubling + 3 additions. *)
  Definition precompute_w4
    (double : F * F * F -> F * F * F)
    (P : F * F * F) : list (F * F * F) :=
    let dbl := double P in
    let t1 := curve_add P dbl in        (* [3]P *)
    let t2 := curve_add t1 dbl in       (* [5]P *)
    let t3 := curve_add t2 dbl in       (* [7]P *)
    [P; t1; t2; t3].

  Lemma precompute_w4_length : forall dbl P,
    length (precompute_w4 dbl P) = 4%nat.
  Proof. reflexivity. Qed.

End Precompute.

(** ** Constant-time lookup specification *)

(** The bedrock2 constant-time table lookup iterates through all
    table entries, using conditional moves (select_znz) to select
    the matching entry. This ensures no timing side-channel.

    For the GLV proof, this is assumed as a hypothesis:

    HTableLookup : forall pOut pTable idx ...
      (table_sep pTable T * FElem_out pOut * R) m →
      0 <= idx < 4 →
      call functions "ct_table_lookup" tr m [pOut; pTable; idx_word]
        (fun tr' m' _ => (FElem_out pOut (nth idx T id) * ...) m')

    The actual bedrock2 implementation (unrolled for 4 entries):
      func ct_table_lookup(outx, outy, outz, table, idx) {
        // Initialize to table[0]
        felem_copy(outx, table);
        felem_copy(outy, table + felem_size);
        felem_copy(outz, table + 2*felem_size);
        // For each entry 1..3: conditionally overwrite
        cond = (idx == 1);
        select_znz(outx, cond, outx, table + 3*felem_size);
        select_znz(outy, cond, outy, table + 4*felem_size);
        select_znz(outz, cond, outz, table + 5*felem_size);
        // ... repeat for entries 2 and 3
      }
*)
