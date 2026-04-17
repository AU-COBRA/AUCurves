(** * SafeRustReflection_bls12: reflection on a real bedrock2 [spec_of]
 *    using the actual [AbstractField.FElem] predicate from the BLS12
 *    field representation infrastructure.
 *
 * This file completes the wiring chain. Where [SafeRustReflection_real]
 * used user-supplied predicates, this file builds a [spec_of] using
 * the actual [@AbstractField.FElem _ _ _ _ _ _ rep] term that appears
 * in real BLS12 specs. The walker pattern-matches on the head shape
 * regardless of how the predicate is constructed, so the same
 * reflection works without any change.
 *
 * The key insight: [walk] doesn't care about the head symbol's name —
 * it matches [?P ?ptr ?val] for the leaf and [?sep ?head ?tail] for
 * the connective. Both real bedrock2 [Separation.sep] and the actual
 * [@FElem _ ... rep] satisfy these shape constraints.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Require Import Bedrock.ToSafeRustString.
Require Import Bedrock.SafeRustReflection_walker.
Require Import Bedrock.SafeRustReflection_specof.
Require Import Bedrock.SafeRustReflection_real.

Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.

Require Import Bedrock.Specs.AbstractField.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Printf.

Set Default Proof Mode "Classic".
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Setup: word/mem context + three FieldRepresentation instances     *)
(* ================================================================ *)

Section BLS12.
  Context {width : Z} {BW : Bitwidth width}.
  Context {word : word.word width} {mem : map.map word Init.Byte.byte}.
  Context {F_Fp F_Fp2 F_Fp12 : Type}.
  Context {pf_Fp   : FieldParameters F_Fp}.
  Context {pf_Fp2  : FieldParameters F_Fp2}.
  Context {pf_Fp12 : FieldParameters F_Fp12}.
  Context {rep_Fp   : @FieldRepresentation F_Fp   pf_Fp   width BW word mem}.
  Context {rep_Fp2  : @FieldRepresentation F_Fp2  pf_Fp2  width BW word mem}.
  Context {rep_Fp12 : @FieldRepresentation F_Fp12 pf_Fp12 width BW word mem}.

  (** The three real [FElem] predicates, exactly as they appear in
      real BLS12 specs (e.g., [BLS12_PairingTop.v] line 192). *)
  Local Notation FElem_Fp   := (@AbstractField.FElem _ _ _ _ _ _ rep_Fp).
  Local Notation FElem_Fp2  := (@AbstractField.FElem _ _ _ _ _ _ rep_Fp2).
  Local Notation FElem_Fp12 := (@AbstractField.FElem _ _ _ _ _ _ rep_Fp12).

  Variable Fp_bounded : list word -> Prop.
  Variable Fp2_bounded : list word -> Prop.
  Variable funcs_t : Type.
  Variable WP : funcs_t -> string -> trace -> mem -> list word ->
                (trace -> mem -> list word -> Prop) -> Prop.

  (** A real-shaped [spec_of] using the actual [FElem] predicates. *)
  Definition spec_of_real_bls12_pairing : funcs_t -> Prop :=
    fun functions =>
      forall (pout p_px p_py p_qx p_qy : word),
      forall (old_out : list word) (p_x p_y q_x q_y : list word),
      forall (Rr : mem -> Prop),
      forall (tr : trace) (m : mem),
        Fp2_bounded q_x /\
        Fp2_bounded q_y /\
        Fp_bounded p_x /\
        Fp_bounded p_y /\
        (sep (FElem_Fp12 pout old_out)
        (sep (FElem_Fp p_px p_x)
        (sep (FElem_Fp p_py p_y)
        (sep (FElem_Fp2 p_qx q_x)
        (sep (FElem_Fp2 p_qy q_y) Rr))))) m ->
        WP functions "bls12_pairing" tr m nil
          (fun tr' m' rets =>
             rets = nil /\
             tr = tr' /\
             exists (out : list word),
               (sep (FElem_Fp12 pout out)
               (sep (FElem_Fp p_px p_x)
               (sep (FElem_Fp p_py p_y)
               (sep (FElem_Fp2 p_qx q_x)
               (sep (FElem_Fp2 p_qy q_y) Rr))))) m').
End BLS12.

(* ================================================================ *)
(* Run the reflection on the real spec                               *)
(* ================================================================ *)

Section RunBLS12.
  Context {width : Z} {BW : Bitwidth width}.
  Context {word_inst : word.word width} {mem_inst : map.map word_inst Init.Byte.byte}.
  Context {F_Fp F_Fp2 F_Fp12 : Type}.
  Context {pf_Fp   : FieldParameters F_Fp}.
  Context {pf_Fp2  : FieldParameters F_Fp2}.
  Context {pf_Fp12 : FieldParameters F_Fp12}.
  Context {rep_Fp   : @FieldRepresentation F_Fp   pf_Fp   width BW word_inst mem_inst}.
  Context {rep_Fp2  : @FieldRepresentation F_Fp2  pf_Fp2  width BW word_inst mem_inst}.
  Context {rep_Fp12 : @FieldRepresentation F_Fp12 pf_Fp12 width BW word_inst mem_inst}.

  Goal True.
  Proof.
    (* Build the pre and post sep trees using the real [@FElem _ ... rep] *)
    ltac2:(reflect_real
      constr:(
        sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp12 (word.of_Z 1) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp (word.of_Z 2) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp (word.of_Z 3) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp2 (word.of_Z 4) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp2 (word.of_Z 5) nil)
            (fun (_ : mem_inst) => True))))))
      constr:(
        sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp12 (word.of_Z 1) (cons (word.of_Z 99) nil))
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp (word.of_Z 2) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp (word.of_Z 3) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp2 (word.of_Z 4) nil)
       (sep (@AbstractField.FElem _ _ _ _ _ _ rep_Fp2 (word.of_Z 5) nil)
            (fun (_ : mem_inst) => True))))))
      [(constr:(@AbstractField.FElem _ _ _ _ _ _ rep_Fp),   constr:(Fp_381));
       (constr:(@AbstractField.FElem _ _ _ _ _ _ rep_Fp2),  constr:(Fp2_381));
       (constr:(@AbstractField.FElem _ _ _ _ _ _ rep_Fp12), constr:(Fp12_381))]).
    exact I.
  Qed.
End RunBLS12.
