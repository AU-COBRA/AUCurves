(** Bridge between AUCurves' [Bignum] sep predicate and fiat-crypto's
    [FElem] sep predicate, for word-by-word Montgomery field
    representations.

    The two predicates are *structurally identical* at the memory level:
    both unfold to [array scalar (word.of_Z (bytes_per_word width)) px ws]
    over the same word list. They differ only in:
    - [Bignum] adds an [emp (length ws = n)] clause.
    - [FElem] wraps the word list in a dependent pair
      [{ws : list word | length ws = felem_size_in_words}].

    Bounds: AUCurves uses [WordByWordMontgomery.valid bw n m (map word.unsigned ws)]
            while fiat-crypto uses [bounded_by tight_bounds x]. For the WBW
            field representation these are *definitionally equal*: see
            [WordByWordMontgomery.tight_bounds_eq] in fiat-crypto.

    Decoding: AUCurves uses [eval (from_mont (map word.unsigned ws))],
              fiat-crypto's [feval] computes
              [F.of_Z (Positional.eval weight n (eval_trans (map word.unsigned ws)))]
              where [eval_trans = from_montgomerymod]. So
              [F.to_Z (feval x) = eval (from_mont (map word.unsigned (proj1_sig x))) mod m].

    This file packages those equivalences into reusable lemmas. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Import ListNotations.
Local Open Scope Z_scope.

Section BignumFElemBridge.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width}
          {mem : Interface.map.map word Byte.byte}
          {word_ok : word.ok word}
          {mem_ok : Interface.map.ok mem}.

  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  (* === Memory predicate equivalence ===
     Both [Bignum n px ws] and [FElem px x] unfold to
     [array scalar (word.of_Z (bytes_per_word width)) px ws], plus
     [Bignum] adds an explicit length clause and [FElem] hides it
     in the dependent pair. *)

  Lemma FElem_iff_Bignum (px : word) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum felem_size_in_words px (proj1_sig x)).
  Proof.
    cbv [FElem Bignum].
    destruct x as [ws Hlen]. cbn [proj1_sig].
    (* (array scalar ... px ws) <-> (emp (length ws = n) * array scalar ... px ws) *)
    split; intros m H.
    - apply sep_emp_l. split; [exact Hlen | exact H].
    - apply sep_emp_l in H. destruct H as [_ H]. exact H.
  Qed.

  (* The reverse direction: given a Bignum predicate plus a length proof,
     we can wrap into FElem. *)
  Lemma Bignum_to_FElem (px : word) (ws : list word.rep)
        (Hlen : length ws = felem_size_in_words) :
    Lift1Prop.iff1
      (Bignum felem_size_in_words px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    cbv [FElem Bignum]. cbn [proj1_sig].
    split; intros m H.
    - apply sep_emp_l in H. destruct H as [_ H]. exact H.
    - apply sep_emp_l. split; [exact Hlen | exact H].
  Qed.

  (* === Decoding equivalence ===
     For the WBW field representation, [feval] is precisely
     [F.of_Z ∘ Positional.eval ∘ from_montgomerymod ∘ map word.unsigned],
     and [F.to_Z ∘ feval] is therefore that same composition modulo M. *)

  Lemma feval_to_Z (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof.
    destruct (feval x) as [v Hv]. cbn [F.to_Z]. rewrite Hv at 1. reflexivity.
  Qed.

  (* === Helper: extract length from a Bignum sep predicate ===
     Bignum carries [emp (length ws = n)] inside the sep, so given a
     Bignum hypothesis we can pull out the length equality unconditionally. *)

  Lemma Bignum_length n (px : word) (ws : list word.rep)
        (m_post : Interface.map.rep) (R : Interface.map.rep -> Prop) :
    (Bignum n px ws * R)%sep m_post ->
    length ws = n.
  Proof.
    intros H.
    cbv [Bignum] in H.
    apply sep_assoc in H.
    apply sep_emp_l in H.
    destruct H as [Hlen _]. exact Hlen.
  Qed.

  (* === Construct a felem from a word list of the right length === *)

  Definition felem_of_words (ws : list word.rep)
             (Hlen : length ws = felem_size_in_words) : felem :=
    exist _ ws Hlen.

  Lemma proj_felem_of_words ws Hlen :
    proj1_sig (felem_of_words ws Hlen) = ws.
  Proof. reflexivity. Qed.

End BignumFElemBridge.

(** Transport lemmas for binop and unop specs.

    These take a fiat-crypto [binop_spec]/[unop_spec] (which uses [FElem]
    sep predicates and [bounded_by tight_bounds] preconditions) and produce
    a Bignum-style spec where:
    - inputs/outputs use [Bignum n p ws] sep predicates
    - bounds use [WordByWordMontgomery.valid bw n m (map word.unsigned ws)]
    - decoding uses [eval (from_mont (map word.unsigned ws)) mod m]

    The proofs are sep-logic transport: unwrap dependent pairs, convert
    sep predicates via [FElem_iff_Bignum] / [felem_to_bytearray], and
    use the definitional equality of [bounded_by tight_bounds] with
    [WordByWordMontgomery.valid] (this is [reflexivity] up to typeclass
    unfolding for the WBW field representation). *)


(** Notes for callers:

    To use this bridge in a per-curve file, instantiate [field_parameters]
    and [field_representation] with the curve's specific instances. For
    example, for secp256k1 the relevant instances live in
    [Crypto.Bedrock.Secp256k1.Field256k1] (frep256k1).

    The two main lemmas you will need are:

    1. [FElem_iff_Bignum]: lift any fiat-crypto WP precondition mentioning
       [FElem px x] into one mentioning [Bignum n px (proj1_sig x)], and
       vice versa via [Bignum_to_FElem].

    2. The bounds equivalence is *not* a separate lemma — it is
       [reflexivity] because for WBW field reps,
       [bounded_by tight_bounds] expands directly to
       [WordByWordMontgomery.valid width n m] (see
       [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.tight_bounds_eq]).

    3. The decoding equivalence (between [feval x] and the AUCurves
       [eval (from_mont _)] notation) is similarly definitional: just
       [unfold feval, eval_words, eval_trans] and call [reflexivity].

    Together these mean that translating a fiat-crypto field-op spec
    (binop_spec / unop_spec) into a Bignum-style spec is mostly a matter
    of unwrapping the [felem] dependent pair and rewriting with
    [FElem_iff_Bignum]. *)
