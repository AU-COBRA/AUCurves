(** * Bedrock2 field specs for cubic extensions (Fp6 = Fp2[v]/(v^3 - xi)).

    Analogous to QuadraticFieldExtensionsSpecs.v for Fp2.

    An Fp6 element is a triple (c0, c1, c2) of Fp2 elements stored
    consecutively in memory: 3 Fp2 elements = 6 Fp elements.

    We define FieldParameters/FieldRepresentation instances so that the
    generic AbstractField spec machinery (binop_spec, unop_spec, etc.)
    can be reused for Fp6 operations.
*)

Require Import Rupicola.Lib.Api.
Require Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.FieldExtensions.Theory.FieldsUtil.
Require Import Crypto.Algebra.Hierarchy.
Require Theory.BLS12Pairing.Fp6.
Module BLS12Fp6Spec := Theory.BLS12Pairing.Fp6.
From Stdlib Require Import Numbers.DecimalString.

Local Open Scope Z_scope.

Section CubicExtension.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_parameters : PrimeFieldParameters}
          {prime_parameters_ok : PrimeFieldParameters_ok}.
  Existing Instance prime_field_parameters.
  Context {field_representation : AbstractField.FieldRepresentation}
          {field_representation_ok : AbstractField.FieldRepresentation_ok}.

  Variable beta : F M_pos.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big_cubic : 2 < M_pos.

  (* ξ = (xi_re, xi_im) in Fp2 — the cubic non-residue for Fp6 = Fp2[v]/(v³ - ξ) *)
  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Context {fp6_prefix : string}.
  Context {fp2_prefix : string}.

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters field_representation beta fp2_prefix.

  (* ================================================================ *)
  (* Fp6 Gallina operations (from Theory.BLS12Pairing.Fp6)              *)
  (* ================================================================ *)

  Local Definition fp6_zero_val : Fp6 := BLS12Fp6Spec.fp6_zero M_pos.
  Local Definition fp6_one_val  : Fp6 := BLS12Fp6Spec.fp6_one M_pos.
  Local Definition fp6_add_fn := BLS12Fp6Spec.fp6_add M_pos.
  Local Definition fp6_sub_fn := BLS12Fp6Spec.fp6_sub M_pos.
  Local Definition fp6_neg_fn := BLS12Fp6Spec.fp6_neg M_pos.
  Local Definition fp6_mul_fn := BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im.
  Local Definition fp6_sqr_fn := BLS12Fp6Spec.fp6_sqr M_pos beta xi_re xi_im.
  Local Definition fp6_inv_fn := BLS12Fp6Spec.fp6_inv M_pos beta xi_re xi_im.

  (* Fp6 division defined in terms of mul and inv *)
  Local Definition fp6_div_fn (a b : Fp6) : Fp6 := fp6_mul_fn a (fp6_inv_fn b).

  (* Decidable equality for Fp2 — from two Fp decisions *)
  Local Instance eq_dec_Fp2_local : DecidableRel (@eq Fp2).
  Proof.
    intros [a0 a1] [b0 b1].
    destruct (F.eq_dec a0 b0); [|right; intro H; inversion H; contradiction].
    destruct (F.eq_dec a1 b1); [|right; intro H; inversion H; contradiction].
    left. subst. reflexivity.
  Defined.

  (* Decidable equality for Fp6 — from three Fp2 decisions *)
  Local Instance eq_dec_Fp6 : DecidableRel (@eq Fp6).
  Proof.
    intros x y.
    destruct x as [[x0 x1] x2]. destruct y as [[y0 y1] y2].
    destruct (eq_dec_Fp2_local x0 y0); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_Fp2_local x1 y1); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_Fp2_local x2 y2); [|right; intro H; inversion H; contradiction].
    left. subst. reflexivity.
  Defined.

  (* ================================================================ *)
  (* Fp6 FieldParameters instance                                      *)
  (* ================================================================ *)

  Instance Fp6_field_parameters : AbstractField.FieldParameters Fp6.
  Proof.
    econstructor.
      - exact fp6_zero_val.
      - exact fp6_one_val.
      - exact fp6_neg_fn.
      - exact fp6_inv_fn.
      - exact fp6_add_fn.
      - exact fp6_sub_fn.
      - exact fp6_mul_fn.
      - exact fp6_div_fn.
      - eapply eq_dec_Fp6.
      - exact fp6_zero_val. (* a24 — dummy for curves *)
      - exact (fp6_prefix ++ "mul")%string.
      - exact (fp6_prefix ++ "add")%string.
      - exact (fp6_prefix ++ "sub")%string.
      - exact (fp6_prefix ++ "opp")%string.
      - exact (fp6_prefix ++ "square")%string.
      - exact (fp6_prefix ++ "scmula24")%string.
      - exact (fp6_prefix ++ "inv")%string.
      - exact (fp6_prefix ++ "from_bytes")%string.
      - exact (fp6_prefix ++ "to_bytes")%string.
      - exact (fp6_prefix ++ "select_znz")%string.
      - exact (fp6_prefix ++ "felem_copy")%string.
      - exact (fp6_prefix ++ "from_word")%string.
      - exact (fp6_prefix ++ "from_list")%string.
  Defined.

  (* ================================================================ *)
  (* Fp6 element decomposition helpers                                 *)
  (* ================================================================ *)

  (* An Fp6 element in memory is 3 consecutive Fp2 elements.
     Each Fp2 is 2 * felem_size_in_words words.
     So Fp6 is 6 * felem_size_in_words words = 3 * Fp2_size words. *)

  Local Notation Fp2_size_in_words := (2 * AbstractField.felem_size_in_words (F:=Fp))%nat.
  Local Notation Fp6_size_in_words := (3 * Fp2_size_in_words)%nat.

  (* Decompose an Fp6 word list into 3 Fp2 components *)
  Definition c0_felem (Fp6_list : list word) : list word := firstn Fp2_size_in_words Fp6_list.
  Definition c1_felem (Fp6_list : list word) : list word := firstn Fp2_size_in_words (skipn Fp2_size_in_words Fp6_list).
  Definition c2_felem (Fp6_list : list word) : list word := skipn (2 * Fp2_size_in_words) Fp6_list.

  Definition c0_felem_bytes (Fp6_list : list byte) : list byte :=
    firstn (Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp2))) Fp6_list.
  Definition c1_felem_bytes (Fp6_list : list byte) : list byte :=
    firstn (Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp2)))
           (skipn (Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp2))) Fp6_list).
  Definition c2_felem_bytes (Fp6_list : list byte) : list byte :=
    skipn (2 * Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp2))) Fp6_list.

  (* ================================================================ *)
  (* Fp6 FieldRepresentation instance                                  *)
  (* ================================================================ *)

  (* Evaluate an Fp6 element from its word-level representation *)
  Local Definition Fp6_feval (ws : list word) : Fp6 :=
    ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
      @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws)).

  Local Definition Fp6_feval_bytes (bs : list byte) : Fp6 :=
    ((@AbstractField.feval_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem_bytes bs),
      @AbstractField.feval_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem_bytes bs)),
     @AbstractField.feval_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem_bytes bs)).

  Instance Fp6_field_representation : AbstractField.FieldRepresentation (F:=Fp6).
  Proof.
    econstructor.
      - exact Fp6_feval.
      - exact Fp6_feval_bytes.
      - exact Fp6_size_in_words.
      - exact (3 * AbstractField.encoded_felem_size_in_bytes (F:=Fp2))%nat.
      - exact (fun bs => @AbstractField.bytes_in_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem_bytes bs)
                       /\ @AbstractField.bytes_in_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem_bytes bs)
                       /\ @AbstractField.bytes_in_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem_bytes bs)).
      - exact (fun (y : @AbstractField.bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) felem =>
                 @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst y (c0_felem felem)
              /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst y (c1_felem felem)
              /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst y (c2_felem felem)).
      - exact (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
      - exact (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Defined.

  Instance Fp6_field_representation_ok : @AbstractField.FieldRepresentation_ok _ _ _ _ _ _ Fp6_field_representation.
  Proof.
    econstructor; destruct field_representation_ok; intros.
    destruct H as [H0 [H1 H2]].
    unfold bounded_by, loose_bounds, tight_bounds in *; simpl in *.
    split; [|split]; destruct_products; split; apply relax_bounds; assumption.
  Defined.

End CubicExtension.
