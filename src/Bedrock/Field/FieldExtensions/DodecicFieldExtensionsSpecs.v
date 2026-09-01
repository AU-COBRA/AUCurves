(** * Bedrock2 field specs for dodecic extensions (Fp12 = Fp6[w]/(w^2 - v)).

    Analogous to CubicFieldExtensionsSpecs.v for Fp6.

    An Fp12 element is a pair (c0, c1) of Fp6 elements stored
    consecutively in memory: 2 Fp6 elements = 6 Fp2 elements = 12 Fp elements.

    We define FieldParameters/FieldRepresentation instances so that the
    generic AbstractField spec machinery (binop_spec, unop_spec, etc.)
    can be reused for Fp12 operations.
*)

Require Import Rupicola.Lib.Api.
Require Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.FieldExtensions.Theory.FieldsUtil.
Require Import Crypto.Algebra.Hierarchy.
Require Theory.BLS12Pairing.Fp12.
Module BLS12Fp12Spec := Theory.BLS12Pairing.Fp12.
From Stdlib Require Import Numbers.DecimalString.

Local Open Scope Z_scope.

Section DodecicExtension.

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
  Hypothesis M_big_dodecic : 2 < M_pos.

  (* ξ = (xi_re, xi_im) in Fp2 — the cubic non-residue for Fp6 = Fp2[v]/(v³ - ξ) *)
  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  (* Fp12 function name prefix, provided by downstream code *)
  Context {fp12_prefix : string}.
  (* Fp6 and Fp2 prefixes needed for the underlying layer instances *)
  Context {fp6_prefix : string}.
  Context {fp2_prefix : string}.

  (* We need Fp2 and Fp6 field parameters and representations from lower layers *)
  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters field_representation beta fp2_prefix.

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters beta xi_re xi_im (fp6_prefix:=fp6_prefix).
  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* Fp12 Gallina operations (from Theory.BLS12Pairing.Fp12)            *)
  (* ================================================================ *)

  Local Definition fp12_zero_val : Fp12 := BLS12Fp12Spec.fp12_zero M_pos.
  Local Definition fp12_one_val  : Fp12 := BLS12Fp12Spec.fp12_one M_pos.
  Local Definition fp12_add_fn := BLS12Fp12Spec.fp12_add M_pos.
  Local Definition fp12_sub_fn := BLS12Fp12Spec.fp12_sub M_pos.
  Local Definition fp12_neg_fn := BLS12Fp12Spec.fp12_neg M_pos.
  Local Definition fp12_mul_fn := BLS12Fp12Spec.fp12_mul M_pos beta xi_re xi_im.
  Local Definition fp12_inv_fn := BLS12Fp12Spec.fp12_inv M_pos beta xi_re xi_im.

  (* Fp12 division defined in terms of mul and inv *)
  Local Definition fp12_div_fn (a b : Fp12) : Fp12 := fp12_mul_fn a (fp12_inv_fn b).

  (* ================================================================ *)
  (* Decidable equality                                                *)
  (* ================================================================ *)

  (* Decidable equality for Fp2 -- from two Fp decisions *)
  Local Instance eq_dec_Fp2_local : DecidableRel (@eq Fp2).
  Proof.
    intros [a0 a1] [b0 b1].
    destruct (F.eq_dec a0 b0); [|right; intro H; inversion H; contradiction].
    destruct (F.eq_dec a1 b1); [|right; intro H; inversion H; contradiction].
    left. subst. reflexivity.
  Defined.

  (* Decidable equality for Fp6 -- from three Fp2 decisions *)
  Local Instance eq_dec_Fp6_local : DecidableRel (@eq Fp6).
  Proof.
    intros x y.
    destruct x as [[x0 x1] x2]. destruct y as [[y0 y1] y2].
    destruct (eq_dec_Fp2_local x0 y0); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_Fp2_local x1 y1); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_Fp2_local x2 y2); [|right; intro H; inversion H; contradiction].
    left. subst. reflexivity.
  Defined.

  (* Decidable equality for Fp12 -- from two Fp6 decisions *)
  Local Instance eq_dec_Fp12 : DecidableRel (@eq Fp12).
  Proof.
    intros [x0 x1] [y0 y1].
    destruct (eq_dec_Fp6_local x0 y0); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_Fp6_local x1 y1); [|right; intro H; inversion H; contradiction].
    left. subst. reflexivity.
  Defined.

  (* ================================================================ *)
  (* Fp12 FieldParameters instance                                     *)
  (* ================================================================ *)

  Instance Fp12_field_parameters : AbstractField.FieldParameters Fp12.
  Proof.
    econstructor.
      - exact fp12_zero_val.
      - exact fp12_one_val.
      - exact fp12_neg_fn.
      - exact fp12_inv_fn.
      - exact fp12_add_fn.
      - exact fp12_sub_fn.
      - exact fp12_mul_fn.
      - exact fp12_div_fn.
      - eapply eq_dec_Fp12.
      - exact fp12_zero_val. (* a24 -- dummy for curves *)
      - exact (fp12_prefix ++ "mul")%string.
      - exact (fp12_prefix ++ "add")%string.
      - exact (fp12_prefix ++ "sub")%string.
      - exact (fp12_prefix ++ "opp")%string.
      - exact (fp12_prefix ++ "square")%string.
      - exact (fp12_prefix ++ "scmula24")%string.
      - exact (fp12_prefix ++ "inv")%string.
      - exact (fp12_prefix ++ "from_bytes")%string.
      - exact (fp12_prefix ++ "to_bytes")%string.
      - exact (fp12_prefix ++ "select_znz")%string.
      - exact (fp12_prefix ++ "felem_copy")%string.
      - exact (fp12_prefix ++ "from_word")%string.
      - exact (fp12_prefix ++ "from_list")%string.
  Defined.

  (* ================================================================ *)
  (* Fp12 element decomposition helpers                                *)
  (* ================================================================ *)

  (* An Fp12 element in memory is 2 consecutive Fp6 elements.
     Each Fp6 is 3 * Fp2_size_in_words words.
     So Fp12 is 6 * Fp2_size_in_words words = 2 * Fp6_size words. *)

  Local Notation Fp2_size_in_words := (2 * AbstractField.felem_size_in_words (F:=Fp))%nat.
  Local Notation Fp6_size_in_words := (3 * Fp2_size_in_words)%nat.
  Local Notation Fp12_size_in_words := (2 * Fp6_size_in_words)%nat.

  (* Decompose an Fp12 word list into 2 Fp6 components *)
  Definition d0_felem (Fp12_list : list word) : list word := firstn Fp6_size_in_words Fp12_list.
  Definition d1_felem (Fp12_list : list word) : list word := skipn Fp6_size_in_words Fp12_list.

  Definition d0_felem_bytes (Fp12_list : list byte) : list byte :=
    firstn (Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp6))) Fp12_list.
  Definition d1_felem_bytes (Fp12_list : list byte) : list byte :=
    skipn (Z.to_nat (AbstractField.felem_size_in_bytes (F:=Fp6))) Fp12_list.

  (* ================================================================ *)
  (* Fp12 FieldRepresentation instance                                 *)
  (* ================================================================ *)

  (* Evaluate an Fp12 element from its word-level representation *)
  Local Definition Fp12_feval (ws : list word) : Fp12 :=
    (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
     @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws)).

  Local Definition Fp12_feval_bytes (bs : list byte) : Fp12 :=
    (@AbstractField.feval_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem_bytes bs),
     @AbstractField.feval_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem_bytes bs)).

  Instance Fp12_field_representation : AbstractField.FieldRepresentation (F:=Fp12).
  Proof.
    econstructor.
      - exact Fp12_feval.
      - exact Fp12_feval_bytes.
      - exact Fp12_size_in_words.
      - exact (2 * AbstractField.encoded_felem_size_in_bytes (F:=Fp6))%nat.
      - exact (fun bs => @AbstractField.bytes_in_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem_bytes bs)
                       /\ @AbstractField.bytes_in_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem_bytes bs)).
      - exact (fun (y : @AbstractField.bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) felem =>
                 @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst y (d0_felem felem)
              /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst y (d1_felem felem)).
      - exact (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      - exact (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Defined.

  Instance Fp12_field_representation_ok : @AbstractField.FieldRepresentation_ok _ _ _ _ _ _ Fp12_field_representation.
  Proof.
    econstructor; destruct field_representation_ok; intros.
    destruct H as [H0 H1].
    unfold bounded_by, loose_bounds, tight_bounds in *; simpl in *.
    split; destruct_products; (split; [|split]); split; apply relax_bounds; assumption.
  Defined.

End DodecicExtension.
