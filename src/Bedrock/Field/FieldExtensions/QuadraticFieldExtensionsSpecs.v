Require Import Rupicola.Lib.Api.
Require Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.FieldExtensions.Theory.FieldsUtil.
Require Import Crypto.Algebra.Hierarchy.
From Stdlib Require Import Numbers.DecimalString.

Local Open Scope Z_scope.

Section QuadraticExtension.

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

  (* Quadratic non-residue β for Fp2 = Fp[u]/(u² - β).
     Declared after Context so that after Section closure,
     beta/beta_nz/beta_qnr/M_big are the LAST explicit args. *)
  Variable beta : F M_pos.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big : 2 < M_pos.

  Local Notation Fp2 := ((F M_pos) * (F M_pos))%type.

  (* Fp2 function name prefix, provided by downstream code *)
  Variable fp2_prefix : string.

  Instance Fp2_field_parameters : AbstractField.FieldParameters Fp2.
  Proof.
      econstructor.
        - exact (zerop2 M_pos).
        - exact (onep2 M_pos).
        - exact (oppp2 M_pos).
        - exact (invp2 M_pos beta).
        - exact (addp2 M_pos).
        - exact (subp2 M_pos).
        - exact (mulp2 M_pos beta).
        - exact (divp2 M_pos beta).
        - eapply eq_dec_Fp2.
        - exact (F.zero, F.zero). (* a24 — dummy for Weierstrass curves *)
        - exact (fp2_prefix ++ "mul")%string.
        - exact (fp2_prefix ++ "add")%string.
        - exact (fp2_prefix ++ "sub")%string.
        - exact (fp2_prefix ++ "opp")%string.
        - exact (fp2_prefix ++ "square")%string.
        - exact (fp2_prefix ++ "scmula24")%string.
        - exact (fp2_prefix ++ "inv")%string.
        - exact (fp2_prefix ++ "from_bytes")%string.
        - exact (fp2_prefix ++ "to_bytes")%string.
        - exact (fp2_prefix ++ "select_znz")%string.
        - exact (fp2_prefix ++ "felem_copy")%string.
        - exact (fp2_prefix ++ "from_word")%string.
        - exact (fp2_prefix ++ "from_list")%string.
  Defined.

  Instance Fp2_field_parameters_ok : @AbstractField.FieldParameters_ok _ Fp2_field_parameters.
  Proof.
    econstructor;
    exact (@std_to_fiatCrypto_field _ _ _ _ _ _ _ _ _ (FFp2 M_pos M_prime M_big beta beta_nz beta_qnr)).
  Defined.

  Definition fst_felem (Fp2_list : list word) : list word := firstn felem_size_in_words Fp2_list.
  Definition snd_felem (Fp2_list : list word) : list word := skipn felem_size_in_words Fp2_list.

  Definition fst_felem_bytes (Fp2_list : list byte) : list byte := firstn (Z.to_nat felem_size_in_bytes) Fp2_list.
  Definition snd_felem_bytes (Fp2_list : list byte) : list byte := skipn (Z.to_nat felem_size_in_bytes) Fp2_list.

  Instance Fp2_field_representation : AbstractField.FieldRepresentation (F:=Fp2).
  Proof.
    econstructor.
      - exact (fun y => (feval (fst_felem y), feval (snd_felem y))).
      - exact (fun y => (feval_bytes (fst_felem_bytes y), feval_bytes (snd_felem_bytes y))).
      - exact (2 * felem_size_in_words)%nat.
      - exact (2 * encoded_felem_size_in_bytes)%nat.
      - exact (fun y => bytes_in_bounds (fst_felem_bytes y) /\ bytes_in_bounds (snd_felem_bytes y)).
      - exact (fun (y : bounds) felem => (bounded_by y (fst_felem felem)) /\ (bounded_by y (snd_felem felem))).
      - exact loose_bounds.
      - exact tight_bounds.
  Defined.

  Instance Fp2_field_representation_ok : @AbstractField.FieldRepresentation_ok _ _ _ _ _ _ Fp2_field_representation.
  Proof.
    econstructor; destruct field_representation_ok; intros.
    split; eapply relax_bounds; apply H.
  Defined.

End QuadraticExtension.
