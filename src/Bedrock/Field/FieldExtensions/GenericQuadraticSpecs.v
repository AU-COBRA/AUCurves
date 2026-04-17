(** * Generic quadratic extension specs: FieldParameters + FieldRepresentation.

    Parameterized over any base field with FieldParameters and
    FieldRepresentation instances.  Replaces QuadraticFieldExtensionsSpecs.v
    (which is hardcoded to PrimeFieldParameters / F M_pos).

    Instances:
      - [QE_field_parameters]      : FieldParameters (BaseField * BaseField)
      - [QE_field_representation]  : FieldRepresentation (F := BaseField * BaseField)
      - [QE_field_representation_ok] *)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Crypto.Algebra.Hierarchy.

Local Open Scope Z_scope.

Section GenericQuadraticExtension.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* ================================================================ *)
  (* Base field parameters                                             *)
  (* ================================================================ *)

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable nonresidue : BaseField.
  Variable prefix : string.

  (* Decidable Leibniz equality on the base field — needed for the extension. *)
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation QE := (BaseField * BaseField)%type.

  (* ================================================================ *)
  (* FieldParameters instance for the quadratic extension              *)
  (* ================================================================ *)

  Instance QE_field_parameters : FieldParameters QE :=
    {| Fzero := @qe_zero _ base_fp;
       Fone  := @qe_one _ base_fp;
       Feq   := @eq QE;
       Fopp  := @qe_opp _ base_fp;
       Finv  := @qe_inv _ base_fp nonresidue;
       Fadd  := @qe_add _ base_fp;
       Fsub  := @qe_sub _ base_fp;
       Fmul  := @qe_mul _ base_fp nonresidue;
       Fdiv  := @qe_div _ base_fp nonresidue;
       Feq_dec := @eq_dec_QE _ eq_dec_base;
       a24   := @qe_zero _ base_fp;
       mul   := (prefix ++ "mul")%string;
       add   := (prefix ++ "add")%string;
       sub   := (prefix ++ "sub")%string;
       opp   := (prefix ++ "opp")%string;
       square := (prefix ++ "square")%string;
       scmula24 := (prefix ++ "scmula24")%string;
       inv   := (prefix ++ "inv")%string;
       from_bytes := (prefix ++ "from_bytes")%string;
       to_bytes := (prefix ++ "to_bytes")%string;
       select_znz := (prefix ++ "select_znz")%string;
       felem_copy := (prefix ++ "felem_copy")%string;
       from_word := (prefix ++ "from_word")%string;
       from_list := (prefix ++ "from_list")%string;
    |}.

  (* ================================================================ *)
  (* Element decomposition helpers                                     *)
  (* ================================================================ *)

  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).

  (* Canonical decomposition functions — imported by GenericSplitJoin and proofs *)
  Definition qe_fst_felem (l : list word) : list word := firstn base_size l.
  Definition qe_snd_felem (l : list word) : list word := skipn base_size l.
  Definition qe_offset_word : word := word.of_Z (Memory.bytes_per_word width * Z.of_nat base_size).

  Definition qe_fst_felem_bytes (l : list byte) : list byte :=
    firstn (Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr)) l.
  Definition qe_snd_felem_bytes (l : list byte) : list byte :=
    skipn (Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr)) l.

  (* ================================================================ *)
  (* FieldRepresentation instance                                      *)
  (* ================================================================ *)

  Local Definition QE_feval (ws : list word) : QE :=
    (@feval _ base_fp _ _ _ _ base_repr (qe_fst_felem ws),
     @feval _ base_fp _ _ _ _ base_repr (qe_snd_felem ws)).

  Local Definition QE_feval_bytes (bs : list byte) : QE :=
    (@feval_bytes _ base_fp _ _ _ _ base_repr (qe_fst_felem_bytes bs),
     @feval_bytes _ base_fp _ _ _ _ base_repr (qe_snd_felem_bytes bs)).

  Instance QE_field_representation : @FieldRepresentation QE QE_field_parameters width BW word mem.
  Proof.
    econstructor.
      - exact QE_feval.
      - exact QE_feval_bytes.
      - exact (2 * base_size)%nat.
      - exact (2 * @encoded_felem_size_in_bytes _ base_fp _ _ _ _ base_repr)%nat.
      - exact (fun bs => @bytes_in_bounds _ base_fp _ _ _ _ base_repr (qe_fst_felem_bytes bs)
                       /\ @bytes_in_bounds _ base_fp _ _ _ _ base_repr (qe_snd_felem_bytes bs)).
      - exact (fun (y : @bounds _ base_fp _ _ _ _ base_repr) felem =>
                 @bounded_by _ base_fp _ _ _ _ base_repr y (qe_fst_felem felem)
              /\ @bounded_by _ base_fp _ _ _ _ base_repr y (qe_snd_felem felem)).
      - exact (@loose_bounds _ base_fp _ _ _ _ base_repr).
      - exact (@tight_bounds _ base_fp _ _ _ _ base_repr).
  Defined.

  Instance QE_field_representation_ok
    : @FieldRepresentation_ok QE QE_field_parameters _ _ _ _ QE_field_representation.
  Proof.
    econstructor. intros X [H0 H1].
    split; apply (@relax_bounds _ _ _ _ _ _ _ base_repr_ok); assumption.
  Defined.

End GenericQuadraticExtension.
