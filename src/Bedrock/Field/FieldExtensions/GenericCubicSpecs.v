(** * Generic cubic extension specs: FieldParameters + FieldRepresentation.

    Parameterized over any base field with FieldParameters and
    FieldRepresentation instances.  Replaces CubicFieldExtensionsSpecs.v
    (which is hardcoded to Fp2 = F M_pos × F M_pos).

    Instances:
      - [CE_field_parameters]      : FieldParameters (BaseField * BaseField * BaseField)
      - [CE_field_representation]  : FieldRepresentation (F := ...)
      - [CE_field_representation_ok] *)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Crypto.Algebra.Hierarchy.

Local Open Scope Z_scope.

Section GenericCubicExtension.

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

  (** mul_by_nr : multiplication by the cubic non-residue in the base field.
      For Fp6 = Fp2[v]/(v³ - ξ), this is fp2_mul_xi (multiply by ξ). *)
  Variable mul_by_nr : BaseField -> BaseField.

  Variable prefix : string.

  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation CE := (BaseField * BaseField * BaseField)%type.

  (* ================================================================ *)
  (* FieldParameters instance                                          *)
  (* ================================================================ *)

  Instance CE_field_parameters : FieldParameters CE :=
    {| Fzero := @ce_zero _ base_fp;
       Fone  := @ce_one _ base_fp;
       Feq   := @eq CE;
       Fopp  := @ce_opp _ base_fp;
       Finv  := @ce_inv _ base_fp mul_by_nr;
       Fadd  := @ce_add _ base_fp;
       Fsub  := @ce_sub _ base_fp;
       Fmul  := @ce_mul _ base_fp mul_by_nr;
       Fdiv  := @ce_div _ base_fp mul_by_nr;
       Feq_dec := @eq_dec_CE _ eq_dec_base;
       a24   := @ce_zero _ base_fp;
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

  Definition ce_c0_felem (l : list word) : list word := firstn base_size l.
  Definition ce_c1_felem (l : list word) : list word :=
    firstn base_size (skipn base_size l).
  Definition ce_c2_felem (l : list word) : list word := skipn (2 * base_size) l.

  Definition ce_c0_felem_bytes (l : list byte) : list byte :=
    firstn (Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr)) l.
  Definition ce_c1_felem_bytes (l : list byte) : list byte :=
    firstn (Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr))
           (skipn (Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr)) l).
  Definition ce_c2_felem_bytes (l : list byte) : list byte :=
    skipn (2 * Z.to_nat (@felem_size_in_bytes _ base_fp _ _ _ _ base_repr)) l.

  (* ================================================================ *)
  (* FieldRepresentation instance                                      *)
  (* ================================================================ *)

  Local Definition CE_feval (ws : list word) : CE :=
    ((@feval _ base_fp _ _ _ _ base_repr (ce_c0_felem ws),
      @feval _ base_fp _ _ _ _ base_repr (ce_c1_felem ws)),
     @feval _ base_fp _ _ _ _ base_repr (ce_c2_felem ws)).

  Local Definition CE_feval_bytes (bs : list byte) : CE :=
    ((@feval_bytes _ base_fp _ _ _ _ base_repr (ce_c0_felem_bytes bs),
      @feval_bytes _ base_fp _ _ _ _ base_repr (ce_c1_felem_bytes bs)),
     @feval_bytes _ base_fp _ _ _ _ base_repr (ce_c2_felem_bytes bs)).

  Instance CE_field_representation : @FieldRepresentation CE CE_field_parameters width BW word mem.
  Proof.
    econstructor.
      - exact CE_feval.
      - exact CE_feval_bytes.
      - exact (3 * base_size)%nat.
      - exact (3 * @encoded_felem_size_in_bytes _ base_fp _ _ _ _ base_repr)%nat.
      - exact (fun bs =>
                 @bytes_in_bounds _ base_fp _ _ _ _ base_repr (ce_c0_felem_bytes bs)
              /\ @bytes_in_bounds _ base_fp _ _ _ _ base_repr (ce_c1_felem_bytes bs)
              /\ @bytes_in_bounds _ base_fp _ _ _ _ base_repr (ce_c2_felem_bytes bs)).
      - exact (fun (y : @bounds _ base_fp _ _ _ _ base_repr) felem =>
                 @bounded_by _ base_fp _ _ _ _ base_repr y (ce_c0_felem felem)
              /\ @bounded_by _ base_fp _ _ _ _ base_repr y (ce_c1_felem felem)
              /\ @bounded_by _ base_fp _ _ _ _ base_repr y (ce_c2_felem felem)).
      - exact (@loose_bounds _ base_fp _ _ _ _ base_repr).
      - exact (@tight_bounds _ base_fp _ _ _ _ base_repr).
  Defined.

  Instance CE_field_representation_ok
    : @FieldRepresentation_ok CE CE_field_parameters _ _ _ _ CE_field_representation.
  Proof.
    econstructor. intros X [H0 [H1 H2]].
    split; [|split]; apply (@relax_bounds _ _ _ _ _ _ _ base_repr_ok); assumption.
  Defined.

End GenericCubicExtension.
