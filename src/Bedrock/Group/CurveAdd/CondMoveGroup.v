Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
    {field_representation_ok : FieldRepresentation_ok}
    {group_cmov : string}.

  Local Notation F := (F M_pos).
  Notation F_cmov := select_znz.

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_group_cmov : spec_of group_cmov :=
    fnspec! group_cmov
      (pXout pYout pZout pX1 pY1 pZ1 pX2 pY2 pZ2 pc : word)
      / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) c R,
      { requires tr mem :=
          (FElem (Some tight_bounds) pX1 X1
           * FElem (Some tight_bounds) pX2 X2
           * FElem (Some tight_bounds) pY1 Y1
           * FElem (Some tight_bounds) pY2 Y2
           * FElem (Some tight_bounds) pZ1 Z1
           * FElem (Some tight_bounds) pZ2 Z2
           * FElem (Some tight_bounds) pXout Xoutold
           * FElem (Some tight_bounds) pYout Youtold
           * FElem (Some tight_bounds) pZout Zoutold
           * scalar pc c
           * R)%sep mem /\
            ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true;
        ensures tr' mem' :=
          exists Xout Yout Zout (* output values *)
            : F , exists cout,
            (
              (if ((word.unsigned c) =? 1)
               then (Xout = X2)
               else (Xout = X1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Yout = Y2)
                 else (Yout = Y1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Zout = Z2)
                 else (Zout = Z1))
            )
            /\ (FElem (Some tight_bounds) pX1 X1
               * FElem (Some tight_bounds) pX2 X2
               * FElem (Some tight_bounds) pY1 Y1
               * FElem (Some tight_bounds) pY2 Y2
               * FElem (Some tight_bounds) pZ1 Z1
               * FElem (Some tight_bounds) pZ2 Z2
               * FElem (Some tight_bounds) pXout Xout
               * FElem (Some tight_bounds) pYout Yout
               * FElem (Some tight_bounds) pZout Zout
               * scalar pc cout
               * R)%sep mem'}.


  Definition cmov_func : function_t :=
    (group_cmov, (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (F_cmov) [expr.var ("outx"); expr.load access_size.word (expr.var ("pc")); expr.var ("x1"); expr.var("x2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("outy"); expr.load access_size.word (expr.var ("pc")); expr.var ("y1"); expr.var("y2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("outz"); expr.load access_size.word (expr.var ("pc")); expr.var ("z1"); expr.var("z2")])))).

  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (cmov_func :: nil)). *)
  (* Eval native_compute in c_mod. *)

  Ltac solve_locals l1 := subst l1; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

  Local Instance spec_of_select_znz : spec_of select_znz := spec_of_selectznz.

  (* TODO: Move? *)
  Lemma bignum_1_scalar pc c :
    forall m R, (@Bignum.Bignum width word mem 1 pc [c] ⋆ R) m <-> (scalar pc c ⋆ R) m.
  intros. apply Util.iff1_sep_cancel_both.
    unfold Bignum.Bignum. simpl. split.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - easy.
  Qed.

  Lemma cmov_ok : program_logic_goal_for_function! cmov_func.
  Proof. exact I. Qed.

End __.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
    {field_representation_ok : FieldRepresentation_ok}
    {group_cmov_alt : string}.

  Local Notation F := (F M_pos).
  Notation F_cmov := select_znz.

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_group_cmov_alt : spec_of group_cmov_alt :=
    fnspec! group_cmov_alt
      (pXout pYout pZout pX1 pY1 pZ1 pX2 pY2 pZ2 pc : word)
      / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) c R1 R2 Rc Rout,
      { requires tr mem :=
          (FElem (Some tight_bounds) pX1 X1
           ⋆ FElem (Some tight_bounds) pY1 Y1
           ⋆ FElem (Some tight_bounds) pZ1 Z1
           ⋆ R1) mem
           /\ (FElem (Some tight_bounds) pX2 X2
              ⋆ FElem (Some tight_bounds) pY2 Y2
              ⋆ FElem (Some tight_bounds) pZ2 Z2
              ⋆ R2) mem
           /\ (FElem (Some tight_bounds) pXout Xoutold
              ⋆ FElem (Some tight_bounds) pYout Youtold
              ⋆ FElem (Some tight_bounds) pZout Zoutold
              ⋆ Rout) mem
          /\ (scalar pc c ⋆ Rc) mem
          /\ ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true;
        ensures tr' mem' :=
          tr = tr' /\
          exists Xout Yout Zout (* output values *),
            ((if ((word.unsigned c) =? 1)
               then (Xout = X2)
               else (Xout = X1))
              /\ (if ((word.unsigned c) =? 1)
                 then (Yout = Y2)
                 else (Yout = Y1))
              /\ (if ((word.unsigned c) =? 1)
                 then (Zout = Z2)
                 else (Zout = Z1)))
            /\ (FElem (Some tight_bounds) pXout Xout
               * FElem (Some tight_bounds) pYout Yout
               * FElem (Some tight_bounds) pZout Zout
               * Rout)%sep mem'}.

  Definition cmov_alt_func : function_t :=
    (group_cmov_alt, (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"], []:list String.string, bedrock_func_body:(
      stackalloc felem_size_in_bytes as auxx;
      stackalloc felem_size_in_bytes as auxy;
      stackalloc felem_size_in_bytes as auxz;
      coq:(cmd.call [] (F_cmov) [expr.var ("auxx"); expr.load access_size.word (expr.var ("pc")); expr.var ("x1"); expr.var("x2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("auxy"); expr.load access_size.word (expr.var ("pc")); expr.var ("y1"); expr.var("y2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("auxz"); expr.load access_size.word (expr.var ("pc")); expr.var ("z1"); expr.var("z2")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outx"); expr.var ("auxx")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outy"); expr.var ("auxy")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outz"); expr.var ("auxz")])))).

  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (cmov_func :: nil)). *)
  (* Eval native_compute in c_mod. *)

  Ltac solve_locals l1 := subst l1; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

  Local Instance spec_of_select_znz' : spec_of select_znz := spec_of_selectznz.
  Local Instance spec_of_felem_copy : spec_of felem_copy := spec_of_felem_copy.

  Lemma cmov_alt_ok : program_logic_goal_for_function! cmov_alt_func.
  Proof. exact I. Qed.

End __.
#[global] Existing Instance spec_of_group_cmov.
#[global] Existing Instance spec_of_group_cmov_alt.
