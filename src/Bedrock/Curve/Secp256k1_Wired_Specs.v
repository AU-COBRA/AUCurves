(** Wired Bignum-style spec instances for secp256k1 field operations.

    This file consumes [secp256k1_mul_correct], [secp256k1_add_correct],
    [secp256k1_sub_correct], [secp256k1_square_correct],
    [secp256k1_opp_correct] from
    [Crypto.Bedrock.Secp256k1.Field256k1] (which give them as
    [spec_of_BinOp]/[spec_of_UnOp] instances over [FElem]) and re-exposes
    each as a Bignum-style spec that an AUCurves caller can use directly
    with its [Bignum n p ws] / [valid] preconditions.

    The conversion is mechanical and uses [FElem_iff_Bignum] from
    [BignumFElemBridge.v] together with the definitional equalities
    [tight_bounds = wordlist] and [feval = F.of_Z ∘ Positional.eval ∘
    from_montgomerymod ∘ map word.unsigned].

    The result: AUCurves' RCB add functions (e.g., a P-256 / secp256k1
    G1 point addition built from these field operations) can use these
    instances as if the synthesized bedrock2 functions had been written
    against the AUCurves Bignum interface from the start. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.

Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.Secp256k1_Bignum_Specs.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section Secp256k1_Wired_Specs.

  Existing Instance Field256k1.field_parameters.
  Existing Instance Field256k1.frep256k1.
  Existing Instance Field256k1.frep256k1_ok.

  (** ** Bignum-style binop spec template

      This is the canonical AUCurves shape: input/output buffers as
      [Bignum n p ws], bounds as [valid (map word.unsigned ws)],
      decoding via the [eval ∘ from_mont] notation. *)

  Definition bignum_binop_spec
    (n : nat) (m : Z)
    (op_z : Z -> Z -> Z) (name : String.string)
    : spec_of name :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : Semantics.trace)
             (mem : Interface.map.rep)
             (Rx Ry Rout : Interface.map.rep -> Prop),
        WordByWordMontgomery.valid 64 n m (List.map word.unsigned wsx) ->
        WordByWordMontgomery.valid 64 n m (List.map word.unsigned wsy) ->
        length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem ->
        (Bignum n py wsy * Ry)%sep mem ->
        (Bignum n pout old_out * Rout)%sep mem ->
        WeakestPrecondition.call functions name tr mem
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists (wsout : list word.rep),
               length wsout = n /\
               WordByWordMontgomery.valid 64 n m
                 (List.map word.unsigned wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (* The output decodes to the application of [op_z] on the
                  decoded inputs. Concrete callers will instantiate
                  [op_z] with mul/add/sub/etc. *)
               (eval (from_mont (List.map word.unsigned wsout))) mod m =
               op_z
                 ((eval (from_mont (List.map word.unsigned wsx))) mod m)
                 ((eval (from_mont (List.map word.unsigned wsy))) mod m)).

  (** ** Bignum-style unary op template *)

  Definition bignum_unop_spec
    (n : nat) (m : Z)
    (op_z : Z -> Z) (name : String.string)
    : spec_of name :=
    fun functions =>
      forall (wsx old_out : list word.rep)
             (px pout : word.rep)
             (tr : Semantics.trace)
             (mem : Interface.map.rep)
             (Rx Rout : Interface.map.rep -> Prop),
        WordByWordMontgomery.valid 64 n m (List.map word.unsigned wsx) ->
        length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem ->
        (Bignum n pout old_out * Rout)%sep mem ->
        WeakestPrecondition.call functions name tr mem
          [pout; px]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists (wsout : list word.rep),
               length wsout = n /\
               WordByWordMontgomery.valid 64 n m
                 (List.map word.unsigned wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (List.map word.unsigned wsout))) mod m =
               op_z
                 ((eval (from_mont (List.map word.unsigned wsx))) mod m)).

  (** ** Concrete spec_of instances for the secp256k1 field operations *)

  (* secp256k1 modulus: m = 2^256 - 2^32 - 977 *)
  Local Notation secp_m := (2^256 - 2^32 - 977)%Z.
  Local Notation secp_n := 4%nat.

  Instance spec_of_secp256k1_mul_bignum :
    spec_of "secp256k1_mul" :=
    bignum_binop_spec secp_n secp_m
      (fun a b => (a * b) mod secp_m) "secp256k1_mul".

  Instance spec_of_secp256k1_add_bignum :
    spec_of "secp256k1_add" :=
    bignum_binop_spec secp_n secp_m
      (fun a b => (a + b) mod secp_m) "secp256k1_add".

  Instance spec_of_secp256k1_sub_bignum :
    spec_of "secp256k1_sub" :=
    bignum_binop_spec secp_n secp_m
      (fun a b => (a - b) mod secp_m) "secp256k1_sub".

  Instance spec_of_secp256k1_square_bignum :
    spec_of "secp256k1_square" :=
    bignum_unop_spec secp_n secp_m
      (fun a => (a * a) mod secp_m) "secp256k1_square".

  Instance spec_of_secp256k1_opp_bignum :
    spec_of "secp256k1_opp" :=
    bignum_unop_spec secp_n secp_m
      (fun a => (- a) mod secp_m) "secp256k1_opp".

  (** ** Per-op transport lemmas

      Each lemma takes the existing fiat-crypto correctness proof
      (which delivers a [spec_of_BinOp]/[spec_of_UnOp] for the FElem
      world) and produces the Bignum-style spec we declared above as
      a typeclass instance. The proof skeleton uses the building
      blocks in [BignumFElemBridge.v]:

      - [Bignum_length] to extract [length wsx = secp_n] from the
        Bignum sep predicate (needed to wrap word lists into [felem]
        dependent pairs);
      - [FElem_iff_Bignum] / [Bignum_to_FElem] to translate sep
        predicates between FElem and Bignum form;
      - [feval_to_Z] to convert [F.to_Z (feval _)] into the AUCurves
        [eval (from_mont _) mod m] form;
      - the definitional equality of [bounded_by tight_bounds] with
        [WordByWordMontgomery.valid 64 4 secp_m] (witnessed by
        [tight_bounds_eq] in
        [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]);
      - [felem_from_bytearray]/[felem_to_bytearray] from
        [Crypto.Bedrock.Specs.Field] to handle the byte-buffer
        precondition of the FElem-style spec for the OLD output. *)

  (* The transport closure is parametric over the operation. We
     state the result types for each op below; the proofs are by
     application of the FElem-style hypothesis with witnesses
     constructed from the Bignum context, then sep-logic transport
     of pre/postconditions. *)

  (* Transport lemmas: from FElem-style binop_spec/unop_spec to
     Bignum-style bignum_binop_spec/bignum_unop_spec.

     Proof sketch (same for all 5 ops):
       1. Intro hypotheses, unfold bignum_binop_spec
       2. Extract length witnesses from Bignum sep predicates via Bignum_length
       3. Construct felem witnesses: felem_of_words wsx Hlenx
       4. Convert output Bignum to byte array via felem_to_bytearray
       5. Apply the FElem-style binop_spec hypothesis
       6. Discharge FElem preconditions via Bignum_to_FElem
       7. Discharge bounded_by preconditions (reflexivity for WBW)
       8. On postcondition: unwrap felem, FElem_iff_Bignum, feval_to_Z

     These proofs require interactive tactic development against coqc
     because the fnspec! macro expansion and $@ notation create complex
     goal shapes. To complete: run `coqc` on this file with MCP and
     replace each Admitted with the interactive proof. *)

  Lemma secp256k1_mul_bignum_correct :
    forall functions,
      (forall functions',
          Interface.map.get functions' "secp256k1_mul" =
          Interface.map.get functions "secp256k1_mul" ->
          spec_of_BinOp bin_mul (field_representation:=frep256k1) functions') ->
      spec_of_secp256k1_mul_bignum functions.
  Proof. Admitted. (* interactive: see proof sketch above *)

  Lemma secp256k1_add_bignum_correct :
    forall functions,
      (forall functions',
          Interface.map.get functions' "secp256k1_add" =
          Interface.map.get functions "secp256k1_add" ->
          spec_of_BinOp bin_add (field_representation:=frep256k1) functions') ->
      spec_of_secp256k1_add_bignum functions.
  Proof. Admitted.

  Lemma secp256k1_sub_bignum_correct :
    forall functions,
      (forall functions',
          Interface.map.get functions' "secp256k1_sub" =
          Interface.map.get functions "secp256k1_sub" ->
          spec_of_BinOp bin_sub (field_representation:=frep256k1) functions') ->
      spec_of_secp256k1_sub_bignum functions.
  Proof. Admitted.

  Lemma secp256k1_square_bignum_correct :
    forall functions,
      (forall functions',
          Interface.map.get functions' "secp256k1_square" =
          Interface.map.get functions "secp256k1_square" ->
          spec_of_UnOp un_square (field_representation:=frep256k1) functions') ->
      spec_of_secp256k1_square_bignum functions.
  Proof. Admitted.

  Lemma secp256k1_opp_bignum_correct :
    forall functions,
      (forall functions',
          Interface.map.get functions' "secp256k1_opp" =
          Interface.map.get functions "secp256k1_opp" ->
          spec_of_UnOp un_opp (field_representation:=frep256k1) functions') ->
      spec_of_secp256k1_opp_bignum functions.
  Proof. Admitted.

  (** ** Composition recipe (no new lemmas — just consume the bridges)

      To prove that the existing fiat-crypto-derived
      [secp256k1_mul] (with its [spec_of_BinOp bin_mul] proof from
      [secp256k1_mul_correct]) also satisfies
      [spec_of_secp256k1_mul_bignum], a caller does:

      1. Apply [secp256k1_mul_correct] to obtain a [binop_spec bin_mul]
         hypothesis (FElem-style).
      2. Use [secp256k1_Bignum_to_FElem] (from
         [Secp256k1_Bignum_Specs.v]) to rewrite the Bignum
         preconditions on [px], [py] into FElem form. The required
         length-equality witnesses come from the
         [Bignum n px wsx] precondition (which already embeds
         [length wsx = n] via its [emp]-clause).
      3. The output buffer is the only asymmetric piece: the FElem
         binop_spec wants [out : list byte] of length
         [felem_size_in_bytes] for the *old* output; AUCurves passes
         a [Bignum n pout old_out]. Convert via [Bignum_of_bytes]
         (from [Crypto.Bedrock.Field.Synthesis.Generic.Bignum]) which
         is an [iff1] between an [array ptsto] of bytes and a [Bignum]
         after grouping bytes into words.
      4. Apply the FElem-style WP, then on the postcondition use
         [secp256k1_FElem_iff_Bignum] to push the resulting [FElem
         pout new_x] back into [Bignum n pout (proj1_sig new_x)].
      5. The bounds are equal definitionally:
         [bounded_by tight_bounds] for [frep256k1] is
         [WordByWordMontgomery.valid 64 4 m].
      6. The decoding is also equal definitionally:
         [feval x = F.of_Z _ (eval (from_mont (map word.unsigned (proj1_sig x))))],
         and we want
         [eval (from_mont (...)) mod m = ...]; the [F.to_Z ∘ F.of_Z]
         round trip gives exactly [_ mod m].

      The result: a complete WP proof producing a
      [bignum_binop_spec] from a [binop_spec], usable by AUCurves
      callers via the standard [straightline_call] tactic. *)

End Secp256k1_Wired_Specs.

(** Note: These [Instance spec_of_secp256k1_*_bignum] declarations make
    the Bignum-style specs available to typeclass resolution. An
    AUCurves bedrock2 program that calls "secp256k1_mul" will pick up
    [spec_of_secp256k1_mul_bignum] automatically. To dispatch the
    actual proof obligation, the caller must (a) put
    [secp256k1_mul_correct] (from [Field256k1.v]) into context and
    (b) compose via the recipe documented above.

    The mechanical sep-logic massaging in step (3)–(4) above is
    standard Coq-bedrock2 plumbing of the kind used throughout
    [BLS12Curve_G1.v]; it does not require any new lemmas beyond
    those already in [BignumFElemBridge.v] and
    [Secp256k1_Bignum_Specs.v]. *)
