Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery. 
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import bedrock2.string2ident.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Bedrock.Examples.felem_copy_64.
Require Import coqutil.Tactics.letexists.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.Word.
Require Import bedrock2.Lift1Prop.
Require Import coqutil.Map.Properties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ptsto_bytes.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Byte.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Util.
Local Open Scope Z_scope.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Local Open Scope string_scope.
Import ListNotations.
Require Import bedrock2.NotationsCustomEntry.
(* Require Import bedrock2.NotationsInConstr. *)
Require Import bedrock2.Syntax.
(* Local Open Scope bedrock_expr. *)
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Coq.ZArith.ZArith.
(* Require Import bedrock2.NotationsInConstr. *)
Require Import bedrock2.Syntax.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Local Open Scope Z_scope.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.

Require Import Theory.Fields.QuadraticFieldExtensions.

Require Import Bedrock.Field.bls12prime.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.




Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Section Spec.

Local Open Scope Z_scope.

(*Parameters to be changed: specify prime and import reification from cache.*)
    Local Notation m := bls12prime.m.
    Local Definition prefix := "bls12_"%string. (* placed before function names *)

    Require Import Bedrock.Field.bls12prime.

    Existing Instances Defaults64.default_parameters bls12_bedrock2_funcs
    bls12_bedrock2_specs bls12_bedrock2_correctness.
(*  We require that the prime specified here is the same that was used for reification:
    Change names to match reification cache.*)
(*  We instantiate specs of all imported bedrock2 functions.
    This needs to be done for typeclass inference to work properly.*)

  Instance spec_of_reified_mul :
  spec_of (append prefix "mul") := spec_of_mul.

  Instance spec_of_reified_square :
  spec_of (append prefix "square") := spec_of_square.

  Instance spec_of_reified_add :
  spec_of (append prefix "add") := spec_of_add.

  Instance spec_of_reified_sub :
  spec_of (append prefix "sub") := spec_of_sub.

  Instance spec_of_reified_opp :
  spec_of (append prefix "opp") := spec_of_opp.

  Instance spec_of_reified_to_montgomery :
  spec_of (append prefix "to_montgomery") := spec_of_to_montgomery.

  Instance spec_of_reified_from_montgomery :
  spec_of (append prefix "from_montgomery") := spec_of_from_montgomery.

  Instance spec_of_reified_nonzero :
  spec_of (append prefix "nonzero") := spec_of_nonzero.

  Instance spec_of_reified_selectznz :
  spec_of (append prefix "selectznz") := spec_of_selectznz.

  Instance spec_of_reified_to_bytes :
  spec_of (append prefix "to_bytes") := spec_of_to_bytes.

  Instance spec_of_reified_from_bytes :
  spec_of (append prefix "from_bytes") := spec_of_from_bytes.
(*Instantiation done.*)

(*Initializing parameters; do not touch*)
Local Notation bw := (@width (semantics)).
Local Notation m' := (@WordByWordMontgomery.m' m bw).
Notation n := (WordByWordMontgomery.n m bw).
Local Notation eval := (@WordByWordMontgomery.eval bw n).
Local Notation valid := (@WordByWordMontgomery.valid bw n m).
Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').

Local Definition valid_words w := valid (List.map (@Interface.word.unsigned 64 Naive.word64) w).
Local Definition map_words := List.map (@Interface.word.unsigned 64 Naive.word64).
Local Notation r := (WordByWordMontgomery.r bw).
Local Notation r' := (WordByWordMontgomery.r' m bw).
Local Definition num_bytes := Eval compute in (Z.of_nat (((Z.to_nat bw * n) / 8)%nat)).
(* Local Notation word.add := (@word.add (@width)) *)

Local Notation evfst x := (eval (from_mont (fst x))).
Local Notation evsnd x := (eval (from_mont (snd x))).

Lemma r_equiv : r = MontgomeryRingTheory.r bw.
Proof.
  cbv. auto.
Qed.

Lemma r'_correct : (MontgomeryRingTheory.r bw * r') mod m = 1.
Proof. cbv; auto. Qed.

Lemma m'_correct : m * m' mod MontgomeryRingTheory.r bw = (-1) mod MontgomeryRingTheory.r bw.
Proof. cbv; auto. Qed.

Lemma bw_big : 0 < bw.
Proof. cbv; auto. Qed.

Lemma n_nz : n <> 0%nat.
Proof. cbv; intros; discriminate. Qed.

Lemma m_big : m < MontgomeryRingTheory.r bw ^ (Z.of_nat n).
Proof. cbv; auto. Qed.

Lemma m_small : 1 < m.
Proof. cbv; auto. Qed.

Local Notation valid_mod := (@valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).

Ltac postcondition_pre := repeat (split; [solve [reflexivity]| ]); repeat (
  lazymatch goal with
  | |- exists _, _ => eexists
  | _ => fail
  end); repeat ( split; [| ecancel_assumption]).

  Ltac copy_next R fR thism pX1 wX1 RX1 a H := straightline_call; [subst R; remember fR as thisP;
  eassert (thisH : ((fun m => (Bignum n pX1 wX1 * RX1)%sep m /\ thisP m) * Bignum n a _ * _)%sep thism) by (subst thisP; ecancel_assumption); subst thisP; apply thisH |]; clear H; repeat straightline.

Definition Fp2_add_Gallina_spec in1 in2 out :=
    valid (fst out) /\ valid (snd out) /\
    evfst out = (evfst in1 + evfst in2) mod m /\
    evsnd out = (evsnd in1 + evsnd in2) mod m.

Definition Fp2_sub_Gallina_spec in1 in2 out :=
  valid (fst out) /\ valid (snd out) /\
  evfst out = (evfst in1 - evfst in2) mod m /\
  evsnd out = (evsnd in1 - evsnd in2) mod m.

Definition Fp2_mul_Gallina_spec in1 in2 out :=
    valid (fst out) /\ valid (snd out) /\
    evfst out = (evfst in1 * evfst in2 - evsnd in1 * evsnd in2) mod m /\
    evsnd out = (evfst in1 * evsnd in2 + evfst in2 * evsnd in1) mod m.

Definition Fp2_square_Gallina_spec inp out :=
  valid (fst out) /\ valid (snd out) /\
  evfst out = ((evfst inp + evsnd inp) * (evfst inp - evsnd inp) ) mod m /\
  evsnd out = (2 * (evfst inp * evsnd inp)) mod m.

    (*Why let-bindings? Are they necessary?*)
  Definition Fp2_add : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let add := (append prefix "add") in  
  ("Fp2_add", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
    add (outr, yr, xr);
    add (outi, yi, xi)
    )
  )).

  Definition Fp2_mul : Syntax.func :=
    let outr := "outr" in
    let outi := "outi" in
    let xr := "xr" in
    let xi := "xi" in
    let yr := "yr" in
    let yi := "yi" in
    let v0 := "v0" in
    let v1 := "v1" in
    let v2 := "v2" in
    let add := (append prefix "add") in
    let mul := (append prefix "mul") in
    let sub := (append prefix "sub") in  
    ("Fp2_mul", (
      [outr; outi; xr; xi; yr; yi], [],
      bedrock_func_body:(
      stackalloc num_bytes as v0 {
        stackalloc num_bytes as v1 {
          stackalloc num_bytes as v2 {
            mul (v0, xr, yr);
            mul (v1, xi, yi);
            sub (outr, v0, v1);
            add (v2, xr, xi);
            add (outi, yr, yi);
            mul (outi, v2, outi);
            sub (outi, outi, v0);
            sub (outi, outi, v1)
          }
        }
      }
      )
    )).

  Definition Fp2_sub : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let add := (append prefix "add") in  
  ("Fp2_sub", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
    sub (outr, xr, yr);
    sub (outi, xi, yi)
    )
  )).
    
  Definition Fp2_square : Syntax.func :=
    let outr := "outr" in
    let outi := "outi" in
    let inr := "inr" in
    let ini := "ini" in
    let v := "v" in
    let add := (append prefix "add") in
    let mul := (append prefix "mul") in
    let sub := (append prefix "sub") in
    ("Fp2_square", (
      [outr; outi; inr; ini], [],
      bedrock_func_body:(
        stackalloc num_bytes as v {
          add(v, inr, ini);
          sub(outr, inr, ini);
          mul(outr, outr, v);
          mul(outi, inr, ini);
          add(outi, outi, outi)
        }
      )
    )).


  Local Open Scope string_scope.
  Local Infix "*" := sep : sep_scope.
  Delimit Scope sep_scope with sep.

Instance spec_of_my_add: spec_of Fp2_add :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
    (*typeclass isntead of valid?*)
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    (((Bignum n pxr wxr) ) *
    ((Bignum n pxi wxi) ) *
    ((Bignum n pyr wyr) ) *
    ((Bignum n pyi wyi) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_add") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep),
        (
                (Fp2_add_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * (Bignum n pxr wxr)
              * (Bignum n pxi wxi) * (Bignum n pyr wyr) * (Bignum n pyi wyi) * Rout)%sep m'))).


Instance spec_of_my_sub: spec_of Fp2_sub :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    (((Bignum n pxr wxr) ) *
    ((Bignum n pxi wxi) ) *
    ((Bignum n pyr wyr) ) *
    ((Bignum n pyi wyi) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_sub") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep),
        (
                (Fp2_sub_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) *
                (Bignum n pxr wxr) * (Bignum n pxi wxi) * 
                (Bignum n pyr wyr) * (Bignum n pyi wyi) * Rout)%sep m'))).


Instance spec_of_my_mul: spec_of Fp2_mul :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    (((Bignum n pxr wxr) ) *
    ((Bignum n pxi wxi) ) *
    ((Bignum n pyr wyr) ) *
    ((Bignum n pyi wyi) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_mul") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Routnew,
        (
                (Fp2_mul_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) *
             (Bignum n pxr wxr) * (Bignum n pxi wxi) * 
             (Bignum n pyr wyr) * (Bignum n pyi wyi) * Rout * Routnew)%sep m'))).



Instance spec_of_my_square: spec_of Fp2_square :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (winr wini : list Interface.word.rep)
    (pinr pini poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned winr) /\
    valid (List.map Interface.word.unsigned wini) ->
    (((Bignum n pinr winr) ) *
    ((Bignum n pini wini) ) *
    (Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_square") t m0
    ([poutr; pouti; pinr; pini])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Rout,
        (
                (Fp2_square_Gallina_spec (List.map Interface.word.unsigned winr, List.map Interface.word.unsigned wini)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) *
             (Bignum n pinr winr) * (Bignum n pini wini) * Rout)%sep m')))).

Theorem Fp2_add_ok: program_logic_goal_for_function! Fp2_add.
Proof.
    (*Initializing*)
    straightline_init_with_change.
    repeat straightline.

    (*first function call*)
    handle_call; [eauto ..|].
    (*Second function call*)
    handle_call; [eauto .. |].

    (*Prove Postcondition*)
    postcondition_pre.

    split; [split; [eauto| split; [eauto| split]]| split; eauto].
        + rewrite !Prod.fst_pair, Z.add_comm.
          apply valid_mod in H8. rewrite <- H8. assumption.
        + rewrite !Prod.snd_pair, Z.add_comm.
          apply valid_mod in H11. rewrite <- H11. assumption.
Qed.


Theorem Fp2_sub_ok: program_logic_goal_for_function! Fp2_sub.
Proof.
    (*Initializing*)
    straightline_init_with_change.
    repeat straightline.


    (*first function call*)
    handle_call; [eauto ..|].
    (*Second function call*)
    handle_call; [eauto .. |].

    (*Prove postcondition*)
    postcondition_pre.
    split; [split; [eauto| split; [eauto| split]]| split; eauto].
    - rewrite !Prod.fst_pair; apply valid_mod in H8; rewrite <- H8; assumption.
    - rewrite !Prod.snd_pair; apply valid_mod in H11; rewrite <- H11; assumption.
Qed.
(* Notation msplit := Interface.map.split. *)

Notation montsub a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) -
       eval (from_mont (c))) mod m).

Notation montadd a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) +
       eval (from_mont (c))) mod m).

Notation montmul a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) *
       eval (from_mont (c))) mod m).

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Lemma postcond_from_precond xr xi yr yi resr resi x1 x2 x3 x4 x5 x6:
  montsub resi x1 x2 -> valid resi -> valid x1 -> valid x2
  -> montsub x1 x3 x4 -> montmul x3 x5 x6 -> valid x3 -> valid x6
  -> montadd x6 yr yi -> valid x5 -> montadd x5 xr xi -> valid resr
  -> montsub resr x4 x2 -> montmul x2 xi yi -> valid x4 -> montmul x4 xr yr
  -> valid xr -> valid xi -> valid yr -> valid yi
-> Fp2_mul_Gallina_spec (xr, xi) (yr, yi) (resr, resi).
Proof.
  intros. unfold Fp2_mul_Gallina_spec.
  split; [auto|].
  split; [auto|]. split.
                    - rewrite !Prod.fst_pair, !Prod.snd_pair.
                      rewrite (valid_mod H10) in H11; rewrite H11.
                      rewrite (valid_mod H13) in H14; rewrite H14.
                      rewrite (valid_mod H2) in H12; rewrite H12.
                      rewrite <- Zminus_mod. reflexivity.
                    - rewrite !Prod.fst_pair, !Prod.snd_pair.
                      (*Put valid in type, try using congruence.*)
                      rewrite (valid_mod H0) in H; rewrite H.
                      rewrite (valid_mod H1) in H3; rewrite H3.
                      rewrite (valid_mod H5) in H4; rewrite H4.
                      rewrite (valid_mod H8) in H9; rewrite H9.
                      rewrite (valid_mod H6) in H7; rewrite H7.
                      rewrite (valid_mod H13) in H14; rewrite H14.
                      rewrite (valid_mod H2) in H12; rewrite H12.
                      rewrite <- Z.mul_mod; [| cbv; intros; discriminate].
                      remember (eval (from_mont xr)) as xr'.
                      remember (eval (from_mont yr)) as yr'.
                      remember (eval (from_mont xi)) as xi'.
                      remember (eval (from_mont yi)) as yi'.
                      pull_Zmod. apply (f_equal (fun y => (y mod m))). ring.
Qed.

Lemma numbytes_correct : 48 = Z.of_nat (n * Z.to_nat word_size_in_bytes).
Proof.
  auto.
Qed.

  Ltac straightline' H :=
    lazymatch goal with
    | [Hminit : ?mcond (?minit : @Interface.map.rep _ _ _)
        |- forall (_ : @word.rep _ _)
                  (_ _ : @Interface.map.rep _ _ _),
            anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] => 
        let a := (fresh "a") in
        let mStack := (fresh "mStack") in
        let mnew := (fresh "mnew") in
        let Hany := (fresh "Hany") in
        let HanyBignum := (fresh "HanyBignum") in
        let anyval := (fresh "anyval") in
        let Hsplit := (fresh "Hsplit") in
        let Hmnew := (fresh "Hmnew") in
        let R := (fresh "R") in
        intros a mStack mnew Hany Hsplit; destruct (anybytes_Bignum n mStack numbytes a H Hany) as [anyval HanyBignum];
        destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit (empty_frame mcond minit Hminit) (empty_frame (Bignum _ _ _) mStack HanyBignum)) as [R Hmnew];
        clear Hany Hsplit HanyBignum
    | _ => straightline
    end.

    Ltac defrag_in_context := lazymatch goal with
| [
    |- exists (_ _ : @Interface.map.rep _ _ _),
      (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
      repeat lazymatch goal with 
      | [ H : (?Rl * ((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] => 
        let Ha := (fresh "Ha") in
        let m := fresh "m" in
        let mStack := fresh "mStack" in
        assert (Ha : ((Bignum n addr aval) * (Rl * Rr))%sep mem) by ecancel_assumption;
        destruct Ha as [mStack [m [? []]]];
        exists m; exists mStack; split; [ eapply Bignum_anybytes; [apply numbytes_correct |eassumption] | split; [apply Properties.map.split_comm; auto|]]
      | [ H : (((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] => 
        let Ha := (fresh "Ha") in
        let m := fresh "m" in
        let mStack := fresh "mStack" in
        assert (Ha : ((Bignum n addr aval) * (Rr))%sep mem) by ecancel_assumption;
        destruct Ha as [mStack [m [? []]]];
        exists m; exists mStack; split; [ eapply Bignum_anybytes; [apply numbytes_correct |eassumption] | split; [apply Properties.map.split_comm; auto|]]
          
      | [ H : _ mem |- _ ] => apply (sep_assoc_proj2 mem) in H
      end
end.

Ltac defrag_in_context' := lazymatch goal with
| [
    |- exists (_ _ : @Interface.map.rep _ _ _),
      (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
      match goal with 
      | [ H : _ mem |- _ ] => cleanup_hyp H mem
      end
    end; defrag_in_context.

  Lemma Bignum_eq: forall x p, Bignum n p x = (emp (Datatypes.length x = n) * array Scalars.scalar (word.of_Z word_size_in_bytes) p x)%sep.
Proof. auto. Qed.


Theorem Fp2_mul_ok: program_logic_goal_for_function! Fp2_mul.
Proof.
  (*Handle parts of function up until function calls.
    We use a modified version of Bedrock2's straightline tactic.
    This version  undoes the fragmentation of memory in the context
    done by stack allocation.*)
    repeat (straightline' numbytes_correct).
    (*Handle function calls.
    Note that the use of the "auto" tactic here is to handle preconditions af callees.
    In this case auto is sufficient, but for more complicated function calls
    this should be done manually.*)
    repeat (handle_call; [auto| auto| ]).

  (*Fragmentation of the memory after function body is necessary for stack allocation
    to ensure that output and intermediate variables are stored correctly in memory
    TODO: find a better name for this tactic.*)
    cleanup_hyp H28 a5.
    repeat defrag_in_context'.
  
    (* Handle parts of function up until proving the postcondition*)
    repeat (straightline' numbytes_correct).

  (*Postcondition is proved. Trivial subgoals are handled by tactic postcondition_pre*)
    postcondition_pre.
    split; [split; [eauto| split; [eauto|]]| split; eauto].

  (*We have proved that the Gallina specification is met in a separate lemma: postcond_from_precond.
    A more natural approach would be to prove the precondition directly here.
    We use a lemma to illustrate the fact that proving the non-Bedrock2 specific parts of
    the postcondition is separated from the Bedrock2 specific parts, which are mostly automated.*)
  apply (postcond_from_precond (map word.unsigned wxr) (map word.unsigned wxi) (map word.unsigned wyr) (map word.unsigned wyi) (map word.unsigned x1) (map word.unsigned x6)
  (map word.unsigned x5) (map word.unsigned x0) (map word.unsigned x4) (map word.unsigned x) 
  (map word.unsigned x2) (map word.unsigned x3) 
  ); auto.
  Qed.

  Theorem Fp2_square_ok: program_logic_goal_for_function! Fp2_square.
  Proof.
    (*Handle parts of function up until function calls.
      We use a modified version of Bedrock2's straightline tactic.
      This version  undoes the fragmentation of memory in the context
      done by stack allocation.*)
    repeat (straightline' numbytes_correct).
    (*Handle function calls.
      Note that the use of the "auto" tactic here is to handle preconditions af callees.
      In this case auto is sufficient, but for more complicated function calls
      this should be done manually.*)
    repeat (handle_call; [auto| auto| ]).
  
    (*Fragmentation of the memory after function body is necessary for stack allocation
      to ensure that output and intermediate variables are stored correctly in memory
      TODO: find a better name for this tactic.*)
    repeat defrag_in_context'.
    
    (* Handle parts of function up until proving the postcondition*)
    repeat (straightline' numbytes_correct).
  
    (*Postcondition is proved
      reflexivity solves first part; which will always be the case when no complicated
      reasoning about separation logic is needed, i.e. when the seperating conjuction is
      used only as a means of referencing memory. *)
      postcondition_pre.
 
    (*Postcondition*)
    do 2 (split; [auto|]).
    split.
      - rewrite !Prod.snd_pair, !Prod.fst_pair.
        rewrite (valid_mod H12) in H9; rewrite H9.
        rewrite (valid_mod H8) in H5; rewrite H5.
        rewrite (valid_mod H10) in H7; rewrite H7.
        remember (eval (from_mont (map word.unsigned winr))) as inr.
        remember (eval (from_mont (map word.unsigned wini))) as ini.
        pull_Zmod; rewrite Z.mul_comm; reflexivity.
      - rewrite !Prod.snd_pair, !Prod.fst_pair.
        remember (eval (from_mont (map word.unsigned winr))) as inr.
        remember (eval (from_mont (map word.unsigned wini))) as ini.
        rewrite (valid_mod H18) in H16; rewrite H16.
        rewrite (valid_mod H15) in H13; rewrite H13.
        pull_Zmod. apply (f_equal (fun y => y mod Spec.m)). ring.
    Qed.

(*Lemmas*)
Notation N aw := (word.add (word.of_Z word_size_in_bytes) aw).

Lemma nval : n = 6%nat.
Proof. auto. Qed.


Lemma length_nil {A : Type} (l : list A) : length l = 0%nat -> l = [].
Proof.
  destruct l; auto; discriminate.
Qed.

Definition Fp2_add_alt2 : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let xrsep := "xrsep" in
  let xisep := "xisep" in
  let yrsep := "yrsep" in
  let yisep := "yisep" in
  let add := (append prefix "add") in  
  let felem_copy := ("felem_copy_64") in  
  ("Fp2_add_alt2", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
      stackalloc num_bytes as xrsep {
        stackalloc num_bytes as xisep {
          stackalloc num_bytes as yrsep {
            stackalloc num_bytes as yisep {
              (*Copies real part of first operand*)
              felem_copy (xrsep, xr);
              felem_copy (yrsep, yr);
              felem_copy (xisep, xi);
              felem_copy (yisep, yi);

              Fp2_add (outr, outi, xrsep, xisep, yrsep, yisep)
            }
          }
        }
      }
    )
  )).

Instance spec_of_my_add_alt2: spec_of Fp2_add_alt2 :=
fun functions : list (string * (list string * list string * Syntax.cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Ryr Ryi Rout : Interface.map.rep -> Prop),
    (*typeclass isntead of valid?*)
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    ((Bignum n pxr wxr) * Rxr)%sep m0 ->
    ((Bignum n pxi wxi) * Rxi)%sep m0 ->
    ((Bignum n pyr wyr) * Ryr)%sep m0 ->
    ((Bignum n pyi wyi) * Ryi)%sep m0 ->
    ((Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_add_alt2") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Routnew,
        (
                (Fp2_add_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Rout * Routnew)%sep m'))).

Ltac remember_sep_in_hyp H Hname :=
  lazymatch H with
  | ?R _ => remember R as Hname end.

(* Ltac pack_disj_hyps_4 H1 H2 H3 H4 H5 := *)

Theorem Fp2_add_alt2_okay: program_logic_goal_for_function! Fp2_add_alt2.
Proof.
  do 7 straightline' numbytes_correct.
  
  (*Assert single hypothesis for stackallocation.*)
  remember (Bignum n pxr wxr * Rxr)%sep as Rxr'.
  remember (Bignum n pyr wyr * Ryr)%sep as Ryr'.
  remember (Bignum n pxi wxi * Rxi)%sep as Rxi'.
  remember (Bignum n pyi wyi * Ryi)%sep as Ryi'.
  remember ((Bignum n poutr wold_outr * Bignum n pouti wold_outi * Rout)%sep) as Rout'.

  assert (
      id (fun m => (Rxr' m /\ Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m)) m0).
  {
    cbv [id]. split; auto.
  }

  (*Allocate memory on stack. *)
  repeat straightline' numbytes_correct. clear H1 Hmnew Hmnew0 Hmnew1.
  repeat straightline' numbytes_correct. cbv [id] in *.

 (*Handle calls to felem_copy*)

  copy_next Rxr' (fun m => Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m) mnew2 pxr wxr Rxr a Hmnew2.
  copy_next Ryr' (fun m => Rxi' m /\ Ryi' m /\ Rout' m) a4 pyr wyr Ryr a1 H15.
  copy_next Rxi' (fun m => Ryi' m /\ Rout' m) a6 pxi wxi Rxi a0 H15.
  copy_next Ryi' (fun m => Rout' m) a4 pyi wyi Ryi a2 H15.

 (*Handle function call*)
 repeat straightline.
 straightline_call.
 2:
 {
   assert (Hnumlimbs : n = num_limbs) by auto.
   repeat rewrite Hnumlimbs. repeat rewrite Hnumlimbs in H15. ecancel_assumption.
 }
 1: split; auto.

 (*Defragment memory in context after stack allocation. *)
 repeat straightline.
 repeat defrag_in_context'.

 (*Postcondition*)
 postcondition_pre.
 split; [auto| split; auto].
Qed.


Definition Fp2_sub_alt2 : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let xrsep := "xrsep" in
  let xisep := "xisep" in
  let yrsep := "yrsep" in
  let yisep := "yisep" in
  let add := (append prefix "add") in  
  let felem_copy := ("felem_copy_64") in  
  ("Fp2_sub_alt2", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
      stackalloc num_bytes as xrsep {
        stackalloc num_bytes as xisep {
          stackalloc num_bytes as yrsep {
            stackalloc num_bytes as yisep {
              (*Copies real part of first operand*)
              felem_copy (xrsep, xr);
              felem_copy (yrsep, yr);
              felem_copy (xisep, xi);
              felem_copy (yisep, yi);

              Fp2_sub (outr, outi, xrsep, xisep, yrsep, yisep)
            }
          }
        }
      }
    )
  )).

Instance spec_of_my_sub_alt2: spec_of Fp2_sub_alt2 :=
fun functions : list (string * (list string * list string * Syntax.cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Ryr Ryi Rout : Interface.map.rep -> Prop),
    (*typeclass isntead of valid?*)
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    ((Bignum n pxr wxr) * Rxr)%sep m0 ->
    ((Bignum n pxi wxi) * Rxi)%sep m0 ->
    ((Bignum n pyr wyr) * Ryr)%sep m0 ->
    ((Bignum n pyi wyi) * Ryi)%sep m0 ->
    ((Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_sub_alt2") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Routnew,
        (
                (Fp2_sub_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Rout * Routnew)%sep m'))).

Theorem Fp2_sub_alt2_okay: program_logic_goal_for_function! Fp2_sub_alt2.
Proof.
  do 7 straightline' numbytes_correct.

  (*Assert single hypothesis for stackallocation.*)
  remember (Bignum n pxr wxr * Rxr)%sep as Rxr'.
  remember (Bignum n pyr wyr * Ryr)%sep as Ryr'.
  remember (Bignum n pxi wxi * Rxi)%sep as Rxi'.
  remember (Bignum n pyi wyi * Ryi)%sep as Ryi'.
  remember ((Bignum n poutr wold_outr * Bignum n pouti wold_outi * Rout)%sep) as Rout'.

  assert (
      id (fun m => (Rxr' m /\ Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m)) m0).
  {
    cbv [id]. split; auto.
  }


  (*Allocate memory on stack. *)
  repeat straightline' numbytes_correct. clear H1 Hmnew Hmnew0 Hmnew1.
  repeat straightline'. cbv [id] in *.

 (*Handle calls to felem_copy*)
  copy_next Rxr' (fun m => Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m) mnew2 pxr wxr Rxr a Hmnew2.
  copy_next Ryr' (fun m => Rxi' m /\ Ryi' m /\ Rout' m) a4 pyr wyr Ryr a1 H15.
  copy_next Rxi' (fun m => Ryi' m /\ Rout' m) a6 pxi wxi Rxi a0 H15.
  copy_next Ryi' (fun m => Rout' m) a4 pyi wyi Ryi a2 H15.

 (*Handle function call*)
 repeat straightline.
 straightline_call.
 2: {
   assert (Hnumlimbs : n = num_limbs) by auto. rewrite !Hnumlimbs. rewrite !Hnumlimbs in H15. ecancel_assumption.
 }
 1: split; auto.

 (*Defragment memory in context after stack allocation. *)
 repeat straightline.
 repeat defrag_in_context'.

 (*Postcondition*)
 postcondition_pre.
 split; [auto| split; auto].
Qed.


Definition Fp2_mul_alt2 : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let yr := "yr" in
  let yi := "yi" in
  let xrsep := "xrsep" in
  let xisep := "xisep" in
  let yrsep := "yrsep" in
  let yisep := "yisep" in
  let add := (append prefix "add") in
  let felem_copy := ("felem_copy_64") in  
  ("Fp2_mul_alt2", (
    [outr; outi; xr; xi; yr; yi], [],
    bedrock_func_body:(
      stackalloc num_bytes as xrsep {
        stackalloc num_bytes as xisep {
          stackalloc num_bytes as yrsep {
            stackalloc num_bytes as yisep {
              (*Copies real part of first operand*)
              felem_copy (xrsep, xr);
              felem_copy (yrsep, yr);
              felem_copy (xisep, xi);
              felem_copy (yisep, yi);

              Fp2_mul (outr, outi, xrsep, xisep, yrsep, yisep)
            }
          }
        }
      }
    )
  )).

Instance spec_of_my_mul_alt2: spec_of Fp2_mul_alt2 :=
fun functions : list (string * (list string * list string * Syntax.cmd)) =>
    forall (wxr wxi wyr wyi : list Interface.word.rep)
    (pxr pxi pyr pyi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Ryr Ryi Rout : Interface.map.rep -> Prop),
    (*typeclass isntead of valid?*)
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) /\
    valid (List.map Interface.word.unsigned wyr) /\
    valid (List.map Interface.word.unsigned wyi) ->
    ((Bignum n pxr wxr) * Rxr)%sep m0 ->
    ((Bignum n pxi wxi) * Rxi)%sep m0 ->
    ((Bignum n pyr wyr) * Ryr)%sep m0 ->
    ((Bignum n pyi wyi) * Ryi)%sep m0 ->
    ((Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_mul_alt2") t m0
    ([poutr; pouti; pxr; pxi; pyr; pyi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Routnew,
        (
                (Fp2_mul_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned wyr, List.map Interface.word.unsigned wyi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Rout * Routnew)%sep m'))).

Theorem Fp2_mul_alt2_okay: program_logic_goal_for_function! Fp2_mul_alt2.
Proof.
  do 7 straightline' numbytes_correct.

  (*Assert single hypothesis for stackallocation.*)
  remember (Bignum n pxr wxr * Rxr)%sep as Rxr'.
  remember (Bignum n pyr wyr * Ryr)%sep as Ryr'.
  remember (Bignum n pxi wxi * Rxi)%sep as Rxi'.
  remember (Bignum n pyi wyi * Ryi)%sep as Ryi'.
  remember ((Bignum n poutr wold_outr * Bignum n pouti wold_outi * Rout)%sep) as Rout'.

  assert (
      id (fun m => (Rxr' m /\ Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m)) m0).
  {
    cbv [id]. split; auto.
  }


  (*Allocate memory on stack. *)
  repeat straightline' numbytes_correct. clear H1 Hmnew Hmnew0 Hmnew1.
  repeat straightline' numbytes_correct. cbv [id] in *.

 (*Handle calls to felem_copy*)
  copy_next Rxr' (fun m => Ryr' m /\ Rxi' m /\ Ryi' m /\ Rout' m) mnew2 pxr wxr Rxr a Hmnew2.
  copy_next Ryr' (fun m => Rxi' m /\ Ryi' m /\ Rout' m) a4 pyr wyr Ryr a1 H15.
  copy_next Rxi' (fun m => Ryi' m /\ Rout' m) a6 pxi wxi Rxi a0 H15.
  copy_next Ryi' (fun m => Rout' m) a4 pyi wyi Ryi a2 H15.

 (*Handle function call*)
 repeat straightline.
 straightline_call.
 2: {
   assert (Hnumlimbs : n = num_limbs) by auto. rewrite !Hnumlimbs. rewrite !Hnumlimbs in H15.
   ecancel_assumption.
 }
 1: split; auto.

 (*Defragment memory in context after stack allocation. *)
 repeat straightline.
 repeat defrag_in_context'.

 (*Postcondition*)
 postcondition_pre.
 split; [auto| split; auto].
Qed.


Definition Fp2_square_alt2 : Syntax.func :=
  let outr := "outr" in
  let outi := "outi" in
  let xr := "xr" in
  let xi := "xi" in
  let xrsep := "xrsep" in
  let xisep := "xisep" in
  let felem_copy := ("felem_copy_64") in  
  ("Fp2_square_alt2", (
    [outr; outi; xr; xi], [],
    bedrock_func_body:(
      stackalloc num_bytes as xrsep {
        stackalloc num_bytes as xisep {
          (*Copies real part of first operand*)
          felem_copy (xrsep, xr);
          felem_copy (xisep, xi);

          Fp2_square (outi, outr, xrsep, xisep)
        }
      }
    )
  )).

Instance spec_of_my_square_alt2: spec_of Fp2_square_alt2 :=
fun functions : list (string * (list string * list string * Syntax.cmd)) =>
    forall (wxr wxi : list Interface.word.rep)
    (pxr pxi poutr pouti : Interface.word.rep)
    (wold_outr wold_outi : list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rxr Rxi Rout : Interface.map.rep -> Prop),
    (*typeclass isntead of valid?*)
    valid (List.map Interface.word.unsigned wxr) /\
    valid (List.map Interface.word.unsigned wxi) ->
    ((Bignum n pxr wxr) * Rxr)%sep m0 ->
    ((Bignum n pxi wxi) * Rxi)%sep m0 ->
    ((Bignum n poutr wold_outr) * (Bignum n pouti wold_outi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "Fp2_square_alt2") t m0
    ([pouti; poutr; pxr; pxi])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutr wouti : list Interface.word.rep) Routnew,
        (
                (Fp2_square_Gallina_spec (List.map Interface.word.unsigned wxr, List.map Interface.word.unsigned wxi)
                (List.map Interface.word.unsigned woutr, List.map Interface.word.unsigned wouti) /\
                valid (List.map Interface.word.unsigned woutr) /\
                valid (List.map Interface.word.unsigned wouti)) /\
             ((Bignum n poutr woutr) * (Bignum n pouti wouti) * Routnew)%sep m'))).

Theorem Fp2_square_alt2_okay: program_logic_goal_for_function! Fp2_square_alt2.
Proof.
  do 4 straightline' numbytes_correct.

  (*Assert single hypothesis for stackallocation.*)
  remember (Bignum n pxr wxr * Rxr)%sep as Rxr'.
  remember (Bignum n pxi wxi * Rxi)%sep as Rxi'.
  remember ((Bignum n poutr wold_outr * Bignum n pouti wold_outi * Rout)%sep) as Rout'.

  assert (
      id (fun m => (Rxr' m /\ Rxi' m /\ Rout' m)) m0).
  {
    cbv [id]. split; auto.
  }


  (*Allocate memory on stack. *)
  repeat straightline' numbytes_correct. clear Hmnew.
  repeat straightline' numbytes_correct. cbv [id] in *.

 (*Handle calls to felem_copy*)
  copy_next Rxr' (fun m => Rxi' m /\ Rout' m) mnew0 pxr wxr Rxr a Hmnew0.
  copy_next Rxi' (fun m => Rout' m) a2 pxi wxi Rxi a0 H10.

 (*Handle function call*)
 repeat straightline.
 straightline_call.
 2: {
   assert (Hnumlimbs : n = num_limbs) by auto. rewrite !Hnumlimbs. rewrite !Hnumlimbs in H10. ecancel_assumption.
 }
 1: split; auto.

 (*Defragment memory in context after stack allocation. *)
 repeat straightline.
 repeat defrag_in_context'.

 (*Postcondition*)
 repeat straightline. do 2 split; auto.
 do 3 eexists. split.
 2: ecancel_assumption.
 split.
 2: destruct H13; destruct H19; split; auto.
 auto.
Qed.
End Spec.