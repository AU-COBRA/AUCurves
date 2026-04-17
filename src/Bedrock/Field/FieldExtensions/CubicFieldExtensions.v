(** * Rupicola compilation layer for cubic extensions (Fp6 = Fp2[v]/(v^3 - xi)).

    Analogous to QuadraticFieldExtensions.v for Fp2.

    Defines bedrock2 function bodies for Fp6 operations.  Includes a
    fp2_mul_xi helper (multiply by xi = 1+u), Karatsuba Fp6 multiplication,
    Chung-Hasan SQR3 squaring, and cubic extension inverse.
    WP proofs are currently stubs (exact I).
*)

Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import bedrock2.NotationsCustomEntry.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Section Fp6.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_parameters : PrimeFieldParameters}
          {prime_parameters_ok : PrimeFieldParameters_ok}
          (beta : F M_pos)
          {beta_nz : beta <> @F.zero M_pos}
          {beta_qnr : ~(exists x, @F.mul M_pos x x = beta)}
          {M_big : 2 < Z.pos M_pos}.

  (* ξ = (xi_re, xi_im) in Fp2 — the cubic non-residue for Fp6 = Fp2[v]/(v³ - ξ) *)
  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  (* note that this excludes non-saturated representations *)
  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* Prefixes for function names *)
  Variable fp6_prefix : string.
  Variable fp2_prefix : string.

  (* ================================================================ *)
  (* Fp2 instances from the quadratic layer                            *)
  (* ================================================================ *)

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_fp_ok_inst : @AbstractField.FieldParameters_ok _ Fp2_fp_inst :=
    Fp2_field_parameters_ok beta beta_nz beta_qnr M_big fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation beta fp2_prefix.
  Local Instance Fp2_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp2 Fp2_fp_inst _ _ _ _ Fp2_repr_inst :=
    @Fp2_field_representation_ok width BW word mem prime_parameters F_representation F_representation_ok beta fp2_prefix.

  (* ================================================================ *)
  (* Fp6 instances from the cubic layer                                *)
  (* ================================================================ *)

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters beta xi_re xi_im (fp6_prefix:=fp6_prefix).

  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  Local Instance Fp6_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp6 Fp6_fp_inst _ _ _ _ Fp6_repr_inst :=
    Fp6_field_representation_ok beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* FElem with optional bounds (reused from QuadraticFieldExtensions) *)
  (* ================================================================ *)

  Local Definition FElem
    {F' : Type} {fp' : AbstractField.FieldParameters F'}
    {fr' : @AbstractField.FieldRepresentation F' fp' width BW word mem}
    (mbounds : option (@AbstractField.bounds F' fp' _ _ _ _ fr'))
    (px : word) (v : F') : mem -> Prop :=
    Lift1Prop.ex1 (fun ws : @AbstractField.felem F' fp' _ _ _ _ fr' =>
      (emp (@AbstractField.feval F' fp' _ _ _ _ fr' ws = v /\
            match mbounds with
            | Some b => @AbstractField.bounded_by F' fp' _ _ _ _ fr' b ws
            | None => True
            end)
       * @AbstractField.FElem F' fp' _ _ _ _ fr' px ws)%sep).

  (* ================================================================ *)
  (* Fp2-level offset helpers                                          *)
  (* ================================================================ *)

  (* Offset in bytes for one Fp2 element = 2 * felem_size_in_words * bytes_per_word *)
  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Notation fp2_felem_offset_word := (word.of_Z fp2_felem_offset).

  (* Offset to 2nd Fp2 component = 1 * fp2_felem_offset *)
  Local Definition fp6_c1_offset : word := fp2_felem_offset_word.
  (* Offset to 3rd Fp2 component = 2 * fp2_felem_offset *)
  Local Definition fp6_c2_offset : word := word.of_Z (2 * fp2_felem_offset).

  (* Helper: offset expression to the ith Fp2 component *)
  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  (* ================================================================ *)
  (* Fp-level offset helpers (for accessing Fp components within Fp2) *)
  (* ================================================================ *)

  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
  Local Definition expr_fp_snd (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp_felem_offset).

  (* ================================================================ *)
  (* Fp6 FElem decomposition and reassembly                           *)
  (* ================================================================ *)

  Local Notation FElem_Fp2 := (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).

  Lemma Fp6_list_decomp : forall l, c0_felem l ++ c1_felem l ++ c2_felem l = l.
  Proof.
    intros. unfold c0_felem, c1_felem, c2_felem.
    set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
    replace (2 * n)%nat with (n + n)%nat by lia.
    change (skipn (n + n) l) with (ListDef.skipn (n + n) l).
    rewrite <- Lists.List.skipn_skipn.
    change (ListDef.skipn n (ListDef.skipn n l)) with (skipn n (skipn n l)).
    rewrite (QuadraticFieldExtensions.firstn_skipn (skipn n l) n).
    apply QuadraticFieldExtensions.firstn_skipn.
  Qed.

  Lemma Fp2_FElem_length pout
    (out : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m :
    FElem_Fp2 pout out m ->
    length out = Fp2_felem_size.
  Proof.
    unfold AbstractField.FElem, Bignum.Bignum.
    intros [me [ma [_ [[_ H] _]]]]. exact H.
  Qed.

  Lemma c0_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c0_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c0_felem.
    apply QuadraticFieldExtensions.length_firstn. lia.
  Qed.

  Local Notation fp_felem_size := (@AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).

  Lemma c1_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c1_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c1_felem.
    set (n := Fp2_felem_size) in *.
    apply QuadraticFieldExtensions.length_firstn.
    change (skipn n l) with (ListDef.skipn n l).
    rewrite Lists.List.length_skipn.
    change (2 * fp_felem_size)%nat with n. lia.
  Qed.

  Lemma c2_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c2_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c2_felem.
    set (n := Fp2_felem_size) in *.
    change (skipn (2 * n) l) with (ListDef.skipn (2 * n) l).
    rewrite Lists.List.length_skipn.
    change (2 * fp_felem_size)%nat with n. lia.
  Qed.

  Lemma Fp6_raw_FElem_split pout
    (out : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) m :
    @AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout out m ->
    (FElem_Fp2 pout (c0_felem out) *
     (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem out) *
      FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out)))%sep m.
  Proof.
    intros H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me.
    assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    set (n := Fp2_felem_size) in *.
    change (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
      with (3 * n)%nat in Hlen.
    assert (Hdecomp : out = c0_felem out ++ c1_felem out ++ c2_felem out)
      by (symmetry; apply Fp6_list_decomp).
    rewrite Hdecomp in Ha.
    (* First split: c0 ++ (c1 ++ c2) *)
    apply array_append' in Ha.
    destruct Ha as [m0 [m12 [Hms01 [Ha0 Ha12]]]].
    assert (Hlen0 : length (c0_felem out) = n) by (apply c0_felem_length; lia).
    rewrite Hlen0 in Ha12.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha12.
    (* Second split: c1 ++ c2 *)
    apply array_append' in Ha12.
    destruct Ha12 as [m1 [m2 [Hms12 [Ha1 Ha2]]]].
    assert (Hlen1 : length (c1_felem out) = n) by (apply c1_felem_length; lia).
    rewrite Hlen1 in Ha2.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha2.
    (* Fix c2 address: (pout + off1) + off1 = pout + off2 *)
    replace (word.add (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
                      (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
      with (word.add pout fp6_c2_offset) in Ha2
      by (unfold fp6_c2_offset; fold n;
          replace (2 * (Memory.bytes_per_word width * Z.of_nat n))
            with (Memory.bytes_per_word width * Z.of_nat n + Memory.bytes_per_word width * Z.of_nat n) by lia;
          rewrite word.ring_morph_add; apply word.add_assoc).
    (* Assemble the 3 FElems *)
    exists m0, (map.putmany m1 m2).
    destruct Hms01 as [Heq01 Hd01]. subst.
    destruct Hms12 as [Heq12 Hd12]. subst.
    split; [split; [reflexivity | exact Hd01] |]. split.
    - exists map.empty, m0. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen0] | exact Ha0].
    - exists m1, m2. split; [split; [reflexivity | exact Hd12] |]. split.
      + exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl | exact Hlen1] | exact Ha1].
      + exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl |] | exact Ha2].
        apply c2_felem_length. lia.
  Qed.

  Lemma Fp6_raw_FElem_join pout c0 c1 c2 m :
    length c0 = Fp2_felem_size ->
    length c1 = Fp2_felem_size ->
    length c2 = Fp2_felem_size ->
    (FElem_Fp2 pout c0 *
     (FElem_Fp2 (word.add pout fp6_c1_offset) c1 *
      FElem_Fp2 (word.add pout fp6_c2_offset) c2))%sep m ->
    @AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout (c0 ++ c1 ++ c2) m.
  Proof.
    intros Hlen0 Hlen1 Hlen2 H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [m0 [m12 [Hms01 [H0 H12]]]].
    destruct H0 as [me0 [ma0 [Hms0 [[Hme0 Hlen0'] Ha0]]]].
    subst me0. assert (m0 = ma0) by (apply Properties.map.split_empty_l in Hms0; exact Hms0). subst.
    destruct H12 as [m1 [m2 [Hms12 [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    destruct H2 as [me2 [ma2 [Hms2 [[Hme2 Hlen2'] Ha2]]]].
    subst me2. assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms2; exact Hms2). subst.
    set (n := Fp2_felem_size) in *.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite !length_app.
      change (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        with (3 * n)%nat. lia.
    - (* Join arrays using array_append' *)
      pose proof (proj2 (array_append'
        scalar (word.of_Z (Memory.bytes_per_word width))
        c0 (c1 ++ c2) pout m)) as Hback.
      apply Hback. clear Hback.
      exists ma0, (map.putmany ma1 ma2).
      destruct Hms01 as [Heq01 Hd01]. subst.
      destruct Hms12 as [Heq12 Hd12]. subst.
      split; [split; [reflexivity | exact Hd01] |]. split.
      { exact Ha0. }
      { rewrite Hlen0'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
        pose proof (proj2 (array_append'
          scalar (word.of_Z (Memory.bytes_per_word width))
          c1 c2 (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n))) (map.putmany ma1 ma2))) as Hback2.
        apply Hback2. clear Hback2.
        exists ma1, ma2.
        split; [split; [reflexivity | exact Hd12] |]. split.
        { exact Ha1. }
        { rewrite Hlen1'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
          replace (word.add (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
                            (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
            with (word.add pout fp6_c2_offset)
            by (unfold fp6_c2_offset; fold n;
                replace (2 * (Memory.bytes_per_word width * Z.of_nat n))
                  with (Memory.bytes_per_word width * Z.of_nat n + Memory.bytes_per_word width * Z.of_nat n) by lia;
                rewrite word.ring_morph_add; apply word.add_assoc).
          exact Ha2. } }
  Qed.

  (* c0/c1/c2 decomposition lemmas for concatenated output *)
  Lemma c0_felem_app (a b c : list word) :
    length a = Fp2_felem_size ->
    c0_felem (a ++ b ++ c) = a.
  Proof.
    intro H. unfold c0_felem.
    set (n := (2 * fp_felem_size)%nat).
    assert (Hn : n = length a) by (symmetry; exact H).
    rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity.
  Qed.

  Lemma c1_felem_app (a b c : list word) :
    length a = Fp2_felem_size ->
    length b = Fp2_felem_size ->
    c1_felem (a ++ b ++ c) = b.
  Proof.
    intros Ha Hb. unfold c1_felem.
    set (n := (2 * fp_felem_size)%nat).
    assert (Hn : n = length a) by (symmetry; exact Ha).
    rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
    assert (Hn' : length a = length b) by (rewrite Ha, Hb; reflexivity).
    rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity.
  Qed.

  Lemma c2_felem_app (a b c : list word) :
    length a = Fp2_felem_size ->
    length b = Fp2_felem_size ->
    c2_felem (a ++ b ++ c) = c.
  Proof.
    intros Ha Hb. unfold c2_felem.
    set (n := (2 * fp_felem_size)%nat).
    replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite <- ListUtil.skipn_skipn.
    assert (Hn : n = length a) by (symmetry; exact Ha).
    rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
    assert (Hn' : length a = length b) by (rewrite Ha, Hb; reflexivity).
    rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* spec_of instances for the underlying Fp2 operations               *)
  (* ================================================================ *)

  Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
    AbstractField.spec_of_felem_copy (F:=Fp2).
  Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp2).
  Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp2).
  Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp2).
  Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp2).
  Instance spec_of_Fp2_square : spec_of (AbstractField.square (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp2).
  Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp2).

  (* Fp-level spec_of instances (used by fp2_mul_xi) *)
  Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy (F:=Fp).
  Instance spec_of_Fp_add : spec_of (AbstractField.add (F:=Fp)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp).
  Instance spec_of_Fp_sub : spec_of (AbstractField.sub (F:=Fp)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp).

  (* Function name for the fp2_mul_xi helper *)
  Local Definition fp2_mul_xi_name := (fp2_prefix ++ "mul_xi")%string.

  (* ================================================================ *)
  (* FieldNames for Fp6                                                *)
  (* ================================================================ *)

  Context {Fp6_names : FieldNames (F:=Fp6)}.
  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {Fp_names : FieldNames (F:=Fp)}.

  (* ================================================================ *)
  (* Fp6 function bodies (placeholder: cmd.skip)                       *)
  (* ================================================================ *)

  Import Syntax BinInt String List.ListNotations.

  (* Generate real WP goals for (string * func) definitions *)
  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

  Local Ltac2 Notation "instance_of" type(constr) :=
    lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

  Local Ltac2 rec callee_specs_ft (cmd : constr) : constr list :=
    multi_match! cmd with
      | cmd.cond _ ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.seq ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.while _ ?c => callee_specs_ft c
      | cmd.stackalloc _ _ ?c => callee_specs_ft c
      | cmd.call _ ?f _ => [instance_of (spec_of $f)]
      | _ => []
    end.

  Local Ltac2 program_logic_goal_for_ft (proc : constr) : unit :=
    let unfolded := eval hnf in $proc in
    lazy_match! unfolded with
    | (?fname, (?params, ?rets, ?body)) =>
      let fname_spec := instance_of (spec_of $fname) in
      let specs := callee_specs_ft body in
      let goal := (fun (functions : constr) =>
        List.fold_right (fun ps c => '(($ps $functions) -> $c)) specs '($fname_spec $functions)) in
      exact (forall functions (EnvContains : map.get functions $fname = Some ($params, $rets, $body)),
        ltac2:(let g := goal &functions in exact $g))
    end.

  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
  Local Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
     Control.plus (fun () => program_logic_goal_for_ft (Ltac2.Constr.pretype proc)) (fun _ => exact True)))
    (at level 10, only parsing).

  (* -------------------------------------------------------------- *)
  (* fp2_mul_xi: multiply Fp2 element by ξ in Fp2                    *)
  (* Each curve provides its own body + model + spec.                 *)
  (* BLS12-381: (a0,a1) -> (a0-a1, a0+a1)  [ξ=1+u, β=-1]           *)
  (* BLS12-377: (a0,a1) -> (-5*a1, a0)      [ξ=u, β=-5]             *)
  (* -------------------------------------------------------------- *)

  (* Curve provides the function body *)
  Variable Fp2_mul_xi : function_t.
  Hypothesis Fp2_mul_xi_name_eq : fst Fp2_mul_xi = fp2_mul_xi_name.

  (* UnOp instance for fp2_mul_xi — model is always the generalized spec *)
  Local Instance un_Fp2_mul_xi
    : @AbstractField.UnOp _ _ _ _ Fp2 Fp2_fp_inst Fp2_repr_inst fp2_mul_xi_name :=
    {| AbstractField.un_model := BLS12Fp6Spec.fp2_mul_xi M_pos beta xi_re xi_im;
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst |}.

  (* Fp2_mul_xi spec — flat version for in-place calls (px = pout) *)
  Instance spec_of_Fp2_mul_xi : spec_of fp2_mul_xi_name :=
    AbstractField.unop_spec (field_representation:=Fp2_repr_inst) un_Fp2_mul_xi.

  (* Nested version for non-in-place calls — gives cross-disjointness for free *)
  Definition spec_of_Fp2_mul_xi_nested : spec_of fp2_mul_xi_name :=
    AbstractField.unop_spec_nested (field_representation:=Fp2_repr_inst) un_Fp2_mul_xi.

  (* Curve must prove both specs. The nested version is strictly stronger
     for the non-in-place case. *)
  Hypothesis Fp2_mul_xi_ok :
    forall functions, map.get functions fp2_mul_xi_name = Some (snd Fp2_mul_xi) ->
    spec_of_Fp_felem_copy functions ->
    spec_of_Fp_sub functions ->
    spec_of_Fp_add functions ->
    spec_of_Fp2_mul_xi functions.

  Hypothesis Fp2_mul_xi_nested_ok :
    forall functions, map.get functions fp2_mul_xi_name = Some (snd Fp2_mul_xi) ->
    spec_of_Fp_felem_copy functions ->
    spec_of_Fp_sub functions ->
    spec_of_Fp_add functions ->
    spec_of_Fp2_mul_xi_nested functions.

  Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ F_representation).
  Local Notation fp_felem_offset_word := (word.of_Z fp_felem_offset).

  (* Disjointness automation for map algebra *)
  Local Ltac map_disjoint_auto :=
    lazymatch goal with
    | |- map.disjoint (map.putmany _ _) _ =>
        apply map.disjoint_putmany_l; split; map_disjoint_auto
    | |- map.disjoint _ (map.putmany _ _) =>
        apply map.disjoint_putmany_r; split; map_disjoint_auto
    | |- map.disjoint ?a ?b =>
        first [ assumption
              | (unfold map.disjoint; intros ?k ?v1 ?v2 ?Hg1 ?Hg2;
                 match goal with H : map.disjoint _ _ |- _ => exact (H k v2 v1 Hg2 Hg1) end) ]
    end.

  (* Swap two adjacent elements in a right-associated putmany chain:
     putmany a (putmany b X) → putmany b (putmany a X) *)
  Local Ltac map_swap a b :=
    rewrite (map.putmany_assoc a b);
    let D := fresh "D" in
    assert (D : map.disjoint a b) by map_disjoint_auto;
    rewrite (map.putmany_comm a b D);
    clear D;
    rewrite <- (map.putmany_assoc b a).

  (* ================================================================ *)
  (* WP proof automation tactics                                       *)
  (* ================================================================ *)

  (* Solve map.get goals by trying put_same/put_diff repeatedly *)
  Local Ltac solve_map_get :=
    repeat (first [ apply map.get_put_same
                  | rewrite map.get_put_diff by (cbv; congruence) ]).

  (* Solve dexprs goals for function call arguments.
     Handles expr.var lookups, expr.op offsets, and expr.literal.
     Call after [exists [arg1; arg2; ...]. split.] *)
  Local Ltac solve_dexprs :=
    (* Substitute context-level let definitions (l, l0, ..., lN from stackallocs)
       so that map.get_put_same/diff can see through the locals map chain *)
    repeat match goal with x := map.put _ _ _ |- _ => unfold x in *; clear x end;
    cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2 expr_fp_snd
         WeakestPrecondition.expr WeakestPrecondition.expr_body];
    repeat first
      [ exact eq_refl
      | eexists; split;
        [ solve_map_get; try exact eq_refl | ]
      | straightline ].

  (* Solve map.putmany equality goals by right-associating and selection-sorting.
     Strategy: match RHS head, bubble it forward in LHS, strip with f_equal, recurse. *)
  Local Ltac solve_putmany_eq_aux n :=
    match n with
    | O => fail "solve_putmany_eq: out of fuel"
    | S ?n' =>
      first [
        reflexivity
      | (* Strip matching heads *)
        match goal with
        | |- map.putmany ?a _ = map.putmany ?a _ =>
          apply (f_equal (map.putmany a)); solve_putmany_eq_aux n'
        end
      | (* Bubble the RHS head (target) forward in LHS *)
        match goal with
        | |- _ = map.putmany ?target _ =>
          match goal with
          | |- context [map.putmany ?a (map.putmany target ?rest)] =>
            rewrite (map.putmany_assoc a target rest);
            rewrite (map.putmany_comm a target) by map_disjoint_auto;
            rewrite <- (map.putmany_assoc target a rest);
            solve_putmany_eq_aux n'
          end
        end
      | (* Two-element swap: a ∪ b = b ∪ a *)
        match goal with
        | |- map.putmany ?a ?b = map.putmany ?b ?a =>
          apply map.putmany_comm; map_disjoint_auto
        end
      ]
    end.
  Local Ltac solve_putmany_eq :=
    rewrite <- !map.putmany_assoc;
    solve_putmany_eq_aux 50%nat.

  (* Decompose Fp6 bounded_by into 3 Fp2 bounded_by in a specific hypothesis *)
  Local Ltac fp6_bounds_decompose_in H :=
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in H;
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in H;
    let H0 := fresh H "0" in
    let H12 := fresh H in
    destruct H as [H0 H12];
    let H1 := fresh H "1" in
    let H2 := fresh H "2" in
    destruct H12 as [H1 H2].

  (* Change Fp6 feval to 3 Fp2 fevals of c0/c1/c2 components *)
  Local Ltac fp6_feval_eq :=
    change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                   @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                  @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws)));
    cbv beta.

  (* Change Fp6 bounded_by to 3 Fp2 bounded_by of c0/c1/c2 components *)
  Local Ltac fp6_bounded_by_eq :=
    change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                   /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                   /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem));
    cbv beta.

  (* Fp2-level bounds equivalence: loose → tight (lifts bounds_equiv to Fp2) *)
  Lemma Fp2_bounds_tight_of_loose : forall x,
    @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) x ->
    @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) x.
  Proof.
    intros fe [Hfst Hsnd].
    split; apply bounds_equiv; assumption.
  Qed.

  (* Fp2-level bounds relaxation: tight → loose (lifts relax_bounds to Fp2) *)
  Lemma Fp2_bounds_loose_of_tight : forall x,
    @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) x ->
    @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) x.
  Proof.
    intros fe [Hfst Hsnd].
    split; exact (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok _ Hfst)
              || exact (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok _ Hsnd).
  Qed.

  (* Solve bounded_by goals: try direct assumption or bounds_equiv *)
  Local Ltac solve_bounds :=
    first [ assumption | apply bounds_equiv; assumption
          | apply Fp2_bounds_tight_of_loose; assumption
          | apply Fp2_bounds_loose_of_tight; assumption
          | apply relax_bounds; assumption ].

  (* Derive all pairwise disjointness from putmany disjointness hypotheses *)
  Local Ltac split_all_disjointness :=
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
    end.

  (* Bridge between generic theory (parameterized by β) and
     BLS12-specific Fp6 spec (hardcoded u²=-1).
     Each curve instantiation provides these proofs.
     For β=-1: use mul_neg_1 / invp2_plus_norm.
     For other β: generalize the Fp6 spec accordingly. *)
  Hypothesis mulp2_eq_fp2_mul : forall a b,
    QuadraticExtensions.mulp2 M_pos beta a b = BLS12Fp6Spec.fp2_mul M_pos beta a b.
  Hypothesis invp2_eq_fp2_inv : forall x,
    QuadraticExtensions.invp2 M_pos beta x = BLS12Fp6Spec.fp2_inv M_pos beta x.

  (* Fp2_mul_xi_ok proof is now provided per-curve via spec_of_Fp2_mul_xi hypothesis.
     The old BLS12-381-specific proof has been moved to the instantiation file. *)

  (* REMOVED: Fp2_mul_xi_ok proof (was 340 lines, BLS12-381 specific) *)
  (* The proof is now provided at curve instantiation time. *)

  (* The old Fp2_mul_xi_ok proof (340 lines) has been removed.
     It is now provided per-curve via spec_of_Fp2_mul_xi. *)
  (* BEGIN_DELETE_OLD_PROOF *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_felem_copy : function_t :=
    (AbstractField.felem_copy (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x")])
    ))).

  Instance spec_of_Fp6_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).

  Lemma Fp6_felem_copy_ok : program_logic_goal_for_function! Fp6_felem_copy.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFcopy3.
    unfold spec_of_Fp6_copy, AbstractField.spec_of_felem_copy.
    intros pout px out x R Rout tr mem0 [Hmem0_1 Hmem0_2].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_felem_copy].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for first call: [out; x] (c0 at offset 0) *)
    exists [pout; px]. split.
    { unfold dexprs, expr_fp6_c0. repeat straightline.
      eexists. split. { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [list_map]. eexists. split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body]. apply map.get_put_same. }
      exact eq_refl. }
    (* === Decompose preconditions === *)
    destruct Hmem0_1 as [m_x [m_or [Hsep1 [Hx Hor]]]].
    destruct Hor as [m_o [m_r [Hsep_or [Ho Hr]]]].
    (* Split Fp6 FElems into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split _ _ _ Hx) as Hx_split.
    destruct Hx_split as [m_x0 [m_x12 [Hsep_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsep_x12 [Hx1 Hx2]]]].
    pose proof (Fp6_raw_FElem_split _ _ _ Ho) as Ho_split.
    destruct Ho_split as [m_o0 [m_o12 [Hsep_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsep_o12 [Ho1 Ho2]]]].
    (* Relate two preconditions using FElem_to_bytes + anybytes_unique_domain *)
    destruct Hmem0_2 as [m_o' [m_rout [Hsep2 [Ho' Hrout]]]].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout out m_o Ho) as Hph_o.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout out m_o' Ho') as Hph_o'.
    unfold AbstractField.Placeholder in Hph_o, Hph_o'.
    pose proof (Memory.anybytes_unique_domain _ _ _ _ Hph_o Hph_o') as Hsd.
    destruct Hsep1 as [Heq1 Hd1]. destruct Hsep_or as [Heq_or Hd_or]. subst m_or mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_x_o Hd_x_r].
    assert (Hsplit_mem : map.split (map.putmany m_x (map.putmany m_o m_r)) m_o (map.putmany m_x m_r)).
    { split.
      { rewrite map.putmany_assoc.
        rewrite (map.putmany_comm m_x m_o Hd_x_o).
        symmetry. apply map.putmany_assoc. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x_o k v2 v1 Hg2 Hg1). }
        { exact Hd_or. } } }
    pose proof (proj1 (map.split_comm _ _ _) Hsplit_mem) as Hsplit_mem'.
    pose proof (proj1 (map.split_comm _ _ _) Hsep2) as Hsep2'.
    pose proof (map.split_diff Hsd Hsplit_mem' Hsep2') as [Heq_rout Heq_o'].
    subst m_o'.
    rewrite <- Heq_rout in Hrout.
    clear Heq_rout Hsd Hsep2 Hsep2' Hsplit_mem Hsplit_mem' Hph_o Hph_o' Ho'.
    (* Now: Hrout : Rout (map.putmany m_x m_r) *)
    (* Inline map.split equalities *)
    destruct Hsep_x as [Heq_x Hd_x012]. destruct Hsep_x12 as [Heq_x12 Hd_x12].
    destruct Hsep_o as [Heq_o Hd_o012]. destruct Hsep_o12 as [Heq_o12 Hd_o12].
    subst m_x m_o m_x12 m_o12.
    (* Derive pairwise disjointness *)
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x0_o Hd_x12_o].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x12_o) as [Hd_x1_o Hd_x2_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x0_o) as [Hd_x0_o0 Hd_x0_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x0_o12) as [Hd_x0_o1 Hd_x0_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o0 Hd_x1_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o12) as [Hd_x1_o1 Hd_x1_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o) as [Hd_x2_o0 Hd_x2_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o12) as [Hd_x2_o1 Hd_x2_o2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x0_r Hd_x12_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x12_r) as [Hd_x1_r Hd_x2_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o0_r Hd_o12_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_o12_r) as [Hd_o1_r Hd_o2_r].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x012) as [Hd_x0_x1 Hd_x0_x2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_o012) as [Hd_o0_o1 Hd_o0_o2].
    clear Hd_x_o Hd_x_r Hd_or Hd1 Hd_x0_o Hd_x12_o Hd_x0_o12 Hd_x1_o Hd_x1_o12 Hd_x2_o Hd_x2_o12 Hd_x12_r Hd_o12_r.
    (* === First Fp2 copy call (c0) via weaken_call === *)
    set (rest1 := map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout px (c0_felem out) (c0_felem x)
        (fun m => (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆
                   (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆
                    (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem out) ⋆
                     (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out) ⋆ R)))) m)
        (eq rest1)
        tr).
      split.
      { (* Precondition 1: (FElem px (c0 x) * FElem pout (c0 out) * frame) *)
        exists (map.putmany m_x0 m_o0),
               (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r)))).
        split; [split |].
        { rewrite !map.putmany_assoc.
          repeat (apply f_equal2; [| reflexivity]).
          rewrite (map.disjoint_putmany_commutes _ m_x2 m_o0 Hd_x2_o0).
          rewrite (map.disjoint_putmany_commutes m_x0 m_x1 m_o0 Hd_x1_o0).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x0, m_o0.
          split; [split; [reflexivity | exact Hd_x0_o0] |].
          split; [exact Hx0 | exact Ho0]. }
        { exists m_x1, (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx1 |].
          exists m_x2, (map.putmany m_o1 (map.putmany m_o2 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx2 |].
          exists m_o1, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Ho1 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Precondition 2: (FElem pout (c0 out) * eq rest1) *)
        exists m_o0, rest1.
        split; [split |].
        { subst rest1.
          rewrite !map.putmany_assoc.
          repeat (apply f_equal2; [| reflexivity]).
          rewrite (map.disjoint_putmany_commutes _ m_x2 m_o0 Hd_x2_o0).
          rewrite (map.disjoint_putmany_commutes m_x0 m_x1 m_o0 Hd_x1_o0).
          rewrite (map.putmany_comm m_x0 m_o0 Hd_x0_o0).
          reflexivity. }
        { subst rest1. map_disjoint_auto. }
        split; [exact Ho0 | exact eq_refl]. } }
    (* === Process postcondition of first call === *)
    intros t' m' rets [Hrets [Htr1 Hsep_post1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for second call: [out+off1; x+off1] *)
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body expr_fp6_c1].
      repeat straightline.
      unfold list_map. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    (* Unpack postcondition of first call *)
    destruct Hsep_post1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_p1 Hd_p1].
    subst rest1.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p1) as [Hd_n0_x0 Hd_n0_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest) as [Hd_n0_x1 Hd_n0_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest2) as [Hd_n0_x2 Hd_n0_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest3) as [Hd_n0_o1 Hd_n0_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest4) as [Hd_n0_o2 Hd_n0_r].
    clear Hd_n0_rest Hd_n0_rest2 Hd_n0_rest3 Hd_n0_rest4.
    (* === Second Fp2 copy call (c1) via weaken_call === *)
    set (rest2 := map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 (word.add pout fp6_c1_offset) (word.add px fp6_c1_offset)
        (c1_felem out) (c1_felem x)
        (fun m => (FElem_Fp2 pout (c0_felem x) ⋆
                   (FElem_Fp2 px (c0_felem x) ⋆
                    (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆
                     (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out) ⋆ R)))) m)
        (eq rest2)
        tr).
      split.
      { (* Precondition 1: (FElem (px+off1) (c1 x) * FElem (pout+off1) (c1 out) * frame) m' *)
        subst m'.
        exists (map.putmany m_x1 m_o1),
               (map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x2 (map.putmany m_o2 m_r)))).
        split; [split |].
        { map_swap m_x2 m_o1.
          map_swap m_x0 m_x1.
          map_swap m_new0 m_x1.
          map_swap m_x0 m_o1.
          map_swap m_new0 m_o1.
          rewrite <- (map.putmany_assoc m_x1 m_o1).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x1, m_o1.
          split; [split; [reflexivity | exact Hd_x1_o1] |].
          split; [exact Hx1 | exact Ho1]. }
        { exists m_new0, (map.putmany m_x0 (map.putmany m_x2 (map.putmany m_o2 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew0 |].
          exists m_x0, (map.putmany m_x2 (map.putmany m_o2 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx0 |].
          exists m_x2, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx2 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Precondition 2: (FElem (pout+off1) (c1 out) * eq rest2) m' *)
        subst m'.
        exists m_o1, rest2.
        split; [split |].
        { subst rest2.
          map_swap m_x2 m_o1.
          map_swap m_x1 m_o1.
          map_swap m_x0 m_o1.
          map_swap m_new0 m_o1.
          reflexivity. }
        { subst rest2. map_disjoint_auto. }
        split; [exact Ho1 | exact eq_refl]. } }
    (* === Process postcondition of second call === *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_post2]].
    subst rets2. symmetry in Htr2. subst t''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for third call: [out+off2; x+off2] *)
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body expr_fp6_c2].
      repeat straightline.
      unfold list_map. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    (* Unpack postcondition of second call *)
    destruct Hsep_post2 as [m_new1 [m_frame2 [Hsp_post2 [Hnew1 Hframe2]]]].
    subst m_frame2.
    destruct Hsp_post2 as [Heq_p2 Hd_p2].
    subst rest2.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p2) as [Hd_n1_n0 Hd_n1_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest) as [Hd_n1_x0 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_x1 Hd_n1_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest3) as [Hd_n1_x2 Hd_n1_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest4) as [Hd_n1_o2 Hd_n1_r].
    clear Hd_n1_rest Hd_n1_rest2 Hd_n1_rest3 Hd_n1_rest4.
    (* === Third Fp2 copy call (c2) via weaken_call === *)
    set (rest3 := map.putmany m_new0 (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy3 (word.add pout fp6_c2_offset) (word.add px fp6_c2_offset)
        (c2_felem out) (c2_felem x)
        (fun m => (FElem_Fp2 pout (c0_felem x) ⋆
                   (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem x) ⋆
                    (FElem_Fp2 px (c0_felem x) ⋆
                     (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆ R)))) m)
        (eq rest3)
        tr).
      split.
      { (* Precondition 1: (FElem (px+off2) (c2 x) * FElem (pout+off2) (c2 out) * frame) m'' *)
        subst m''.
        exists (map.putmany m_x2 m_o2),
               (map.putmany m_new0 (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 m_r)))).
        split; [split |].
        { map_swap m_x1 m_x2.
          map_swap m_x0 m_x2.
          map_swap m_new0 m_x2.
          map_swap m_new1 m_x2.
          map_swap m_x1 m_o2.
          map_swap m_x0 m_o2.
          map_swap m_new0 m_o2.
          map_swap m_new1 m_o2.
          map_swap m_new1 m_new0.
          rewrite <- (map.putmany_assoc m_x2 m_o2).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x2, m_o2.
          split; [split; [reflexivity | exact Hd_x2_o2] |].
          split; [exact Hx2 | exact Ho2]. }
        { exists m_new0, (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew0 |].
          exists m_new1, (map.putmany m_x0 (map.putmany m_x1 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew1 |].
          exists m_x0, (map.putmany m_x1 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx0 |].
          exists m_x1, m_r.
          split; [split; [reflexivity | exact Hd_x1_r] |].
          split; [exact Hx1 | exact Hr]. } }
      { (* Precondition 2: (FElem (pout+off2) (c2 out) * eq rest3) m'' *)
        subst m''.
        exists m_o2, rest3.
        split; [split |].
        { subst rest3.
          map_swap m_x2 m_o2.
          map_swap m_x1 m_o2.
          map_swap m_x0 m_o2.
          map_swap m_new0 m_o2.
          map_swap m_new1 m_o2.
          map_swap m_new1 m_new0.
          reflexivity. }
        { subst rest3. map_disjoint_auto. }
        split; [exact Ho2 | exact eq_refl]. } }
    (* === Final: process third postcondition and close === *)
    intros t''' m''' rets3 [Hrets3 [Htr3 Hsep_post3]].
    subst rets3. symmetry in Htr3. subst t'''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* Destruct third postcondition *)
    destruct Hsep_post3 as [m_new2 [m_frame3 [Hsp_post3 [Hnew2 Hframe3]]]].
    subst m_frame3.
    destruct Hsp_post3 as [Heq_p3 Hd_p3].
    subst rest3.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p3) as [Hd_n2_n0 Hd_n2_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest) as [Hd_n2_n1 Hd_n2_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest2) as [Hd_n2_x0 Hd_n2_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest3) as [Hd_n2_x1 Hd_n2_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest4) as [Hd_n2_x2 Hd_n2_r].
    clear Hd_n2_rest Hd_n2_rest2 Hd_n2_rest3 Hd_n2_rest4.
    (* Reconstruct Fp6 FElem for x *)
    assert (Hdecomp : x = c0_felem x ++ c1_felem x ++ c2_felem x)
      by (symmetry; apply Fp6_list_decomp).
    rewrite Hdecomp.
    exists (map.putmany m_new0 (map.putmany m_new1 m_new2)),
           (map.putmany (map.putmany m_x0 (map.putmany m_x1 m_x2)) m_r).
    split; [split |].
    { subst m'''.
      map_swap m_new2 m_new0.
      map_swap m_new2 m_new1.
      rewrite <- !map.putmany_assoc.
      reflexivity. }
    { map_disjoint_auto. }
    split.
    { (* Fp6_raw_FElem_join *)
      apply Fp6_raw_FElem_join.
      { exact (Fp2_FElem_length _ _ _ Hnew0). }
      { exact (Fp2_FElem_length _ _ _ Hnew1). }
      { exact (Fp2_FElem_length _ _ _ Hnew2). }
      exists m_new0, (map.putmany m_new1 m_new2).
      split; [split; [reflexivity |] |].
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n1_n0 k v2 v1 Hg2 Hg1). }
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n0 k v2 v1 Hg2 Hg1). } }
      split; [exact Hnew0 |].
      exists m_new1, m_new2.
      split; [split; [reflexivity |] |].
      { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n1 k v2 v1 Hg2 Hg1). }
      split; [exact Hnew1 | exact Hnew2]. }
    { exact Hrout. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_add: componentwise addition of 3 Fp2 elements               *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_add : function_t :=
    (AbstractField.add (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      (* Copy inputs to stack-allocated temporaries *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* out.c0 = x.c0 + y.c0 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* out.c1 = x.c1 + y.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* out.c2 = x.c2 + y.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")])
    ))).

  Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp6).

  Lemma Fp6_add_ok : program_logic_goal_for_function! Fp6_add.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFadd1 HFadd2 HFadd3.
    unfold spec_of_Fp6_add, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_add].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_xrx_sY Hd_sX_sY].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_x_sY Hd_rx_sY].
    (* For copy spec, relate the two preconditions *)
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === First Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { subst l0 l.
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ AbstractField.FElem (F:=Fp6) allocy allocy_val) m)
        (eq (map.putmany (map.putmany m_x m_rx) mStackY))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * R1) *)
        exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
        split; [split |].
        { rewrite <- !map.putmany_assoc. f_equal.
          map_swap m_rx mStackX. reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, mStackY.
          split; [split; [reflexivity | exact Hd_rx_sY] |].
          split; [exact Hrx | exact Hallocy]. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout1) *)
        exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
        split; [split |].
        { rewrite map.putmany_assoc.
          let D := fresh "D" in
          assert (D : map.disjoint (map.putmany m_x m_rx) mStackX) by map_disjoint_auto;
          rewrite (map.putmany_comm (map.putmany m_x m_rx) mStackX D); clear D.
          rewrite <- map.putmany_assoc. reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process first copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 copy call: y → allocy === *)
    (* Decompose copy1 postcondition *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    (* Decompose Hmemy *)
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    (* Derive disjointness facts *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_xrx_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY'].
    (* dexprs for second copy *)
    exists [allocy; py]. split.
    { subst l0 l.
      eexists. split. { apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (AbstractField.FElem (F:=Fp6) allocx x ⋆ Ry) m)
        (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
        tr).
      split.
      { (* Precondition 1: (FElem py y * FElem allocy allocy_val * R2) *)
        rewrite Heq_mem0_y.
        exists (map.putmany m_y mStackY), (map.putmany m_new1 m_ry).
        split; [split |].
        { transitivity (map.putmany m_new1 (map.putmany (map.putmany m_y mStackY) m_ry)).
          { f_equal. apply map.disjoint_putmany_commutes. exact Hd_ry_sY'. }
          transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y mStackY)) m_ry).
          { apply map.putmany_assoc. }
          transitivity (map.putmany (map.putmany m_new1 m_ry) (map.putmany m_y mStackY)).
          { apply map.disjoint_putmany_commutes.
            apply map.disjoint_putmany_l. split; [exact Hd_yry |].
            unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_ry_sY' k v2 v1 H2 H1). }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_y | exact Hd_n1_sY]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_yry k v2 v1 H2 H1). }
            { exact Hd_ry_sY'. } } }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_y k v2 v1 H2 H1). }
            { exact Hd_yry. } }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_sY k v2 v1 H2 H1). }
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_ry_sY' k v2 v1 H2 H1). } } }
        split.
        { exists m_y, mStackY.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfelem_y | exact Hallocy]. }
        { exists m_new1, m_ry.
          split; [split; [reflexivity | exact Hd_n1_ry] |].
          split; [exact Hfelem_allocx | exact Hry]. } }
      { (* Precondition 2: (FElem allocy allocy_val * Rout2) *)
        rewrite Heq_mem0_y.
        exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
        split; [split |].
        { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
          { apply map.putmany_assoc. }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_xrx_sY]. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_n1_sY k v2 v1 H2 H1). }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_xrx_sY k v2 v1 H2 H1). } }
        split; [exact Hallocy | exact eq_refl]. } }
    (* Process second copy postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 3: Three Fp2 add calls === *)
    (* Decompose copy2 postcondition *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp6 FElems into 3 Fp2 components each *)
    pose proof (Fp6_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    pose proof (Fp6_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay12 [Hsp_ay [Hfe_ay0 Hay12]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay0_12].
    destruct Hay12 as [m_ay1 [m_ay2 [Hsp_ay12 [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay12 as [Heq_ay12 Hd_ay12].
    (* Split output FElem *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx, Hby.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    destruct Hby as [Hby0 [Hby1 Hby2]].
    (* Derive Heq_yr: m_y ++ m_ry = m_out ++ m_rr *)
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    (* Subst decomposed maps *)
    subst m_ax12 m_ay12 m_o12 m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 10-way sep fact *)
    assert (Hsep10 :
      ((FElem_Fp2 allocy (c0_felem y) ⋆
        (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y))) ⋆
       ((FElem_Fp2 allocx (c0_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
          FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x))) ⋆
        ((FElem_Fp2 pout (c0_felem old_out) ⋆
          (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
           FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out))) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 (map.putmany m_ay1 m_ay2))
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)))).
    { exists (map.putmany m_ay0 (map.putmany m_ay1 m_ay2)),
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, (map.putmany m_ay1 m_ay2).
        split; [split; [reflexivity | exact Hd_ay0_12] |].
        split; [exact Hfe_ay0 |].
        exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay12] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === Phase 4: First Fp2 add call: add(out.c0, allocx.c0, allocy.c0) === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout allocx allocy
           (c0_felem old_out) (c0_felem x) (c0_felem y)
           _ tr).
         split; [exact Hbx0 |].
         split; [exact Hby0 |].
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    (* Process first Fp2 add postcondition *)
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out0' [Hfeval0 [Hbound0 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 4: Second Fp2 add call: add(out.c1, allocx.c1, allocy.c1) === *)
    exists [word.add pout fp6_c1_offset; word.add allocx fp6_c1_offset;
            word.add allocy fp6_c1_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout fp6_c1_offset)
           (word.add allocx fp6_c1_offset) (word.add allocy fp6_c1_offset)
           (c1_felem old_out) (c1_felem x) (c1_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         pose proof Hsep_add1 as H'. ecancel_assumption. }
    (* Process second Fp2 add postcondition *)
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out1' [Hfeval1 [Hbound1 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 4: Third Fp2 add call: add(out.c2, allocx.c2, allocy.c2) === *)
    exists [word.add pout fp6_c2_offset; word.add allocx fp6_c2_offset;
            word.add allocy fp6_c2_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 (word.add pout fp6_c2_offset)
           (word.add allocx fp6_c2_offset) (word.add allocy fp6_c2_offset)
           (c2_felem old_out) (c2_felem x) (c2_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_add2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add2 as H'. ecancel_assumption. }
         pose proof Hsep_add2 as H'. ecancel_assumption. }
    (* Process third Fp2 add postcondition *)
    intros t_add3 m_add3 rets_add3 [Hrets_add3 [Htr_add3 [out2' [Hfeval2 [Hbound2 Hsep_add3]]]]].
    subst rets_add3 t_add3.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 5: Destructure Hsep_add3 into 10 map components === *)
    destruct Hsep_add3 as [m_A [m_rest1 [[Heq_add3 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_J [[Heq_r8 Hd_IJ] [HI HJ]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7 m_rest8 m_add3.
    (* Derive pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    (* === Phase 6: Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp2 allocy (c0_felem y) ⋆
      (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
       FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y)))
      (map.putmany m_D (map.putmany m_E m_FF))).
    { exists m_D, (map.putmany m_E m_FF).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_FF.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HFF]. }
    pose proof (Fp6_raw_FElem_join allocy (c0_felem y) (c1_felem y) (c2_felem y)
      (map.putmany m_D (map.putmany m_E m_FF))
      Hlen_D Hlen_E Hlen_FF Hjoin_y) as Hfp6_y.
    rewrite Fp6_list_decomp in Hfp6_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocy y
      (map.putmany m_D (map.putmany m_E m_FF)) Hfp6_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    (* Provide witnesses for allocy deallocation *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))))),
      (map.putmany m_D (map.putmany m_E m_FF)).
    split. { exact Hanybytes_y. }
    split. { split.
      { (* Equality: rearrange putmany to move D, E, FF to the end *)
        rewrite (map.putmany_assoc m_E m_FF
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_assoc m_D (map.putmany m_E m_FF)
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_comm (map.putmany m_D (map.putmany m_E m_FF))
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 7: Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_G (map.putmany m_HH m_I))).
    { exists m_G, (map.putmany m_HH m_I).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HG |].
      exists m_HH, m_I.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HHH | exact HI]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_G (map.putmany m_HH m_I))
      Hlen_G Hlen_HH Hlen_I Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_G (map.putmany m_HH m_I)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    (* Provide witnesses for allocx deallocation *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_J))),
      (map.putmany m_G (map.putmany m_HH m_I)).
    split. { exact Hanybytes_x. }
    split. { split.
      { (* Equality: rearrange putmany to move G, HH, I to the end *)
        rewrite (map.putmany_assoc m_HH m_I m_J).
        rewrite (map.putmany_assoc m_G (map.putmany m_HH m_I) m_J).
        rewrite (map.putmany_comm (map.putmany m_G (map.putmany m_HH m_I)) m_J).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 8: Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    (* sep *)
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_J.
      split; [split |].
      { rewrite (map.putmany_assoc m_B m_C m_J).
        rewrite (map.putmany_assoc m_A (map.putmany m_B m_C) m_J).
        f_equal.
        rewrite (map.putmany_assoc m_A m_B m_C).
        rewrite (map.putmany_comm m_A m_B). 2: { exact Hd33. }
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HJ]. }
  Qed.


  (* Copy-eliminated Fp6_add: operates directly on input pointers.
     Proved correct — the per-call sep frame ensures each Fp2_add
     reads from an untouched input slice. *)
  Definition Fp6_add_nocopy : function_t :=
    ((AbstractField.add (F:=Fp6) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "inx"); expr_fp6_c0 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "inx"); expr_fp6_c1 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "inx"); expr_fp6_c2 (expr.var "iny")])
    ))).

  (* The nocopy version satisfies the SAME spec as the original Fp6_add. *)
  Lemma Fp6_add_nocopy_ok :
    forall functions
      (EnvContains : map.get functions (fst Fp6_add_nocopy) = Some (snd Fp6_add_nocopy))
      (HFadd1 : spec_of_Fp2_add functions)
      (HFadd2 : spec_of_Fp2_add functions)
      (HFadd3 : spec_of_Fp2_add functions),
    forall pout px py old_out x y Rr tr mem0,
      @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
        (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x ->
      @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
        (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) y ->
      (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst px x ⋆
       (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst py y ⋆
        (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout old_out ⋆ Rr))) mem0 ->
      WeakestPrecondition.call functions (fst Fp6_add_nocopy) tr mem0 [pout; px; py]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\
           exists result,
             @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst result =
             @AbstractField.Fadd _ Fp6_fp_inst
               (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x)
               (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst y) /\
             @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
               (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) result /\
             (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout result ⋆
              (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst px x ⋆
               (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst py y ⋆ Rr))) mem').
  Proof.
    intros functions EnvContains HFadd1 HFadd2 HFadd3.
    intros pout px py old_out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_add_nocopy].
    eexists. split. { exact eq_refl. }
    (* Decompose Fp6 sep into Fp2 components *)
    (* Decompose Fp6 sep into Fp2 components *)
    destruct Hsep as [m_x [m_yr [[Heq_m0 Hd_x_yr] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[Heq_yr Hd_y_or] [Hfy Hor]]]].
    destruct Hor as [m_o [m_rr [[Heq_or Hd_o_rr] [Hfo Hrr]]]].
    subst m_yr m_or mem0.
    pose proof (Fp6_raw_FElem_split px x m_x Hfx) as Hx_sep.
    pose proof (Fp6_raw_FElem_split py y m_y Hfy) as Hy_sep.
    pose proof (Fp6_raw_FElem_split pout old_out m_o Hfo) as Ho_sep.
    destruct Hx_sep as [m_x0 [m_x12 [[Heq_x Hd_x0] [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [[Heq_x12 Hd_x12] [Hx1 Hx2]]]]. subst m_x12 m_x.
    destruct Hy_sep as [m_y0 [m_y12 [[Heq_y Hd_y0] [Hy0 Hy12]]]].
    destruct Hy12 as [m_y1 [m_y2 [[Heq_y12 Hd_y12] [Hy1 Hy2]]]]. subst m_y12 m_y.
    destruct Ho_sep as [m_o0 [m_o12 [[Heq_o Hd_o0] [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [[Heq_o12 Hd_o12] [Ho1 Ho2]]]]. subst m_o12 m_o.
    change bounded_by with (fun b ws =>
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem ws) /\
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem ws) /\
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem ws)) in Hbx, Hby.
    cbv beta in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]]. destruct Hby as [Hby0 [Hby1 Hby2]].
    split_all_disjointness. rewrite <- !map.putmany_assoc.
    assert (Hsep_fp2 : (FElem_Fp2 px (c0_felem x) ⋆ (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆ (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆ (FElem_Fp2 py (c0_felem y) ⋆ (FElem_Fp2 (word.add py fp6_c1_offset) (c1_felem y) ⋆ (FElem_Fp2 (word.add py fp6_c2_offset) (c2_felem y) ⋆ (FElem_Fp2 pout (c0_felem old_out) ⋆ (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆ (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out) ⋆ Rr))))))))) (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_y0 (map.putmany m_y1 (map.putmany m_y2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))))))).
    { build_sep. }
    (* Call 1 *)
    (* === Call 1: Fp2_add(out.c0, inx.c0, iny.c0) === *)
    exists [pout; px; py]. split.
    { cbv [dexprs list_map expr_fp6_c0 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout px py (c0_felem old_out) (c0_felem x) (c0_felem y) _ tr).
         split; [exact Hbx0 |]. split; [exact Hby0 |].
         split.
         { eexists. exact Hsep_fp2. }
         split.
         { eexists. pose proof Hsep_fp2 as H'. ecancel_assumption. }
         pose proof Hsep_fp2 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1 t1. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 2: Fp2_add(out.c1, inx.c1, iny.c1) === *)
    exists [word.add pout fp6_c1_offset; word.add px fp6_c1_offset; word.add py fp6_c1_offset]. split.
    { cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout fp6_c1_offset) (word.add px fp6_c1_offset) (word.add py fp6_c1_offset) (c1_felem old_out) (c1_felem x) (c1_felem y) _ tr).
         split; [exact Hbx1 |]. split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1 [Hfeval1 [Hbound1 Hsep2]]]]].
    subst rets2 t2. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 3: Fp2_add(out.c2, inx.c2, iny.c2) === *)
    exists [word.add pout fp6_c2_offset; word.add px fp6_c2_offset; word.add py fp6_c2_offset]. split.
    { cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 (word.add pout fp6_c2_offset) (word.add px fp6_c2_offset) (word.add py fp6_c2_offset) (c2_felem old_out) (c2_felem x) (c2_felem y) _ tr).
         split; [exact Hbx2 |]. split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out2 [Hfeval2 [Hbound2 Hsep3]]]]].
    subst rets3 t3.
    eexists. split. { exact eq_refl. }
    cbv beta. (* reduces list_map without triggering x-name conflict *)
    split. { exact eq_refl. } split. { exact eq_refl. }
    (* === Final postcondition === *)
    (* Destruct Hsep3 to get submaps *)
    destruct Hsep3 as [m_R0 [m_S0 [[Heq_S0 Hd_S0] [HR0 HS0]]]].
    destruct HS0 as [m_R1 [m_S1 [[Heq_S1 Hd_S1] [HR1 HS1]]]].
    destruct HS1 as [m_R2 [m_S2 [[Heq_S2 Hd_S2] [HR2 HS2]]]].
    destruct HS2 as [m_px0 [m_T0 [[Heq_T0 Hd_T0] [Hpx0 HT0]]]].
    destruct HT0 as [m_px1 [m_T1 [[Heq_T1 Hd_T1] [Hpx1 HT1]]]].
    destruct HT1 as [m_px2 [m_T2 [[Heq_T2 Hd_T2] [Hpx2 HT2]]]].
    destruct HT2 as [m_py0 [m_T3 [[Heq_T3 Hd_T3] [Hpy0 HT3]]]].
    destruct HT3 as [m_py1 [m_T4 [[Heq_T4 Hd_T4] [Hpy1 HT4]]]].
    destruct HT4 as [m_py2 [m_rr' [[Heq_T5 Hd_T5] [Hpy2 Hrr']]]].
    subst m_S0 m_S1 m_S2 m_T0 m_T1 m_T2 m_T3 m_T4.
    (* Get Fp2 lengths *)
    pose proof (Fp2_FElem_length _ _ _ HR0) as Hlen_out2.
    pose proof (Fp2_FElem_length _ _ _ HR1) as Hlen_out1.
    pose proof (Fp2_FElem_length _ _ _ HR2) as Hlen_out0.
    pose proof (Fp2_FElem_length _ _ _ Hpx0) as Hlen_px0.
    pose proof (Fp2_FElem_length _ _ _ Hpx1) as Hlen_px1.
    pose proof (Fp2_FElem_length _ _ _ Hpx2) as Hlen_px2.
    pose proof (Fp2_FElem_length _ _ _ Hpy0) as Hlen_py0.
    pose proof (Fp2_FElem_length _ _ _ Hpy1) as Hlen_py1.
    pose proof (Fp2_FElem_length _ _ _ Hpy2) as Hlen_py2.
    (* c0/c1/c2 decomposition of output *)
    assert (Hc0 : c0_felem (out0 ++ out1 ++ out2) = out0).
    { unfold c0_felem. apply ListUtil.firstn_app_sharp. exact Hlen_out0. }
    assert (Hc1 : c1_felem (out0 ++ out1 ++ out2) = out1).
    { unfold c1_felem.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      apply ListUtil.firstn_app_sharp. exact Hlen_out1. }
    assert (Hc2 : c2_felem (out0 ++ out1 ++ out2) = out2).
    { unfold c2_felem.
      set (n := Fp2_felem_size) in *.
      change (2 * fp_felem_size)%nat with n.
      rewrite List.app_assoc.
      rewrite ListUtil.skipn_app_sharp.
      2: { rewrite List.length_app. lia. }
      reflexivity. }
    (* Provide witness *)
    exists (out0 ++ out1 ++ out2).
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0, Hc1, Hc2.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0, Hc1, Hc2.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    (* sep: join Fp2 results into Fp6, join Fp2 inputs into Fp6, provide with Rr *)
    { split_all_disjointness.
      (* Join output Fp2s into Fp6 *)
      assert (Hjoin_out : (FElem_Fp2 pout out0 ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1 ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2))
        (map.putmany m_R2 (map.putmany m_R1 m_R0))).
      { exists m_R2, (map.putmany m_R1 m_R0).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR2 |].
        exists m_R1, m_R0.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR1 | exact HR0]. }
      pose proof (Fp6_raw_FElem_join pout out0 out1 out2
        (map.putmany m_R2 (map.putmany m_R1 m_R0))
        Hlen_out0 Hlen_out1 Hlen_out2 Hjoin_out) as Hfp6_out.
      (* Join input x Fp2s into Fp6 *)
      assert (Hjoin_px : (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆
         FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x)))
        (map.putmany m_px0 (map.putmany m_px1 m_px2))).
      { exists m_px0, (map.putmany m_px1 m_px2).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx0 |].
        exists m_px1, m_px2.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx1 | exact Hpx2]. }
      pose proof (Fp6_raw_FElem_join px (c0_felem x) (c1_felem x) (c2_felem x)
        (map.putmany m_px0 (map.putmany m_px1 m_px2))
        Hlen_px0 Hlen_px1 Hlen_px2 Hjoin_px) as Hfp6_x.
      rewrite Fp6_list_decomp in Hfp6_x.
      (* Join input y Fp2s into Fp6 *)
      assert (Hjoin_py : (FElem_Fp2 py (c0_felem y) ⋆
        (FElem_Fp2 (word.add py fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add py fp6_c2_offset) (c2_felem y)))
        (map.putmany m_py0 (map.putmany m_py1 m_py2))).
      { exists m_py0, (map.putmany m_py1 m_py2).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy0 |].
        exists m_py1, m_py2.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy1 | exact Hpy2]. }
      pose proof (Fp6_raw_FElem_join py (c0_felem y) (c1_felem y) (c2_felem y)
        (map.putmany m_py0 (map.putmany m_py1 m_py2))
        Hlen_py0 Hlen_py1 Hlen_py2 Hjoin_py) as Hfp6_y.
      rewrite Fp6_list_decomp in Hfp6_y.
      (* Build final sep: FElem pout result * (FElem px x * (FElem py y * Rr)) *)
      exists (map.putmany m_R2 (map.putmany m_R1 m_R0)),
             (map.putmany (map.putmany m_px0 (map.putmany m_px1 m_px2))
               (map.putmany (map.putmany m_py0 (map.putmany m_py1 m_py2)) m_rr')).
      split; [split |].
      { rewrite Heq_S0. rewrite <- !map.putmany_assoc.
        map_swap m_R1 m_R2. map_swap m_R0 m_R2. map_swap m_R0 m_R1.
        reflexivity. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out |].
      exists (map.putmany m_px0 (map.putmany m_px1 m_px2)),
             (map.putmany (map.putmany m_py0 (map.putmany m_py1 m_py2)) m_rr').
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp6_x |].
      exists (map.putmany m_py0 (map.putmany m_py1 m_py2)), m_rr'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp6_y | exact Hrr']. }
  Qed.

  (* Nocopy Fp6_sub: operates directly on inputs, no copies. *)
  Definition Fp6_sub_nocopy : function_t :=
    ((AbstractField.sub (F:=Fp6) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "inx"); expr_fp6_c0 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "inx"); expr_fp6_c1 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "inx"); expr_fp6_c2 (expr.var "iny")])
    ))).

  Lemma Fp6_sub_nocopy_ok :
    forall functions
      (EnvContains : map.get functions (fst Fp6_sub_nocopy) = Some (snd Fp6_sub_nocopy))
      (HFsub1 : spec_of_Fp2_sub functions)
      (HFsub2 : spec_of_Fp2_sub functions)
      (HFsub3 : spec_of_Fp2_sub functions),
    forall pout px py old_out x y Rr tr mem0,
      @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
        (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x ->
      @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
        (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) y ->
      (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst px x ⋆
       (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst py y ⋆
        (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout old_out ⋆ Rr))) mem0 ->
      WeakestPrecondition.call functions (fst Fp6_sub_nocopy) tr mem0 [pout; px; py]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\
           exists result,
             @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst result =
             @AbstractField.Fsub _ Fp6_fp_inst
               (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x)
               (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst y) /\
             @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
               (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) result /\
             (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout result ⋆
              (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst px x ⋆
               (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst py y ⋆ Rr))) mem').
  Proof.
    intros functions EnvContains HFsub1 HFsub2 HFsub3.
    intros pout px py old_out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_sub_nocopy].
    eexists. split. { exact eq_refl. }
    destruct Hsep as [m_x [m_yr [[Heq_m0 Hd_x_yr] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[Heq_yr Hd_y_or] [Hfy Hor]]]].
    destruct Hor as [m_o [m_rr [[Heq_or Hd_o_rr] [Hfo Hrr]]]].
    subst m_yr m_or mem0.
    pose proof (Fp6_raw_FElem_split px x m_x Hfx) as Hx_sep.
    pose proof (Fp6_raw_FElem_split py y m_y Hfy) as Hy_sep.
    pose proof (Fp6_raw_FElem_split pout old_out m_o Hfo) as Ho_sep.
    destruct Hx_sep as [m_x0 [m_x12 [[Heq_x Hd_x0] [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [[Heq_x12 Hd_x12] [Hx1 Hx2]]]]. subst m_x12 m_x.
    destruct Hy_sep as [m_y0 [m_y12 [[Heq_y Hd_y0] [Hy0 Hy12]]]].
    destruct Hy12 as [m_y1 [m_y2 [[Heq_y12 Hd_y12] [Hy1 Hy2]]]]. subst m_y12 m_y.
    destruct Ho_sep as [m_o0 [m_o12 [[Heq_o Hd_o0] [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [[Heq_o12 Hd_o12] [Ho1 Ho2]]]]. subst m_o12 m_o.
    change bounded_by with (fun b ws =>
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem ws) /\
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem ws) /\
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem ws)) in Hbx, Hby.
    cbv beta in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]]. destruct Hby as [Hby0 [Hby1 Hby2]].
    split_all_disjointness. rewrite <- !map.putmany_assoc.
    assert (Hsep_fp2 : (FElem_Fp2 px (c0_felem x) ⋆ (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆ (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆ (FElem_Fp2 py (c0_felem y) ⋆ (FElem_Fp2 (word.add py fp6_c1_offset) (c1_felem y) ⋆ (FElem_Fp2 (word.add py fp6_c2_offset) (c2_felem y) ⋆ (FElem_Fp2 pout (c0_felem old_out) ⋆ (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆ (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out) ⋆ Rr))))))))) (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_y0 (map.putmany m_y1 (map.putmany m_y2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))))))).
    { build_sep. }
    (* === Call 1: Fp2_sub(out.c0, inx.c0, iny.c0) === *)
    exists [pout; px; py]. split.
    { cbv [dexprs list_map expr_fp6_c0 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout px py (c0_felem old_out) (c0_felem x) (c0_felem y) _ tr).
         split; [exact Hbx0 |]. split; [exact Hby0 |].
         split.
         { eexists. exact Hsep_fp2. }
         split.
         { eexists. pose proof Hsep_fp2 as H'. ecancel_assumption. }
         pose proof Hsep_fp2 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1 t1. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 2: Fp2_sub(out.c1, inx.c1, iny.c1) === *)
    exists [word.add pout fp6_c1_offset; word.add px fp6_c1_offset; word.add py fp6_c1_offset]. split.
    { cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout fp6_c1_offset) (word.add px fp6_c1_offset) (word.add py fp6_c1_offset) (c1_felem old_out) (c1_felem x) (c1_felem y) _ tr).
         split; [exact Hbx1 |]. split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1 [Hfeval1 [Hbound1 Hsep2]]]]].
    subst rets2 t2. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 3: Fp2_sub(out.c2, inx.c2, iny.c2) === *)
    exists [word.add pout fp6_c2_offset; word.add px fp6_c2_offset; word.add py fp6_c2_offset]. split.
    { cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 (word.add pout fp6_c2_offset) (word.add px fp6_c2_offset) (word.add py fp6_c2_offset) (c2_felem old_out) (c2_felem x) (c2_felem y) _ tr).
         split; [exact Hbx2 |]. split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out2 [Hfeval2 [Hbound2 Hsep3]]]]].
    subst rets3 t3.
    eexists. split. { exact eq_refl. }
    cbv beta.
    split. { exact eq_refl. } split. { exact eq_refl. }
    (* === Final postcondition === *)
    destruct Hsep3 as [m_R0 [m_S0 [[Heq_S0 Hd_S0] [HR0 HS0]]]].
    destruct HS0 as [m_R1 [m_S1 [[Heq_S1 Hd_S1] [HR1 HS1]]]].
    destruct HS1 as [m_R2 [m_S2 [[Heq_S2 Hd_S2] [HR2 HS2]]]].
    destruct HS2 as [m_px0 [m_T0 [[Heq_T0 Hd_T0] [Hpx0 HT0]]]].
    destruct HT0 as [m_px1 [m_T1 [[Heq_T1 Hd_T1] [Hpx1 HT1]]]].
    destruct HT1 as [m_px2 [m_T2 [[Heq_T2 Hd_T2] [Hpx2 HT2]]]].
    destruct HT2 as [m_py0 [m_T3 [[Heq_T3 Hd_T3] [Hpy0 HT3]]]].
    destruct HT3 as [m_py1 [m_T4 [[Heq_T4 Hd_T4] [Hpy1 HT4]]]].
    destruct HT4 as [m_py2 [m_rr' [[Heq_T5 Hd_T5] [Hpy2 Hrr']]]].
    subst m_S0 m_S1 m_S2 m_T0 m_T1 m_T2 m_T3 m_T4.
    pose proof (Fp2_FElem_length _ _ _ HR0) as Hlen_out2.
    pose proof (Fp2_FElem_length _ _ _ HR1) as Hlen_out1.
    pose proof (Fp2_FElem_length _ _ _ HR2) as Hlen_out0.
    pose proof (Fp2_FElem_length _ _ _ Hpx0) as Hlen_px0.
    pose proof (Fp2_FElem_length _ _ _ Hpx1) as Hlen_px1.
    pose proof (Fp2_FElem_length _ _ _ Hpx2) as Hlen_px2.
    pose proof (Fp2_FElem_length _ _ _ Hpy0) as Hlen_py0.
    pose proof (Fp2_FElem_length _ _ _ Hpy1) as Hlen_py1.
    pose proof (Fp2_FElem_length _ _ _ Hpy2) as Hlen_py2.
    assert (Hc0 : c0_felem (out0 ++ out1 ++ out2) = out0).
    { unfold c0_felem. apply ListUtil.firstn_app_sharp. exact Hlen_out0. }
    assert (Hc1 : c1_felem (out0 ++ out1 ++ out2) = out1).
    { unfold c1_felem.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      apply ListUtil.firstn_app_sharp. exact Hlen_out1. }
    assert (Hc2 : c2_felem (out0 ++ out1 ++ out2) = out2).
    { unfold c2_felem. set (n := Fp2_felem_size) in *.
      change (2 * fp_felem_size)%nat with n.
      rewrite List.app_assoc. rewrite ListUtil.skipn_app_sharp.
      2: { rewrite List.length_app. lia. } reflexivity. }
    exists (out0 ++ out1 ++ out2).
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0, Hc1, Hc2.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0, Hc1, Hc2.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    { split_all_disjointness.
      assert (Hjoin_out : (FElem_Fp2 pout out0 ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1 ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2))
        (map.putmany m_R2 (map.putmany m_R1 m_R0))).
      { exists m_R2, (map.putmany m_R1 m_R0).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR2 |].
        exists m_R1, m_R0.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR1 | exact HR0]. }
      pose proof (Fp6_raw_FElem_join pout out0 out1 out2
        (map.putmany m_R2 (map.putmany m_R1 m_R0))
        Hlen_out0 Hlen_out1 Hlen_out2 Hjoin_out) as Hfp6_out.
      assert (Hjoin_px : (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆
         FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x)))
        (map.putmany m_px0 (map.putmany m_px1 m_px2))).
      { exists m_px0, (map.putmany m_px1 m_px2).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx0 |].
        exists m_px1, m_px2.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx1 | exact Hpx2]. }
      pose proof (Fp6_raw_FElem_join px (c0_felem x) (c1_felem x) (c2_felem x)
        (map.putmany m_px0 (map.putmany m_px1 m_px2))
        Hlen_px0 Hlen_px1 Hlen_px2 Hjoin_px) as Hfp6_x.
      rewrite Fp6_list_decomp in Hfp6_x.
      assert (Hjoin_py : (FElem_Fp2 py (c0_felem y) ⋆
        (FElem_Fp2 (word.add py fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add py fp6_c2_offset) (c2_felem y)))
        (map.putmany m_py0 (map.putmany m_py1 m_py2))).
      { exists m_py0, (map.putmany m_py1 m_py2).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy0 |].
        exists m_py1, m_py2.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy1 | exact Hpy2]. }
      pose proof (Fp6_raw_FElem_join py (c0_felem y) (c1_felem y) (c2_felem y)
        (map.putmany m_py0 (map.putmany m_py1 m_py2))
        Hlen_py0 Hlen_py1 Hlen_py2 Hjoin_py) as Hfp6_y.
      rewrite Fp6_list_decomp in Hfp6_y.
      exists (map.putmany m_R2 (map.putmany m_R1 m_R0)),
             (map.putmany (map.putmany m_px0 (map.putmany m_px1 m_px2))
               (map.putmany (map.putmany m_py0 (map.putmany m_py1 m_py2)) m_rr')).
      split; [split |].
      { rewrite Heq_S0. rewrite <- !map.putmany_assoc.
        map_swap m_R1 m_R2. map_swap m_R0 m_R2. map_swap m_R0 m_R1.
        reflexivity. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out |].
      exists (map.putmany m_px0 (map.putmany m_px1 m_px2)),
             (map.putmany (map.putmany m_py0 (map.putmany m_py1 m_py2)) m_rr').
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp6_x |].
      exists (map.putmany m_py0 (map.putmany m_py1 m_py2)), m_rr'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp6_y | exact Hrr']. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_sub: componentwise subtraction of 3 Fp2 elements            *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_sub : function_t :=
    (AbstractField.sub (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* out.c0 = x.c0 - y.c0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* out.c1 = x.c1 - y.c1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* out.c2 = x.c2 - y.c2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")])
    ))).

  Instance spec_of_Fp6_sub : spec_of (AbstractField.sub (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp6).

  Lemma Fp6_sub_ok : program_logic_goal_for_function! Fp6_sub.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFsub1 HFsub2 HFsub3.
    unfold spec_of_Fp6_sub, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_sub].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_xrx_sY Hd_sX_sY].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_x_sY Hd_rx_sY].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === First Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { subst l0 l.
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ AbstractField.FElem (F:=Fp6) allocy allocy_val) m)
        (eq (map.putmany (map.putmany m_x m_rx) mStackY))
        tr).
      split.
      { exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
        split; [split |].
        { rewrite <- !map.putmany_assoc. f_equal.
          map_swap m_rx mStackX. reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, mStackY.
          split; [split; [reflexivity | exact Hd_rx_sY] |].
          split; [exact Hrx | exact Hallocy]. } }
      { exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
        split; [split |].
        { rewrite map.putmany_assoc.
          let D := fresh "D" in
          assert (D : map.disjoint (map.putmany m_x m_rx) mStackX) by map_disjoint_auto;
          rewrite (map.putmany_comm (map.putmany m_x m_rx) mStackX D); clear D.
          rewrite <- map.putmany_assoc. reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 copy call: y → allocy === *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_xrx_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY'].
    exists [allocy; py]. split.
    { subst l0 l.
      eexists. split. { apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (AbstractField.FElem (F:=Fp6) allocx x ⋆ Ry) m)
        (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
        tr).
      split.
      { rewrite Heq_mem0_y.
        exists (map.putmany m_y mStackY), (map.putmany m_new1 m_ry).
        split; [split |].
        { transitivity (map.putmany m_new1 (map.putmany (map.putmany m_y mStackY) m_ry)).
          { f_equal. apply map.disjoint_putmany_commutes. exact Hd_ry_sY'. }
          transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y mStackY)) m_ry).
          { apply map.putmany_assoc. }
          transitivity (map.putmany (map.putmany m_new1 m_ry) (map.putmany m_y mStackY)).
          { apply map.disjoint_putmany_commutes.
            apply map.disjoint_putmany_l. split; [exact Hd_yry |].
            unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_ry_sY' k v2 v1 H2 H1). }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_y | exact Hd_n1_sY]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_yry k v2 v1 H2 H1). }
            { exact Hd_ry_sY'. } } }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_y k v2 v1 H2 H1). }
            { exact Hd_yry. } }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_sY k v2 v1 H2 H1). }
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_ry_sY' k v2 v1 H2 H1). } } }
        split.
        { exists m_y, mStackY.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfelem_y | exact Hallocy]. }
        { exists m_new1, m_ry.
          split; [split; [reflexivity | exact Hd_n1_ry] |].
          split; [exact Hfelem_allocx | exact Hry]. } }
      { rewrite Heq_mem0_y.
        exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
        split; [split |].
        { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
          { apply map.putmany_assoc. }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_xrx_sY]. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_n1_sY k v2 v1 H2 H1). }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_xrx_sY k v2 v1 H2 H1). } }
        split; [exact Hallocy | exact eq_refl]. } }
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 3: Three Fp2 sub calls === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    pose proof (Fp6_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    pose proof (Fp6_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay12 [Hsp_ay [Hfe_ay0 Hay12]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay0_12].
    destruct Hay12 as [m_ay1 [m_ay2 [Hsp_ay12 [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay12 as [Heq_ay12 Hd_ay12].
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx, Hby.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    destruct Hby as [Hby0 [Hby1 Hby2]].
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    subst m_ax12 m_ay12 m_o12 m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 10-way sep fact *)
    assert (Hsep10 :
      ((FElem_Fp2 allocy (c0_felem y) ⋆
        (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y))) ⋆
       ((FElem_Fp2 allocx (c0_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
          FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x))) ⋆
        ((FElem_Fp2 pout (c0_felem old_out) ⋆
          (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
           FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out))) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 (map.putmany m_ay1 m_ay2))
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)))).
    { exists (map.putmany m_ay0 (map.putmany m_ay1 m_ay2)),
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, (map.putmany m_ay1 m_ay2).
        split; [split; [reflexivity | exact Hd_ay0_12] |].
        split; [exact Hfe_ay0 |].
        exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay12] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === First Fp2 sub call === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout allocx allocy
           (c0_felem old_out) (c0_felem x) (c0_felem y)
           _ tr).
         split; [exact Hbx0 |].
         split; [exact Hby0 |].
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    intros t_sub1 m_sub1 rets_sub1 [Hrets_sub1 [Htr_sub1 [out0' [Hfeval0 [Hbound0 Hsep_sub1]]]]].
    subst rets_sub1 t_sub1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp2 sub call === *)
    exists [word.add pout fp6_c1_offset; word.add allocx fp6_c1_offset;
            word.add allocy fp6_c1_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout fp6_c1_offset)
           (word.add allocx fp6_c1_offset) (word.add allocy fp6_c1_offset)
           (c1_felem old_out) (c1_felem x) (c1_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         pose proof Hsep_sub1 as H'. ecancel_assumption. }
    intros t_sub2 m_sub2 rets_sub2 [Hrets_sub2 [Htr_sub2 [out1' [Hfeval1 [Hbound1 Hsep_sub2]]]]].
    subst rets_sub2 t_sub2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Third Fp2 sub call === *)
    exists [word.add pout fp6_c2_offset; word.add allocx fp6_c2_offset;
            word.add allocy fp6_c2_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 (word.add pout fp6_c2_offset)
           (word.add allocx fp6_c2_offset) (word.add allocy fp6_c2_offset)
           (c2_felem old_out) (c2_felem x) (c2_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_sub2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_sub2 as H'. ecancel_assumption. }
         pose proof Hsep_sub2 as H'. ecancel_assumption. }
    intros t_sub3 m_sub3 rets_sub3 [Hrets_sub3 [Htr_sub3 [out2' [Hfeval2 [Hbound2 Hsep_sub3]]]]].
    subst rets_sub3 t_sub3.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 5: Destructure sep into 10 map components === *)
    destruct Hsep_sub3 as [m_A [m_rest1 [[Heq_sub3 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_J [[Heq_r8 Hd_IJ] [HI HJ]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7 m_rest8 m_sub3.
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    (* === Phase 6: Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp2 allocy (c0_felem y) ⋆
      (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
       FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y)))
      (map.putmany m_D (map.putmany m_E m_FF))).
    { exists m_D, (map.putmany m_E m_FF).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_FF.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HFF]. }
    pose proof (Fp6_raw_FElem_join allocy (c0_felem y) (c1_felem y) (c2_felem y)
      (map.putmany m_D (map.putmany m_E m_FF))
      Hlen_D Hlen_E Hlen_FF Hjoin_y) as Hfp6_y.
    rewrite Fp6_list_decomp in Hfp6_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocy y
      (map.putmany m_D (map.putmany m_E m_FF)) Hfp6_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))))),
      (map.putmany m_D (map.putmany m_E m_FF)).
    split. { exact Hanybytes_y. }
    split. { split.
      { rewrite (map.putmany_assoc m_E m_FF
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_assoc m_D (map.putmany m_E m_FF)
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_comm (map.putmany m_D (map.putmany m_E m_FF))
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 7: Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_G (map.putmany m_HH m_I))).
    { exists m_G, (map.putmany m_HH m_I).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HG |].
      exists m_HH, m_I.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HHH | exact HI]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_G (map.putmany m_HH m_I))
      Hlen_G Hlen_HH Hlen_I Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_G (map.putmany m_HH m_I)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_J))),
      (map.putmany m_G (map.putmany m_HH m_I)).
    split. { exact Hanybytes_x. }
    split. { split.
      { rewrite (map.putmany_assoc m_HH m_I m_J).
        rewrite (map.putmany_assoc m_G (map.putmany m_HH m_I) m_J).
        rewrite (map.putmany_comm (map.putmany m_G (map.putmany m_HH m_I)) m_J).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 8: Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_J.
      split; [split |].
      { rewrite (map.putmany_assoc m_B m_C m_J).
        rewrite (map.putmany_assoc m_A (map.putmany m_B m_C) m_J).
        f_equal.
        rewrite (map.putmany_assoc m_A m_B m_C).
        rewrite (map.putmany_comm m_A m_B). 2: { exact Hd33. }
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HJ]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_neg: componentwise negation                                  *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_opp : function_t :=
    (AbstractField.opp (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* out.c0 = -x.c0 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx")]);
      (* out.c1 = -x.c1 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx")]);
      (* out.c2 = -x.c2 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx")])
    ))).

  Instance spec_of_Fp6_opp : spec_of (AbstractField.opp (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp6).

  Lemma Fp6_opp_ok : program_logic_goal_for_function! Fp6_opp.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFopp1 HFopp2 HFopp3.
    unfold spec_of_Fp6_opp, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_opp].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    (* For copy spec, relate the two preconditions *)
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { subst l.
      eexists. split.
      { rewrite map.get_put_same. exact eq_refl. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence). apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy allocx px allocx_val x
        Rx
        (eq (map.putmany m_x m_rx))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * Rx) *)
        exists (map.putmany m_x mStackX), m_rx.
        split; [split |].
        { rewrite <- !map.putmany_assoc. f_equal.
          rewrite (map.putmany_comm m_rx mStackX Hd_rx_sX).
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { exact Hd_x_rx. }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_rx_sX k v2 v1 H2 H1). } }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exact Hrx. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout) *)
        exists mStackX, (map.putmany m_x m_rx).
        split; [split |].
        { rewrite map.putmany_assoc.
          let D := fresh "D" in
          assert (D : map.disjoint (map.putmany m_x m_rx) mStackX) by map_disjoint_auto;
          rewrite (map.putmany_comm (map.putmany m_x m_rx) mStackX D); clear D.
          rewrite <- map.putmany_assoc. reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Decompose copy postcondition *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp6 FElems into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split allocx x m_new Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    (* Split output FElem *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Derive Heq_xr: m_x ++ m_rx = m_out ++ m_rr *)
    assert (Heq_xr : map.putmany m_x m_rx = map.putmany m_out m_rr)
      by exact Heq_m0_out.
    (* Subst decomposed maps *)
    subst m_ax12 m_o12 m_out m_new.
    rewrite Heq_xr in Hd_n_f.
    (* Build 7-way sep fact *)
    assert (Hsep7 :
      ((FElem_Fp2 allocx (c0_felem x) ⋆
        (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
         FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x))) ⋆
       ((FElem_Fp2 pout (c0_felem old_out) ⋆
         (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
          FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out))) ⋆ Rr))
      (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr))).
    { exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n_f] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === First Fp2 opp call: opp(out.c0, allocx.c0) === *)
    exists [pout; allocx]. split.
    1: { subst l.
         cbv [dexprs list_map expr_fp6_c0 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { rewrite map.get_put_diff by (cbv; congruence).
           rewrite map.get_put_diff by (cbv; congruence).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp1 pout allocx
           (c0_felem old_out) (c0_felem x)
           _ tr).
         split; [exact Hbx0 |].
         rewrite Heq_m0_out.
         split.
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    (* Process first Fp2 opp postcondition *)
    intros t_opp1 m_opp1 rets_opp1 [Hrets_opp1 [Htr_opp1 [out0' [Hfeval0 [Hbound0 Hsep_opp1]]]]].
    subst rets_opp1 t_opp1.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp2 opp call: opp(out.c1, allocx.c1) === *)
    exists [word.add pout fp6_c1_offset; word.add allocx fp6_c1_offset].
    split.
    1: { subst l.
         cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { rewrite map.get_put_diff by (cbv; congruence).
           rewrite map.get_put_diff by (cbv; congruence).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp2 (word.add pout fp6_c1_offset)
           (word.add allocx fp6_c1_offset)
           (c1_felem old_out) (c1_felem x)
           _ tr).
         split; [exact Hbx1 |].
         split.
         { eexists. pose proof Hsep_opp1 as H'. ecancel_assumption. }
         pose proof Hsep_opp1 as H'. ecancel_assumption. }
    (* Process second Fp2 opp postcondition *)
    intros t_opp2 m_opp2 rets_opp2 [Hrets_opp2 [Htr_opp2 [out1' [Hfeval1 [Hbound1 Hsep_opp2]]]]].
    subst rets_opp2 t_opp2.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Third Fp2 opp call: opp(out.c2, allocx.c2) === *)
    exists [word.add pout fp6_c2_offset; word.add allocx fp6_c2_offset].
    split.
    1: { subst l.
         cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { rewrite map.get_put_diff by (cbv; congruence).
           rewrite map.get_put_diff by (cbv; congruence).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp3 (word.add pout fp6_c2_offset)
           (word.add allocx fp6_c2_offset)
           (c2_felem old_out) (c2_felem x)
           _ tr).
         split; [exact Hbx2 |].
         split.
         { eexists. pose proof Hsep_opp2 as H'. ecancel_assumption. }
         pose proof Hsep_opp2 as H'. ecancel_assumption. }
    (* Process third Fp2 opp postcondition *)
    intros t_opp3 m_opp3 rets_opp3 [Hrets_opp3 [Htr_opp3 [out2' [Hfeval2 [Hbound2 Hsep_opp3]]]]].
    subst rets_opp3 t_opp3.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure Hsep_opp3 into map components === *)
    destruct Hsep_opp3 as [m_A [m_rest1 [[Heq_opp3 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_G [[Heq_r5 Hd_FG] [HF HG]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_opp3.
    (* Derive pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HF) as Hlen_F.
    (* === Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_D (map.putmany m_E m_F))).
    { exists m_D, (map.putmany m_E m_F).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_F.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HF]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_D (map.putmany m_E m_F))
      Hlen_D Hlen_E Hlen_F Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_D (map.putmany m_E m_F)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    (* Provide witnesses for allocx deallocation *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_G))),
      (map.putmany m_D (map.putmany m_E m_F)).
    split. { exact Hanybytes_x. }
    split. { split.
      { rewrite (map.putmany_assoc m_E m_F m_G).
        rewrite (map.putmany_assoc m_D (map.putmany m_E m_F) m_G).
        rewrite (map.putmany_comm (map.putmany m_D (map.putmany m_E m_F)) m_G).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0, Hfeval1, Hfeval2.
      unfold AbstractField.Fopp; simpl.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta.
      unfold BLS12Fp6Spec.fp6_neg, BLS12Fp6Spec.fp6_build,
             BLS12Fp6Spec.fp6_c0, BLS12Fp6Spec.fp6_c1, BLS12Fp6Spec.fp6_c2.
      cbv beta.
      unfold AbstractField.Fopp; simpl.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    (* sep *)
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_G.
      split; [split |].
      { rewrite (map.putmany_assoc m_B m_C m_G).
        rewrite (map.putmany_assoc m_A (map.putmany m_B m_C) m_G).
        f_equal.
        rewrite (map.putmany_assoc m_A m_B m_C).
        rewrite (map.putmany_comm m_A m_B). 2: { map_disjoint_auto. }
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HG]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_mul: Karatsuba-like multiplication                           *)
  (*                                                                  *)
  (* a0b0 = a.c0 * b.c0                                              *)
  (* a1b1 = a.c1 * b.c1                                              *)
  (* a2b2 = a.c2 * b.c2                                              *)
  (* t0 = (a.c1 + a.c2)(b.c1 + b.c2) - a1b1 - a2b2                 *)
  (* out.c0 = a0b0 + xi * t0                                         *)
  (* t1 = (a.c0 + a.c1)(b.c0 + b.c1) - a0b0 - a1b1                 *)
  (* out.c1 = t1 + xi * a2b2                                         *)
  (* t2 = (a.c0 + a.c2)(b.c0 + b.c2) - a0b0 - a2b2                 *)
  (* out.c2 = t2 + a1b1                                              *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_mul : function_t :=
    (AbstractField.mul (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a0b0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a1b1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a2b2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as u;
      (* Copy inputs to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* a0b0 = a.c0 * b.c0 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a0b0"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* a1b1 = a.c1 * b.c1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a1b1"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* a2b2 = a.c2 * b.c2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a2b2"; expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")]);
      (* --- c0 = a0b0 + xi * ((a1+a2)(b1+b2) - a1b1 - a2b2) --- *)
      (* t = a.c1 + a.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      (* u = b.c1 + b.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c1 (expr.var "allocy"); expr_fp6_c2 (expr.var "allocy")]);
      (* t = t * u = (a1+a2)(b1+b2) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a1b1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a1b1"]);
      (* t = t - a2b2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a2b2"]);
      (* t = xi * t *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "t"]);
      (* out.c0 = a0b0 + xi*t0 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "a0b0"; expr.var "t"]);
      (* --- c1 = (a0+a1)(b0+b1) - a0b0 - a1b1 + xi*(a2b2) --- *)
      (* t = a.c0 + a.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      (* u = b.c0 + b.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c0 (expr.var "allocy"); expr_fp6_c1 (expr.var "allocy")]);
      (* t = t * u = (a0+a1)(b0+b1) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a0b0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a0b0"]);
      (* t = t - a1b1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a1b1"]);
      (* u = xi * a2b2 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "u"; expr.var "a2b2"]);
      (* out.c1 = t + xi*a2b2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "t"; expr.var "u"]);
      (* --- c2 = (a0+a2)(b0+b2) - a0b0 - a2b2 + a1b1 --- *)
      (* t = a.c0 + a.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      (* u = b.c0 + b.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c0 (expr.var "allocy"); expr_fp6_c2 (expr.var "allocy")]);
      (* t = t * u = (a0+a2)(b0+b2) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a0b0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a0b0"]);
      (* t = t - a2b2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a2b2"]);
      (* out.c2 = t + a1b1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "t"; expr.var "a1b1"])
    ))).

  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp6).

  Lemma Fp6_mul_ok : program_logic_goal_for_function! Fp6_mul.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2
      HFmul1 HFmul2 HFmul3 HFadd1 HFadd2 HFmul4 HFsub1 HFsub2 HFmulxi1 HFadd3
      HFadd4 HFadd5 HFmul5 HFsub3 HFsub4 HFmulxi2 HFadd6
      HFadd7 HFadd8 HFmul6 HFsub5 HFsub6 HFadd9.
    unfold spec_of_Fp6_mul, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_mul].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === 7 Stackallocs === *)
    split. { apply Z_mod_mult. }
    intros allocx mStack_ax m1 Hstack_ax Hm1.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros allocy mStack_ay m2 Hstack_ay Hm2.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a0b0_ptr mStack_a0b0 m3 Hstack_a0b0 Hm3.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a1b1_ptr mStack_a1b1 m4 Hstack_a1b1 Hm4.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a2b2_ptr mStack_a2b2 m5 Hstack_a2b2 Hm5.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros t_ptr mStack_t m6 Hstack_t Hm6.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros u_ptr mStack_u m7 Hstack_u Hm7.
    (* === FElem_from_bytes === *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfb_ax.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocy) as Hfb_ay.
    unfold AbstractField.Placeholder in Hfb_ax, Hfb_ay.
    pose proof (proj1 (Hfb_ax mStack_ax) Hstack_ax) as [allocx_val Hallocx]. clear Hfb_ax.
    pose proof (proj1 (Hfb_ay mStack_ay) Hstack_ay) as [allocy_val Hallocy]. clear Hfb_ay.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok a0b0_ptr) as Hfb1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok a1b1_ptr) as Hfb2.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok a2b2_ptr) as Hfb3.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok t_ptr) as Hfb4.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok u_ptr) as Hfb5.
    unfold AbstractField.Placeholder in Hfb1, Hfb2, Hfb3, Hfb4, Hfb5.
    pose proof (proj1 (Hfb1 mStack_a0b0) Hstack_a0b0) as [a0b0_val Ha0b0_fe]. clear Hfb1.
    pose proof (proj1 (Hfb2 mStack_a1b1) Hstack_a1b1) as [a1b1_val Ha1b1_fe]. clear Hfb2.
    pose proof (proj1 (Hfb3 mStack_a2b2) Hstack_a2b2) as [a2b2_val Ha2b2_fe]. clear Hfb3.
    pose proof (proj1 (Hfb4 mStack_t) Hstack_t) as [t_val Ht_fe]. clear Hfb4.
    pose proof (proj1 (Hfb5 mStack_u) Hstack_u) as [u_val Hu_fe]. clear Hfb5.
    (* === Decompose memory === *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfy Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    destruct Hm3 as [Heq_m3 Hd_m3]. subst m3.
    destruct Hm4 as [Heq_m4 Hd_m4]. subst m4.
    destruct Hm5 as [Heq_m5 Hd_m5]. subst m5.
    destruct Hm6 as [Heq_m6 Hd_m6]. subst m6.
    destruct Hm7 as [Heq_m7 Hd_m7]. subst m7.
    split_all_disjointness.
    (* === First Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ (AbstractField.FElem (F:=Fp6) allocy allocy_val ⋆
                   (FElem_Fp2 a0b0_ptr a0b0_val ⋆ (FElem_Fp2 a1b1_ptr a1b1_val ⋆
                   (FElem_Fp2 a2b2_ptr a2b2_val ⋆ (FElem_Fp2 t_ptr t_val ⋆
                   FElem_Fp2 u_ptr u_val)))))) m)
        (eq (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_ay (map.putmany mStack_a0b0
                 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
                   (map.putmany mStack_t mStack_u)))))))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * R1) *)
        exists (map.putmany m_x mStack_ax),
               (map.putmany m_rx (map.putmany mStack_ay (map.putmany mStack_a0b0
                 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
                   (map.putmany mStack_t mStack_u)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStack_ax.
          split; [split; [reflexivity | exact Hd27] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, (map.putmany mStack_ay (map.putmany mStack_a0b0
            (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t mStack_u))))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hrx |].
          exists mStack_ay, (map.putmany mStack_a0b0
            (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t mStack_u)))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hallocy |].
          exists mStack_a0b0, (map.putmany mStack_a1b1
            (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha0b0_fe |].
          exists mStack_a1b1, (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha1b1_fe |].
          exists mStack_a2b2, (map.putmany mStack_t mStack_u).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha2b2_fe |].
          exists mStack_t, mStack_u.
          split; [split; [reflexivity | exact Hd0] |].
          split; [exact Ht_fe | exact Hu_fe]. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout1) *)
        exists mStack_ax, (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_ay (map.putmany mStack_a0b0
                 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
                   (map.putmany mStack_t mStack_u)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process first copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 copy call: y → allocy === *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    (* Decompose Hmemy *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_stacks].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_stacks) as [Hd_n1_sY Hd_n1_rest1].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest1) as [Hd_n1_s0 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_s1 Hd_n1_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest3) as [Hd_n1_s2 Hd_n1_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest4) as [Hd_n1_st Hd_n1_su].
    clear Hd_n1_stacks Hd_n1_rest1 Hd_n1_rest2 Hd_n1_rest3 Hd_n1_rest4.
    rewrite Heq_mem0_y in *.
    (* Derive disjointness for allocy copy *)
    assert (Hd_xrx_sY : map.disjoint (map.putmany m_y m_ry) mStack_ay).
    { rewrite <- Heq_mem0_y. map_disjoint_auto. }
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY].
    (* Derive disjointness for m_y/m_ry against stack maps *)
    assert (Hd_yr_stacks : map.disjoint (map.putmany m_y m_ry)
      (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
        (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u))))).
    { rewrite <- Heq_mem0_y. map_disjoint_auto. }
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_yr_stacks) as [Hd_y_stacks Hd_ry_stacks].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_y_stacks) as [Hd_y_s0 Hd_y_rest1].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_y_rest1) as [Hd_y_s1 Hd_y_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_y_rest2) as [Hd_y_s2 Hd_y_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_y_rest3) as [Hd_y_st Hd_y_su].
    clear Hd_y_rest1 Hd_y_rest2 Hd_y_rest3.
    exists [allocy; py]. split.
    { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (AbstractField.FElem (F:=Fp6) allocx x ⋆ (Ry ⋆
                   (FElem_Fp2 a0b0_ptr a0b0_val ⋆ (FElem_Fp2 a1b1_ptr a1b1_val ⋆
                   (FElem_Fp2 a2b2_ptr a2b2_val ⋆ (FElem_Fp2 t_ptr t_val ⋆
                   FElem_Fp2 u_ptr u_val)))))) m)
        (eq (map.putmany m_new1 (map.putmany (map.putmany m_y m_ry)
              (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
                (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)))))))
        tr).
      split.
      { (* Precondition 1: ((FElem py y ⋆ FElem allocy allocy_val) ⋆ R) total_mem *)
        (* ⋆ is left-assoc: first witness = combined FElems, second = frame R *)
        exists (map.putmany m_y mStack_ay),
               (map.putmany m_new1 (map.putmany m_ry
                 (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
                   (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { (* (FElem py y ⋆ FElem allocy allocy_val) (putmany m_y mStack_ay) *)
          exists m_y, mStack_ay.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfy | exact Hallocy]. }
        { (* R_big: (FElem allocx x ⋆ (Ry ⋆ stacks)) rest *)
          exists m_new1, (map.putmany m_ry
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
              (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u))))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hfelem_allocx |].
          exists m_ry, (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
            (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)))).
          split; [split; [reflexivity | exact Hd_ry_stacks] |].
          split; [exact Hry |].
          exists mStack_a0b0, (map.putmany mStack_a1b1
            (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha0b0_fe |].
          exists mStack_a1b1, (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha1b1_fe |].
          exists mStack_a2b2, (map.putmany mStack_t mStack_u).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ha2b2_fe |].
          exists mStack_t, mStack_u.
          split; [split; [reflexivity | exact Hd0] |].
          split; [exact Ht_fe | exact Hu_fe]. } }
      { (* Precondition 2: (FElem allocy allocy_val ⋆ Rout) total_mem *)
        exists mStack_ay, (map.putmany m_new1 (map.putmany (map.putmany m_y m_ry)
          (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
            (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocy | exact eq_refl]. } }
    (* Process second copy postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 3: Split Fp6 FElems and set up big sep for operations === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp6 FElems into 3 Fp2 components each *)
    pose proof (Fp6_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    pose proof (Fp6_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay12 [Hsp_ay [Hfe_ay0 Hay12]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay0_12].
    destruct Hay12 as [m_ay1 [m_ay2 [Hsp_ay12 [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay12 as [Heq_ay12 Hd_ay12].
    (* Split output FElem *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx, Hby.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    destruct Hby as [Hby0 [Hby1 Hby2]].
    (* Subst decomposed maps *)
    subst m_ax12 m_ay12 m_o12 m_out m_new1 m_new2.
    (* Derive Heq_yr: m_y ++ m_ry = m_out ++ m_rr *)
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)
      by exact Heq_m0_out.
    (* Derive disjointness for n2 against output components *)
    rewrite Heq_yr in Hd_n2_f2.
    (* Hd_n2_f2 is now: disjoint n2 (ax_all ∪ (out_rr ∪ stacks)) *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_f2) as [Hd_n2_ax Hd_n2_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest) as [Hd_n2_outrr Hd_n2_stacks].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_outrr) as [Hd_n2_outAll Hd_n2_rr].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_outAll) as [Hd_n2_o0 Hd_n2_o12All].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_o12All) as [Hd_n2_o1 Hd_n2_o2].
    clear Hd_n2_o12All Hd_n2_rest.
    (* Derive disjointness for n1 against output components *)
    assert (Hd_n1_mem0_out : map.disjoint (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
      (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
    { rewrite <- Heq_yr. rewrite <- Heq_mem0_y.
      apply map.disjoint_putmany_r. split; [exact Hd_n1_x | exact Hd_n1_rx]. }
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0_out) as [Hd_n1_outAll Hd_n1_rr].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_outAll) as [Hd_n1_o0 Hd_n1_o12All].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_o12All) as [Hd_n1_o1 Hd_n1_o2].
    clear Hd_n1_o12All.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_out_rr) as [Hd_o0_rr Hd_o12_rr].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_o12_rr) as [Hd_o1_rr Hd_o2_rr].
    split_all_disjointness.
    (* Disjointness for Fp2 stacks against output components *)
    assert (Hd_stacks_outAll : map.disjoint
      (map.putmany mStack_a0b0 (map.putmany mStack_a1b1
        (map.putmany mStack_a2b2 (map.putmany mStack_t mStack_u))))
      (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
    { rewrite <- Heq_yr. rewrite <- Heq_mem0_y. map_disjoint_auto. }
    split_all_disjointness.
    (* Rewrite m'' using output decomposition *)
    subst m''.
    rewrite Heq_yr.
    (* Right-associate memory for easier decomposition *)
    rewrite <- !map.putmany_assoc.
    (* Move m_rr past all stack maps to the end (Rr should be rightmost in sep) *)
    rewrite (map.putmany_assoc m_rr mStack_a0b0).
    rewrite (map.putmany_comm m_rr mStack_a0b0) by map_disjoint_auto.
    rewrite <- (map.putmany_assoc mStack_a0b0 m_rr).
    rewrite (map.putmany_assoc m_rr mStack_a1b1).
    rewrite (map.putmany_comm m_rr mStack_a1b1) by map_disjoint_auto.
    rewrite <- (map.putmany_assoc mStack_a1b1 m_rr).
    rewrite (map.putmany_assoc m_rr mStack_a2b2).
    rewrite (map.putmany_comm m_rr mStack_a2b2) by map_disjoint_auto.
    rewrite <- (map.putmany_assoc mStack_a2b2 m_rr).
    rewrite (map.putmany_assoc m_rr mStack_t).
    rewrite (map.putmany_comm m_rr mStack_t) by map_disjoint_auto.
    rewrite <- (map.putmany_assoc mStack_t m_rr).
    rewrite (map.putmany_comm m_rr mStack_u) by map_disjoint_auto.
    (* Build big sep fact: 14 Fp2 regions + Rr *)
    assert (Hsep14 :
      ((FElem_Fp2 allocy (c0_felem y) ⋆
        (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
         (FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y) ⋆
          (FElem_Fp2 allocx (c0_felem x) ⋆
           (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
            (FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x) ⋆
             (FElem_Fp2 pout (c0_felem old_out) ⋆
              (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
               (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out) ⋆
                (FElem_Fp2 a0b0_ptr a0b0_val ⋆
                 (FElem_Fp2 a1b1_ptr a1b1_val ⋆
                  (FElem_Fp2 a2b2_ptr a2b2_val ⋆
                   (FElem_Fp2 t_ptr t_val ⋆
                    (FElem_Fp2 u_ptr u_val ⋆ Rr))))))))))))))
      (map.putmany m_ay0 (map.putmany m_ay1 (map.putmany m_ay2
        (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))))))))))))))).
    { exists m_ay0, (map.putmany m_ay1 (map.putmany m_ay2
        (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))))))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ay0 |].
      exists m_ay1, (map.putmany m_ay2
        (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ay1 |].
      exists m_ay2, (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ay2 |].
      exists m_ax0, (map.putmany m_ax1 (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_ax2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax1 |].
      exists m_ax2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o0 |].
      exists m_o1, (map.putmany m_o2
            (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o1 |].
      exists m_o2, (map.putmany mStack_a0b0 (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o2 |].
      exists mStack_a0b0, (map.putmany mStack_a1b1 (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha0b0_fe |].
      exists mStack_a1b1, (map.putmany mStack_a2b2
              (map.putmany mStack_t (map.putmany mStack_u m_rr))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha1b1_fe |].
      exists mStack_a2b2, (map.putmany mStack_t (map.putmany mStack_u m_rr)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha2b2_fe |].
      exists mStack_t, (map.putmany mStack_u m_rr).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht_fe |].
      exists mStack_u, m_rr.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hu_fe | exact Hrr_out]. }
    (* Change Fp6 bounded_by to Fp2 bounded_by — needed for bounds on allocx/allocy components *)
    change bin_xbounds with (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) in Hbx0, Hbx1, Hbx2.
    change (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) in Hbx0, Hbx1, Hbx2.
    change bin_ybounds with (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) in Hby0, Hby1, Hby2.
    change (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) in Hby0, Hby1, Hby2.
    (* Lift bounds_equiv from Fp level to Fp2 level *)
    assert (Fp2_bounds_equiv : forall z,
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
        (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) z ->
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
        (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) z).
    { intro z.
      cbv [AbstractField.bounded_by AbstractField.loose_bounds AbstractField.tight_bounds
           Fp2_repr_inst Fp2_field_representation].
      intros [H1 H2]. split; apply bounds_equiv; assumption. }
    (* === Phase 4: 23 Fp2 operation calls === *)
    (* Each call: dexprs, weaken_call with bounds + ecancel, destructure postcondition *)
    (* Call 1: a0b0 = mul(allocx.c0, allocy.c0) *)
    exists [a0b0_ptr; allocx; allocy]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 a0b0_ptr allocx allocy
           a0b0_val (c0_felem x) (c0_felem y) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         pose proof Hsep14 as H'. ecancel_assumption. }
    intros t1 m1' rets1 [Hrets1 [Htr1 [a0b0' [Hfeval_a0b0 [Hbound_a0b0 Hsep1]]]]].
    subst rets1 t1.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: a1b1 = mul(allocx.c1, allocy.c1) *)
    exists [a1b1_ptr; word.add allocx fp6_c1_offset; word.add allocy fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 a1b1_ptr (word.add allocx fp6_c1_offset) (word.add allocy fp6_c1_offset)
           a1b1_val (c1_felem x) (c1_felem y) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2' rets2' [Hrets2' [Htr2' [a1b1' [Hfeval_a1b1 [Hbound_a1b1 Hsep2]]]]].
    subst rets2' t2.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: a2b2 = mul(allocx.c2, allocy.c2) *)
    exists [a2b2_ptr; word.add allocx fp6_c2_offset; word.add allocy fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul3 a2b2_ptr (word.add allocx fp6_c2_offset) (word.add allocy fp6_c2_offset)
           a2b2_val (c2_felem x) (c2_felem y) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3' rets3 [Hrets3 [Htr3 [a2b2' [Hfeval_a2b2 [Hbound_a2b2 Hsep3]]]]].
    subst rets3 t3.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 4: t = add(allocx.c1, allocx.c2) *)
    exists [t_ptr; word.add allocx fp6_c1_offset; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 t_ptr (word.add allocx fp6_c1_offset) (word.add allocx fp6_c2_offset)
           t_val (c1_felem x) (c2_felem x) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4 m4' rets4 [Hrets4 [Htr4 [t1' [Hfeval_t1 [Hbound_t1 Hsep4]]]]].
    subst rets4 t4.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 5: u = add(allocy.c1, allocy.c2) *)
    exists [u_ptr; word.add allocy fp6_c1_offset; word.add allocy fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 u_ptr (word.add allocy fp6_c1_offset) (word.add allocy fp6_c2_offset)
           u_val (c1_felem y) (c2_felem y) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep4 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep4 as H'. ecancel_assumption. }
         pose proof Hsep4 as H'. ecancel_assumption. }
    intros t5 m5' rets5 [Hrets5 [Htr5 [u1' [Hfeval_u1 [Hbound_u1 Hsep5]]]]].
    subst rets5 t5.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 6: t = mul(t, u) *)
    exists [t_ptr; t_ptr; u_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul4 t_ptr t_ptr u_ptr
           t1' t1' u1' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep5 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep5 as H'. ecancel_assumption. }
         pose proof Hsep5 as H'. ecancel_assumption. }
    intros t6 m6' rets6 [Hrets6 [Htr6 [t2' [Hfeval_t2 [Hbound_t2 Hsep6]]]]].
    subst rets6 t6.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 7: t = sub(t, a1b1) *)
    exists [t_ptr; t_ptr; a1b1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 t_ptr t_ptr a1b1_ptr
           t2' t2' a1b1' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         pose proof Hsep6 as H'. ecancel_assumption. }
    intros t7 m7' rets7 [Hrets7 [Htr7 [t3' [Hfeval_t3 [Hbound_t3 Hsep7]]]]].
    subst rets7 t7.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 8: t = sub(t, a2b2) *)
    exists [t_ptr; t_ptr; a2b2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 t_ptr t_ptr a2b2_ptr
           t3' t3' a2b2' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    intros t8 m8' rets8 [Hrets8 [Htr8 [t4' [Hfeval_t4 [Hbound_t4 Hsep8]]]]].
    subst rets8 t8.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 9: t = mul_xi(t) — unop *)
    exists [t_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi1 t_ptr t_ptr
           t4' t4' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep8 as H'. ecancel_assumption. }
         pose proof Hsep8 as H'. ecancel_assumption. }
    intros t9 m9' rets9 [Hrets9 [Htr9 [t5' [Hfeval_t5 [Hbound_t5 Hsep9]]]]].
    subst rets9 t9.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 10: out.c0 = add(a0b0, t) *)
    exists [pout; a0b0_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 pout a0b0_ptr t_ptr
           (c0_felem old_out) a0b0' t5' _ tr).
         split; [solve_bounds |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep9 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep9 as H'. ecancel_assumption. }
         pose proof Hsep9 as H'. ecancel_assumption. }
    intros t10 m10' rets10 [Hrets10 [Htr10 [out0' [Hfeval_out0 [Hbound_out0 Hsep10]]]]].
    subst rets10 t10.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 11: t = add(allocx.c0, allocx.c1) *)
    exists [t_ptr; allocx; word.add allocx fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd4 t_ptr allocx (word.add allocx fp6_c1_offset)
           t5' (c0_felem x) (c1_felem x) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    intros t11 m11' rets11 [Hrets11 [Htr11 [t6' [Hfeval_t6 [Hbound_t6 Hsep11]]]]].
    subst rets11 t11.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 12: u = add(allocy.c0, allocy.c1) *)
    exists [u_ptr; allocy; word.add allocy fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd5 u_ptr allocy (word.add allocy fp6_c1_offset)
           u1' (c0_felem y) (c1_felem y) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep11 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep11 as H'. ecancel_assumption. }
         pose proof Hsep11 as H'. ecancel_assumption. }
    intros t12 m12' rets12 [Hrets12 [Htr12 [u2' [Hfeval_u2 [Hbound_u2 Hsep12]]]]].
    subst rets12 t12.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 13: t = mul(t, u) *)
    exists [t_ptr; t_ptr; u_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul5 t_ptr t_ptr u_ptr
           t6' t6' u2' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep12 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep12 as H'. ecancel_assumption. }
         pose proof Hsep12 as H'. ecancel_assumption. }
    intros t13 m13' rets13 [Hrets13 [Htr13 [t7' [Hfeval_t7 [Hbound_t7 Hsep13]]]]].
    subst rets13 t13.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 14: t = sub(t, a0b0) *)
    exists [t_ptr; t_ptr; a0b0_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 t_ptr t_ptr a0b0_ptr
           t7' t7' a0b0' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep13 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep13 as H'. ecancel_assumption. }
         pose proof Hsep13 as H'. ecancel_assumption. }
    intros t14 m14' rets14 [Hrets14 [Htr14 [t8' [Hfeval_t8 [Hbound_t8 Hsep14']]]]].
    subst rets14 t14.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 15: t = sub(t, a1b1) *)
    exists [t_ptr; t_ptr; a1b1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub4 t_ptr t_ptr a1b1_ptr
           t8' t8' a1b1' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep14' as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep14' as H'. ecancel_assumption. }
         pose proof Hsep14' as H'. ecancel_assumption. }
    intros t15 m15' rets15 [Hrets15 [Htr15 [t9' [Hfeval_t9 [Hbound_t9 Hsep15]]]]].
    subst rets15 t15.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 16: u = mul_xi(a2b2) — unop *)
    exists [u_ptr; a2b2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi2 u_ptr a2b2_ptr
           u2' a2b2' _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep15 as H'. ecancel_assumption. }
         pose proof Hsep15 as H'. ecancel_assumption. }
    intros t16 m16' rets16 [Hrets16 [Htr16 [u3' [Hfeval_u3 [Hbound_u3 Hsep16]]]]].
    subst rets16 t16.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 17: out.c1 = add(t, u) *)
    exists [word.add pout fp6_c1_offset; t_ptr; u_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd6 (word.add pout fp6_c1_offset) t_ptr u_ptr
           (c1_felem old_out) t9' u3' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         pose proof Hsep16 as H'. ecancel_assumption. }
    intros t17 m17' rets17 [Hrets17 [Htr17 [out1' [Hfeval_out1 [Hbound_out1 Hsep17]]]]].
    subst rets17 t17.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 18: t = add(allocx.c0, allocx.c2) *)
    exists [t_ptr; allocx; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd7 t_ptr allocx (word.add allocx fp6_c2_offset)
           t9' (c0_felem x) (c2_felem x) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep17 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep17 as H'. ecancel_assumption. }
         pose proof Hsep17 as H'. ecancel_assumption. }
    intros t18 m18' rets18 [Hrets18 [Htr18 [t10' [Hfeval_t10 [Hbound_t10 Hsep18]]]]].
    subst rets18 t18.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 19: u = add(allocy.c0, allocy.c2) *)
    exists [u_ptr; allocy; word.add allocy fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd8 u_ptr allocy (word.add allocy fp6_c2_offset)
           u3' (c0_felem y) (c2_felem y) _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [apply Fp2_bounds_equiv; assumption |].
         split. { eexists. pose proof Hsep18 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep18 as H'. ecancel_assumption. }
         pose proof Hsep18 as H'. ecancel_assumption. }
    intros t19 m19' rets19 [Hrets19 [Htr19 [u4' [Hfeval_u4 [Hbound_u4 Hsep19]]]]].
    subst rets19 t19.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 20: t = mul(t, u) *)
    exists [t_ptr; t_ptr; u_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul6 t_ptr t_ptr u_ptr
           t10' t10' u4' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep19 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep19 as H'. ecancel_assumption. }
         pose proof Hsep19 as H'. ecancel_assumption. }
    intros t20 m20' rets20 [Hrets20 [Htr20 [t11' [Hfeval_t11 [Hbound_t11 Hsep20]]]]].
    subst rets20 t20.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 21: t = sub(t, a0b0) *)
    exists [t_ptr; t_ptr; a0b0_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub5 t_ptr t_ptr a0b0_ptr
           t11' t11' a0b0' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep20 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep20 as H'. ecancel_assumption. }
         pose proof Hsep20 as H'. ecancel_assumption. }
    intros t21 m21' rets21 [Hrets21 [Htr21 [t12' [Hfeval_t12 [Hbound_t12 Hsep21]]]]].
    subst rets21 t21.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 22: t = sub(t, a2b2) *)
    exists [t_ptr; t_ptr; a2b2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub6 t_ptr t_ptr a2b2_ptr
           t12' t12' a2b2' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep21 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep21 as H'. ecancel_assumption. }
         pose proof Hsep21 as H'. ecancel_assumption. }
    intros t22 m22' rets22 [Hrets22 [Htr22 [t13' [Hfeval_t13 [Hbound_t13 Hsep22]]]]].
    subst rets22 t22.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 23: out.c2 = add(t, a1b1) *)
    exists [word.add pout fp6_c2_offset; t_ptr; a1b1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd9 (word.add pout fp6_c2_offset) t_ptr a1b1_ptr
           (c2_felem old_out) t13' a1b1' _ tr).
         split; [apply Fp2_bounds_equiv; assumption |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep22 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep22 as H'. ecancel_assumption. }
         pose proof Hsep22 as H'. ecancel_assumption. }
    intros t23 m23' rets23 [Hrets23 [Htr23 [out2' [Hfeval_out2 [Hbound_out2 Hsep23]]]]].
    subst rets23 t23.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 5: Destructure final sep and stack deallocation === *)
    (* Destructure Hsep23 into 14 map components *)
    destruct Hsep23 as [m_A [m_rest1 [[Heq_final Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_rest9 [[Heq_r8 Hd_I] [HI Hrest9]]]].
    destruct Hrest9 as [m_J [m_rest10 [[Heq_r9 Hd_J] [HJ Hrest10]]]].
    destruct Hrest10 as [m_K [m_rest11 [[Heq_r10 Hd_K] [HK Hrest11]]]].
    destruct Hrest11 as [m_L [m_rest12 [[Heq_r11 Hd_L] [HL Hrest12]]]].
    destruct Hrest12 as [m_M [m_rest13 [[Heq_r12 Hd_M] [HM Hrest13]]]].
    destruct Hrest13 as [m_N [m_P [[Heq_r13 Hd_NP] [HN HP]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7
          m_rest8 m_rest9 m_rest10 m_rest11 m_rest12 m_rest13 m23'.
    (* Derive all pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    pose proof (Fp2_FElem_length _ _ _ HJ) as Hlen_J.
    pose proof (Fp2_FElem_length _ _ _ HK) as Hlen_K.
    pose proof (Fp2_FElem_length _ _ _ HL) as Hlen_L.
    pose proof (Fp2_FElem_length _ _ _ HM) as Hlen_M.
    pose proof (Fp2_FElem_length _ _ _ HN) as Hlen_N.
    (* === Stack deallocation: u (Fp2) === *)
    (* Actual Hsep23 order after ecancel_assumption through 23 calls:
       m_A=out2'@pout.c2, m_B=t13'@t, m_C=u4'@u,
       m_D=out1'@pout.c1, m_E=out0'@pout.c0,
       m_FF=a2b2', m_G=a1b1', m_HH=a0b0',
       m_I=y0, m_J=y1, m_K=y2, m_L=x0, m_M=x1, m_N=x2, m_P=Rr *)
    assert (Hbytes_u : Memory.anybytes u_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_C).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst u_ptr u4' m_C HC). }
    (* dealloc u *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_D (map.putmany m_E
      (map.putmany m_FF (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L (map.putmany m_M
          (map.putmany m_N m_P))))))))))))), m_C.
    split. { exact Hbytes_u. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc t (Fp2) *)
    assert (Hbytes_t : Memory.anybytes t_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_B).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst t_ptr t13' m_B HB). }
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E
      (map.putmany m_FF (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L (map.putmany m_M
          (map.putmany m_N m_P)))))))))))), m_B.
    split. { exact Hbytes_t. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc a2b2 (Fp2) *)
    assert (Hbytes_a2b2 : Memory.anybytes a2b2_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_FF).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst a2b2_ptr a2b2' m_FF HFF). }
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L (map.putmany m_M
          (map.putmany m_N m_P))))))))))), m_FF.
    split. { exact Hbytes_a2b2. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc a1b1 (Fp2) *)
    assert (Hbytes_a1b1 : Memory.anybytes a1b1_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_G).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst a1b1_ptr a1b1' m_G HG). }
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E
      (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L (map.putmany m_M
          (map.putmany m_N m_P)))))))))), m_G.
    split. { exact Hbytes_a1b1. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc a0b0 (Fp2) *)
    assert (Hbytes_a0b0 : Memory.anybytes a0b0_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_HH).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst a0b0_ptr a0b0' m_HH HHH). }
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E
      (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L (map.putmany m_M
          (map.putmany m_N m_P))))))))), m_HH.
    split. { exact Hbytes_a0b0. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc allocy (Fp6) *)
    assert (Hjoin_y : (FElem_Fp2 allocy (c0_felem y) ⋆
      (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
       FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y)))
      (map.putmany m_I (map.putmany m_J m_K))).
    { exists m_I, (map.putmany m_J m_K).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HI |].
      exists m_J, m_K.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HJ | exact HK]. }
    pose proof (Fp6_raw_FElem_join allocy (c0_felem y) (c1_felem y) (c2_felem y)
      (map.putmany m_I (map.putmany m_J m_K))
      Hlen_I Hlen_J Hlen_K Hjoin_y) as Hfp6_y.
    rewrite Fp6_list_decomp in Hfp6_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocy y
      (map.putmany m_I (map.putmany m_J m_K)) Hfp6_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E
      (map.putmany m_L (map.putmany m_M (map.putmany m_N m_P)))))),
      (map.putmany m_I (map.putmany m_J m_K)).
    split. { exact Hanybytes_y. }
    split. { split.
      { (* Group I,J,K and swap past L..P *)
        rewrite (map.putmany_assoc m_J m_K).
        rewrite (map.putmany_assoc m_I).
        rewrite (map.putmany_comm
          (map.putmany m_I (map.putmany m_J m_K))
          (map.putmany m_L (map.putmany m_M (map.putmany m_N m_P)))).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_E).
        rewrite (map.putmany_assoc m_D).
        rewrite (map.putmany_assoc m_A).
        reflexivity. }
      { map_disjoint_auto. } }
    (* dealloc allocx (Fp6) *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_L (map.putmany m_M m_N))).
    { exists m_L, (map.putmany m_M m_N).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HL |].
      exists m_M, m_N.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HM | exact HN]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_L (map.putmany m_M m_N))
      Hlen_L Hlen_M Hlen_N Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_L (map.putmany m_M m_N)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_D (map.putmany m_E m_P))),
      (map.putmany m_L (map.putmany m_M m_N)).
    split. { exact Hanybytes_x. }
    split. { split.
      { (* Group L,M,N and swap past P *)
        rewrite (map.putmany_assoc m_M m_N).
        rewrite (map.putmany_assoc m_L).
        rewrite (map.putmany_comm
          (map.putmany m_L (map.putmany m_M m_N)) m_P).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_E).
        rewrite (map.putmany_assoc m_D).
        rewrite (map.putmany_assoc m_A).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 6: Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_E).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_E).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_E, Hlen_D; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_E).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_E, Hlen_D; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    split.
    { (* feval *)
      fp6_feval_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      (* Replace bin_model with the concrete Fp6 spec *)
      change bin_model with (@AbstractField.Fmul _ Fp6_fp_inst).
      change (@AbstractField.Fmul _ Fp6_fp_inst) with (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im).
      unfold BLS12Fp6Spec.fp6_mul, BLS12Fp6Spec.fp6_c0, BLS12Fp6Spec.fp6_c1,
             BLS12Fp6Spec.fp6_c2, BLS12Fp6Spec.fp6_build.
      cbv beta. cbn [fst snd].
      (* Rewrite all Fp2-level feval equations *)
      rewrite Hfeval_out0, Hfeval_out1, Hfeval_out2.
      rewrite Hfeval_t13, Hfeval_t12, Hfeval_t11. rewrite Hfeval_u4.
      rewrite Hfeval_t10, Hfeval_t9, Hfeval_t8, Hfeval_t7.
      rewrite Hfeval_u3, Hfeval_u2, Hfeval_t6.
      rewrite Hfeval_t5, Hfeval_t4, Hfeval_t3, Hfeval_t2, Hfeval_t1.
      rewrite Hfeval_u1.
      rewrite Hfeval_a0b0, Hfeval_a1b1, Hfeval_a2b2.
      (* Expose concrete Fp2 operations (mulp2, addp2, subp2) *)
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add
           AbstractField.bin_sub AbstractField.un_model un_Fp2_mul_xi
           AbstractField.Fmul AbstractField.Fadd AbstractField.Fsub
           Fp2_fp_inst QuadraticFieldExtensionsSpecs.Fp2_field_parameters].
      (* Bridge mulp2→fp2_mul (not definitionally equal: generic β vs -1) *)
      rewrite !mulp2_eq_fp2_mul.
      (* Bridge addp2→fp2_add and subp2→fp2_sub (definitionally equal,
         but change helps the kernel on this large term) *)
      change (QuadraticExtensions.addp2 M_pos) with (BLS12Fp6Spec.fp2_add M_pos).
      change (QuadraticExtensions.subp2 M_pos) with (BLS12Fp6Spec.fp2_sub M_pos).
      reflexivity. }
    split.
    { (* bounded_by *)
      fp6_bounded_by_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      (* Reduce bin_outbounds and tight/loose_bounds through Fp6 repr to Fp2 level *)
      cbv [AbstractField.bin_outbounds AbstractField.bin_mul
           AbstractField.bin_add AbstractField.bin_sub
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation].
      cbv [AbstractField.bin_outbounds AbstractField.bin_mul
           AbstractField.bin_add AbstractField.bin_sub
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation]
        in Hbound_out0, Hbound_out1, Hbound_out2.
      split; [|split]; solve_bounds. }
    { (* sep: (FElem pout (out0'++out1'++out2') * Rr) final_mem *)
      (* m_E=out0'@pout.c0, m_D=out1'@pout.c1, m_A=out2'@pout.c2 *)
      assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_E (map.putmany m_D m_A))).
      { exists m_E, (map.putmany m_D m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HE |].
        exists m_D, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HD | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_E (map.putmany m_D m_A))
        Hlen_E Hlen_D Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_E (map.putmany m_D m_A)), m_P.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HP]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_sqr: Chung-Hasan SQR3 squaring                              *)
  (*                                                                  *)
  (* s0 = a.c0^2                                                      *)
  (* s1 = 2 * a.c0 * a.c1                                            *)
  (* s2 = (a.c0 - a.c1 + a.c2)^2                                    *)
  (* s3 = 2 * a.c1 * a.c2                                            *)
  (* s4 = a.c2^2                                                      *)
  (* out.c0 = s0 + xi * s3                                           *)
  (* out.c1 = s1 + xi * s4                                           *)
  (* out.c2 = s1 + s2 + s3 - s0 - s4                                *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_sqr : function_t :=
    (AbstractField.square (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s3;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s4;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t;
      (* Copy input to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* s0 = a0^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s0"; expr_fp6_c0 (expr.var "allocx")]);
      (* t = a0*a1; s1 = t + t = 2*a0*a1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "s1"; expr.var "t"; expr.var "t"]);
      (* s2 = (a0 - a1 + a2)^2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "t"; expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s2"; expr.var "t"]);
      (* t = a1*a2; s3 = t + t = 2*a1*a2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "s3"; expr.var "t"; expr.var "t"]);
      (* s4 = a2^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s4"; expr_fp6_c2 (expr.var "allocx")]);
      (* out.c0 = s0 + xi*s3 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "s3"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "s0"; expr.var "t"]);
      (* out.c1 = s1 + xi*s4 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "s4"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "s1"; expr.var "t"]);
      (* out.c2 = s1 + s2 + s3 - s0 - s4 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "s1"; expr.var "s2"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "s3"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "s0"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "t"; expr.var "s4"])
    ))).

  (* Custom un_model for Fp6 square: uses the Chung-Hasan SQR3 formula
     (fp6_sqr) rather than the generic Fsquare = Fmul x x (fp6_mul x x).
     These are algebraically equal but structurally different. *)
  Local Instance un_Fp6_sqr
    : @AbstractField.UnOp _ _ _ _ Fp6 Fp6_fp_inst Fp6_repr_inst
        (AbstractField.square (F:=Fp6)) :=
    {| AbstractField.un_model := BLS12Fp6Spec.fp6_sqr M_pos beta xi_re xi_im;
       AbstractField.un_xbounds := @AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst;
       AbstractField.un_outbounds := @AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst |}.

  Instance spec_of_Fp6_sqr : spec_of (AbstractField.square (F:=Fp6)) :=
    AbstractField.unop_spec un_Fp6_sqr.

  Lemma Fp6_sqr_ok : program_logic_goal_for_function! Fp6_sqr.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains
      HFcopy HFsqr1 HFmul1 HFadd1 HFsub1 HFadd2 HFsqr2
      HFmul2 HFadd3 HFsqr3 HFmulxi1 HFadd4 HFmulxi2
      HFadd5 HFadd6 HFadd7 HFsub2 HFsub3.
    unfold spec_of_Fp6_sqr, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_sqr].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === 7 Stackallocs: allocx (Fp6) + s0,s1,s2,s3,s4,t (Fp2) === *)
    split. { apply Z_mod_mult. }
    intros allocx mStack_ax m1 Hstack_ax Hm1.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros s0_ptr mStack_s0 m2 Hstack_s0 Hm2.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros s1_ptr mStack_s1 m3 Hstack_s1 Hm3.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros s2_ptr mStack_s2 m4 Hstack_s2 Hm4.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros s3_ptr mStack_s3 m5 Hstack_s3 Hm5.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros s4_ptr mStack_s4 m6 Hstack_s4 Hm6.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros t_ptr mStack_t m7 Hstack_t Hm7.
    (* === FElem_from_bytes === *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfb_ax.
    unfold AbstractField.Placeholder in Hfb_ax.
    pose proof (proj1 (Hfb_ax mStack_ax) Hstack_ax) as [allocx_val Hallocx]. clear Hfb_ax.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok s0_ptr) as Hfb1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok s1_ptr) as Hfb2.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok s2_ptr) as Hfb3.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok s3_ptr) as Hfb4.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok s4_ptr) as Hfb5.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok t_ptr) as Hfb6.
    unfold AbstractField.Placeholder in Hfb1, Hfb2, Hfb3, Hfb4, Hfb5, Hfb6.
    pose proof (proj1 (Hfb1 mStack_s0) Hstack_s0) as [s0_val Hs0_fe]. clear Hfb1.
    pose proof (proj1 (Hfb2 mStack_s1) Hstack_s1) as [s1_val Hs1_fe]. clear Hfb2.
    pose proof (proj1 (Hfb3 mStack_s2) Hstack_s2) as [s2_val Hs2_fe]. clear Hfb3.
    pose proof (proj1 (Hfb4 mStack_s3) Hstack_s3) as [s3_val Hs3_fe]. clear Hfb4.
    pose proof (proj1 (Hfb5 mStack_s4) Hstack_s4) as [s4_val Hs4_fe]. clear Hfb5.
    pose proof (proj1 (Hfb6 mStack_t) Hstack_t) as [t_val Ht_fe]. clear Hfb6.
    (* === Decompose memory === *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    destruct Hm3 as [Heq_m3 Hd_m3]. subst m3.
    destruct Hm4 as [Heq_m4 Hd_m4]. subst m4.
    destruct Hm5 as [Heq_m5 Hd_m5]. subst m5.
    destruct Hm6 as [Heq_m6 Hd_m6]. subst m6.
    destruct Hm7 as [Heq_m7 Hd_m7]. subst m7.
    split_all_disjointness.
    (* === Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy allocx px allocx_val x
        (fun m => (Rx ⋆ (FElem_Fp2 s0_ptr s0_val ⋆ (FElem_Fp2 s1_ptr s1_val ⋆
                   (FElem_Fp2 s2_ptr s2_val ⋆ (FElem_Fp2 s3_ptr s3_val ⋆
                   (FElem_Fp2 s4_ptr s4_val ⋆ FElem_Fp2 t_ptr t_val)))))) m)
        (eq (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_s0 (map.putmany mStack_s1
                 (map.putmany mStack_s2 (map.putmany mStack_s3
                   (map.putmany mStack_s4 mStack_t)))))))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * R) *)
        exists (map.putmany m_x mStack_ax),
               (map.putmany m_rx (map.putmany mStack_s0 (map.putmany mStack_s1
                 (map.putmany mStack_s2 (map.putmany mStack_s3
                   (map.putmany mStack_s4 mStack_t)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStack_ax.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, (map.putmany mStack_s0 (map.putmany mStack_s1
            (map.putmany mStack_s2 (map.putmany mStack_s3
              (map.putmany mStack_s4 mStack_t))))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hrx |].
          exists mStack_s0, (map.putmany mStack_s1
            (map.putmany mStack_s2 (map.putmany mStack_s3
              (map.putmany mStack_s4 mStack_t)))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hs0_fe |].
          exists mStack_s1, (map.putmany mStack_s2 (map.putmany mStack_s3
              (map.putmany mStack_s4 mStack_t))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hs1_fe |].
          exists mStack_s2, (map.putmany mStack_s3 (map.putmany mStack_s4 mStack_t)).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hs2_fe |].
          exists mStack_s3, (map.putmany mStack_s4 mStack_t).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hs3_fe |].
          exists mStack_s4, mStack_t.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hs4_fe | exact Ht_fe]. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout) *)
        exists mStack_ax, (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_s0 (map.putmany mStack_s1
                 (map.putmany mStack_s2 (map.putmany mStack_s3
                   (map.putmany mStack_s4 mStack_t)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Post-copy: Split FElems and build big sep === *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp6 FElem at allocx into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split allocx x m_new Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    (* Split output FElem into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Subst decomposed maps *)
    subst m_ax12 m_o12 m_out m_new.
    assert (Heq_xr : map.putmany m_x m_rx = map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)
      by exact Heq_m0_out.
    rewrite Heq_xr in Hd_n_f.
    split_all_disjointness.
    (* Derive disjointness between output/rr maps and stack temporaries.
       Chain: mStack_* ⊥ m_x, m_rx (from stackalloc); m_x++m_rx = m_o*++m_rr (Heq_xr). *)
    assert (Hd_stacks_out : map.disjoint
      (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
        (map.putmany mStack_s3 (map.putmany mStack_s4 mStack_t)))))
      (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
    { rewrite <- Heq_xr. map_disjoint_auto. }
    split_all_disjointness.
    (* Rewrite goal memory: decompose m_x++m_rx, right-associate, move m_rr to end *)
    rewrite Heq_xr.
    rewrite <- !map.putmany_assoc.
    map_swap m_rr mStack_s0.
    map_swap m_rr mStack_s1.
    map_swap m_rr mStack_s2.
    map_swap m_rr mStack_s3.
    map_swap m_rr mStack_s4.
    rewrite (map.putmany_comm m_rr mStack_t) by map_disjoint_auto.
    (* Build 12-way sep: 3 allocx + 3 output + 6 stacks *)
    assert (Hsep12 :
      (FElem_Fp2 allocx (c0_felem x) ⋆
        (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x) ⋆
          (FElem_Fp2 pout (c0_felem old_out) ⋆
           (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
            (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out) ⋆
             (FElem_Fp2 s0_ptr s0_val ⋆
              (FElem_Fp2 s1_ptr s1_val ⋆
               (FElem_Fp2 s2_ptr s2_val ⋆
                (FElem_Fp2 s3_ptr s3_val ⋆
                 (FElem_Fp2 s4_ptr s4_val ⋆
                  (FElem_Fp2 t_ptr t_val ⋆ Rr))))))))))))
      (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))))))))))))).
    { exists m_ax0, (map.putmany m_ax1 (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr)))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax1 |].
      exists m_ax2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr)))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o0 |].
      exists m_o1, (map.putmany m_o2
          (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o1 |].
      exists m_o2, (map.putmany mStack_s0 (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o2 |].
      exists mStack_s0, (map.putmany mStack_s1 (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hs0_fe |].
      exists mStack_s1, (map.putmany mStack_s2
            (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hs1_fe |].
      exists mStack_s2, (map.putmany mStack_s3 (map.putmany mStack_s4
              (map.putmany mStack_t m_rr))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hs2_fe |].
      exists mStack_s3, (map.putmany mStack_s4 (map.putmany mStack_t m_rr)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hs3_fe |].
      exists mStack_s4, (map.putmany mStack_t m_rr).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hs4_fe |].
      exists mStack_t, m_rr.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht_fe | exact Hrr_out]. }
    (* Change Fp6 bounded_by to Fp2 level *)
    change un_xbounds with (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) in Hbx0, Hbx1, Hbx2.
    change (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) in Hbx0, Hbx1, Hbx2.
    (* === 17 Fp2 operation calls === *)
    (* Call 1: s0 = sqr(allocx.c0) — s0 = a0^2 *)
    exists [s0_ptr; allocx]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr1 s0_ptr allocx
           s0_val (c0_felem x) _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep12 as H'. ecancel_assumption. }
         pose proof Hsep12 as H'. ecancel_assumption. }
    intros t1 m1' rets1 [Hrets1 [Htr1 [s0' [Hfeval_s0 [Hbound_s0 Hsep1]]]]].
    subst rets1 t1.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: t = mul(allocx.c0, allocx.c1) — t = a0*a1 *)
    exists [t_ptr; allocx; word.add allocx fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 t_ptr allocx (word.add allocx fp6_c1_offset)
           t_val (c0_felem x) (c1_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2' rets2 [Hrets2 [Htr2 [t1' [Hfeval_t1 [Hbound_t1 Hsep2]]]]].
    subst rets2 t2.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: s1 = add(t, t) — s1 = 2*a0*a1 *)
    exists [s1_ptr; t_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 s1_ptr t_ptr t_ptr
           s1_val t1' t1' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3' rets3 [Hrets3 [Htr3 [s1' [Hfeval_s1 [Hbound_s1 Hsep3]]]]].
    subst rets3 t3.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 4: t = sub(allocx.c0, allocx.c1) — t = a0-a1 *)
    exists [t_ptr; allocx; word.add allocx fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 t_ptr allocx (word.add allocx fp6_c1_offset)
           t1' (c0_felem x) (c1_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4 m4' rets4 [Hrets4 [Htr4 [t2' [Hfeval_t2 [Hbound_t2 Hsep4]]]]].
    subst rets4 t4.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 5: t = add(t, allocx.c2) — t = (a0-a1)+a2 *)
    exists [t_ptr; t_ptr; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 t_ptr t_ptr (word.add allocx fp6_c2_offset)
           t2' t2' (c2_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep4 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep4 as H'. ecancel_assumption. }
         pose proof Hsep4 as H'. ecancel_assumption. }
    intros t5 m5' rets5 [Hrets5 [Htr5 [t3' [Hfeval_t3 [Hbound_t3 Hsep5]]]]].
    subst rets5 t5.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 6: s2 = sqr(t) — s2 = ((a0-a1)+a2)^2 *)
    exists [s2_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr2 s2_ptr t_ptr
           s2_val t3' _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep5 as H'. ecancel_assumption. }
         pose proof Hsep5 as H'. ecancel_assumption. }
    intros t6 m6' rets6 [Hrets6 [Htr6 [s2' [Hfeval_s2 [Hbound_s2 Hsep6]]]]].
    subst rets6 t6.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 7: t = mul(allocx.c1, allocx.c2) — t = a1*a2 *)
    exists [t_ptr; word.add allocx fp6_c1_offset; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 t_ptr (word.add allocx fp6_c1_offset) (word.add allocx fp6_c2_offset)
           t3' (c1_felem x) (c2_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         pose proof Hsep6 as H'. ecancel_assumption. }
    intros t7 m7' rets7 [Hrets7 [Htr7 [t4' [Hfeval_t4 [Hbound_t4 Hsep7]]]]].
    subst rets7 t7.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 8: s3 = add(t, t) — s3 = 2*a1*a2 *)
    exists [s3_ptr; t_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 s3_ptr t_ptr t_ptr
           s3_val t4' t4' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    intros t8 m8' rets8 [Hrets8 [Htr8 [s3' [Hfeval_s3 [Hbound_s3 Hsep8]]]]].
    subst rets8 t8.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 9: s4 = sqr(allocx.c2) — s4 = a2^2 *)
    exists [s4_ptr; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr3 s4_ptr (word.add allocx fp6_c2_offset)
           s4_val (c2_felem x) _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep8 as H'. ecancel_assumption. }
         pose proof Hsep8 as H'. ecancel_assumption. }
    intros t9 m9' rets9 [Hrets9 [Htr9 [s4' [Hfeval_s4 [Hbound_s4 Hsep9]]]]].
    subst rets9 t9.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 10: t = mul_xi(s3) — t = xi*s3 *)
    exists [t_ptr; s3_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi1 t_ptr s3_ptr
           t4' s3' _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep9 as H'. ecancel_assumption. }
         pose proof Hsep9 as H'. ecancel_assumption. }
    intros t10 m10' rets10 [Hrets10 [Htr10 [t5' [Hfeval_t5 [Hbound_t5 Hsep10]]]]].
    subst rets10 t10.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 11: out.c0 = add(s0, t) — out.c0 = s0 + xi*s3 *)
    exists [pout; s0_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd4 pout s0_ptr t_ptr
           (c0_felem old_out) s0' t5' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    intros t11 m11' rets11 [Hrets11 [Htr11 [out0' [Hfeval_out0 [Hbound_out0 Hsep11]]]]].
    subst rets11 t11.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 12: t = mul_xi(s4) — t = xi*s4 *)
    exists [t_ptr; s4_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi2 t_ptr s4_ptr
           t5' s4' _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep11 as H'. ecancel_assumption. }
         pose proof Hsep11 as H'. ecancel_assumption. }
    intros t12 m12' rets12 [Hrets12 [Htr12 [t6' [Hfeval_t6 [Hbound_t6 Hsep12']]]]].
    subst rets12 t12.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 13: out.c1 = add(s1, t) — out.c1 = s1 + xi*s4 *)
    exists [word.add pout fp6_c1_offset; s1_ptr; t_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd5 (word.add pout fp6_c1_offset) s1_ptr t_ptr
           (c1_felem old_out) s1' t6' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep12' as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep12' as H'. ecancel_assumption. }
         pose proof Hsep12' as H'. ecancel_assumption. }
    intros t13 m13' rets13 [Hrets13 [Htr13 [out1' [Hfeval_out1 [Hbound_out1 Hsep13]]]]].
    subst rets13 t13.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 14: t = add(s1, s2) — t = s1+s2 *)
    exists [t_ptr; s1_ptr; s2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd6 t_ptr s1_ptr s2_ptr
           t6' s1' s2' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep13 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep13 as H'. ecancel_assumption. }
         pose proof Hsep13 as H'. ecancel_assumption. }
    intros t14 m14' rets14 [Hrets14 [Htr14 [t7' [Hfeval_t7 [Hbound_t7 Hsep14]]]]].
    subst rets14 t14.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 15: t = add(t, s3) — t = (s1+s2)+s3 *)
    exists [t_ptr; t_ptr; s3_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd7 t_ptr t_ptr s3_ptr
           t7' t7' s3' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         pose proof Hsep14 as H'. ecancel_assumption. }
    intros t15 m15' rets15 [Hrets15 [Htr15 [t8' [Hfeval_t8 [Hbound_t8 Hsep15]]]]].
    subst rets15 t15.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 16: t = sub(t, s0) — t = ((s1+s2)+s3)-s0 *)
    exists [t_ptr; t_ptr; s0_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 t_ptr t_ptr s0_ptr
           t8' t8' s0' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep15 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep15 as H'. ecancel_assumption. }
         pose proof Hsep15 as H'. ecancel_assumption. }
    intros t16 m16' rets16 [Hrets16 [Htr16 [t9' [Hfeval_t9 [Hbound_t9 Hsep16]]]]].
    subst rets16 t16.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 17: out.c2 = sub(t, s4) — out.c2 = (((s1+s2)+s3)-s0)-s4 *)
    exists [word.add pout fp6_c2_offset; t_ptr; s4_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 (word.add pout fp6_c2_offset) t_ptr s4_ptr
           (c2_felem old_out) t9' s4' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         pose proof Hsep16 as H'. ecancel_assumption. }
    intros t17 m17' rets17 [Hrets17 [Htr17 [out2' [Hfeval_out2 [Hbound_out2 Hsep17]]]]].
    subst rets17 t17.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure final sep and stack deallocation === *)
    destruct Hsep17 as [m_A [m_rest1 [[Heq_final Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_rest9 [[Heq_r8 Hd_I] [HI Hrest9]]]].
    destruct Hrest9 as [m_J [m_rest10 [[Heq_r9 Hd_J] [HJ Hrest10]]]].
    destruct Hrest10 as [m_K [m_rest11 [[Heq_r10 Hd_K] [HK Hrest11]]]].
    destruct Hrest11 as [m_L [m_P [[Heq_r11 Hd_LP] [HL HP]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7
          m_rest8 m_rest9 m_rest10 m_rest11 m17'.
    (* Derive all pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    pose proof (Fp2_FElem_length _ _ _ HJ) as Hlen_J.
    pose proof (Fp2_FElem_length _ _ _ HK) as Hlen_K.
    pose proof (Fp2_FElem_length _ _ _ HL) as Hlen_L.
    (* === Stack deallocation: t (Fp2) === *)
    (* Hsep17 order after ecancel through 17 calls:
       m_A=out2'@pout.c2, m_B=t9'@t, m_C=out1'@pout.c1, m_D=out0'@pout.c0,
       m_E=s4'@s4, m_FF=s3'@s3, m_G=s2'@s2, m_HH=s1'@s1,
       m_I=s0'@s0, m_J=x0@ax.c0, m_K=x1@ax.c1, m_L=x2@ax.c2, m_P=Rr *)
    assert (Hbytes_t : Memory.anybytes t_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_B).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst t_ptr t9' m_B HB). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D (map.putmany m_E
      (map.putmany m_FF (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))))))), m_B.
    split. { exact Hbytes_t. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc s4 (Fp2) *)
    assert (Hbytes_s4 : Memory.anybytes s4_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_E).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst s4_ptr s4' m_E HE). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D
      (map.putmany m_FF (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))))))), m_E.
    split. { exact Hbytes_s4. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc s3 (Fp2) *)
    assert (Hbytes_s3 : Memory.anybytes s3_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_FF).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst s3_ptr s3' m_FF HFF). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))))), m_FF.
    split. { exact Hbytes_s3. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc s2 (Fp2) *)
    assert (Hbytes_s2 : Memory.anybytes s2_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_G).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst s2_ptr s2' m_G HG). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D
      (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))))), m_G.
    split. { exact Hbytes_s2. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc s1 (Fp2) *)
    assert (Hbytes_s1 : Memory.anybytes s1_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_HH).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst s1_ptr s1' m_HH HHH). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D
      (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))), m_HH.
    split. { exact Hbytes_s1. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc s0 (Fp2) *)
    assert (Hbytes_s0 : Memory.anybytes s0_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_I).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst s0_ptr s0' m_I HI). }
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D
      (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))), m_I.
    split. { exact Hbytes_s0. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc allocx (Fp6) *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_J (map.putmany m_K m_L))).
    { exists m_J, (map.putmany m_K m_L).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HJ |].
      exists m_K, m_L.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HK | exact HL]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_J (map.putmany m_K m_L))
      Hlen_J Hlen_K Hlen_L Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_J (map.putmany m_K m_L)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_D m_P))),
      (map.putmany m_J (map.putmany m_K m_L)).
    split. { exact Hanybytes_x. }
    split. { split.
      { rewrite <- !map.putmany_assoc.
        apply (f_equal (map.putmany m_A)).
        apply (f_equal (map.putmany m_C)).
        apply (f_equal (map.putmany m_D)).
        rewrite (map.putmany_comm m_L m_P) by map_disjoint_auto.
        map_swap m_K m_P.
        map_swap m_J m_P.
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_D).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_D).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_D, Hlen_C; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_D).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_D, Hlen_C; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    split.
    { (* feval *)
      fp6_feval_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      change un_model with (BLS12Fp6Spec.fp6_sqr M_pos beta xi_re xi_im).
      unfold BLS12Fp6Spec.fp6_sqr, BLS12Fp6Spec.fp6_c0, BLS12Fp6Spec.fp6_c1,
             BLS12Fp6Spec.fp6_c2, BLS12Fp6Spec.fp6_build.
      cbv beta. cbn [fst snd].
      rewrite Hfeval_out0, Hfeval_out1, Hfeval_out2.
      rewrite Hfeval_t9, Hfeval_t8, Hfeval_t7.
      rewrite Hfeval_t6, Hfeval_t5.
      rewrite Hfeval_s4, Hfeval_s3, Hfeval_s2, Hfeval_s1, Hfeval_s0.
      rewrite Hfeval_t4, Hfeval_t3, Hfeval_t2, Hfeval_t1.
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add
           AbstractField.bin_sub AbstractField.un_model AbstractField.un_square
           un_Fp2_mul_xi
           AbstractField.Fmul AbstractField.Fadd AbstractField.Fsub
           AbstractField.Fsquare
           Fp2_fp_inst QuadraticFieldExtensionsSpecs.Fp2_field_parameters].
      rewrite !mulp2_eq_fp2_mul.
      change (QuadraticExtensions.addp2 M_pos) with (BLS12Fp6Spec.fp2_add M_pos).
      change (QuadraticExtensions.subp2 M_pos) with (BLS12Fp6Spec.fp2_sub M_pos).
      reflexivity. }
    split.
    { (* bounded_by *)
      fp6_bounded_by_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      cbv [AbstractField.un_outbounds un_Fp6_sqr
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation].
      cbv [AbstractField.un_outbounds un_Fp6_sqr
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation]
        in Hbound_out0, Hbound_out1, Hbound_out2.
      split; [|split]; solve_bounds. }
    { (* sep: (FElem pout (out0'++out1'++out2') * Rr) final_mem *)
      assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_D (map.putmany m_C m_A))).
      { exists m_D, (map.putmany m_C m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HD |].
        exists m_C, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_D (map.putmany m_C m_A))
        Hlen_D Hlen_C Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_D (map.putmany m_C m_A)), m_P.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HP]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_inv: cubic extension inverse                                 *)
  (*                                                                  *)
  (* A = a0^2 - xi*(a1*a2)                                           *)
  (* B = xi*(a2^2) - a0*a1                                           *)
  (* C = a1^2 - a0*a2                                                *)
  (* F = a0*A + xi*(a2*B + a1*C)                                     *)
  (* out = (A/F, B/F, C/F)                                           *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_inv : function_t :=
    (AbstractField.inv (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vA;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vB;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vC;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t3;
      (* Copy input to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* A = a0^2 - xi*(a1*a2) *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c0 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t3"; expr.var "t2"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vA"; expr.var "t1"; expr.var "t3"]);
      (* B = xi*(a2^2) - a0*a1 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t3"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vB"; expr.var "t3"; expr.var "t2"]);
      (* C = a1^2 - a0*a2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vC"; expr.var "t1"; expr.var "t2"]);
      (* FF = a0*A + xi*(a2*B + a1*C) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t1"; expr_fp6_c0 (expr.var "allocx"); expr.var "vA"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c2 (expr.var "allocx"); expr.var "vB"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t3"; expr_fp6_c1 (expr.var "allocx"); expr.var "vC"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t2"; expr.var "t2"; expr.var "t3"]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t2"; expr.var "t2"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t1"; expr.var "t1"; expr.var "t2"]);
      (* t1 = FF^{-1} *)
      coq:(cmd.call [] (AbstractField.inv (F:=Fp2)) [expr.var "t1"; expr.var "t1"]);
      (* out = (A/F, B/F, C/F) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "vA"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "vB"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "vC"; expr.var "t1"])
    ))).

  Instance spec_of_Fp6_inv : spec_of (AbstractField.inv (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp6).

  Lemma Fp6_inv_ok : program_logic_goal_for_function! Fp6_inv.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains
      HFcopy HFsqr1 HFmul1 HFmulxi1 HFsub1
      HFsqr2 HFmulxi2 HFmul2 HFsub2
      HFsqr3 HFmul3 HFsub3
      HFmul4 HFmul5 HFmul6 HFadd1 HFmulxi3 HFadd2
      HFinv HFmul7 HFmul8 HFmul9.
    unfold spec_of_Fp6_inv, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_inv].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === 7 Stackallocs: allocx (Fp6) + vA,vB,vC,t1,t2,t3 (Fp2) === *)
    split. { apply Z_mod_mult. }
    intros allocx mStack_ax m1 Hstack_ax Hm1.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros vA_ptr mStack_vA m2 Hstack_vA Hm2.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros vB_ptr mStack_vB m3 Hstack_vB Hm3.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros vC_ptr mStack_vC m4 Hstack_vC Hm4.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros t1_ptr mStack_t1 m5 Hstack_t1 Hm5.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros t2_ptr mStack_t2 m6 Hstack_t2 Hm6.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros t3_ptr mStack_t3 m7 Hstack_t3 Hm7.
    (* === FElem_from_bytes === *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfb_ax.
    unfold AbstractField.Placeholder in Hfb_ax.
    pose proof (proj1 (Hfb_ax mStack_ax) Hstack_ax) as [allocx_val Hallocx]. clear Hfb_ax.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok vA_ptr) as Hfb1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok vB_ptr) as Hfb2.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok vC_ptr) as Hfb3.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok t1_ptr) as Hfb4.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok t2_ptr) as Hfb5.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok t3_ptr) as Hfb6.
    unfold AbstractField.Placeholder in Hfb1, Hfb2, Hfb3, Hfb4, Hfb5, Hfb6.
    pose proof (proj1 (Hfb1 mStack_vA) Hstack_vA) as [vA_val HvA_fe]. clear Hfb1.
    pose proof (proj1 (Hfb2 mStack_vB) Hstack_vB) as [vB_val HvB_fe]. clear Hfb2.
    pose proof (proj1 (Hfb3 mStack_vC) Hstack_vC) as [vC_val HvC_fe]. clear Hfb3.
    pose proof (proj1 (Hfb4 mStack_t1) Hstack_t1) as [t1_val Ht1_fe]. clear Hfb4.
    pose proof (proj1 (Hfb5 mStack_t2) Hstack_t2) as [t2_val Ht2_fe]. clear Hfb5.
    pose proof (proj1 (Hfb6 mStack_t3) Hstack_t3) as [t3_val Ht3_fe]. clear Hfb6.
    (* === Decompose memory === *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    destruct Hm3 as [Heq_m3 Hd_m3]. subst m3.
    destruct Hm4 as [Heq_m4 Hd_m4]. subst m4.
    destruct Hm5 as [Heq_m5 Hd_m5]. subst m5.
    destruct Hm6 as [Heq_m6 Hd_m6]. subst m6.
    destruct Hm7 as [Heq_m7 Hd_m7]. subst m7.
    split_all_disjointness.
    (* === Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy allocx px allocx_val x
        (fun m => (Rx ⋆ (FElem_Fp2 vA_ptr vA_val ⋆ (FElem_Fp2 vB_ptr vB_val ⋆
                   (FElem_Fp2 vC_ptr vC_val ⋆ (FElem_Fp2 t1_ptr t1_val ⋆
                   (FElem_Fp2 t2_ptr t2_val ⋆ FElem_Fp2 t3_ptr t3_val)))))) m)
        (eq (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_vA (map.putmany mStack_vB
                 (map.putmany mStack_vC (map.putmany mStack_t1
                   (map.putmany mStack_t2 mStack_t3)))))))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * R) *)
        exists (map.putmany m_x mStack_ax),
               (map.putmany m_rx (map.putmany mStack_vA (map.putmany mStack_vB
                 (map.putmany mStack_vC (map.putmany mStack_t1
                   (map.putmany mStack_t2 mStack_t3)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStack_ax.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, (map.putmany mStack_vA (map.putmany mStack_vB
            (map.putmany mStack_vC (map.putmany mStack_t1
              (map.putmany mStack_t2 mStack_t3))))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hrx |].
          exists mStack_vA, (map.putmany mStack_vB
            (map.putmany mStack_vC (map.putmany mStack_t1
              (map.putmany mStack_t2 mStack_t3)))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HvA_fe |].
          exists mStack_vB, (map.putmany mStack_vC (map.putmany mStack_t1
              (map.putmany mStack_t2 mStack_t3))).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HvB_fe |].
          exists mStack_vC, (map.putmany mStack_t1 (map.putmany mStack_t2 mStack_t3)).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HvC_fe |].
          exists mStack_t1, (map.putmany mStack_t2 mStack_t3).
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ht1_fe |].
          exists mStack_t2, mStack_t3.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Ht2_fe | exact Ht3_fe]. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout) *)
        exists mStack_ax, (map.putmany (map.putmany m_x m_rx)
               (map.putmany mStack_vA (map.putmany mStack_vB
                 (map.putmany mStack_vC (map.putmany mStack_t1
                   (map.putmany mStack_t2 mStack_t3)))))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Post-copy: Split FElems and build big sep === *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp6 FElem at allocx into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split allocx x m_new Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    (* Split output FElem into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Subst decomposed maps *)
    subst m_ax12 m_o12 m_out m_new.
    assert (Heq_xr : map.putmany m_x m_rx = map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)
      by exact Heq_m0_out.
    rewrite Heq_xr in Hd_n_f.
    split_all_disjointness.
    (* Derive disjointness between output/rr maps and stack temporaries *)
    assert (Hd_stacks_out : map.disjoint
      (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
        (map.putmany mStack_t1 (map.putmany mStack_t2 mStack_t3)))))
      (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
    { rewrite <- Heq_xr. map_disjoint_auto. }
    split_all_disjointness.
    (* Rewrite goal memory: decompose m_x++m_rx, right-associate, move m_rr to end *)
    rewrite Heq_xr.
    rewrite <- !map.putmany_assoc.
    map_swap m_rr mStack_vA.
    map_swap m_rr mStack_vB.
    map_swap m_rr mStack_vC.
    map_swap m_rr mStack_t1.
    map_swap m_rr mStack_t2.
    rewrite (map.putmany_comm m_rr mStack_t3) by map_disjoint_auto.
    (* Build 13-way sep: 3 allocx + 3 output + 6 stacks + Rr *)
    assert (Hsep13 :
      (FElem_Fp2 allocx (c0_felem x) ⋆
        (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x) ⋆
          (FElem_Fp2 pout (c0_felem old_out) ⋆
           (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
            (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out) ⋆
             (FElem_Fp2 vA_ptr vA_val ⋆
              (FElem_Fp2 vB_ptr vB_val ⋆
               (FElem_Fp2 vC_ptr vC_val ⋆
                (FElem_Fp2 t1_ptr t1_val ⋆
                 (FElem_Fp2 t2_ptr t2_val ⋆
                  (FElem_Fp2 t3_ptr t3_val ⋆ Rr))))))))))))
      (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))))))))))))).
    { exists m_ax0, (map.putmany m_ax1 (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_ax2
        (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr)))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax1 |].
      exists m_ax2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr)))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o0 |].
      exists m_o1, (map.putmany m_o2
          (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o1 |].
      exists m_o2, (map.putmany mStack_vA (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o2 |].
      exists mStack_vA, (map.putmany mStack_vB (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HvA_fe |].
      exists mStack_vB, (map.putmany mStack_vC
            (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HvB_fe |].
      exists mStack_vC, (map.putmany mStack_t1 (map.putmany mStack_t2
              (map.putmany mStack_t3 m_rr))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HvC_fe |].
      exists mStack_t1, (map.putmany mStack_t2 (map.putmany mStack_t3 m_rr)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht1_fe |].
      exists mStack_t2, (map.putmany mStack_t3 m_rr).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht2_fe |].
      exists mStack_t3, m_rr.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht3_fe | exact Hrr_out]. }
    (* Change Fp6 bounded_by to Fp2 level *)
    change un_xbounds with (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) in Hbx0, Hbx1, Hbx2.
    change (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) in Hbx0, Hbx1, Hbx2.
    (* === 21 Fp2 operation calls === *)
    (* Call 1: t1 = sqr(allocx.c0) — a0^2 *)
    exists [t1_ptr; allocx]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr1 t1_ptr allocx
           t1_val (c0_felem x) _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep13 as H'. ecancel_assumption. }
         pose proof Hsep13 as H'. ecancel_assumption. }
    intros t1' m1' rets1 [Hrets1 [Htr1 [t1_1 [Hfeval_t1_1 [Hbound_t1_1 Hsep1]]]]].
    subst rets1 t1'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: t2 = mul(allocx.c1, allocx.c2) — a1*a2 *)
    exists [t2_ptr; word.add allocx fp6_c1_offset; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 t2_ptr (word.add allocx fp6_c1_offset) (word.add allocx fp6_c2_offset)
           t2_val (c1_felem x) (c2_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2' m2' rets2 [Hrets2 [Htr2 [t2_1 [Hfeval_t2_1 [Hbound_t2_1 Hsep2]]]]].
    subst rets2 t2'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: t3 = mul_xi(t2) — xi*(a1*a2) *)
    exists [t3_ptr; t2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi1 t3_ptr t2_ptr
           t3_val t2_1 _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep2 as H'. ecancel_assumption. }
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3' m3' rets3 [Hrets3 [Htr3 [t3_1 [Hfeval_t3_1 [Hbound_t3_1 Hsep3]]]]].
    subst rets3 t3'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 4: vA = sub(t1, t3) — A = a0^2 - xi*(a1*a2) *)
    exists [vA_ptr; t1_ptr; t3_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 vA_ptr t1_ptr t3_ptr
           vA_val t1_1 t3_1 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep3 as H'. ecancel_assumption. }
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4' m4' rets4 [Hrets4 [Htr4 [vA' [Hfeval_vA [Hbound_vA Hsep4]]]]].
    subst rets4 t4'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 5: t1 = sqr(allocx.c2) — a2^2 *)
    exists [t1_ptr; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr2 t1_ptr (word.add allocx fp6_c2_offset)
           t1_1 (c2_felem x) _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep4 as H'. ecancel_assumption. }
         pose proof Hsep4 as H'. ecancel_assumption. }
    intros t5' m5' rets5 [Hrets5 [Htr5 [t1_2 [Hfeval_t1_2 [Hbound_t1_2 Hsep5]]]]].
    subst rets5 t5'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 6: t3 = mul_xi(t1) — xi*(a2^2) *)
    exists [t3_ptr; t1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi2 t3_ptr t1_ptr
           t3_1 t1_2 _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep5 as H'. ecancel_assumption. }
         pose proof Hsep5 as H'. ecancel_assumption. }
    intros t6' m6' rets6 [Hrets6 [Htr6 [t3_2 [Hfeval_t3_2 [Hbound_t3_2 Hsep6]]]]].
    subst rets6 t6'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 7: t2 = mul(allocx.c0, allocx.c1) — a0*a1 *)
    exists [t2_ptr; allocx; word.add allocx fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 t2_ptr allocx (word.add allocx fp6_c1_offset)
           t2_1 (c0_felem x) (c1_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep6 as H'. ecancel_assumption. }
         pose proof Hsep6 as H'. ecancel_assumption. }
    intros t7' m7' rets7 [Hrets7 [Htr7 [t2_2 [Hfeval_t2_2 [Hbound_t2_2 Hsep7]]]]].
    subst rets7 t7'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 8: vB = sub(t3, t2) — B = xi*(a2^2) - a0*a1 *)
    exists [vB_ptr; t3_ptr; t2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 vB_ptr t3_ptr t2_ptr
           vB_val t3_2 t2_2 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    intros t8' m8' rets8 [Hrets8 [Htr8 [vB' [Hfeval_vB [Hbound_vB Hsep8]]]]].
    subst rets8 t8'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 9: t1 = sqr(allocx.c1) — a1^2 *)
    exists [t1_ptr; word.add allocx fp6_c1_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr3 t1_ptr (word.add allocx fp6_c1_offset)
           t1_2 (c1_felem x) _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep8 as H'. ecancel_assumption. }
         pose proof Hsep8 as H'. ecancel_assumption. }
    intros t9' m9' rets9 [Hrets9 [Htr9 [t1_3 [Hfeval_t1_3 [Hbound_t1_3 Hsep9]]]]].
    subst rets9 t9'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 10: t2 = mul(allocx.c0, allocx.c2) — a0*a2 *)
    exists [t2_ptr; allocx; word.add allocx fp6_c2_offset]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul3 t2_ptr allocx (word.add allocx fp6_c2_offset)
           t2_2 (c0_felem x) (c2_felem x) _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep9 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep9 as H'. ecancel_assumption. }
         pose proof Hsep9 as H'. ecancel_assumption. }
    intros t10' m10' rets10 [Hrets10 [Htr10 [t2_3 [Hfeval_t2_3 [Hbound_t2_3 Hsep10]]]]].
    subst rets10 t10'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 11: vC = sub(t1, t2) — C = a1^2 - a0*a2 *)
    exists [vC_ptr; t1_ptr; t2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 vC_ptr t1_ptr t2_ptr
           vC_val t1_3 t2_3 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    intros t11' m11' rets11 [Hrets11 [Htr11 [vC' [Hfeval_vC [Hbound_vC Hsep11]]]]].
    subst rets11 t11'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 12: t1 = mul(allocx.c0, vA) — a0*A *)
    exists [t1_ptr; allocx; vA_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul4 t1_ptr allocx vA_ptr
           t1_3 (c0_felem x) vA' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep11 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep11 as H'. ecancel_assumption. }
         pose proof Hsep11 as H'. ecancel_assumption. }
    intros t12' m12' rets12 [Hrets12 [Htr12 [t1_4 [Hfeval_t1_4 [Hbound_t1_4 Hsep12]]]]].
    subst rets12 t12'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 13: t2 = mul(allocx.c2, vB) — a2*B *)
    exists [t2_ptr; word.add allocx fp6_c2_offset; vB_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul5 t2_ptr (word.add allocx fp6_c2_offset) vB_ptr
           t2_3 (c2_felem x) vB' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep12 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep12 as H'. ecancel_assumption. }
         pose proof Hsep12 as H'. ecancel_assumption. }
    intros t13' m13' rets13 [Hrets13 [Htr13 [t2_4 [Hfeval_t2_4 [Hbound_t2_4 Hsep13']]]]].
    subst rets13 t13'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 14: t3 = mul(allocx.c1, vC) — a1*C *)
    exists [t3_ptr; word.add allocx fp6_c1_offset; vC_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul6 t3_ptr (word.add allocx fp6_c1_offset) vC_ptr
           t3_2 (c1_felem x) vC' _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep13' as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep13' as H'. ecancel_assumption. }
         pose proof Hsep13' as H'. ecancel_assumption. }
    intros t14' m14' rets14 [Hrets14 [Htr14 [t3_3 [Hfeval_t3_3 [Hbound_t3_3 Hsep14]]]]].
    subst rets14 t14'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 15: t2 = add(t2, t3) — a2*B + a1*C *)
    exists [t2_ptr; t2_ptr; t3_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 t2_ptr t2_ptr t3_ptr
           t2_4 t2_4 t3_3 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep14 as H'. ecancel_assumption. }
         pose proof Hsep14 as H'. ecancel_assumption. }
    intros t15' m15' rets15 [Hrets15 [Htr15 [t2_5 [Hfeval_t2_5 [Hbound_t2_5 Hsep15]]]]].
    subst rets15 t15'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 16: t2 = mul_xi(t2) — xi*(a2*B + a1*C) *)
    exists [t2_ptr; t2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi3 t2_ptr t2_ptr
           t2_5 t2_5 _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep15 as H'. ecancel_assumption. }
         pose proof Hsep15 as H'. ecancel_assumption. }
    intros t16' m16' rets16 [Hrets16 [Htr16 [t2_6 [Hfeval_t2_6 [Hbound_t2_6 Hsep16]]]]].
    subst rets16 t16'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 17: t1 = add(t1, t2) — FF = a0*A + xi*(a2*B + a1*C) *)
    exists [t1_ptr; t1_ptr; t2_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 t1_ptr t1_ptr t2_ptr
           t1_4 t1_4 t2_6 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep16 as H'. ecancel_assumption. }
         pose proof Hsep16 as H'. ecancel_assumption. }
    intros t17' m17' rets17 [Hrets17 [Htr17 [t1_5 [Hfeval_t1_5 [Hbound_t1_5 Hsep17]]]]].
    subst rets17 t17'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 18: t1 = inv(t1) — FF^{-1} *)
    exists [t1_ptr; t1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFinv t1_ptr t1_ptr
           t1_5 t1_5 _ tr).
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep17 as H'. ecancel_assumption. }
         pose proof Hsep17 as H'. ecancel_assumption. }
    intros t18' m18' rets18 [Hrets18 [Htr18 [t1_6 [Hfeval_t1_6 [Hbound_t1_6 Hsep18]]]]].
    subst rets18 t18'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 19: out.c0 = mul(vA, t1) — A/FF *)
    exists [pout; vA_ptr; t1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul7 pout vA_ptr t1_ptr
           (c0_felem old_out) vA' t1_6 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep18 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep18 as H'. ecancel_assumption. }
         pose proof Hsep18 as H'. ecancel_assumption. }
    intros t19' m19' rets19 [Hrets19 [Htr19 [out0' [Hfeval_out0 [Hbound_out0 Hsep19]]]]].
    subst rets19 t19'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 20: out.c1 = mul(vB, t1) — B/FF *)
    exists [word.add pout fp6_c1_offset; vB_ptr; t1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul8 (word.add pout fp6_c1_offset) vB_ptr t1_ptr
           (c1_felem old_out) vB' t1_6 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep19 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep19 as H'. ecancel_assumption. }
         pose proof Hsep19 as H'. ecancel_assumption. }
    intros t20' m20' rets20 [Hrets20 [Htr20 [out1' [Hfeval_out1 [Hbound_out1 Hsep20]]]]].
    subst rets20 t20'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* Call 21: out.c2 = mul(vC, t1) — C/FF *)
    exists [word.add pout fp6_c2_offset; vC_ptr; t1_ptr]. split.
    1: { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul9 (word.add pout fp6_c2_offset) vC_ptr t1_ptr
           (c2_felem old_out) vC' t1_6 _ tr).
         split; [solve_bounds |].
         split; [solve_bounds |].
         split. { eexists. pose proof Hsep20 as H'. ecancel_assumption. }
         split. { eexists. pose proof Hsep20 as H'. ecancel_assumption. }
         pose proof Hsep20 as H'. ecancel_assumption. }
    intros t21' m21' rets21 [Hrets21 [Htr21 [out2' [Hfeval_out2 [Hbound_out2 Hsep21]]]]].
    subst rets21 t21'.
    cbv [map.putmany_of_list_zip].
    exists l5. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure final sep and stack deallocation === *)
    (* Hsep21 order after ecancel through 21 calls:
       m_A=out2'@pout.c2, m_B=out1'@pout.c1, m_C=out0'@pout.c0,
       m_D=t1_6@t1, m_E=t2_6@t2, m_FF=t3_3@t3,
       m_G=vC'@vC, m_HH=vB'@vB, m_I=vA'@vA,
       m_J=x0@allocx.c0, m_K=x1@allocx.c1, m_L=x2@allocx.c2, m_P=Rr *)
    destruct Hsep21 as [m_A [m_rest1 [[Heq_final Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_rest9 [[Heq_r8 Hd_I] [HI Hrest9]]]].
    destruct Hrest9 as [m_J [m_rest10 [[Heq_r9 Hd_J] [HJ Hrest10]]]].
    destruct Hrest10 as [m_K [m_rest11 [[Heq_r10 Hd_K] [HK Hrest11]]]].
    destruct Hrest11 as [m_L [m_P [[Heq_r11 Hd_LP] [HL HP]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7
          m_rest8 m_rest9 m_rest10 m_rest11 m21'.
    (* Derive all pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    pose proof (Fp2_FElem_length _ _ _ HJ) as Hlen_J.
    pose proof (Fp2_FElem_length _ _ _ HK) as Hlen_K.
    pose proof (Fp2_FElem_length _ _ _ HL) as Hlen_L.
    (* === Stack deallocation: 6 Fp2 temps + 1 Fp6 allocx === *)
    (* dealloc t3 (Fp2) *)
    assert (Hbytes_t3 : Memory.anybytes t3_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_FF).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst t3_ptr t3_3 m_FF HFF). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C (map.putmany m_D
      (map.putmany m_E (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))))))), m_FF.
    split. { exact Hbytes_t3. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc t2 (Fp2) *)
    assert (Hbytes_t2 : Memory.anybytes t2_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_E).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst t2_ptr t2_6 m_E HE). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C (map.putmany m_D
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))))))), m_E.
    split. { exact Hbytes_t2. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc t1 (Fp2) *)
    assert (Hbytes_t1 : Memory.anybytes t1_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_D).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst t1_ptr t1_6 m_D HD). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))))), m_D.
    split. { exact Hbytes_t1. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc vC (Fp2) *)
    assert (Hbytes_vC : Memory.anybytes vC_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_G).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst vC_ptr vC' m_G HG). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_HH (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))))), m_G.
    split. { exact Hbytes_vC. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc vB (Fp2) *)
    assert (Hbytes_vB : Memory.anybytes vB_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_HH).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst vB_ptr vB' m_HH HHH). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_I
        (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P))))))), m_HH.
    split. { exact Hbytes_vB. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc vA (Fp2) *)
    assert (Hbytes_vA : Memory.anybytes vA_ptr
      (@AbstractField.felem_size_in_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m_I).
    { exact (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
        Fp2_fp_inst Fp2_repr_inst vA_ptr vA' m_I HI). }
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_J (map.putmany m_K (map.putmany m_L m_P)))))), m_I.
    split. { exact Hbytes_vA. }
    split. { split; [| map_disjoint_auto]. solve_putmany_eq. }
    (* dealloc allocx (Fp6) *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_J (map.putmany m_K m_L))).
    { exists m_J, (map.putmany m_K m_L).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HJ |].
      exists m_K, m_L.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HK | exact HL]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_J (map.putmany m_K m_L))
      Hlen_J Hlen_K Hlen_L Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_J (map.putmany m_K m_L)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_P))),
      (map.putmany m_J (map.putmany m_K m_L)).
    split. { exact Hanybytes_x. }
    split. { split.
      { rewrite <- !map.putmany_assoc.
        apply (f_equal (map.putmany m_A)).
        apply (f_equal (map.putmany m_B)).
        apply (f_equal (map.putmany m_C)).
        rewrite (map.putmany_comm m_L m_P) by map_disjoint_auto.
        map_swap m_K m_P.
        map_swap m_J m_P.
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    split.
    { (* feval *)
      fp6_feval_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      change un_model with (@AbstractField.Finv _ Fp6_fp_inst).
      change (@AbstractField.Finv _ Fp6_fp_inst) with (BLS12Fp6Spec.fp6_inv M_pos beta xi_re xi_im).
      unfold BLS12Fp6Spec.fp6_inv, BLS12Fp6Spec.fp6_c0, BLS12Fp6Spec.fp6_c1,
             BLS12Fp6Spec.fp6_c2, BLS12Fp6Spec.fp6_build.
      cbv beta. cbn [fst snd].
      rewrite Hfeval_out0, Hfeval_out1, Hfeval_out2.
      rewrite Hfeval_t1_6, Hfeval_t1_5, Hfeval_t1_4.
      rewrite Hfeval_t2_6, Hfeval_t2_5, Hfeval_t2_4.
      rewrite Hfeval_t3_3.
      rewrite Hfeval_vA, Hfeval_vB, Hfeval_vC.
      rewrite Hfeval_t1_1, Hfeval_t3_1, Hfeval_t2_1.
      rewrite Hfeval_t3_2, Hfeval_t2_2, Hfeval_t1_2.
      rewrite Hfeval_t1_3, Hfeval_t2_3.
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add
           AbstractField.bin_sub AbstractField.un_model AbstractField.un_square
           AbstractField.un_inv un_Fp2_mul_xi
           AbstractField.Fmul AbstractField.Fadd AbstractField.Fsub
           AbstractField.Fsquare AbstractField.Finv
           Fp2_fp_inst QuadraticFieldExtensionsSpecs.Fp2_field_parameters].
      rewrite !mulp2_eq_fp2_mul.
      rewrite !invp2_eq_fp2_inv.
      change (QuadraticExtensions.addp2 M_pos) with (BLS12Fp6Spec.fp2_add M_pos).
      change (QuadraticExtensions.subp2 M_pos) with (BLS12Fp6Spec.fp2_sub M_pos).
      reflexivity. }
    split.
    { (* bounded_by *)
      fp6_bounded_by_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      cbv [AbstractField.un_outbounds AbstractField.un_inv
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation].
      cbv [AbstractField.un_outbounds AbstractField.un_inv
           AbstractField.bin_outbounds AbstractField.bin_mul
           AbstractField.tight_bounds AbstractField.loose_bounds
           Fp6_repr_inst CubicFieldExtensionsSpecs.Fp6_field_representation]
        in Hbound_out0, Hbound_out1, Hbound_out2.
      split; [|split]; solve_bounds. }
    { (* sep: (FElem pout (out0'++out1'++out2') * Rr) final_mem *)
      assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_P.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HP]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* Collected function list for downstream linking                    *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_funcs : list function_t :=
    [ Fp2_mul_xi;
      Fp6_felem_copy;
      Fp6_add;
      Fp6_sub;
      Fp6_opp;
      Fp6_mul;
      Fp6_sqr;
      Fp6_inv;
      Fp6_add_nocopy;
      Fp6_sub_nocopy ].

End Fp6.
