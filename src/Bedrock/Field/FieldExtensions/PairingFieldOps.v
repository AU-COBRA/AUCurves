(** * Bedrock2 compilation layer for pairing-specific field operations.

    Provides additional operations needed for the optimal Ate pairing
    that are not part of the standard FieldParameters interface:
    - fp2_conjugate: (a0, a1) -> (a0, -a1)
    - fp6_mul_fp2: scale Fp6 by an Fp2 scalar
    - fp6_frobenius: Frobenius endomorphism on Fp6 (gamma constants as extra args)
    - fp6_frobenius_p2: Frobenius squared on Fp6
    - fp12_frobenius: Frobenius on Fp12
    - fp12_frobenius_p2: Frobenius squared on Fp12

    WP proofs are currently stubs (exact I).
*)

Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Section PairingOps.
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

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* Quadratic non-residue β for Fp2 = Fp[u]/(u² - β) *)
  Variable beta : F M_pos.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big : 2 < Z.pos M_pos.

  (* ξ = (xi_re, xi_im) in Fp2 — the cubic non-residue for Fp6 = Fp2[v]/(v³ - ξ) *)
  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.

  Variable fp12_prefix : string.
  Variable fp6_prefix : string.
  Variable fp2_prefix : string.

  (* ================================================================ *)
  (* Lower-layer instances                                             *)
  (* ================================================================ *)

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation beta fp2_prefix.

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters beta xi_re xi_im (fp6_prefix:=fp6_prefix).
  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  Local Instance Fp12_fp_inst : AbstractField.FieldParameters Fp12 :=
    Fp12_field_parameters beta xi_re xi_im (fp12_prefix:=fp12_prefix).
  Local Instance Fp12_repr_inst : @AbstractField.FieldRepresentation Fp12 Fp12_fp_inst width BW word mem :=
    Fp12_field_representation beta xi_re xi_im (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* Offset helpers                                                    *)
  (* ================================================================ *)

  (* Fp-level offsets within an Fp2 element *)
  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
  Local Definition expr_fp_snd (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp_felem_offset).

  (* Fp2-level offsets within an Fp6 element *)
  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  (* Fp6-level offsets within an Fp12 element *)
  Local Notation fp6_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
  Local Definition expr_fp12_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp12_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp6_felem_offset).

  (* ================================================================ *)
  (* spec_of instances for underlying operations                       *)
  (* ================================================================ *)

  (* Fp-level *)
  Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy.
  Instance spec_of_Fp_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
    AbstractField.unop_spec (F:=Fp) (field_parameters:=prime_field_parameters)
      (field_representation:=F_representation) AbstractField.un_opp.

  (* Fp2-level *)
  Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
    AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=Fp2_repr_inst).
  Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
    AbstractField.binop_spec (F:=Fp2) (field_representation:=Fp2_repr_inst) AbstractField.bin_mul.

  (* Fp6-level *)
  Instance spec_of_Fp6_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).
  Instance spec_of_Fp6_opp : spec_of (AbstractField.opp (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp6).

  (* Fp12-level *)
  Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
    AbstractField.spec_of_felem_copy (F:=Fp12).

  Context {Fp12_names : FieldNames (F:=Fp12)}.
  Context {Fp6_names : FieldNames (F:=Fp6)}.
  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {Fp_names : FieldNames (F:=Fp)}.

  (* ================================================================ *)
  (* Function bodies                                                   *)
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

  (* Function name helpers *)
  Local Definition fp2_conjugate_name := (fp2_prefix ++ "conjugate")%string.
  Local Definition fp6_mul_fp2_name := (fp6_prefix ++ "mul_fp2")%string.
  Local Definition fp6_frobenius_name := (fp6_prefix ++ "frobenius")%string.
  Local Definition fp6_frobenius_p2_name := (fp6_prefix ++ "frobenius_p2")%string.
  Local Definition fp12_frobenius_name := (fp12_prefix ++ "frobenius")%string.
  Local Definition fp12_frobenius_p2_name := (fp12_prefix ++ "frobenius_p2")%string.
  Local Definition fp12_frobenius_p3_name := (fp12_prefix ++ "frobenius_p3")%string.

  (* -------------------------------------------------------------- *)
  (* fp2_conjugate: (a0, a1) -> (a0, -a1)                            *)
  (* -------------------------------------------------------------- *)

  (* Use explicit @ to pin Fp-level instances, avoiding typeclass resolution
     picking Fp12 instances during WP proof unfolding *)
  Local Definition fp_copy_name := @AbstractField.felem_copy _ prime_field_parameters.
  Local Definition fp_opp_name := @AbstractField.opp _ prime_field_parameters.

  Definition Fp2_conjugate : function_t :=
    (fp2_conjugate_name, (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] fp_copy_name [expr.var "out"; expr.var "x"]);
      coq:(cmd.call [] fp_opp_name [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x")])
    ))).

  (* Fp2 conjugation model: (a0, a1) → (a0, -a1) *)
  Local Instance un_Fp2_conjugate
    : @AbstractField.UnOp _ _ _ _ Fp2 Fp2_fp_inst Fp2_repr_inst fp2_conjugate_name :=
    {| AbstractField.un_model := fun x => (fst x, @F.opp M_pos (snd x));
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst |}.

  Instance spec_of_Fp2_conjugate : spec_of fp2_conjugate_name :=
    fnspec! fp2_conjugate_name (pout px : word)
      / (old_out x : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) x /\
        (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst px x ⋆
         (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst pout old_out ⋆ Rr)) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst out =
            (fst (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst x),
             @F.opp M_pos (snd (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst x))) /\
          @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
            (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) out /\
          (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst pout out ⋆
           (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst px x ⋆ Rr)) mem' }.

  Local Typeclasses Opaque Fp12_fp_inst.
  Local Typeclasses Opaque Fp6_fp_inst.
  Local Typeclasses Opaque Fp2_fp_inst.

  Lemma Fp2_conjugate_ok :
    forall functions
      (EnvContains : map.get functions fp2_conjugate_name = Some (snd Fp2_conjugate))
      (HFcopy : spec_of_Fp_felem_copy functions)
      (HFopp : spec_of_Fp_opp functions),
    spec_of_Fp2_conjugate functions.
  Proof.
    intros.
    unfold spec_of_Fp2_conjugate.
    intros pout px old_out x Rr tr mem0 [Hbx Hsep].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_conjugate].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Set up context === *)
    (* Decompose precondition sep *)
    destruct Hsep as [m_x [m_or [Hsep1 [Hx Hor]]]].
    destruct Hor as [m_o [m_r [Hsep_or [Ho Hr]]]].
    (* Split Fp2 FElems into Fp halves *)
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
      word_ok mem_ok prime_parameters F_representation beta fp2_prefix px x m_x Hx)
      as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
      word_ok mem_ok prime_parameters F_representation beta fp2_prefix pout old_out m_o Ho)
      as [m_o1 [m_o2 [Hsep_o [Ho1 Ho2]]]].
    (* Decompose Fp2 bounded_by into 2 Fp bounded_by *)
    change (@AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
      with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b
        (fst_felem ws)
        /\ @AbstractField.bounded_by _ _ _ _ _ _ F_representation b
        (snd_felem ws)) in Hbx.
    destruct Hbx as [Hbx1 Hbx2].
    (* Derive pairwise disjointness *)
    destruct Hsep1 as [Heq1 Hd1]. destruct Hsep_or as [Heq_or Hd_or]. subst m_or mem0.
    destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_o as [Heq_o Hd_o12].
    subst m_x m_o.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_x_o Hd_x_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x1_o Hd_x2_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o1 Hd_x1_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o) as [Hd_x2_o1 Hd_x2_o2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x1_r Hd_x2_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o1_r Hd_o2_r].
    clear Hd_x_o Hd_x_r Hd_or Hd1 Hd_x1_o Hd_x2_o.
    (* === Call 1: Fp copy (out, x) — copies fst half === *)
    (* dexprs for [out; x] *)
    exists [pout; px]. split; [repeat straightline |].
    exists pout. split.
    { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
    cbv [list_map]. eexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      apply map.get_put_same. }
    exact eq_refl.
    (* Set up weaken_call for Fp copy *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy pout px
        (fst_felem old_out)
        (fst_felem x)
        (fun m => ((@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add px (word.of_Z fp_felem_offset))
          (snd_felem x) ⋆
          ((@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add pout (word.of_Z fp_felem_offset))
            (snd_felem old_out) ⋆ Rr)) m)
        (fun m => m = map.putmany m_x1
          (map.putmany m_x2 (map.putmany m_o2 m_r)))
        tr).
      split.
      { (* Condition 1: (FElem px (fst x) * FElem pout (fst out) * frame) mem0 *)
        exists (map.putmany m_x1 m_o1),
               (map.putmany m_x2 (map.putmany m_o2 m_r)).
        split; [split |].
        { rewrite <- (map.putmany_assoc m_o1 m_o2 m_r).
          rewrite (map.putmany_assoc (map.putmany m_x1 m_x2) m_o1
            (map.putmany m_o2 m_r)).
          rewrite (map.disjoint_putmany_commutes _ _ _ Hd_x2_o1).
          symmetry. apply map.putmany_assoc. }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_x12 |].
            apply map.disjoint_putmany_r. split; [exact Hd_x1_o2 | exact Hd_x1_r]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
              exact (Hd_x2_o1 k v2 v1 Hg2 Hg1). }
            apply map.disjoint_putmany_r. split; [exact Hd_o12 | exact Hd_o1_r]. } }
        split.
        { exists m_x1, m_o1.
          split; [split; [reflexivity | exact Hd_x1_o1] |].
          split; [exact Hx1 | exact Ho1]. }
        { exists m_x2, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { apply map.disjoint_putmany_r. split; [exact Hd_x2_o2 | exact Hd_x2_r]. }
          split; [exact Hx2 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Condition 2: (FElem pout (fst out) * Rout1_eq) mem0 *)
        exists m_o1,
          (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r))).
        split; [split |].
        { assert (Hd_x12_o1 : map.disjoint (map.putmany m_x1 m_x2) m_o1)
            by (apply map.disjoint_putmany_l; split;
                [exact Hd_x1_o1 | exact Hd_x2_o1]).
          rewrite <- (map.putmany_assoc m_o1 m_o2 m_r).
          rewrite (map.putmany_assoc (map.putmany m_x1 m_x2) m_o1
            (map.putmany m_o2 m_r)).
          rewrite (map.putmany_comm _ _ Hd_x12_o1).
          rewrite <- (map.putmany_assoc m_o1 (map.putmany m_x1 m_x2)
            (map.putmany m_o2 m_r)).
          rewrite <- (map.putmany_assoc m_x1 m_x2 (map.putmany m_o2 m_r)).
          reflexivity. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
            exact (Hd_x1_o1 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
            exact (Hd_x2_o1 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split; [exact Hd_o12 | exact Hd_o1_r]. }
        split; [exact Ho1 | exact eq_refl]. } }
    (* === Process postcondition of copy call === *)
    intros t' m' rets [Hrets [Htr Hsep_post1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: Fp opp (out+off, x+off) — negates snd half === *)
    (* dexprs for opp call *)
    exists [word.add pout (word.of_Z fp_felem_offset); word.add px (word.of_Z fp_felem_offset)].
    split. { solve_dexprs. }
    (* Decompose copy postcondition before weaken_call *)
    destruct Hsep_post1 as [m_new1 [m_frame1 [Hsp_post1 [Hnew1 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_p1 Hd_p1].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p1) as [Hd_n1_x1 Hd_n1_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest) as [Hd_n1_x2 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_o2 Hd_n1_r].
    clear Hd_n1_rest Hd_n1_rest2.
    (* m' = putmany m_new1 (putmany m_x1 (putmany m_x2 (putmany m_o2 m_r))) *)
    (* We need the opp Rr to include BOTH px halves (fst_x and snd_x), so they *)
    (* survive in the postcondition. The opp spec's "exists Ra" consumes snd_x, *)
    (* but the Rr preserves everything else including both x halves. *)
    (* Rr_opp = snd_x * (fst_copy * (fst_x * Rr)) *)
    (* After opp: (FElem(pout+off) opp * (snd_x * (fst_copy * (fst_x * Rr)))) m'' *)
    (* Build master sep on post-copy memory for the opp call *)
    assert (Hsep_opp :
      ((@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add px (word.of_Z fp_felem_offset)) (snd_felem x) ⋆
       ((@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add pout (word.of_Z fp_felem_offset)) (snd_felem old_out) ⋆
        ((@AbstractField.FElem _ _ _ _ _ _ F_representation)pout (fst_felem x) ⋆
         ((@AbstractField.FElem _ _ _ _ _ _ F_representation)px (fst_felem x) ⋆ Rr)))) m').
    { subst m'.
      exists m_x2, (map.putmany m_o2 (map.putmany m_new1 (map.putmany m_x1 m_r))).
      split; [split |].
      { (* Rearrange:
           putmany m_new1 (putmany m_x1 (putmany m_x2 (putmany m_o2 m_r)))
           = putmany m_x2 (putmany m_o2 (putmany m_new1 (putmany m_x1 m_r))) *)
        (* Move m_x2 to front: swap m_x1 and m_x2 within the nested structure *)
        rewrite (map.putmany_assoc m_x1 m_x2 (map.putmany m_o2 m_r)).
        rewrite (map.putmany_comm m_x1 m_x2 Hd_x12).
        rewrite <- (map.putmany_assoc m_x2 m_x1 (map.putmany m_o2 m_r)).
        (* Now: putmany m_new1 (putmany m_x2 (putmany m_x1 (putmany m_o2 m_r))) *)
        rewrite (map.putmany_assoc m_new1 m_x2).
        rewrite (map.putmany_comm m_new1 m_x2 Hd_n1_x2).
        rewrite <- (map.putmany_assoc m_x2 m_new1).
        (* Now: putmany m_x2 (putmany m_new1 (putmany m_x1 (putmany m_o2 m_r))) *)
        f_equal.
        (* putmany m_new1 (putmany m_x1 (putmany m_o2 m_r))
           = putmany m_o2 (putmany m_new1 (putmany m_x1 m_r)) *)
        rewrite (map.putmany_assoc m_x1 m_o2 m_r).
        rewrite (map.putmany_comm m_x1 m_o2 Hd_x1_o2).
        rewrite <- (map.putmany_assoc m_o2 m_x1 m_r).
        rewrite (map.putmany_assoc m_new1 m_o2).
        rewrite (map.putmany_comm m_new1 m_o2 Hd_n1_o2).
        rewrite <- (map.putmany_assoc m_o2 m_new1).
        reflexivity. }
      { apply map.disjoint_putmany_r. split; [exact Hd_x2_o2 |].
        apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_n1_x2 k v2 v1 Hg2 Hg1). }
        apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_x12 k v2 v1 Hg2 Hg1). }
        { exact Hd_x2_r. } }
      split; [exact Hx2 |].
      exists m_o2, (map.putmany m_new1 (map.putmany m_x1 m_r)).
      split; [split; [reflexivity |] |].
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_n1_o2 k v2 v1 Hg2 Hg1). }
        apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_x1_o2 k v2 v1 Hg2 Hg1). }
        { exact Hd_o2_r. } }
      split; [exact Ho2 |].
      exists m_new1, (map.putmany m_x1 m_r).
      split; [split; [reflexivity |] |].
      { apply map.disjoint_putmany_r.
        split; [exact Hd_n1_x1 | exact Hd_n1_r]. }
      split; [exact Hnew1 |].
      exists m_x1, m_r.
      split; [split; [reflexivity | exact Hd_x1_r] |].
      split; [exact Hx1 | exact Hr]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp (word.add pout (word.of_Z fp_felem_offset))
        (word.add px (word.of_Z fp_felem_offset))
        (snd_felem old_out)
        (snd_felem x)
        _ tr).
      wp_unop_precond ltac:(first [assumption | apply bounds_equiv; assumption]). }
    (* === Process postcondition of opp call === *)
    intros t'' m'' rets [Hrets [Htr2 [opp_out [Hfeval_opp [Hbound_opp Hsep_post2]]]]].
    subst rets.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact Htr2. }
    (* === Final: construct Fp2 output === *)
    (* The opp postcondition sep is: *)
    (* (FElem(pout+off) opp_out * (snd_x * (fst_copy * (fst_x * Rr)))) m'' *)
    (* Decompose into 5 maps *)
    destruct Hsep_post2 as [m_A [m_rest1 [[Heq_opp Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_E [[Heq_r3 Hd_DE] [HD HE]]]].
    subst m_rest1 m_rest2 m_rest3 m''.
    split_all_disjointness.
    (* m'' = putmany m_A (putmany m_B (putmany m_C (putmany m_D m_E))) *)
    (* HA : FElem(pout+off) opp_out on m_A *)
    (* HB : FElem(px+off) (snd x) on m_B *)
    (* HC : FElem(pout) (fst x) on m_C *)
    (* HD : FElem(px) (fst x) on m_D *)
    (* HE : Rr on m_E *)
    assert (Hlen_new1 : length (fst_felem x) =
      @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
    { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
        prime_parameters F_representation _ _ _ Hnew1). }
    assert (Hlen_opp : length opp_out =
      @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
    { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
        prime_parameters F_representation _ _ _ HA). }
    assert (Hlen_x2 : length (snd_felem x) =
      @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
    { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
        prime_parameters F_representation _ _ _ Hx2). }
    exists (fst_felem x ++ opp_out).
    split.
    { (* feval *)
      unfold feval. simpl @AbstractField.feval.
      unfold Fp2_repr_inst, Fp2_field_representation, fst_felem, snd_felem.
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_new1).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_new1).
      rewrite Hfeval_opp.
      cbv [AbstractField.un_model AbstractField.un_opp]. reflexivity. }
    split.
    { (* bounded_by loose *)
      change (@AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b
          (fst_felem ws)
          /\ @AbstractField.bounded_by _ _ _ _ _ _ F_representation b
          (snd_felem ws)).
      unfold fst_felem, snd_felem.
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_new1).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_new1).
      split.
      { apply (@AbstractField.relax_bounds _ _ _ _ _ _ F_representation
          F_representation_ok).
        exact Hbx1. }
      { exact Hbound_opp. } }
    { (* sep: FElem_Fp2 pout (fst x ++ opp_out) * (FElem_Fp2 px x * Rr) *)
      (* Join two Fp FElems into Fp2 for pout *)
      assert (Hjoin_out : ((@AbstractField.FElem _ _ _ _ _ _ F_representation)pout
        (fst_felem x) ⋆
        (@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add pout (word.of_Z fp_felem_offset)) opp_out)
        (map.putmany m_C m_A)).
      { exists m_C, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC | exact HA]. }
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _ word_ok mem_ok prime_parameters F_representation beta fp2_prefix
        pout (fst_felem x) opp_out
        (map.putmany m_C m_A) Hlen_new1 Hlen_opp Hjoin_out) as Hfp2_out.
      (* Join two Fp FElems into Fp2 for px *)
      assert (Hjoin_x : ((@AbstractField.FElem _ _ _ _ _ _ F_representation)px
        (fst_felem x) ⋆
        (@AbstractField.FElem _ _ _ _ _ _ F_representation)(word.add px (word.of_Z fp_felem_offset))
          (snd_felem x))
        (map.putmany m_D m_B)).
      { exists m_D, m_B.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HD | exact HB]. }
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _ word_ok mem_ok prime_parameters F_representation beta fp2_prefix
        px (fst_felem x)
        (snd_felem x)
        (map.putmany m_D m_B) Hlen_new1 Hlen_x2 Hjoin_x) as Hfp2_x.
      rewrite (@QuadraticFieldExtensions.Fp2_list_decomp _ _ _ _
        prime_parameters F_representation x) in Hfp2_x.
      (* Build final sep *)
      exists (map.putmany m_C m_A),
             (map.putmany (map.putmany m_D m_B) m_E).
      split; [split |].
      { (* Rearrange memory to match witnesses *)
        transitivity (map.putmany m_C (map.putmany m_A (map.putmany m_D (map.putmany m_B m_E)))).
        { (* LHS: putmany m_A (putmany m_B (putmany m_C (putmany m_D m_E)))
             = putmany m_C (putmany m_A (putmany m_D (putmany m_B m_E))) *)
          rewrite (map.putmany_assoc m_B m_C).
          rewrite (map.putmany_comm m_B m_C) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_C m_B).
          rewrite (map.putmany_assoc m_A m_C).
          rewrite (map.putmany_comm m_A m_C) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_C m_A).
          f_equal. f_equal.
          rewrite (map.putmany_assoc m_B m_D m_E).
          rewrite (map.putmany_comm m_B m_D) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_D m_B m_E).
          reflexivity. }
        { (* RHS: putmany (putmany m_C m_A) (putmany (putmany m_D m_B) m_E) *)
          rewrite (map.putmany_assoc m_C m_A).
          f_equal.
          rewrite (map.putmany_assoc m_D m_B m_E).
          reflexivity. } }
      { map_disjoint_auto. }
      split; [exact Hfp2_out |].
      exists (map.putmany m_D m_B), m_E.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp2_x | exact HE]. }
  Qed.










  (* -------------------------------------------------------------- *)
  (* fp6_mul_fp2: (c0, c1, c2) * s -> (c0*s, c1*s, c2*s)            *)
  (*   Extra arg: s (pointer to Fp2 scalar)                           *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_mul_fp2 : function_t :=
    (fp6_mul_fp2_name, (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s_copy;
      (* Copy scalar to avoid aliasing with out *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "s_copy"; expr.var "s"]);
      (* out.c0 = x.c0 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x"); expr.var "s_copy"]);
      (* out.c1 = x.c1 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x"); expr.var "s_copy"]);
      (* out.c2 = x.c2 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x"); expr.var "s_copy"])
    ))).

  Local Notation FElem_Fp2 := (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation FElem_Fp12 := (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).
  Local Notation Fp6_feval := (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp12_feval := (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).
  Local Notation Fp6_bounded := (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp12_bounded := (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).

  (* Gallina model for fp6_mul_fp2: scale each Fp2 component by s *)
  Local Definition fp6_mul_fp2_model (x : Fp6) (s : Fp2) : Fp6 :=
    ((@AbstractField.Fmul _ Fp2_fp_inst (fst (fst x)) s,
      @AbstractField.Fmul _ Fp2_fp_inst (snd (fst x)) s),
     @AbstractField.Fmul _ Fp2_fp_inst (snd x) s).

  Instance spec_of_Fp6_mul_fp2 : spec_of fp6_mul_fp2_name :=
    fnspec! fp6_mul_fp2_name (pout px ps : word)
      / (old_out : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (s : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) s /\
        (FElem_Fp6 px x ⋆ (FElem_Fp2 ps s ⋆ (FElem_Fp6 pout old_out ⋆ Rr))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_mul_fp2_model (Fp6_feval x) (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst s) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ (FElem_Fp6 px x ⋆ (FElem_Fp2 ps s ⋆ Rr))) mem' }.

  Local Ltac map_disjoint_auto_mul :=
    lazymatch goal with
    | |- map.disjoint (map.putmany _ _) _ =>
        apply map.disjoint_putmany_l; split; map_disjoint_auto_mul
    | |- map.disjoint _ (map.putmany _ _) =>
        apply map.disjoint_putmany_r; split; map_disjoint_auto_mul
    | |- map.disjoint ?a ?b =>
        first [ assumption
              | (unfold map.disjoint; intros ?k ?v1 ?v2 ?Hg1 ?Hg2;
                 match goal with H : map.disjoint _ _ |- _ => exact (H k v2 v1 Hg2 Hg1) end) ]
    end.

  Local Ltac map_swap_mul a b :=
    rewrite (map.putmany_assoc a b);
    let D := fresh "D" in
    assert (D : map.disjoint a b) by map_disjoint_auto_mul;
    rewrite (map.putmany_comm a b D);
    clear D;
    rewrite <- (map.putmany_assoc b a).

  Lemma Fp6_mul_fp2_ok :
    forall functions
      (EnvContains : map.get functions fp6_mul_fp2_name = Some (snd Fp6_mul_fp2))
      (HFcopy : spec_of_Fp2_felem_copy functions)
      (HFmul : spec_of_Fp2_mul functions),
    spec_of_Fp6_mul_fp2 functions.
  Proof.
    intros functions EnvContains HFcopy HFmul.
    unfold spec_of_Fp6_mul_fp2.
    intros pout px ps old_out x s Rr tr mem0
      [Hbx [Hbs Hmem_all]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_mul_fp2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc s_copy === *)
    split. { apply Z_mod_mult. }
    intros a_scopy mStack mCombined HstackScopy Hm_split.
    (* Convert anybytes to Fp2 FElem *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      word_ok mem_ok a_scopy) as Hfb_sc.
    unfold AbstractField.Placeholder in Hfb_sc.
    pose proof (proj1 (Hfb_sc mStack) HstackScopy) as [sc_val Hsc_felem]. clear Hfb_sc.
    (* Decompose precondition sep *)
    destruct Hmem_all as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]].
    destruct Hr1 as [m_s [m_r2 [[Heq1 Hd1] [Hfs Hr2]]]].
    destruct Hr2 as [m_out [m_rr [[Heq2 Hd2] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 mem0.
    (* Split Fp6 FElems into Fp2 components *)
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix px x _ Hfx)
      as [m_x0 [m_x12 [Hsp_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsp_x12 [Hx1 Hx2]]]].
    destruct Hsp_x as [? Hdxx]. destruct Hsp_x12 as [? Hdxy]. subst.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix pout old_out _ Hfe_out)
      as [m_o0 [m_o12 [Hsp_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Ho1 Ho2]]]].
    destruct Hsp_o as [? Hdox]. destruct Hsp_o12 as [? Hdoy]. subst.
    change FElem with FElem_Fp2 in Hx0, Hx1, Hx2, Ho0, Ho1, Ho2.
    (* Decompose Fp6 bounded_by into 3 Fp2 bounded_by *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Derive all pairwise disjointness *)
    split_all_disjointness.
    destruct Hm_split as [Heq_comb Hd_comb].
    split_all_disjointness.
    (* Flatten mCombined into right-associated putmany *)
    rewrite !map.putmany_assoc in Heq_comb.
    (* Build 9-way sep on mCombined:
       x0, x1, x2, s, o0, o1, o2, Rr, s_copy
       matching the order in Heq_comb after rewrite *)
    assert (Hsep :
      (FElem_Fp2 px (c0_felem x) ⋆
       (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
        (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆
         (FElem_Fp2 ps s ⋆
          (FElem_Fp2 pout (c0_felem old_out) ⋆
           (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem old_out) ⋆
            (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem old_out) ⋆
             (Rr ⋆
              FElem_Fp2 a_scopy sc_val))))))))
      mCombined).
    { subst mCombined.
      rewrite <- ?map.putmany_assoc.
      exists m_x0, (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_s (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mStack))))))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hx0 |].
      exists m_x1, (map.putmany m_x2 (map.putmany m_s (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mStack)))))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hx1 |].
      exists m_x2, (map.putmany m_s (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mStack))))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hx2 |].
      exists m_s, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mStack)))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hfs |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mStack))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Ho0 |].
      exists m_o1, (map.putmany m_o2 (map.putmany m_rr mStack)).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Ho1 |].
      exists m_o2, (map.putmany m_rr mStack).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Ho2 |].
      exists m_rr, mStack.
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hrr | exact Hsc_felem]. }
    (* === Call 1: copy(s_copy, s) === *)
    repeat straightline.
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFcopy a_scopy ps sc_val s _ _ tr).
         split.
         { pose proof Hsep as H'. ecancel_assumption. }
         { pose proof Hsep as H'. ecancel_assumption. } }
    intros t1 m1 rets1 [Hrets1 [Htr1 Hsep1]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: mul(out.c0, x.c0, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'.
         eapply (HFmul'
           pout
           px
           a_scopy (c0_felem old_out) (c0_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx0 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out0' [Hfeval0 [Hbound0 Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: mul(out.c1, x.c1, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul''.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul''.
         eapply (HFmul''
           (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           a_scopy (c1_felem old_out) (c1_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx1 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out1' [Hfeval1 [Hbound1 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: mul(out.c2, x.c2, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'''.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'''.
         eapply (HFmul'''
           (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           a_scopy (c2_felem old_out) (c2_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx2 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4 m4 rets4 [Hrets4 [Htr4 [out2' [Hfeval2 [Hbound2 Hsep4]]]]].
    subst rets4. symmetry in Htr4. subst t4.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "s" => ps; "s_copy" => a_scopy }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Stack deallocation + Final postcondition === *)
    (* Extract FElem lengths *)
    assert (Hlen_out0 : Datatypes.length out0' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep2 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out1 : Datatypes.length out1' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep3 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out2 : Datatypes.length out2' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep4 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    (* Separate s_copy FElem from the rest using ecancel *)
    assert (Hsep_split :
      (FElem_Fp2 a_scopy s ⋆
       (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
         (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2' ⋆
          (FElem_Fp2 px (c0_felem x) ⋆
           (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
            (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆
             (FElem_Fp2 ps s ⋆ Rr)))))))) m4).
    { pose proof Hsep4 as H'. ecancel_assumption. }
    (* Destructure to get the s_copy map and the rest *)
    destruct Hsep_split as [m_sc [m_keep [[Heq_s1 Hd_s1] [Hsc Hkeep]]]].
    subst m4.
    split_all_disjointness.
    (* Convert s_copy FElem to anybytes *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst a_scopy s m_sc Hsc) as Hanybytes_sc.
    unfold AbstractField.Placeholder in Hanybytes_sc.
    (* Provide stackalloc witnesses *)
    exists m_keep, m_sc.
    split. { exact Hanybytes_sc. }
    split. { split.
      { rewrite (map.putmany_comm m_sc m_keep) by map_disjoint_auto_mul.
        reflexivity. }
      { map_disjoint_auto_mul. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. } split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem. rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_out0. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem, c0_felem in Hlen_out0 |- *.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_out1. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      unfold c0_felem in Hlen_out0. fold n in Hlen_out0, Hlen_out1.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out1. reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      unfold fp6_mul_fp2_model, AbstractField.Fmul.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd.
      rewrite Hfeval0, Hfeval1, Hfeval2.
      cbv [bin_model AbstractField.bin_mul].
      reflexivity. }
    (* bounded_by *)
    split.
    { cbv [Fp6_bounded Fp6_repr_inst Fp6_field_representation bounded_by Fp2_field_representation Fp2_repr_inst].
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      cbv [bin_outbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation] in Hbound0, Hbound1, Hbound2.
      destruct Hbound0 as [Hb0a Hb0b]. destruct Hbound1 as [Hb1a Hb1b]. destruct Hbound2 as [Hb2a Hb2b].
      repeat split;
        first [ apply (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok); assumption
              | assumption ]. }
    (* sep *)
    { destruct Hkeep as [m_oc0 [m_kr1 [[Heq_k1 Hd_k1] [Hoc0 Hkr1]]]].
      destruct Hkr1 as [m_oc1 [m_kr2 [[Heq_k2 Hd_k2] [Hoc1 Hkr2]]]].
      destruct Hkr2 as [m_oc2 [m_kr3 [[Heq_k3 Hd_k3] [Hoc2 Hkr3]]]].
      destruct Hkr3 as [m_xc0 [m_kr4 [[Heq_k4 Hd_k4] [Hxc0 Hkr4]]]].
      destruct Hkr4 as [m_xc1 [m_kr5 [[Heq_k5 Hd_k5] [Hxc1 Hkr5]]]].
      destruct Hkr5 as [m_xc2 [m_kr6 [[Heq_k6 Hd_k6] [Hxc2 Hkr6]]]].
      destruct Hkr6 as [m_s' [m_rr' [[Heq_k7 Hd_k7] [Hs' Hrr']]]].
      subst m_kr1 m_kr2 m_kr3 m_kr4 m_kr5 m_kr6 m_keep.
      repeat match goal with
      | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
          let H1 := fresh "Hd" in let H2 := fresh "Hd" in
          destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
      end.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc0) as Hlen_oc0.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc1) as Hlen_oc1.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc2) as Hlen_oc2.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc0) as Hlen_xc0.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc1) as Hlen_xc1.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc2) as Hlen_xc2.
      (* Join output Fp2 -> Fp6 *)
      assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
         FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2'))
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))).
      { exists m_oc0, (map.putmany m_oc1 m_oc2).
        split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hoc0 |].
        exists m_oc1, m_oc2. split; [split; [reflexivity | map_disjoint_auto_mul] |].
        split; [exact Hoc1 | exact Hoc2]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix pout out0' out1' out2'
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)) Hlen_oc0 Hlen_oc1 Hlen_oc2 Hjoin_out) as Hfp6_out.
      (* Join input Fp2 -> Fp6 *)
      assert (Hjoin_x : (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
         FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x)))
        (map.putmany m_xc0 (map.putmany m_xc1 m_xc2))).
      { exists m_xc0, (map.putmany m_xc1 m_xc2).
        split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hxc0 |].
        exists m_xc1, m_xc2. split; [split; [reflexivity | map_disjoint_auto_mul] |].
        split; [exact Hxc1 | exact Hxc2]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix px (c0_felem x) (c1_felem x) (c2_felem x)
        (map.putmany m_xc0 (map.putmany m_xc1 m_xc2)) Hlen_xc0 Hlen_xc1 Hlen_xc2 Hjoin_x) as Hfp6_x.
      rewrite Fp6_list_decomp in Hfp6_x.
      (* Build final sep *)
      exists (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)),
             (map.putmany (map.putmany m_xc0 (map.putmany m_xc1 m_xc2))
               (map.putmany m_s' m_rr')).
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { map_disjoint_auto_mul. }
      split; [exact Hfp6_out |].
      exists (map.putmany m_xc0 (map.putmany m_xc1 m_xc2)),
             (map.putmany m_s' m_rr').
      split; [split; [reflexivity | map_disjoint_auto_mul] |].
      split; [exact Hfp6_x |].
      exists m_s', m_rr'.
      split; [split; [reflexivity | map_disjoint_auto_mul] |].
      split; [exact Hs' | exact Hrr']. }
  Qed.

  (* In-place variant: fp6_mul_fp2(p, p, s) where output aliases input *)
  Lemma Fp6_mul_fp2_inplace :
    forall functions
      (EnvContains : map.get functions fp6_mul_fp2_name = Some (snd Fp6_mul_fp2))
      (HFcopy : spec_of_Fp2_felem_copy functions)
      (HFmul : spec_of_Fp2_mul functions),
    forall p ps
      (x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
      (s : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
      Rr tr mem,
      Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
      @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
        (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) s /\
      (FElem_Fp6 p x ⋆ (FElem_Fp2 ps s ⋆ Rr)) mem ->
    WeakestPrecondition.call functions fp6_mul_fp2_name tr mem
      [p; p; ps]
      (fun tr' mem' rets =>
        rets = nil /\ tr = tr' /\
        exists out,
          Fp6_feval out = fp6_mul_fp2_model (Fp6_feval x)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst s) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 p out ⋆ (FElem_Fp2 ps s ⋆ Rr)) mem').
  Proof.
    intros functions EnvContains HFcopy HFmul.
    intros p ps x s Rr tr mem0
      [Hbx [Hbs Hmem_all]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_mul_fp2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc s_copy === *)
    split. { apply Z_mod_mult. }
    intros a_scopy mStack mCombined HstackScopy Hm_split.
    (* Convert anybytes to Fp2 FElem *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
      word_ok mem_ok a_scopy) as Hfb_sc.
    unfold AbstractField.Placeholder in Hfb_sc.
    pose proof (proj1 (Hfb_sc mStack) HstackScopy) as [sc_val Hsc_felem]. clear Hfb_sc.
    (* Decompose precondition sep *)
    destruct Hmem_all as [m_p [m_r1 [[Heq0 Hd0] [Hfp Hr1]]]].
    destruct Hr1 as [m_s [m_rr [[Heq1 Hd1] [Hfs Hrr]]]].
    subst m_r1 mem0.
    (* Split Fp6 FElem into Fp2 components *)
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix p x _ Hfp)
      as [m_p0 [m_p12 [Hsp_p [Hp0 Hp12]]]].
    destruct Hp12 as [m_p1 [m_p2 [Hsp_p12 [Hp1 Hp2]]]].
    destruct Hsp_p as [? Hdpx]. destruct Hsp_p12 as [? Hdpy]. subst.
    change FElem with FElem_Fp2 in Hp0, Hp1, Hp2.
    (* Decompose Fp6 bounded_by into 3 Fp2 bounded_by *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Derive all pairwise disjointness *)
    split_all_disjointness.
    destruct Hm_split as [Heq_comb Hd_comb].
    split_all_disjointness.
    (* Flatten mCombined into right-associated putmany *)
    rewrite !map.putmany_assoc in Heq_comb.
    (* Build 6-way sep on mCombined:
       p0, p1, p2, s, Rr, s_copy *)
    assert (Hsep :
      (FElem_Fp2 p (c0_felem x) ⋆
       (FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
        (FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆
         (FElem_Fp2 ps s ⋆
          (Rr ⋆
           FElem_Fp2 a_scopy sc_val)))))
      mCombined).
    { subst mCombined.
      rewrite <- ?map.putmany_assoc.
      exists m_p0, (map.putmany m_p1 (map.putmany m_p2 (map.putmany m_s (map.putmany m_rr mStack)))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hp0 |].
      exists m_p1, (map.putmany m_p2 (map.putmany m_s (map.putmany m_rr mStack))).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hp1 |].
      exists m_p2, (map.putmany m_s (map.putmany m_rr mStack)).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hp2 |].
      exists m_s, (map.putmany m_rr mStack).
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hfs |].
      exists m_rr, mStack.
      split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hrr | exact Hsc_felem]. }
    (* === Call 1: copy(s_copy, s) === *)
    repeat straightline.
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFcopy a_scopy ps sc_val s _ _ tr).
         split.
         { pose proof Hsep as H'. ecancel_assumption. }
         { pose proof Hsep as H'. ecancel_assumption. } }
    intros t1 m1 rets1 [Hrets1 [Htr1 Hsep1]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: mul(p.c0, p.c0, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'.
         eapply (HFmul'
           p
           p
           a_scopy (c0_felem x) (c0_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx0 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out0' [Hfeval0 [Hbound0 Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: mul(p.c1, p.c1, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul''.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul''.
         eapply (HFmul''
           (word.add p (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           (word.add p (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           a_scopy (c1_felem x) (c1_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx1 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out1' [Hfeval1 [Hbound1 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: mul(p.c2, p.c2, s_copy) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'''.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'''.
         eapply (HFmul'''
           (word.add p (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (word.add p (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           a_scopy (c2_felem x) (c2_felem x) s _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix));
                 exact Hbx2 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbs |].
         split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4 m4 rets4 [Hrets4 [Htr4 [out2' [Hfeval2 [Hbound2 Hsep4]]]]].
    subst rets4. symmetry in Htr4. subst t4.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => p; "x" => p; "s" => ps; "s_copy" => a_scopy }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Stack deallocation + Final postcondition === *)
    (* Extract FElem lengths *)
    assert (Hlen_out0 : Datatypes.length out0' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep2 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out1 : Datatypes.length out1' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep3 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out2 : Datatypes.length out2' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep4 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    (* Separate s_copy FElem from the rest using ecancel *)
    assert (Hsep_split :
      (FElem_Fp2 a_scopy s ⋆
       (FElem_Fp2 p out0' ⋆
        (FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
         (FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2' ⋆
          (FElem_Fp2 ps s ⋆ Rr))))) m4).
    { pose proof Hsep4 as H'. ecancel_assumption. }
    (* Destructure to get the s_copy map and the rest *)
    destruct Hsep_split as [m_sc [m_keep [[Heq_s1 Hd_s1] [Hsc Hkeep]]]].
    subst m4.
    split_all_disjointness.
    (* Convert s_copy FElem to anybytes *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst a_scopy s m_sc Hsc) as Hanybytes_sc.
    unfold AbstractField.Placeholder in Hanybytes_sc.
    (* Provide stackalloc witnesses *)
    exists m_keep, m_sc.
    split. { exact Hanybytes_sc. }
    split. { split.
      { rewrite (map.putmany_comm m_sc m_keep) by map_disjoint_auto_mul.
        reflexivity. }
      { map_disjoint_auto_mul. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. } split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem. rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_out0. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem, c0_felem in Hlen_out0 |- *.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_out1. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      unfold c0_felem in Hlen_out0. fold n in Hlen_out0, Hlen_out1.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out0.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out1. reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      unfold fp6_mul_fp2_model, AbstractField.Fmul.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd.
      rewrite Hfeval0, Hfeval1, Hfeval2.
      cbv [bin_model AbstractField.bin_mul].
      reflexivity. }
    (* bounded_by *)
    split.
    { cbv [Fp6_bounded Fp6_repr_inst Fp6_field_representation bounded_by Fp2_field_representation Fp2_repr_inst].
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      cbv [bin_outbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation] in Hbound0, Hbound1, Hbound2.
      destruct Hbound0 as [Hb0a Hb0b]. destruct Hbound1 as [Hb1a Hb1b]. destruct Hbound2 as [Hb2a Hb2b].
      repeat split;
        first [ apply (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok); assumption
              | assumption ]. }
    (* sep *)
    { destruct Hkeep as [m_oc0 [m_kr1 [[Heq_k1 Hd_k1] [Hoc0 Hkr1]]]].
      destruct Hkr1 as [m_oc1 [m_kr2 [[Heq_k2 Hd_k2] [Hoc1 Hkr2]]]].
      destruct Hkr2 as [m_oc2 [m_kr3 [[Heq_k3 Hd_k3] [Hoc2 Hkr3]]]].
      destruct Hkr3 as [m_s' [m_rr' [[Heq_k4 Hd_k4] [Hs' Hrr']]]].
      subst m_kr1 m_kr2 m_kr3 m_keep.
      repeat match goal with
      | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
          let H1 := fresh "Hd" in let H2 := fresh "Hd" in
          destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
      end.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc0) as Hlen_oc0.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc1) as Hlen_oc1.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc2) as Hlen_oc2.
      (* Join output Fp2 -> Fp6 *)
      assert (Hjoin_out : (FElem_Fp2 p out0' ⋆
        (FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
         FElem_Fp2 (word.add p (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2'))
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))).
      { exists m_oc0, (map.putmany m_oc1 m_oc2).
        split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact Hoc0 |].
        exists m_oc1, m_oc2. split; [split; [reflexivity | map_disjoint_auto_mul] |].
        split; [exact Hoc1 | exact Hoc2]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix p out0' out1' out2'
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)) Hlen_oc0 Hlen_oc1 Hlen_oc2 Hjoin_out) as Hfp6_out.
      (* Build final sep *)
      exists (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)),
             (map.putmany m_s' m_rr').
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { map_disjoint_auto_mul. }
      split; [exact Hfp6_out |].
      exists m_s', m_rr'.
      split; [split; [reflexivity | map_disjoint_auto_mul] |].
      split; [exact Hs' | exact Hrr']. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_frobenius: raise Fp6 element to p-th power                   *)
  (*   conj(c0) + conj(c1)*gamma1*v + conj(c2)*gamma2*v^2            *)
  (*   Extra args: gamma1, gamma2 (pointers to Fp2 constants)         *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_frobenius : function_t :=
    (fp6_frobenius_name, (["out"; "x"; "gamma1"; "gamma2"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as tmp;
      (* tmp.c0 = conj(x.c0) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c0 (expr.var "tmp"); expr_fp6_c0 (expr.var "x")]);
      (* tmp.c1 = conj(x.c1) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c1 (expr.var "tmp"); expr_fp6_c1 (expr.var "x")]);
      (* tmp.c2 = conj(x.c2) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c2 (expr.var "tmp"); expr_fp6_c2 (expr.var "x")]);
      (* out.c0 = tmp.c0 (just conjugation, no gamma) *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "tmp")]);
      (* out.c1 = conj(c1) * gamma1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "tmp"); expr.var "gamma1"]);
      (* out.c2 = conj(c2) * gamma2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "tmp"); expr.var "gamma2"])
    ))).

  (* Gallina model for Fp6 Frobenius: conj(c0) + conj(c1)*gamma1*v + conj(c2)*gamma2*v^2 *)
  Local Definition fp2_conj (x : Fp2) : Fp2 := (fst x, @F.opp M_pos (snd x)).

  Local Definition fp6_frobenius_model (gamma1 gamma2 : Fp2) (x : Fp6) : Fp6 :=
    let c0 := fst (fst x) in let c1 := snd (fst x) in let c2 := snd x in
    ((fp2_conj c0,
      @AbstractField.Fmul _ Fp2_fp_inst (fp2_conj c1) gamma1),
     @AbstractField.Fmul _ Fp2_fp_inst (fp2_conj c2) gamma2).

  Instance spec_of_Fp6_frobenius : spec_of fp6_frobenius_name :=
    fnspec! fp6_frobenius_name (pout px pgamma1 pgamma2 : word)
      / (old_out x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (gamma1 gamma2 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2 /\
        (FElem_Fp6 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp6 pout old_out ⋆ Rr)))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_frobenius_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2)
            (Fp6_feval x) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ (FElem_Fp6 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆ Rr)))) mem' }.

  Lemma Fp6_frobenius_ok :
    forall functions
      (EnvContains : map.get functions fp6_frobenius_name = Some (snd Fp6_frobenius))
      (HFconj : spec_of_Fp2_conjugate functions)
      (HFcopy : spec_of_Fp2_felem_copy functions)
      (HFmul : spec_of_Fp2_mul functions),
    spec_of_Fp6_frobenius functions.
  Proof.
    intros functions EnvContains HFconj HFcopy HFmul.
    unfold spec_of_Fp6_frobenius.
    intros pout px pgamma1 pgamma2 old_out x gamma1 gamma2 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 Hmem_all]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_frobenius].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc tmp === *)
    split. { apply Z_mod_mult. }
    intros a_tmp mStack mCombined HstackTmp Hm_split.
    (* Convert anybytes to Fp6 FElem *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
      word_ok mem_ok a_tmp) as Hfb_tmp.
    unfold AbstractField.Placeholder in Hfb_tmp.
    pose proof (proj1 (Hfb_tmp mStack) HstackTmp) as [tmp_val Htmp_felem]. clear Hfb_tmp.
    (* Decompose precondition sep *)
    destruct Hmem_all as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]].
    destruct Hr1 as [m_g1 [m_r2 [[Heq1 Hd1] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq2 Hd2] [Hfg2 Hr3]]]].
    destruct Hr3 as [m_out [m_rr [[Heq3 Hd3] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 mem0.
    (* Split Fp6 FElems into Fp2 components *)
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix px x _ Hfx)
      as [m_x0 [m_x12 [Hsp_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsp_x12 [Hx1 Hx2]]]].
    destruct Hsp_x as [? Hdxx]. destruct Hsp_x12 as [? Hdxy]. subst.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix pout old_out _ Hfe_out)
      as [m_o0 [m_o12 [Hsp_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Ho1 Ho2]]]].
    destruct Hsp_o as [? Hdox]. destruct Hsp_o12 as [? Hdoy]. subst.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix a_tmp tmp_val _ Htmp_felem)
      as [m_t0 [m_t12 [Hsp_t [Ht0 Ht12]]]].
    destruct Ht12 as [m_t1 [m_t2 [Hsp_t12 [Ht1 Ht2]]]].
    destruct Hsp_t as [? Hdtx]. destruct Hsp_t12 as [? Hdty]. subst.
    change FElem with FElem_Fp2 in Hx0, Hx1, Hx2, Ho0, Ho1, Ho2, Ht0, Ht1, Ht2.
    (* Decompose Fp6 bounded_by into 3 Fp2 bounded_by *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Derive all pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
    end.
    destruct Hm_split as [Heq_comb Hd_comb].
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
    end.
    (* Flatten mCombined into right-associated putmany *)
    rewrite !map.putmany_assoc in Heq_comb.
    (* Build 12-way sep on mCombined:
       x0, x1, x2, g1, g2, o0, o1, o2, rr, t0, t1, t2
       matching the order in Heq_comb *)
    assert (Hsep :
      (FElem_Fp2 px (c0_felem x) ⋆
       (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
        (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆
         (FElem_Fp2 pgamma1 gamma1 ⋆
          (FElem_Fp2 pgamma2 gamma2 ⋆
           (FElem_Fp2 pout (c0_felem old_out) ⋆
            (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem old_out) ⋆
             (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem old_out) ⋆
              (Rr ⋆
               (FElem_Fp2 a_tmp (c0_felem tmp_val) ⋆
                (FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem tmp_val) ⋆
                 FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem tmp_val))))))))))))
      mCombined).
    { subst mCombined.
      rewrite <- ?map.putmany_assoc.
      exists m_x0, (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2)))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx0 |].
      exists m_x1, (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx1 |].
      exists m_x2, (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2)))))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx2 |].
      exists m_g1, (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2))))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfg1 |].
      exists m_g2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2)))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfg2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho0 |].
      exists m_o1, (map.putmany m_o2 (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2)))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho1 |].
      exists m_o2, (map.putmany m_rr (map.putmany m_t0 (map.putmany m_t1 m_t2))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho2 |].
      exists m_rr, (map.putmany m_t0 (map.putmany m_t1 m_t2)).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hrr |].
      exists m_t0, (map.putmany m_t1 m_t2).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ht0 |].
      exists m_t1, m_t2.
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ht1 | exact Ht2]. }
    (* === Call 1: conjugate(tmp.c0, x.c0) === *)
    repeat straightline.
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { unfold spec_of_Fp2_conjugate in HFconj.
         eapply (HFconj a_tmp px (c0_felem tmp_val) (c0_felem x) _ tr).
         split; [exact Hbx0 |].
         pose proof Hsep as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [conj0 [Hfeval_c0 [Hbound_c0 Hsep1]]]]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: conjugate(tmp.c1, x.c1) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFconj
           (word.add a_tmp (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           (c1_felem tmp_val) (c1_felem x) _ tr).
         split; [exact Hbx1 |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [conj1 [Hfeval_c1 [Hbound_c1 Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: conjugate(tmp.c2, x.c2) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFconj
           (word.add a_tmp (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (c2_felem tmp_val) (c2_felem x) _ tr).
         split; [exact Hbx2 |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [conj2 [Hfeval_c2 [Hbound_c2 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: copy(out.c0, tmp.c0) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { eapply (HFcopy pout a_tmp (c0_felem old_out) conj0 _ _ tr).
         split.
         { pose proof Hsep3 as H'. ecancel_assumption. }
         { pose proof Hsep3 as H'. ecancel_assumption. } }
    intros t4 m4 rets4 [Hrets4 [Htr4 Hsep4]].
    subst rets4. symmetry in Htr4. subst t4.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 5: mul(out.c1, tmp.c1, gamma1) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'.
         eapply (HFmul'
           (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           (word.add a_tmp (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
           pgamma1 (c1_felem old_out) conj1 gamma1 _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbound_c1 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbg1 |].
         split; [eexists; pose proof Hsep4 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep4 as H'; ecancel_assumption |].
         pose proof Hsep4 as H'. ecancel_assumption. }
    intros t5 m5 rets5 [Hrets5 [Htr5 [out1' [Hfeval1 [Hbound1 Hsep5]]]]].
    subst rets5. symmetry in Htr5. subst t5.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 6: mul(out.c2, tmp.c2, gamma2) === *)
    eexists. split.
    { repeat match goal with v := map.put _ _ _ |- _ => subst v end;
      cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body];
      repeat first
        [ exact eq_refl
        | eexists; split;
          [ repeat (first [ apply map.get_put_same
                          | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
        | straightline ]. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul''.
         unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul''.
         eapply (HFmul''
           (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (word.add a_tmp (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           pgamma2 (c2_felem old_out) conj2 gamma2 _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbound_c2 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation];
                 exact Hbg2 |].
         split; [eexists; pose proof Hsep5 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep5 as H'; ecancel_assumption |].
         pose proof Hsep5 as H'. ecancel_assumption. }
    intros t6 m6 rets6 [Hrets6 [Htr6 [out2' [Hfeval2 [Hbound2 Hsep6]]]]].
    subst rets6. symmetry in Htr6. subst t6.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1" => pgamma1; "gamma2" => pgamma2; "tmp" => a_tmp }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Stack deallocation + Final postcondition === *)
    (* Extract FElem lengths for conj0, out1', out2' from the seps. *)
    assert (Hlen_conj0 : Datatypes.length conj0 = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep1 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out1 : Datatypes.length out1' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep5 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    assert (Hlen_out2 : Datatypes.length out2' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { destruct Hsep6 as [mc [_ [_ [Hfc _]]]]. exact (Fp2_FElem_length beta fp2_prefix _ _ _ Hfc). }
    (* === Stack deallocation === *)
    (* Separate tmp Fp2 FElems from the rest using ecancel *)
    assert (Hsep_split :
      (FElem_Fp2 a_tmp conj0 ⋆
       (FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) conj1 ⋆
        (FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) conj2 ⋆
         (FElem_Fp2 pout conj0 ⋆
          (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
           (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2' ⋆
            (FElem_Fp2 px (c0_felem x) ⋆
             (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
              (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆
               (FElem_Fp2 pgamma1 gamma1 ⋆
                (FElem_Fp2 pgamma2 gamma2 ⋆ Rr))))))))))) m6).
    { pose proof Hsep6 as H'. ecancel_assumption. }
    (* Destructure to get the 3 tmp maps and the rest *)
    destruct Hsep_split as [m_tc0 [m_r1 [[Heq_s1 Hd_s1] [Htc0 Hr1]]]].
    destruct Hr1 as [m_tc1 [m_r2 [[Heq_s2 Hd_s2] [Htc1 Hr2]]]].
    destruct Hr2 as [m_tc2 [m_keep [[Heq_s3 Hd_s3] [Htc2 Hkeep]]]].
    subst m_r1 m_r2 m6.
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
    end.
    (* Join tmp FElems back to Fp6 and convert to anybytes *)
    assert (Hjoin_tmp : (FElem_Fp2 a_tmp conj0 ⋆
      (FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) conj1 ⋆
       FElem_Fp2 (word.add a_tmp (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) conj2))
      (map.putmany m_tc0 (map.putmany m_tc1 m_tc2))).
    { exists m_tc0, (map.putmany m_tc1 m_tc2).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Htc0 |].
      exists m_tc1, m_tc2. split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Htc1 | exact Htc2]. }
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Htc0) as Hlen_tc0.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Htc1) as Hlen_tc1.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Htc2) as Hlen_tc2.
    pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix a_tmp conj0 conj1 conj2
      (map.putmany m_tc0 (map.putmany m_tc1 m_tc2))
      Hlen_tc0 Hlen_tc1 Hlen_tc2 Hjoin_tmp) as Hfp6_tmp.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst a_tmp (conj0 ++ conj1 ++ conj2)
      (map.putmany m_tc0 (map.putmany m_tc1 m_tc2)) Hfp6_tmp) as Hanybytes_tmp.
    unfold AbstractField.Placeholder in Hanybytes_tmp.
    (* Provide stackalloc witnesses *)
    exists m_keep, (map.putmany m_tc0 (map.putmany m_tc1 m_tc2)).
    split. { exact Hanybytes_tmp. }
    split. { split.
      { (* mCombined' = putmany m_tc0 (putmany m_tc1 (putmany m_tc2 m_keep))
           = putmany m_keep (putmany m_tc0 (putmany m_tc1 m_tc2)) *)
        rewrite (map.putmany_assoc m_tc1 m_tc2 m_keep).
        rewrite (map.putmany_comm (map.putmany m_tc1 m_tc2) m_keep)
          by (apply map.disjoint_putmany_l; split; assumption).
        rewrite (map.putmany_assoc m_tc0 m_keep _).
        rewrite (map.putmany_comm m_tc0 m_keep) by assumption.
        rewrite <- (map.putmany_assoc m_keep m_tc0 _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. } split. { exact eq_refl. }
    exists (conj0 ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (conj0 ++ out1' ++ out2') = conj0).
    { unfold c0_felem. rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_conj0. }
    assert (Hc1_app : c1_felem (conj0 ++ out1' ++ out2') = out1').
    { unfold c1_felem, c0_felem in Hlen_conj0 |- *.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_conj0.
      rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_out1. }
    assert (Hc2_app : c2_felem (conj0 ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      unfold c0_felem in Hlen_conj0. fold n in Hlen_conj0, Hlen_out1.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_conj0.
      rewrite ListUtil.skipn_app_sharp by exact Hlen_out1. reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      (* conj0 is copy of conjugate output, so feval conj0 = feval of the conjugate
         Hfeval_c0 : feval conj0 = (fst (feval (c0_felem x)), F.opp (snd (feval (c0_felem x))))
         Hfeval1 : feval out1' = bin_model (feval conj1) (feval gamma1)
         Hfeval2 : feval out2' = bin_model (feval conj2) (feval gamma2) *)
      unfold fp6_frobenius_model, fp2_conj, AbstractField.Fmul.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd.
      rewrite Hfeval_c0, Hfeval1, Hfeval2, Hfeval_c1, Hfeval_c2.
      change (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        with (fun ws => (@AbstractField.feval _ _ _ _ _ _ F_representation (fst_felem ws),
                         @AbstractField.feval _ _ _ _ _ _ F_representation (snd_felem ws))).
      cbv beta. simpl fst. simpl snd.
      cbv [bin_model AbstractField.bin_mul].
      reflexivity. }
    (* bounded_by *)
    split.
    { cbv [Fp6_bounded Fp6_repr_inst Fp6_field_representation bounded_by Fp2_field_representation Fp2_repr_inst].
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      (* Hbound_c0 : loose conj0, Hbound1 : bin_outbounds out1', Hbound2 : bin_outbounds out2' *)
      change (@AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (fst_felem felem)
                     /\ @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (snd_felem felem)) in Hbound_c0.
      cbv beta in Hbound_c0. destruct Hbound_c0 as [Hbc0a Hbc0b].
      cbv [bin_outbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation] in Hbound1, Hbound2.
      destruct Hbound1 as [Hb1a Hb1b]. destruct Hbound2 as [Hb2a Hb2b].
      repeat split;
        first [ apply (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok); assumption
              | assumption ]. }
    (* sep: Hkeep already has the right form *)
    { (* Hkeep is the 9-way sep after removing tmp regions.
         Need to join pout FElems into Fp6 and px FElems into Fp6. *)
      destruct Hkeep as [m_oc0 [m_kr1 [[Heq_k1 Hd_k1] [Hoc0 Hkr1]]]].
      destruct Hkr1 as [m_oc1 [m_kr2 [[Heq_k2 Hd_k2] [Hoc1 Hkr2]]]].
      destruct Hkr2 as [m_oc2 [m_kr3 [[Heq_k3 Hd_k3] [Hoc2 Hkr3]]]].
      destruct Hkr3 as [m_xc0 [m_kr4 [[Heq_k4 Hd_k4] [Hxc0 Hkr4]]]].
      destruct Hkr4 as [m_xc1 [m_kr5 [[Heq_k5 Hd_k5] [Hxc1 Hkr5]]]].
      destruct Hkr5 as [m_xc2 [m_kr6 [[Heq_k6 Hd_k6] [Hxc2 Hkr6]]]].
      destruct Hkr6 as [m_g1' [m_kr7 [[Heq_k7 Hd_k7] [Hg1' Hkr7]]]].
      destruct Hkr7 as [m_g2' [m_rr' [[Heq_k8 Hd_k8] [Hg2' Hrr']]]].
      subst m_kr1 m_kr2 m_kr3 m_kr4 m_kr5 m_kr6 m_kr7 m_keep.
      repeat match goal with
      | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
          let H1 := fresh "Hd" in let H2 := fresh "Hd" in
          destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
      end.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc0) as Hlen_oc0.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc1) as Hlen_oc1.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hoc2) as Hlen_oc2.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc0) as Hlen_xc0.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc1) as Hlen_xc1.
      pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hxc2) as Hlen_xc2.
      (* Join output Fp2 → Fp6 *)
      assert (Hjoin_out : (FElem_Fp2 pout conj0 ⋆
        (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆
         FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2'))
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))).
      { exists m_oc0, (map.putmany m_oc1 m_oc2).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hoc0 |].
        exists m_oc1, m_oc2. split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hoc1 | exact Hoc2]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix pout conj0 out1' out2'
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)) Hlen_oc0 Hlen_oc1 Hlen_oc2 Hjoin_out) as Hfp6_out.
      (* Join input Fp2 → Fp6 *)
      assert (Hjoin_x : (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
         FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x)))
        (map.putmany m_xc0 (map.putmany m_xc1 m_xc2))).
      { exists m_xc0, (map.putmany m_xc1 m_xc2).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hxc0 |].
        exists m_xc1, m_xc2. split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hxc1 | exact Hxc2]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix px (c0_felem x) (c1_felem x) (c2_felem x)
        (map.putmany m_xc0 (map.putmany m_xc1 m_xc2)) Hlen_xc0 Hlen_xc1 Hlen_xc2 Hjoin_x) as Hfp6_x.
      rewrite Fp6_list_decomp in Hfp6_x.
      (* Build final sep *)
      exists (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)),
             (map.putmany (map.putmany m_xc0 (map.putmany m_xc1 m_xc2))
               (map.putmany m_g1' (map.putmany m_g2' m_rr'))).
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out |].
      exists (map.putmany m_xc0 (map.putmany m_xc1 m_xc2)),
             (map.putmany m_g1' (map.putmany m_g2' m_rr')).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp6_x |].
      exists m_g1', (map.putmany m_g2' m_rr').
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hg1' |].
      exists m_g2', m_rr'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hg2' | exact Hrr']. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_frobenius_p2: raise Fp6 element to p^2-th power              *)
  (*   c0 + c1*gamma1_p2*v + c2*gamma2_p2*v^2                        *)
  (*   (no conjugation since p^2 ≡ 1 mod 2 on Fp2)                   *)
  (*   Extra args: gamma1_p2, gamma2_p2 (pointers to Fp2 constants)   *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_frobenius_p2 : function_t :=
    (fp6_frobenius_p2_name, (["out"; "x"; "gamma1_p2"; "gamma2_p2"], []:list String.string, bedrock_func_body:(
      (* out.c0 = x.c0 (unchanged) *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x")]);
      (* out.c1 = x.c1 * gamma1_p2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x"); expr.var "gamma1_p2"]);
      (* out.c2 = x.c2 * gamma2_p2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x"); expr.var "gamma2_p2"])
    ))).

  (* Gallina model for Fp6 Frobenius p^2: c0 + c1*gamma1_p2*v + c2*gamma2_p2*v^2 *)
  Local Definition fp6_frobenius_p2_model (gamma1_p2 gamma2_p2 : Fp2) (x : Fp6) : Fp6 :=
    let c0 := fst (fst x) in let c1 := snd (fst x) in let c2 := snd x in
    ((c0, @AbstractField.Fmul _ Fp2_fp_inst c1 gamma1_p2),
     @AbstractField.Fmul _ Fp2_fp_inst c2 gamma2_p2).

  Instance spec_of_Fp6_frobenius_p2 : spec_of fp6_frobenius_p2_name :=
    fnspec! fp6_frobenius_p2_name (pout px pgamma1_p2 pgamma2_p2 : word)
      / (old_out x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (gamma1_p2 gamma2_p2 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2_p2 /\
        (FElem_Fp6 px x ⋆
         (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
          (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
           (FElem_Fp6 pout old_out ⋆ Rr)))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_frobenius_p2_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2_p2)
            (Fp6_feval x) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ (FElem_Fp6 px x ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆ Rr)))) mem' }.

  (* Local tactics for map manipulation (copies of CubicFieldExtensions locals) *)
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

  Local Notation fp_felem_size := (@AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).

  (* Proof sketch for Fp6_frobenius_p2_ok:
     The function performs 1 Fp2 copy + 2 Fp2 mul calls, no stackalloc.
     Callee hypotheses: HFcopy : spec_of_Fp2_felem_copy, HFmul1/HFmul2 : spec_of_Fp2_mul.
     Proof structure (following Fp6_felem_copy_ok / Fp6_add_ok in CubicFieldExtensions.v):
     1. start_func, straightline, decompose big sep precondition into individual sub-maps
     2. Fp6_raw_FElem_split to decompose Fp6 x and old_out into 3 Fp2 FElems each
     3. Derive all pairwise disjointness between sub-maps
     4. Decompose Fp6 bounded_by into 3 Fp2 bounded_by; relax tight->loose via Fp2_bounds_loose_of_tight
     5. Call 1 (copy out.c0 := x.c0): dexprs + weaken_call + eapply HFcopy
        - Two-part copy precondition: build (FElem*FElem*R)mem and (FElem*Rout)mem via map rearrangement
     6. Build big sep for m' after copy (9-way: new0, x0..x2, g1, g2, o1, o2, rr)
     7. Call 2 (mul out.c1 := x.c1*gamma1_p2): dexprs + weaken_call + eapply HFmul1
        - Binop preconditions via ecancel_assumption on big sep
     8. Call 3 (mul out.c2 := x.c2*gamma2_p2): same pattern with HFmul2
     9. Final: exists (c0_felem x ++ out1' ++ out2')
        - feval: change Fp6_feval to 3 Fp2_fevals, rewrite c0/c1/c2_felem projections
        - bounded_by: change Fp6_bounded to 3 Fp2_bounded, apply Fp2_bounds_loose_of_tight
        - sep: Fp6_raw_FElem_join to reassemble 3 Fp2 FElems into Fp6 FElem
     Key lemmas: Fp6_raw_FElem_split/join, Fp2_FElem_length, Fp2_bounds_loose_of_tight,
       c0/c1/c2_felem_app, Fp6_list_decomp, ListUtil.firstn/skipn_app_sharp *)
  (* Fp2 FElem length extraction *)
  Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).

  Local Ltac map_swap a b :=
    rewrite (map.putmany_assoc a b);
    let D := fresh "D" in
    assert (D : map.disjoint a b) by map_disjoint_auto;
    rewrite (map.putmany_comm a b D);
    clear D;
    rewrite <- (map.putmany_assoc b a).

  Lemma Fp6_frobenius_p2_ok :
    forall functions
      (EnvContains : map.get functions fp6_frobenius_p2_name =
        Some (snd Fp6_frobenius_p2))
      (HFcopy : spec_of_Fp2_felem_copy functions)
      (HFmul : spec_of_Fp2_mul functions),
    spec_of_Fp6_frobenius_p2 functions.
  Proof.
    intros functions EnvContains HFcopy HFmul. unfold spec_of_Fp6_frobenius_p2.
    intros pout px pgamma1_p2 pgamma2_p2 old_out x gamma1_p2 gamma2_p2 Rr tr mem0 [Hbx [Hbg1 [Hbg2 Hmem_all]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_frobenius_p2]. eexists. split. { exact eq_refl. } repeat straightline.
    destruct Hmem_all as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]]. destruct Hr1 as [m_g1 [m_r2 [[Heq1 Hd1] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq2 Hd2] [Hfg2 Hr3]]]]. destruct Hr3 as [m_out [m_rr [[Heq3 Hd3] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 mem0.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix px x _ Hfx) as [m_x0 [m_x12 [Hsp_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsp_x12 [Hx1 Hx2]]]]. destruct Hsp_x as [? Hdxx]. destruct Hsp_x12 as [? Hdxy]. subst.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix pout old_out _ Hfe_out) as [m_o0 [m_o12 [Hsp_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Ho1 Ho2]]]]. destruct Hsp_o as [? Hdox]. destruct Hsp_o12 as [? Hdoy]. subst.
    rename Hd0 into Hd_xg. rename Hd1 into Hd_g1r. rename Hd2 into Hd_g2r. rename Hd3 into Hd_or. split_all_disjointness.
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx. fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]]. rewrite <- ?map.putmany_assoc.
    assert (Hsep9 : (FElem_Fp2 px (c0_felem x) ⋆ (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆ (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x) ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 pout (c0_felem old_out) ⋆ (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem old_out) ⋆ (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem old_out) ⋆ Rr)))))))) (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))))))).
    { exists m_x0, (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx0 |].
      exists m_x1, (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx1 |].
      exists m_x2, (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx2 |].
      exists m_g1, (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfg1 |].
      exists m_g2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfg2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2 m_rr)).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho0 |].
      exists m_o1, (map.putmany m_o2 m_rr). split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho1 |].
      exists m_o2, m_rr. split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho2 | exact Hrr]. }
    exists [pout; px]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply HFcopy. split. { pose proof Hsep9 as H'. ecancel_assumption. } { pose proof Hsep9 as H'. ecancel_assumption. } }
    intros t' m' rets [Hrets [Htr1 Hsep1]]. subst rets. symmetry in Htr1. subst t'. cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#). split. { exact eq_refl. } repeat straightline.
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul'. unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul'.
         eapply (HFmul' (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) pgamma1_p2 (c1_felem old_out) (c1_felem x) gamma1_p2 _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation]; apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix)); exact Hbx1 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation]; exact Hbg1 |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |]. pose proof Hsep1 as H'; ecancel_assumption. }
    intros t'' m'' rets2 [Hrets2 [Htr2 [out1' [Hfeval1 [Hbound1 Hsep2]]]]]. subst rets2. symmetry in Htr2. subst t''. cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#). split. { exact eq_refl. } repeat straightline.
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { pose proof HFmul as HFmul''. unfold spec_of_Fp2_mul, AbstractField.binop_spec in HFmul''.
         eapply (HFmul'' (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) pgamma2_p2 (c2_felem old_out) (c2_felem x) gamma2_p2 _ tr).
         split; [cbv [bin_xbounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation]; apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix)); exact Hbx2 |].
         split; [cbv [bin_ybounds AbstractField.bin_mul Fp2_repr_inst Fp2_field_representation]; exact Hbg2 |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |]. pose proof Hsep2 as H'; ecancel_assumption. }
    intros t''' m''' rets3 [Hrets3 [Htr3 [out2' [Hfeval2 [Hbound2 Hsep3]]]]]. subst rets3. symmetry in Htr3. subst t'''. cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. } cbv [list_map get]. split. { exact eq_refl. } split. { exact eq_refl. }
    destruct Hsep3 as [m_A [m_rest1 [[Heq_A HdA] [HA Hrest1]]]]. destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 HdB] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 HdC] [HC Hrest3]]]]. destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 HdD] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 HdE] [HE Hrest5]]]]. destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 HdFF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_RR [[Heq_r6 HdG] [HG HRR]]]]. subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m'''.
    repeat match goal with | H : map.disjoint ?a (map.putmany ?b ?c) |- _ => let H1 := fresh "Hd" in let H2 := fresh "Hd" in destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H end.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HA) as Hlen_A. pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HC) as Hlen_C. pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HE) as Hlen_E. pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ HG) as Hlen_G.
    exists (c0_felem x ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (c0_felem x ++ out1' ++ out2') = c0_felem x).
    { unfold c0_felem. rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_C. }
    assert (Hc1_app : c1_felem (c0_felem x ++ out1' ++ out2') = out1').
    { unfold c1_felem, c0_felem in Hlen_C |- *. rewrite ListUtil.skipn_app_sharp by exact Hlen_C. rewrite ListUtil.firstn_app_sharp. reflexivity. exact Hlen_B. }
    assert (Hc2_app : c2_felem (c0_felem x ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * fp_felem_size)%nat). replace (2 * n)%nat with (n + n)%nat by lia. rewrite <- ListUtil.skipn_skipn. unfold c0_felem in Hlen_C. fold n in Hlen_C, Hlen_B. rewrite ListUtil.skipn_app_sharp by exact Hlen_C. rewrite ListUtil.skipn_app_sharp by exact Hlen_B. reflexivity. }
    split. { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws), @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)), @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))). cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app. rewrite Hfeval1, Hfeval2. unfold fp6_frobenius_p2_model.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x), @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)), @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd. unfold AbstractField.Fmul. simpl. reflexivity. }
    split. { cbv [Fp6_bounded Fp6_repr_inst Fp6_field_representation bounded_by Fp2_field_representation Fp2_repr_inst].
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      destruct Hbx0 as [Hbx0a Hbx0b]. destruct Hbound1 as [Hb1a Hb1b]. destruct Hbound2 as [Hb2a Hb2b].
      repeat split; first [apply (@relax_bounds _ _ _ _ _ _ F_representation F_representation_ok); assumption | assumption]. }
    { assert (Hjoin_out : (FElem_Fp2 pout (c0_felem x) ⋆ (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) out1' ⋆ FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) out2')) (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A). split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact HC |]. exists m_B, m_A. split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix pout (c0_felem x) out1' out2' (map.putmany m_C (map.putmany m_B m_A)) Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      assert (Hjoin_x : (FElem_Fp2 px (c0_felem x) ⋆ (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆ FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x))) (map.putmany m_D (map.putmany m_E m_FF))).
      { exists m_D, (map.putmany m_E m_FF). split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact HD |]. exists m_E, m_FF. split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact HE | exact HFF]. }
      pose proof (Fp6_raw_FElem_join beta xi_re xi_im fp6_prefix fp2_prefix px (c0_felem x) (c1_felem x) (c2_felem x) (map.putmany m_D (map.putmany m_E m_FF)) Hlen_D Hlen_E Hlen_FF Hjoin_x) as Hfp6_x.
      rewrite Fp6_list_decomp in Hfp6_x.
      exists (map.putmany m_C (map.putmany m_B m_A)), (map.putmany (map.putmany m_D (map.putmany m_E m_FF)) (map.putmany m_G m_RR)).
      split; [split |]. { rewrite <- !map.putmany_assoc. map_swap m_A m_B. map_swap m_A m_C. map_swap m_B m_C. reflexivity. } { map_disjoint_auto. }
      split; [exact Hfp6_out |].
      exists (map.putmany m_D (map.putmany m_E m_FF)), (map.putmany m_G m_RR).
      split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfp6_x |].
      exists m_G, m_RR. split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact HG | exact HRR]. }
  Qed.
  (* Old Fp6_frobenius_p2 proof attempt removed. *)
  (* eapply_removed_start_func.
    cbv match beta delta [WeakestPrecondition.func Fp6_frobenius_p2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Decompose big sep into individual sub-maps *)
    destruct Hmem_all as [m_x [m_rest1 [[Heq_mem0 Hd_x_rest1] [Hfx Hrest1]]]].
    destruct Hrest1 as [m_g1 [m_rest2 [[Heq_rest1 Hd_g1_rest2] [Hfg1 Hrest2]]]].
    destruct Hrest2 as [m_g2 [m_rest3 [[Heq_rest2 Hd_g2_rest3] [Hfg2 Hrest3]]]].
    destruct Hrest3 as [m_out [m_rr [[Heq_rest3 Hd_out_rr] [Hfe_out Hrr_out]]]].
    subst m_rest1 m_rest2 m_rest3 mem0.
    (* Decompose Fp6 FElems into Fp2 components *)
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix px x m_x Hfx) as Hx_split.
    destruct Hx_split as [m_x0 [m_x12 [[Heq_x Hd_x012] [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [[Heq_x12 Hd_x12] [Hx1 Hx2]]]].
    subst m_x m_x12.
    pose proof (Fp6_raw_FElem_split beta xi_re xi_im fp6_prefix fp2_prefix pout old_out m_out Hfe_out) as Ho_split.
    destruct Ho_split as [m_o0 [m_o12 [[Heq_o Hd_o012] [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [[Heq_o12 Hd_o12] [Ho1 Ho2]]]].
    subst m_out m_o12.
    (* Decompose Fp6 bounded_by into Fp2 components *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    pose proof (Fp2_bounds_loose_of_tight fp2_prefix _ Hbx1) as Hbx1_loose.
    pose proof (Fp2_bounds_loose_of_tight fp2_prefix _ Hbx2) as Hbx2_loose.
    (* === Call 1: Fp2 copy (out.c0 := x.c0) === *)
    exists [pout; px]. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c0
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { unfold spec_of_Fp2_felem_copy, AbstractField.spec_of_felem_copy.
      eapply (HFcopy pout px (c0_felem old_out) (c0_felem x)
        (fun m => (FElem_Fp2 (word.add px (word.of_Z fp2_felem_offset)) (c1_felem x) ⋆
                   (FElem_Fp2 (word.add px (word.of_Z (2 * fp2_felem_offset))) (c2_felem x) ⋆
                    (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
                     (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
                      (FElem_Fp2 (word.add pout (word.of_Z fp2_felem_offset)) (c1_felem old_out) ⋆
                       (FElem_Fp2 (word.add pout (word.of_Z (2 * fp2_felem_offset))) (c2_felem old_out) ⋆ Rr)))))) m)
        (fun m => m = map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2
           (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))))
        tr).
      admit. (* split into two copy preconditions *) }
    (* Process copy postcondition *)
    intros t' m' rets [Hrets [Htr1 Hsep_post1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* Build big sep for m' after copy *)
    destruct Hsep_post1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    assert (Hsep_m' :
      (FElem_Fp2 pout (c0_felem x) ⋆
       (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px (word.of_Z fp2_felem_offset)) (c1_felem x) ⋆
         (FElem_Fp2 (word.add px (word.of_Z (2 * fp2_felem_offset))) (c2_felem x) ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 (word.add pout (word.of_Z fp2_felem_offset)) (c1_felem old_out) ⋆
             (FElem_Fp2 (word.add pout (word.of_Z (2 * fp2_felem_offset))) (c2_felem old_out) ⋆ Rr)))))))) m').
    { admit. (* build sep from individual FElems and disjointness *) }
    (* === Call 2: Fp2 mul (out.c1 := x.c1 * gamma1_p2) === *)
    eexists. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c1
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFmul1 (word.add pout (word.of_Z fp2_felem_offset))
                      (word.add px (word.of_Z fp2_felem_offset))
                      pgamma1_p2
                      (c1_felem old_out) (c1_felem x) gamma1_p2
                      _ tr).
      admit. (* mul1 preconditions *) }
    (* Process mul1 postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 [out1' [Hfeval1 [Hbound1 Hsep_post2]]]]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: Fp2 mul (out.c2 := x.c2 * gamma2_p2) === *)
    eexists. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { unfold spec_of_Fp2_mul, AbstractField.binop_spec.
      eapply (HFmul2 (word.add pout (word.of_Z (2 * fp2_felem_offset)))
                      (word.add px (word.of_Z (2 * fp2_felem_offset)))
                      pgamma2_p2
                      (c2_felem old_out) (c2_felem x) gamma2_p2
                      _ tr).
      split; [exact Hbx2_loose |].
      split; [exact Hbg2 |].
      split.
      { eexists. pose proof Hsep_post2 as H'. ecancel_assumption. }
      split.
      { eexists. pose proof Hsep_post2 as H'. ecancel_assumption. }
      pose proof Hsep_post2 as H'. ecancel_assumption. }
    (* Process mul2 postcondition *)
    intros t''' m''' rets3 [Hrets3 [Htr3 [out2' [Hfeval2 [Hbound2 Hsep_post3]]]]].
    subst rets3 t'''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* === Final: reconstruct Fp6 output === *)
    exists (c0_felem x ++ out1' ++ out2').
    pose proof (Fp2_FElem_length beta fp2_prefix _ _ _ Hnew0) as Hlen_n0.
    assert (Hlen_out1 : length out1' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { admit. (* extract from Hsep_post2 *) }
    assert (Hlen_out2 : length out2' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { admit. (* extract from Hsep_post3 *) }
    assert (Hc0_app : c0_felem (c0_felem x ++ out1' ++ out2') = c0_felem x).
    { unfold c0_felem. set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (c0_felem x ++ out1' ++ out2') = out1').
    { unfold c1_felem. set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length (c0_felem x) = length out1') by (rewrite Hlen_n0, Hlen_out1; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (c0_felem x ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length (c0_felem x) = length out1') by (rewrite Hlen_n0, Hlen_out1; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval1, Hfeval2.
      unfold fp6_frobenius_p2_model.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd.
      unfold AbstractField.Fmul. simpl.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [| split].
      - apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (@Fp2_field_representation_ok _ _ _ _ prime_parameters F_representation F_representation_ok beta fp2_prefix)). exact Hbx0.
      - apply (Fp2_bounds_loose_of_tight fp2_prefix). exact Hbound1.
      - apply (Fp2_bounds_loose_of_tight fp2_prefix). exact Hbound2. }
    (* sep: (FElem_Fp6 pout (c0_felem x ++ out1' ++ out2') * Rr) m''' *)
    { admit. }
  Admitted. *)

  (* -------------------------------------------------------------- *)
  (* fp12_frobenius: raise Fp12 element to p-th power                 *)
  (*   c0' = fp6_frobenius(c0)                                        *)
  (*   c1' = fp6_mul_fp2(fp6_frobenius(c1), w_frob_c1)               *)
  (*   Extra args: gamma1, gamma2, w_frob_c1                          *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_frobenius : function_t :=
    (fp12_frobenius_name, (["out"; "x"; "gamma1"; "gamma2"; "w_frob_c1"], []:list String.string, bedrock_func_body:(
      (* out.c0 = fp6_frobenius(x.c0) *)
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x"); expr.var "gamma1"; expr.var "gamma2"]);
      (* out.c1 = fp6_frobenius(x.c1) *)
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x"); expr.var "gamma1"; expr.var "gamma2"]);
      (* out.c1 = out.c1 * w_frob_c1 (scalar mul by Fp2) *)
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out"); expr.var "w_frob_c1"])
    ))).

  (* Gallina model for Fp12 Frobenius *)
  Local Definition fp12_frobenius_model (gamma1 gamma2 : Fp2) (w_frob_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_model gamma1 gamma2 c0,
     fp6_mul_fp2_model (fp6_frobenius_model gamma1 gamma2 c1) w_frob_c1).

  Instance spec_of_Fp12_frobenius : spec_of fp12_frobenius_name :=
    fnspec! fp12_frobenius_name (pout px pgamma1 pgamma2 pw_frob_c1 : word)
      / (old_out x : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        (gamma1 gamma2 w_frob_c1 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp12_bounded (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_c1 /\
        (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp12_feval out = fp12_frobenius_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_c1)
            (Fp12_feval x) /\
          Fp12_bounded (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) out /\
          (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆ (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ Rr))))) mem' }.

  Local Lemma Fp6_bounds_tight_of_loose : forall fe,
    Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) fe ->
    Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) fe.
  Proof.
    intros fe H. unfold Fp6_bounded, bounded_by, Fp6_field_representation, Fp6_repr_inst in *.
    simpl in *. destruct H as [[? ?] [[? ?] [? ?]]]. repeat split; apply bounds_equiv; assumption.
  Qed.

  Lemma Fp12_frobenius_ok :
    forall functions
      (EnvContains : map.get functions fp12_frobenius_name = Some (snd Fp12_frobenius))
      (EnvContains_mulfp2 : map.get functions fp6_mul_fp2_name = Some (snd Fp6_mul_fp2))
      (HFfrob : spec_of_Fp6_frobenius functions)
      (HFmulfp2 : spec_of_Fp6_mul_fp2 functions)
      (HFcopy2 : spec_of_Fp2_felem_copy functions)
      (HFmul2 : spec_of_Fp2_mul functions),
    spec_of_Fp12_frobenius functions.
  Proof.
    intros functions EnvContains EnvContains_mulfp2 HFfrob HFmulfp2 HFcopy2 HFmul2.
    unfold spec_of_Fp12_frobenius.
    intros pout px pgamma1 pgamma2 pw_frob_c1
      old_out x gamma1 gamma2 w_frob_c1 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 [Hbw Hmem_all]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_frobenius].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    destruct Hmem_all as [m_x [m_r1 [[Heq_m0 Hd_xr1] [Hfx Hr1]]]].
    destruct Hr1 as [m_g1 [m_r2 [[Heq_r1 Hd_g1r2] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq_r2 Hd_g2r3] [Hfg2 Hr3]]]].
    destruct Hr3 as [m_w [m_r4 [[Heq_r3 Hd_wr4] [Hfw Hr4]]]].
    destruct Hr4 as [m_out [m_rr [[Heq_r4 Hd_outrr] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 m_r4 mem0.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfx) as [m_x0 [m_x1 [[Heq_x Hd_x01] [Hx0 Hx1]]]].
    subst m_x.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfe_out) as [m_o0 [m_o1 [[Heq_o Hd_o01] [Ho0 Ho1]]]].
    subst m_out.
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
      (fun b fe => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem fe)
                /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem fe)) in Hbx.
    cbv beta in Hbx. destruct Hbx as [Hbx0 Hbx1].
    (* Derive pairwise disjointness *)
    split_all_disjointness.
    (* Flatten memory *)
    rewrite <- ?map.putmany_assoc.
    (* Build master sep at Fp6/Fp2 level *)
    assert (Hsep8 :
      (FElem_Fp6 px (d0_felem x) ⋆
       (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp2 pgamma1 gamma1 ⋆
         (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
           (FElem_Fp6 pout (d0_felem old_out) ⋆
            (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
             Rr)))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_g1 (map.putmany m_g2
        (map.putmany m_w (map.putmany m_o0 (map.putmany m_o1 m_rr)))))))).
    { build_sep. }
    (* Call 1: fp6_frobenius(out.c0, x.c0, g1, g2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob pout px pgamma1 pgamma2
           (d0_felem old_out) (d0_felem x) gamma1 gamma2 _ tr).
         split; [exact Hbx0 |]. split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep8 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: fp6_frobenius(out.c1, x.c1, g1, g2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob (word.add pout (word.of_Z fp6_felem_offset))
                        (word.add px (word.of_Z fp6_felem_offset))
                        pgamma1 pgamma2
           (d1_felem old_out) (d1_felem x) gamma1 gamma2 _ tr).
         split; [exact Hbx1 |]. split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1_frob [Hfeval1_frob [Hbound1_frob Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: fp6_mul_fp2(out.c1, out.c1, w) -- self-aliasing, use in-place variant *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (Fp6_mul_fp2_inplace functions EnvContains_mulfp2 HFcopy2 HFmul2
           (word.add pout (word.of_Z fp6_felem_offset))
           pw_frob_c1
           out1_frob w_frob_c1 _ tr m2).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound1_frob |].
         split; [exact Hbw |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out1 [Hfeval1 [Hbound1 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. } split. { exact eq_refl. }
    exists (out0 ++ out1).
    (* Get lengths for d0/d1_felem_app *)
    pose proof Hsep1 as Hsep1_copy.
    destruct Hsep1_copy as [m_out0' [m_restS1 [[HeqS1 HdS1] [Hout0_elem HrestS1]]]].
    assert (Hlen_out0 : Datatypes.length out0 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout0_elem.
      destruct Hout0_elem as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    pose proof Hsep3 as Hsep3_copy.
    destruct Hsep3_copy as [m_out1' [m_rest3 [[Heq3' Hd3'] [Hout1_elem Hrest3]]]].
    assert (Hlen_out1 : Datatypes.length out1 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout1_elem.
      destruct Hout1_elem as [? [? [? [[? Hlen''] ?]]]]. exact Hlen''. }
    assert (Hd0_app : d0_felem (out0 ++ out1) = out0).
    { unfold d0_felem. apply ListUtil.firstn_app_sharp. exact Hlen_out0. }
    assert (Hd1_app : d1_felem (out0 ++ out1) = out1).
    { unfold d1_felem. apply ListUtil.skipn_app_sharp. exact Hlen_out0. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                    @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws))).
      cbv beta. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval0, Hfeval1, Hfeval1_frob.
      unfold fp12_frobenius_model.
      change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x) with
        (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem x),
         @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem x)).
      cbv beta. simpl fst. simpl snd.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem)).
      cbv beta. rewrite Hd0_app, Hd1_app.
      split; assumption. }
    (* sep *)
    { (* Step 1: Assert intermediate sep at the Fp6 level *)
      assert (Hsep_flat :
        (FElem_Fp6 pout out0 ⋆ (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1 ⋆
         (FElem_Fp6 px (d0_felem x) ⋆ (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
          (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆ (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ Rr))))))) m3).
      { pose proof Hsep3 as H'. ecancel_assumption. }
      (* Step 2: Destructure to get memory fragments *)
      destruct Hsep_flat as [m_A [m_B1 [[Heq_flat HdA] [HA HB1]]]].
      destruct HB1 as [m_B [m_C1 [[Heq_B HdB] [HB HC1]]]].
      destruct HC1 as [m_C [m_D1 [[Heq_C HdC] [HC HD1]]]].
      destruct HD1 as [m_D [m_E1 [[Heq_D HdD] [HD HE1]]]].
      destruct HE1 as [m_E [m_F1 [[Heq_E HdE] [HE HF1]]]].
      destruct HF1 as [m_F [m_G1 [[Heq_F HdF] [HF HG1]]]].
      destruct HG1 as [m_G [m_H [[Heq_G HdG] [HG HH]]]].
      subst m_B1 m_C1 m_D1 m_E1 m_F1 m_G1.
      split_all_disjointness.
      (* Step 3: Build FElem_Fp12 facts *)
      assert (Hdecomp_x : x = d0_felem x ++ d1_felem x) by (symmetry; apply Fp12_list_decomp).
      (* FElem_Fp12 pout (out0 ++ out1) *)
      assert (Hjoin_out : (FElem_Fp6 pout out0 ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1) (map.putmany m_A m_B)).
      { exists m_A, m_B. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HA | exact HB]. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix pout out0 out1
        (map.putmany m_A m_B) Hlen_out0 Hlen_out1 Hjoin_out) as Hfp12_out.
      (* FElem_Fp12 px x *)
      assert (Hjoin_x : (FElem_Fp6 px (d0_felem x) ⋆
        FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x)) (map.putmany m_C m_D)).
      { exists m_C, m_D. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HC | exact HD]. }
      (* Get lengths for d0/d1_felem x *)
      assert (Hlen_d0x : Datatypes.length (d0_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HC as HC_copy. unfold AbstractField.FElem, Bignum.Bignum in HC_copy.
        destruct HC_copy as [? [? [? [[? Hlen_d0'] ?]]]]. exact Hlen_d0'. }
      assert (Hlen_d1x : Datatypes.length (d1_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HD as HD_copy. unfold AbstractField.FElem, Bignum.Bignum in HD_copy.
        destruct HD_copy as [? [? [? [[? Hlen_d1'] ?]]]]. exact Hlen_d1'. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix px (d0_felem x) (d1_felem x)
        (map.putmany m_C m_D) Hlen_d0x Hlen_d1x Hjoin_x) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      (* Step 4: Build final sep *)
      rewrite Heq_flat.
      exists (map.putmany m_A m_B),
             (map.putmany (map.putmany m_C m_D) (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H)))).
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_C m_D),
             (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_x |].
      exists m_E, (map.putmany m_F (map.putmany m_G m_H)).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HE |].
      exists m_F, (map.putmany m_G m_H).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HF |].
      exists m_G, m_H.
      split; [split; [reflexivity |] |].
      { exact HdG. }
      split; [exact HG | exact HH]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_frobenius_p2: raise Fp12 element to p^2-th power            *)
  (*   c0' = fp6_frobenius_p2(c0)                                     *)
  (*   c1' = fp6_mul_fp2(fp6_frobenius_p2(c1), w_frob_p2_c1)         *)
  (*   Extra args: gamma1_p2, gamma2_p2, w_frob_p2_c1                 *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_frobenius_p2 : function_t :=
    (fp12_frobenius_p2_name, (["out"; "x"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"], []:list String.string, bedrock_func_body:(
      (* out.c0 = fp6_frobenius_p2(x.c0) *)
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      (* out.c1 = fp6_frobenius_p2(x.c1) *)
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      (* out.c1 = out.c1 * w_frob_p2_c1 *)
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out"); expr.var "w_frob_p2_c1"])
    ))).

  Local Definition fp12_frobenius_p2_model (gamma1_p2 gamma2_p2 : Fp2) (w_frob_p2_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_p2_model gamma1_p2 gamma2_p2 c0,
     fp6_mul_fp2_model (fp6_frobenius_p2_model gamma1_p2 gamma2_p2 c1) w_frob_p2_c1).

  Instance spec_of_Fp12_frobenius_p2 : spec_of fp12_frobenius_p2_name :=
    fnspec! fp12_frobenius_p2_name (pout px pgamma1_p2 pgamma2_p2 pw_frob_p2_c1 : word)
      / (old_out x : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        (gamma1_p2 gamma2_p2 w_frob_p2_c1 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp12_bounded (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_p2_c1 /\
        (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
          (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp12_feval out = fp12_frobenius_p2_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_p2_c1)
            (Fp12_feval x) /\
          Fp12_bounded (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) out /\
          (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

  Lemma Fp12_frobenius_p2_ok :
    forall functions
      (EnvContains : map.get functions fp12_frobenius_p2_name = Some (snd Fp12_frobenius_p2))
      (EnvContains_mulfp2 : map.get functions fp6_mul_fp2_name = Some (snd Fp6_mul_fp2))
      (HFfrob : spec_of_Fp6_frobenius_p2 functions)
      (HFmulfp2 : spec_of_Fp6_mul_fp2 functions)
      (HFcopy2 : spec_of_Fp2_felem_copy functions)
      (HFmul2 : spec_of_Fp2_mul functions),
    spec_of_Fp12_frobenius_p2 functions.
  Proof.
    intros functions EnvContains EnvContains_mulfp2 HFfrob HFmulfp2 HFcopy2 HFmul2.
    unfold spec_of_Fp12_frobenius_p2.
    intros pout px pgamma1_p2 pgamma2_p2 pw_frob_p2_c1
      old_out x gamma1_p2 gamma2_p2 w_frob_p2_c1 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 [Hbw Hmem_all]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_frobenius_p2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    destruct Hmem_all as [m_x [m_r1 [[Heq_m0 Hd_xr1] [Hfx Hr1]]]].
    destruct Hr1 as [m_g1 [m_r2 [[Heq_r1 Hd_g1r2] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq_r2 Hd_g2r3] [Hfg2 Hr3]]]].
    destruct Hr3 as [m_w [m_r4 [[Heq_r3 Hd_wr4] [Hfw Hr4]]]].
    destruct Hr4 as [m_out [m_rr [[Heq_r4 Hd_outrr] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 m_r4 mem0.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfx) as [m_x0 [m_x1 [[Heq_x Hd_x01] [Hx0 Hx1]]]].
    subst m_x.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfe_out) as [m_o0 [m_o1 [[Heq_o Hd_o01] [Ho0 Ho1]]]].
    subst m_out.
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
      (fun b fe => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem fe)
                /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem fe)) in Hbx.
    cbv beta in Hbx. destruct Hbx as [Hbx0 Hbx1].
    (* Derive pairwise disjointness *)
    split_all_disjointness.
    (* Flatten memory *)
    rewrite <- ?map.putmany_assoc.
    (* Build master sep at Fp6/Fp2 level *)
    assert (Hsep8 :
      (FElem_Fp6 px (d0_felem x) ⋆
       (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
         (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
          (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
           (FElem_Fp6 pout (d0_felem old_out) ⋆
            (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
             Rr)))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_g1 (map.putmany m_g2
        (map.putmany m_w (map.putmany m_o0 (map.putmany m_o1 m_rr)))))))).
    { build_sep. }
    (* Call 1: fp6_frobenius_p2(out.c0, x.c0, g1, g2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob pout px pgamma1_p2 pgamma2_p2
           (d0_felem old_out) (d0_felem x) gamma1_p2 gamma2_p2 _ tr).
         split; [exact Hbx0 |]. split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep8 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: fp6_frobenius_p2(out.c1, x.c1, g1, g2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob (word.add pout (word.of_Z fp6_felem_offset))
                        (word.add px (word.of_Z fp6_felem_offset))
                        pgamma1_p2 pgamma2_p2
           (d1_felem old_out) (d1_felem x) gamma1_p2 gamma2_p2 _ tr).
         split; [exact Hbx1 |]. split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1_frob [Hfeval1_frob [Hbound1_frob Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: fp6_mul_fp2(out.c1, out.c1, w) -- self-aliasing, use in-place variant *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (Fp6_mul_fp2_inplace functions EnvContains_mulfp2 HFcopy2 HFmul2
           (word.add pout (word.of_Z fp6_felem_offset))
           pw_frob_p2_c1
           out1_frob w_frob_p2_c1 _ tr m2).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound1_frob |].
         split; [exact Hbw |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [out1 [Hfeval1 [Hbound1 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. } split. { exact eq_refl. }
    exists (out0 ++ out1).
    (* Get lengths for d0/d1_felem_app using COPIES *)
    pose proof Hsep1 as Hsep1_copy.
    destruct Hsep1_copy as [m_out0' [m_restS1 [[HeqS1 HdS1] [Hout0_elem HrestS1]]]].
    assert (Hlen_out0 : Datatypes.length out0 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout0_elem.
      destruct Hout0_elem as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    pose proof Hsep3 as Hsep3_copy.
    destruct Hsep3_copy as [m_out1' [m_rest3 [[Heq3' Hd3'] [Hout1_elem Hrest3]]]].
    assert (Hlen_out1 : Datatypes.length out1 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout1_elem.
      destruct Hout1_elem as [? [? [? [[? Hlen''] ?]]]]. exact Hlen''. }
    assert (Hd0_app : d0_felem (out0 ++ out1) = out0).
    { unfold d0_felem. apply ListUtil.firstn_app_sharp. exact Hlen_out0. }
    assert (Hd1_app : d1_felem (out0 ++ out1) = out1).
    { unfold d1_felem. apply ListUtil.skipn_app_sharp. exact Hlen_out0. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                    @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws))).
      cbv beta. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval0, Hfeval1, Hfeval1_frob.
      unfold fp12_frobenius_p2_model.
      change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x) with
        (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem x),
         @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem x)).
      cbv beta. simpl fst. simpl snd.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem)).
      cbv beta. rewrite Hd0_app, Hd1_app.
      split; assumption. }
    (* sep *)
    { (* Step 1: Assert intermediate sep at the Fp6 level *)
      assert (Hsep_flat :
        (FElem_Fp6 pout out0 ⋆ (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1 ⋆
         (FElem_Fp6 px (d0_felem x) ⋆ (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))))) m3).
      { pose proof Hsep3 as H'. ecancel_assumption. }
      (* Step 2: Destructure to get memory fragments *)
      destruct Hsep_flat as [m_A [m_B1 [[Heq_flat HdA] [HA HB1]]]].
      destruct HB1 as [m_B [m_C1 [[Heq_B HdB] [HB HC1]]]].
      destruct HC1 as [m_C [m_D1 [[Heq_C HdC] [HC HD1]]]].
      destruct HD1 as [m_D [m_E1 [[Heq_D HdD] [HD HE1]]]].
      destruct HE1 as [m_E [m_F1 [[Heq_E HdE] [HE HF1]]]].
      destruct HF1 as [m_F [m_G1 [[Heq_F HdF] [HF HG1]]]].
      destruct HG1 as [m_G [m_H [[Heq_G HdG] [HG HH]]]].
      subst m_B1 m_C1 m_D1 m_E1 m_F1 m_G1.
      split_all_disjointness.
      (* Step 3: Build FElem_Fp12 facts *)
      assert (Hdecomp_x : x = d0_felem x ++ d1_felem x) by (symmetry; apply Fp12_list_decomp).
      (* FElem_Fp12 pout (out0 ++ out1) *)
      assert (Hjoin_out : (FElem_Fp6 pout out0 ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1) (map.putmany m_A m_B)).
      { exists m_A, m_B. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HA | exact HB]. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix pout out0 out1
        (map.putmany m_A m_B) Hlen_out0 Hlen_out1 Hjoin_out) as Hfp12_out.
      (* FElem_Fp12 px x *)
      assert (Hjoin_x : (FElem_Fp6 px (d0_felem x) ⋆
        FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x)) (map.putmany m_C m_D)).
      { exists m_C, m_D. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HC | exact HD]. }
      (* Get lengths for d0/d1_felem x *)
      assert (Hlen_d0x : Datatypes.length (d0_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HC as HC_copy. unfold AbstractField.FElem, Bignum.Bignum in HC_copy.
        destruct HC_copy as [? [? [? [[? Hlen_d0'] ?]]]]. exact Hlen_d0'. }
      assert (Hlen_d1x : Datatypes.length (d1_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HD as HD_copy. unfold AbstractField.FElem, Bignum.Bignum in HD_copy.
        destruct HD_copy as [? [? [? [[? Hlen_d1'] ?]]]]. exact Hlen_d1'. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix px (d0_felem x) (d1_felem x)
        (map.putmany m_C m_D) Hlen_d0x Hlen_d1x Hjoin_x) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      (* Step 4: Build final sep *)
      rewrite Heq_flat.
      exists (map.putmany m_A m_B),
             (map.putmany (map.putmany m_C m_D) (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H)))).
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_C m_D),
             (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_x |].
      exists m_E, (map.putmany m_F (map.putmany m_G m_H)).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HE |].
      exists m_F, (map.putmany m_G m_H).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HF |].
      exists m_G, m_H.
      split; [split; [reflexivity |] |].
      { exact HdG. }
      split; [exact HG | exact HH]. }
  Qed.


  (* -------------------------------------------------------------- *)
  (* fp12_frobenius_p3: raise Fp12 element to p^3-th power            *)
  (*   Composes frobenius_p2 then frobenius:                           *)
  (*     temp = frobenius_p2(x)                                        *)
  (*     out  = frobenius(temp)                                        *)
  (*   Extra args: gamma1, gamma2, gamma1_p2, gamma2_p2,               *)
  (*               w_frob_c1, w_frob_p2_c1                             *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_frobenius_p3 : function_t :=
    (fp12_frobenius_p3_name, (["out"; "x"; "gamma1"; "gamma2"; "gamma1_p2"; "gamma2_p2"; "w_frob_c1"; "w_frob_p2_c1"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c0 (expr.var "tmp"); expr_fp12_c0 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c1 (expr.var "tmp"); expr_fp12_c1 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "tmp"); expr_fp12_c1 (expr.var "tmp"); expr.var "w_frob_p2_c1"]);
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "tmp"); expr.var "gamma1"; expr.var "gamma2"]);
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "tmp"); expr.var "gamma1"; expr.var "gamma2"]);
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out"); expr.var "w_frob_c1"])
    ))).

  (* Gallina model for Fp12 Frobenius cubed: frobenius(frobenius_p2(x)) *)
  Local Definition fp12_frobenius_p3_model
    (gamma1 gamma2 : Fp2) (gamma1_p2 gamma2_p2 : Fp2)
    (w_frob_c1 w_frob_p2_c1 : Fp2) (x : Fp12) : Fp12 :=
    fp12_frobenius_model gamma1 gamma2 w_frob_c1
      (fp12_frobenius_p2_model gamma1_p2 gamma2_p2 w_frob_p2_c1 x).

  Instance spec_of_Fp12_frobenius_p3 : spec_of fp12_frobenius_p3_name :=
    fnspec! fp12_frobenius_p3_name (pout px pgamma1 pgamma2 pgamma1_p2 pgamma2_p2 pw_frob_c1 pw_frob_p2_c1 : word)
      / (old_out x : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        (gamma1 gamma2 gamma1_p2 gamma2_p2 w_frob_c1 w_frob_p2_c1 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp12_bounded (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_c1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_p2_c1 /\
        (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr)))))))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp12_feval out = fp12_frobenius_p3_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_c1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_p2_c1)
            (Fp12_feval x) /\
          Fp12_bounded (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) out /\
          (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
            (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
              (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr)))))))) mem' }.

  Lemma Fp12_frobenius_p3_ok :
    forall functions
      (EnvContains : map.get functions fp12_frobenius_p3_name = Some (snd Fp12_frobenius_p3))
      (EnvContains_mulfp2 : map.get functions fp6_mul_fp2_name = Some (snd Fp6_mul_fp2))
      (HFfrob6 : spec_of_Fp6_frobenius functions)
      (HFfrob6_p2 : spec_of_Fp6_frobenius_p2 functions)
      (HFmulfp2 : spec_of_Fp6_mul_fp2 functions)
      (HFcopy2 : spec_of_Fp2_felem_copy functions)
      (HFmul2 : spec_of_Fp2_mul functions),
    spec_of_Fp12_frobenius_p3 functions.
  Proof.
    intros functions EnvContains EnvContains_mulfp2
      HFfrob6 HFfrob6_p2 HFmulfp2 HFcopy2 HFmul2.
    unfold spec_of_Fp12_frobenius_p3.
    intros pout px pgamma1 pgamma2 pgamma1_p2 pgamma2_p2 pw_frob_c1 pw_frob_p2_c1
      old_out x gamma1 gamma2 gamma1_p2 gamma2_p2 w_frob_c1 w_frob_p2_c1 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 [Hbg1p2 [Hbg2p2 [Hbwf [Hbwfp2 Hmem_all]]]]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_frobenius_p3 expr_fp12_c0 expr_fp12_c1].
    eexists. split. { exact eq_refl. }
    (* Decompose Fp12 FElems into Fp6 halves — same as Fp12_frobenius_ok *)
    destruct Hmem_all as [m_x [m_r1 [[Heq_m0 Hd_xr1] [Hfx Hr1]]]].
    destruct Hr1 as [m_g1 [m_r2 [[Heq_r1 Hd_g1r2] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq_r2 Hd_g2r3] [Hfg2 Hr3]]]].
    destruct Hr3 as [m_g1p2 [m_r4 [[Heq_r3 Hd_g1p2r4] [Hfg1p2 Hr4]]]].
    destruct Hr4 as [m_g2p2 [m_r5 [[Heq_r4 Hd_g2p2r5] [Hfg2p2 Hr5]]]].
    destruct Hr5 as [m_wf [m_r6 [[Heq_r5 Hd_wfr6] [Hfwf Hr6]]]].
    destruct Hr6 as [m_wfp2 [m_r7 [[Heq_r6 Hd_wfp2r7] [Hfwfp2 Hr7]]]].
    destruct Hr7 as [m_out [m_rr [[Heq_r7 Hd_outrr] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 m_r4 m_r5 m_r6 m_r7 mem0.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfx) as [m_x0 [m_x1 [[Heq_x Hd_x01] [Hx0 Hx1]]]].
    subst m_x.
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hfe_out) as [m_o0 [m_o1 [[Heq_o Hd_o01] [Ho0 Ho1]]]].
    subst m_out.
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
      (fun b fe => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem fe)
                /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem fe)) in Hbx.
    cbv beta in Hbx. destruct Hbx as [Hbx0 Hbx1].
    split_all_disjointness.
    rewrite <- ?map.putmany_assoc.
    (* Build master sep at Fp6 level *)
    assert (Hsep10 :
      (FElem_Fp6 px (d0_felem x) ⋆
       (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp2 pgamma1 gamma1 ⋆
         (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
             (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp6 pout (d0_felem old_out) ⋆
               (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
                Rr))))))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_g1 (map.putmany m_g2
        (map.putmany m_g1p2 (map.putmany m_g2p2 (map.putmany m_wf (map.putmany m_wfp2
          (map.putmany m_o0 (map.putmany m_o1 m_rr))))))))))).
    { build_sep. }
    (* Process stackalloc + convert anybytes to FElem *)
    straightline. split. { apply Z_mod_mult. }
    intros a_tmp mSt mCt HaSt HmSt.
    assert (Hti_ex : exists ti, FElem_Fp12 a_tmp ti mSt).
    { pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) as Hconv.
      cbv [Lift1Prop.iff1 Placeholder] in Hconv.
      apply Hconv; [typeclasses eauto | typeclasses eauto | exact HaSt]. }
    destruct Hti_ex as [ti Hti].
    assert (Hsep_tmp :
      ((FElem_Fp6 px (d0_felem x) ⋆
        (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
         (FElem_Fp2 pgamma1 gamma1 ⋆
          (FElem_Fp2 pgamma2 gamma2 ⋆
           (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
              (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
               (FElem_Fp6 pout (d0_felem old_out) ⋆
                (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
                 Rr)))))))))) ⋆
       FElem_Fp12 a_tmp ti) mCt).
    { exists (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_g1 (map.putmany m_g2
        (map.putmany m_g1p2 (map.putmany m_g2p2 (map.putmany m_wf
          (map.putmany m_wfp2 (map.putmany m_o0 (map.putmany m_o1 m_rr)))))))))), mSt.
      exact (conj HmSt (conj Hsep10 Hti)). }
    (* Split tmp Fp12 into two Fp6 halves *)
    pose proof (Fp12_raw_FElem_split beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix _ _ _ Hti) as [m_t0 [m_t1 [[Heq_t Hd_t01] [Ht0 Ht1]]]].
    subst mSt.
    (* Flatten mCt *)
    destruct HmSt as [Heq_mCt Hd_mCt].
    rewrite Heq_mCt. rewrite <- !map.putmany_assoc.
    (* Derive disjointness for t0, t1 *)
    split_all_disjointness.
    (* Build master sep at Fp6/Fp2 level *)
    assert (Hsep12 :
      (FElem_Fp6 px (d0_felem x) ⋆
       (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp2 pgamma1 gamma1 ⋆
         (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
             (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp6 pout (d0_felem old_out) ⋆
               (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
                (Rr ⋆
                 (FElem_Fp6 a_tmp (d0_felem ti) ⋆
                  FElem_Fp6 (word.add a_tmp (word.of_Z fp6_felem_offset)) (d1_felem ti)))))))))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_g1 (map.putmany m_g2
        (map.putmany m_g1p2 (map.putmany m_g2p2 (map.putmany m_wf (map.putmany m_wfp2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_rr (map.putmany m_t0 m_t1))))))))))))).
    { build_sep. }
    (* Call 1: fp6_frobenius_p2(tmp.c0, x.c0, gamma1_p2, gamma2_p2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob6_p2 a_tmp px pgamma1_p2 pgamma2_p2
           (d0_felem ti) (d0_felem x) gamma1_p2 gamma2_p2 _ tr).
         split; [exact Hbx0 |]. split; [exact Hbg1p2 |]. split; [exact Hbg2p2 |].
         pose proof Hsep12 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [tmp0 [Hfeval_t0 [Hbound_t0 Hsep1]]]]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 2: fp6_frobenius_p2(tmp.c1, x.c1, gamma1_p2, gamma2_p2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob6_p2 (word.add a_tmp (word.of_Z fp6_felem_offset))
                             (word.add px (word.of_Z fp6_felem_offset))
                             pgamma1_p2 pgamma2_p2
           (d1_felem ti) (d1_felem x) gamma1_p2 gamma2_p2 _ tr).
         split; [exact Hbx1 |]. split; [exact Hbg1p2 |]. split; [exact Hbg2p2 |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [tmp1_frob [Hfeval_t1_frob [Hbound_t1_frob Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 3: fp6_mul_fp2(tmp.c1, tmp.c1, w_frob_p2_c1) — self-aliasing *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (Fp6_mul_fp2_inplace functions EnvContains_mulfp2 HFcopy2 HFmul2
           (word.add a_tmp (word.of_Z fp6_felem_offset))
           pw_frob_p2_c1
           tmp1_frob w_frob_p2_c1 _ tr m2).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound_t1_frob |].
         split; [exact Hbwfp2 |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    intros t3 m3 rets3 [Hrets3 [Htr3 [tmp1 [Hfeval_t1 [Hbound_t1 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 4: fp6_frobenius(out.c0, tmp.c0, gamma1, gamma2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob6 pout a_tmp pgamma1 pgamma2
           (d0_felem old_out) tmp0 gamma1 gamma2 _ tr).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound_t0 |].
         split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep3 as H'. ecancel_assumption. }
    intros t4 m4 rets4 [Hrets4 [Htr4 [out0 [Hfeval0 [Hbound0 Hsep4]]]]].
    subst rets4. symmetry in Htr4. subst t4.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 5: fp6_frobenius(out.c1, tmp.c1, gamma1, gamma2) *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFfrob6 (word.add pout (word.of_Z fp6_felem_offset))
                          (word.add a_tmp (word.of_Z fp6_felem_offset))
                          pgamma1 pgamma2
           (d1_felem old_out) tmp1 gamma1 gamma2 _ tr).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound_t1 |].
         split; [exact Hbg1 |]. split; [exact Hbg2 |].
         pose proof Hsep4 as H'. ecancel_assumption. }
    intros t5 m5 rets5 [Hrets5 [Htr5 [out1_frob [Hfeval1_frob [Hbound1_frob Hsep5]]]]].
    subst rets5. symmetry in Htr5. subst t5.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Call 6: fp6_mul_fp2(out.c1, out.c1, w_frob_c1) — self-aliasing *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (Fp6_mul_fp2_inplace functions EnvContains_mulfp2 HFcopy2 HFmul2
           (word.add pout (word.of_Z fp6_felem_offset))
           pw_frob_c1
           out1_frob w_frob_c1 _ tr m5).
         split; [apply Fp6_bounds_tight_of_loose; exact Hbound1_frob |].
         split; [exact Hbwf |].
         pose proof Hsep5 as H'. ecancel_assumption. }
    intros t6 m6 rets6 [Hrets6 [Htr6 [out1 [Hfeval1 [Hbound1 Hsep6]]]]].
    subst rets6. symmetry in Htr6. subst t6.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    (* === Stack dealloc + final postcondition === *)
    (* Reorder sep to isolate stack tmp FElems *)
    assert (Hsep_split :
      ((FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1 ⋆
        (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
         (FElem_Fp2 pgamma1 gamma1 ⋆
          (FElem_Fp2 pgamma2 gamma2 ⋆
           (FElem_Fp6 pout out0 ⋆
            (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
             (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
              (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
                (FElem_Fp6 px (d0_felem x) ⋆ Rr)))))))))) ⋆
       (FElem_Fp6 a_tmp tmp0 ⋆ FElem_Fp6 (word.add a_tmp (word.of_Z fp6_felem_offset)) tmp1))
      m6).
    { pose proof Hsep6 as H'. ecancel_assumption. }
    destruct Hsep_split as [m_rest [m_stack [[Heq_m6 Hd_rs] [Hrest Hstack]]]].
    destruct Hstack as [m_st0 [m_st1 [[Heq_st Hd_st] [Hst0 Hst1]]]].
    subst m_stack.
    (* Get lengths for Fp12 join *)
    assert (Hlen_tmp0 : Datatypes.length tmp0 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hst0.
      destruct Hst0 as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    assert (Hlen_tmp1 : Datatypes.length tmp1 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hst1.
      destruct Hst1 as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    (* Join into Fp12 FElem and convert to anybytes *)
    assert (Hjoin_tmp : (FElem_Fp6 a_tmp tmp0 ⋆ FElem_Fp6 (word.add a_tmp (word.of_Z fp6_felem_offset)) tmp1) (map.putmany m_st0 m_st1)).
    { exists m_st0, m_st1. split; [split; [reflexivity | exact Hd_st] |]. split; [exact Hst0 | exact Hst1]. }
    pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix a_tmp tmp0 tmp1
      (map.putmany m_st0 m_st1) Hlen_tmp0 Hlen_tmp1 Hjoin_tmp) as Hfp12_tmp.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst a_tmp (tmp0 ++ tmp1) (map.putmany m_st0 m_st1) Hfp12_tmp) as Hanybytes_tmp.
    unfold AbstractField.Placeholder in Hanybytes_tmp.
    (* Provide stack dealloc witnesses *)
    exists m_rest, (map.putmany m_st0 m_st1).
    split. { exact Hanybytes_tmp. }
    split. { split. { exact Heq_m6. } { exact Hd_rs. } }
    (* list_map *)
    cbv [list_map get]. split. { exact eq_refl. } split. { exact eq_refl. }
    (* Provide Fp12 output *)
    exists (out0 ++ out1).
    (* Get output lengths *)
    pose proof Hrest as Hrest_copy.
    destruct Hrest_copy as [m_out1' [m_restR [[HeqR HdR] [Hout1_elem HrestR]]]].
    assert (Hlen_out1 : Datatypes.length out1 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout1_elem.
      destruct Hout1_elem as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    destruct HrestR as [m_wfc [m_restR2 [[HeqR2 HdR2] [Hwfc HrestR2]]]].
    destruct HrestR2 as [m_g1' [m_restR3 [[HeqR3 HdR3] [Hg1' HrestR3]]]].
    destruct HrestR3 as [m_g2' [m_restR4 [[HeqR4 HdR4] [Hg2' HrestR4]]]].
    destruct HrestR4 as [m_out0' [m_restR5 [[HeqR5 HdR5] [Hout0_elem HrestR5]]]].
    assert (Hlen_out0 : Datatypes.length out0 = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hout0_elem.
      destruct Hout0_elem as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
    assert (Hd0_app : d0_felem (out0 ++ out1) = out0).
    { unfold d0_felem. apply ListUtil.firstn_app_sharp. exact Hlen_out0. }
    assert (Hd1_app : d1_felem (out0 ++ out1) = out1).
    { unfold d1_felem. apply ListUtil.skipn_app_sharp. exact Hlen_out0. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                    @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws))).
      cbv beta. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval0, Hfeval1, Hfeval1_frob, Hfeval_t0, Hfeval_t1, Hfeval_t1_frob.
      unfold fp12_frobenius_p3_model, fp12_frobenius_model, fp12_frobenius_p2_model.
      change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x) with
        (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem x),
         @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem x)).
      cbv beta. simpl fst. simpl snd.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem)).
      cbv beta. rewrite Hd0_app, Hd1_app.
      split; assumption. }
    (* sep *)
    { assert (Hsep_flat :
        (FElem_Fp6 pout out0 ⋆ (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1 ⋆
         (FElem_Fp6 px (d0_felem x) ⋆ (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
          (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
           (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))))))))
        m_rest).
      { pose proof Hrest as H'. ecancel_assumption. }
      (* Destructure to get memory fragments *)
      destruct Hsep_flat as [m_A [m_B1 [[Heq_flat HdA] [HA HB1]]]].
      destruct HB1 as [m_B [m_C1 [[Heq_B HdB] [HB HC1]]]].
      destruct HC1 as [m_C [m_D1 [[Heq_C HdC] [HC HD1]]]].
      destruct HD1 as [m_D [m_E1 [[Heq_D HdD] [HD HE1]]]].
      destruct HE1 as [m_E [m_F1 [[Heq_E HdE] [HE HF1]]]].
      destruct HF1 as [m_F [m_G1 [[Heq_F HdF] [HF HG1]]]].
      destruct HG1 as [m_G [m_H1 [[Heq_G HdG] [HG HH1]]]].
      destruct HH1 as [m_H [m_I1 [[Heq_H HdH] [HH HI1]]]].
      destruct HI1 as [m_I [m_J1 [[Heq_I HdI] [HI HJ1]]]].
      destruct HJ1 as [m_J [m_K [[Heq_J HdJ] [HJ HK]]]].
      subst m_B1 m_C1 m_D1 m_E1 m_F1 m_G1 m_H1 m_I1 m_J1.
      split_all_disjointness.
      (* Build FElem_Fp12 pout (out0 ++ out1) *)
      assert (Hjoin_out : (FElem_Fp6 pout out0 ⋆ FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1) (map.putmany m_A m_B)).
      { exists m_A, m_B. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HA | exact HB]. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix pout out0 out1
        (map.putmany m_A m_B) Hlen_out0 Hlen_out1 Hjoin_out) as Hfp12_out.
      (* Build FElem_Fp12 px x *)
      assert (Hjoin_x : (FElem_Fp6 px (d0_felem x) ⋆ FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x)) (map.putmany m_C m_D)).
      { exists m_C, m_D. split; [split; [reflexivity | map_disjoint_auto_mul] |]. split; [exact HC | exact HD]. }
      assert (Hlen_d0x : Datatypes.length (d0_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HC as HC_copy. unfold AbstractField.FElem, Bignum.Bignum in HC_copy.
        destruct HC_copy as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      assert (Hlen_d1x : Datatypes.length (d1_felem x) = @AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
      { pose proof HD as HD_copy. unfold AbstractField.FElem, Bignum.Bignum in HD_copy.
        destruct HD_copy as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      pose proof (Fp12_raw_FElem_join beta xi_re xi_im fp12_prefix fp6_prefix fp2_prefix px (d0_felem x) (d1_felem x)
        (map.putmany m_C m_D) Hlen_d0x Hlen_d1x Hjoin_x) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      (* Build final sep *)
      rewrite Heq_flat.
      exists (map.putmany m_A m_B),
             (map.putmany (map.putmany m_C m_D) (map.putmany m_E (map.putmany m_F (map.putmany m_G (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K))))))).
      split; [split |].
      { rewrite <- !map.putmany_assoc. reflexivity. }
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_C m_D),
             (map.putmany m_E (map.putmany m_F (map.putmany m_G (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K)))))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact Hfp12_x |].
      exists m_E, (map.putmany m_F (map.putmany m_G (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K))))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HE |].
      exists m_F, (map.putmany m_G (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K)))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HF |].
      exists m_G, (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K))).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HG |].
      exists m_H, (map.putmany m_I (map.putmany m_J m_K)).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HH |].
      exists m_I, (map.putmany m_J m_K).
      split; [split; [reflexivity |] |].
      { split_all_disjointness. map_disjoint_auto_mul. }
      split; [exact HI |].
      exists m_J, m_K.
      split; [split; [reflexivity |] |].
      { exact HdJ. }
      split; [exact HJ | exact HK]. }
  Qed.
  Definition PairingOps_funcs : list function_t :=
    [ Fp2_conjugate;
      Fp6_mul_fp2;
      Fp6_frobenius;
      Fp6_frobenius_p2;
      Fp12_frobenius;
      Fp12_frobenius_p2;
      Fp12_frobenius_p3 ].

End PairingOps.
