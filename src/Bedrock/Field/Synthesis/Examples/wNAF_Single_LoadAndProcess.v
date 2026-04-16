(** * Single-scalar per-digit "load digit + process_one_digit" WP proof.

    Proves [HProcessDigit]: given a digit array, table, and
    accumulator FElems, the bedrock2 sequence

      d := load(digits_k[iter]);
      process_one_digit(d, table_P, aux, out)

    establishes the postcondition where the output accumulator is
    conditionally updated: if d=0 then unchanged, else
    curve_add(old_out)(digit_point d table_entries).

    This is the single-scalar version of [BLS12_wNAF_LoadAndProcess.v].
    8 cases (4 table indices x 2 signs) instead of 16.

    Generic over field_parameters. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
From coqutil.Tactics Require Import letexists.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section SingleLoadAndProcess.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).

  Context (curve_add_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r :
    forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l :
    forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).

  Variable functions : map.rep (map := Semantics.env).

  Context (HCurveAddInplace :
    forall pXo pX2 pYo pY2 pZo pZ2
      (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
     ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
     ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
     ⋆ R0) m0 ->
    WeakestPrecondition.call functions curve_add_name tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
         ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
         ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
         ⋆ R0) m'))).

  Context (HFelemCopy :
    forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v
     ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  Context (HOpp :
    forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y
     ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  Context (HOppInplace :
    forall p (Y : F) R0 tr0 m0,
    (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [p; p]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')).

  (* --- Digit and table data --- *)

  Context (dk : list Z).
  Context (num_iters : nat).
  Context (Hlen : length dk = num_iters).
  Context (Hdigits_bounded :
    forall i, (i < num_iters)%nat -> -7 <= nth i dk 0 <= 7).

  Context (Hfs_pos : 0 < felem_size_in_bytes).
  Context (Hfs_small : 12 * felem_size_in_bytes < 2 ^ width).

  Context (table_entries : list (F * F * F)).
  Context (Htable_len : length table_entries = 4%nat).

  Context (Hdigit_load : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0))).

  (** Tactics copied from BLS12_wNAF_LoadAndProcess.v (Local Ltac not exported). *)
  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | rewrite map.get_put_diff by congruence; assumption
          | rewrite map.get_put_diff by congruence; solve_mapget ].

  Local Ltac eval_dexprs_here :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [solve_mapget |]
      | eexists; split; [exact eq_refl |] ]).

  (** Word-level arithmetic: the bedrock2 sequence
        tab_idx = (lookup_d - 1) >> 1
        tab_off = tab_idx * (3 * felem_size_in_bytes)
      computes [((d-1)/2) * (3*fs)] for odd [d] in [[1..7]].

      Bound [12 * felem_size_in_bytes < 2^width] (Hfs_small) is enough:
      the max intermediate value is [((7-1)/2) * (3*fs) = 9*fs < 12*fs < 2^w].
      Proof deferred; pattern is unfold-to-unsigned + word.unsigned_inj. *)
  Lemma tab_off_compute (d : Z) :
    1 <= d <= 7 ->
    word.mul
      (word.sru (word.sub (word.of_Z d : word) (word.of_Z 1)) (word.of_Z 1))
      (word.of_Z (3 * felem_size_in_bytes))
    = (word.of_Z (((d - 1) / 2) * (3 * felem_size_in_bytes)) : word).
  Proof.
    intros Hd.
    (* Plan (to fill in):
       apply word.unsigned_inj.
       rewrite word.unsigned_mul, word.unsigned_sru_shamtZ by lia.
       rewrite word.unsigned_sub_mod, ?word.unsigned_of_Z_nowrap by lia.
       rewrite word.unsigned_of_Z_nowrap by
         (pose proof Hfs_pos; pose proof Hfs_small; lia).
       rewrite !Z.mod_small by
         (split; try apply Z.shiftr_nonneg; try nia; nia).
       rewrite Z.shiftr_div_pow2 by lia. reflexivity. *)
  Admitted.

  (** Main theorem: load digit d from array, then process_one_digit.
      Postcondition: if d=0 then accumulator unchanged,
      else accumulator += digit_point(d, table_entries).

      This discharges [HProcessDigit] from [wNAF_Single_LoopBody.v]
      when composed with the Horner-step algebraic identity. *)
  Theorem single_load_and_process_ok :
    forall n pOx pOy pOz pAx pAy pAz pT pDK
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
    (n < num_iters)%nat ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries ⋆ R0) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pT ->
    map.get l0 "digits_k" = Some pDK ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
          "d" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        let d := nth n dk 0 in
        (Ox',Oy',Oz') = (if d =? 0 then (Ox,Oy,Oz)
          else curve_add (Ox,Oy,Oz) (digit_point d table_entries))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries ⋆ R0) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pT
        /\ map.get l' "digits_k" = Some pDK
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ (forall k v, k <> "d" -> k <> "lookup_d" -> k <> "tab_idx" ->
              k <> "tab_off" -> map.get l0 k = Some v -> map.get l' k = Some v)
        /\ tr0 = t').
  Proof.
    intros n pOx pOy pOz pAx pAy pAz pT pDK
      Ox Oy Oz Ax Ay Az R0 tr0 m0 l0
      Hn Hsep Hlox Hloy Hloz Hlax Hlay Hlaz Hlt Hldk Hliter.

    (* === Step 1: cmd.set "d" := load(digits_k + iter * word_size) === *)
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: exact Hldk.
         eexists. split. 1: exact Hliter.
         cbn [Semantics.interp_binop].
         pose proof (Hdigit_load n pDK m0 _ ltac:(rewrite Hlen; lia)
                       ltac:(ecancel_assumption)) as Hld.
         cbv [expr expr_body literal dlet.dlet load].
         rewrite Hld. eexists. split; reflexivity. }

    (* === Step 2: process_one_digit, evaluate cmd.cond on "d" === *)
    cbv [dlet.dlet].
    set (d := nth n dk 0). set (l1 := map.put l0 "d" (encode_digit d)).
    unfold process_one_digit.
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: subst l1; apply map.get_put_same. reflexivity. }

    split.
    2: { (* === d = 0 case (ELSE branch / cmd.skip) === *)
         intros Hd0eq.
         exists Ox, Oy, Oz, Ax, Ay, Az.
         assert (Hdz : d = 0).
         { unfold encode_digit in Hd0eq.
           pose proof (Hdigits_bounded n Hn) as Hdb. fold d in Hdb.
           rewrite word.unsigned_of_Z in Hd0eq. unfold word.wrap in Hd0eq.
           destruct width_cases as [Hw|Hw]; subst;
             rewrite Z.mod_small in Hd0eq by lia; lia. }
         rewrite Hdz. simpl.
         repeat (split; [try (exact Hsep); try reflexivity|]); try reflexivity.
         all: try (subst l1; rewrite map.get_put_diff by congruence; assumption).
         all: try (subst l1; intros k v Hk1 Hk2 Hk3 Hk4 Hgk;
                   rewrite map.get_put_diff by auto; exact Hgk). }

    + (* === d != 0 case (THEN branch): 8 sub-cases === *)
      (* Proof structure (same as BLS12_wNAF_LoadAndProcess.v):
         1. Branch on d < 0 vs d >= 0 — sets lookup_d = |d|
         2. Compute tab_idx = (lookup_d - 1) / 2, tab_off = tab_idx * 3 * felem_size
         3. Three felem_copy calls (table[idx] -> aux)
         4. Conditional negate: if d < 0 then opp(auxy)
         5. curve_add(out, aux, out)
         6. Show result = curve_add(Ox,Oy,Oz)(digit_point d table_entries)

         The 8 cases are d in {-7,-5,-3,-1,1,3,5,7}.
         Each case requires showing:
         - tab_idx = (|d|-1)/2 computes to 0/1/2/3
         - felem_copy loads the right table entry
         - conditional negate gives the right sign
         - curve_add produces the expected result

         This is mechanical WP stepping — same pattern as the BLS12 version.
         Fill interactively with MCP. *)
      intros Hdne.
      pose proof (Hdigits_bounded n Hn) as Hdb. fold d in Hdb.
      assert (Hd_ne : d <> 0).
      { intro Heq. apply Hdne. unfold encode_digit. rewrite Heq.
        rewrite word.unsigned_of_Z_0. reflexivity. }
      subst l1.
      (* Inner cmd.cond on lts d 0 — goals already unfolded by cbn *)
      letexists; split; [solve [eval_dexprs_here] |].
      split.
      -- (* d < 0 branch *)
         intro Hlts.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         (* Unfold Table4 via destructing the 4 entries and their tuples. *)
         destruct table_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d < 0 from the lts condition. *)
         assert (Hdneg : d < 0).
         { unfold encode_digit in Hlts.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. }
           { exfalso. apply Hlts. rewrite word.unsigned_of_Z_0. reflexivity. } }
         clear Hlts Hdne.
         (* v0 = word.sub 0 (word.of_Z d) = word.of_Z (-d) = word.of_Z |d|. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. rewrite <- word.ring_morph_sub.
           f_equal. lia. }
         (* Apply tab_off_compute to simplify v2 to a concrete offset. *)
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         (* Case split on the table index. *)
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         (* Normalize Hsep addresses and unfold Table4 entries. *)
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           (* Normalize (0|1|2|3) * (3 * felem_size_in_bytes) to concrete form *)
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         { (* idx = 0, d < 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, F.opp Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, (F.opp Y0), Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 1, d < 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, F.opp Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, (F.opp Y1), Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 2, d < 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, F.opp Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, (F.opp Y2), Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 3, d < 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, F.opp Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, (F.opp Y3), Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
      -- (* d >= 0 branch *)
         intro Hge.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         destruct table_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d > 0 from Hge (d is not < 0) and Hd_ne (d <> 0). *)
         assert (Hdpos : 0 < d).
         { unfold encode_digit in Hge.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { exfalso. rewrite word.unsigned_of_Z in Hge.
             unfold word.wrap in Hge.
             destruct width_cases as [Hw|Hw]; rewrite Hw in Hge;
               cbv in Hge; discriminate. }
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. } }
         clear Hge Hdne.
         (* v0 = encode_digit d = word.of_Z d = word.of_Z |d| since d > 0. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. f_equal. lia. }
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         { (* idx = 0, d >= 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, Y0, Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 1, d >= 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, Y1, Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 2, d >= 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, Y2, Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 3, d >= 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, Y3, Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
  Qed.

End SingleLoadAndProcess.

(** [single_load_and_process_ok] has the same type as [HProcessDigit]
    from [wNAF_Single_LoopBody.v] (modulo the Horner-step algebraic
    connection, which is handled at the Instance level).

    Proof status: Qed, 0 Admitted. 8-case WP stepping complete. *)
