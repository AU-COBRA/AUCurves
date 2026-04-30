(** * Constant-time conditional move on a 5-felem (200-byte) buffer.
 *
 * Used by [ed25519_scalarmult_base] to conditionally update the
 * accumulator with the post-add value, depending on the current
 * scalar bit, in constant time.
 *
 * Bedrock2 program + bedrock2 WP correctness lemma. Intentionally
 * does NOT go through fiat-crypto's [select_znz] pipeline, because
 * [unsaturated_solinas_ops] does not include a [select_znz_op]
 * (only [wbw_montgomery_ops] does). Writing it here avoids modifying
 * upstream fiat-crypto.
 *
 * STATUS: Definition complete, Hoare-spec stated, proof in progress. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
From Stdlib Require Import Morphisms.

Section CMov5Felems.
  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  (** Local Proper instance for [sep ⋆] under [iff1] — needed for setoid_rewrite
      with iff1 hypotheses inside sep-conjuncts. *)
  Local Instance my_sep_proper_iff1 :
    Proper (Lift1Prop.iff1 ==> Lift1Prop.iff1 ==> Lift1Prop.iff1) (@sep _ _ BasicC64Semantics.mem)
    := @Proper_sep_iff1 _ _ BasicC64Semantics.mem BasicC64Semantics.mapok.

  (** Local tactic copied from BLS12_MSM.v:376 — closes
      [map.get (map.put^n m k v) k' = Some _] over a chain of map.puts. *)
  Local Ltac solve_map_get_chain :=
    repeat (rewrite map.get_put_diff by congruence);
    first
      [ rewrite map.get_put_same; reflexivity
      | solve [eauto]
      | solve [symmetry; eauto] ].

  (** Auxiliary lemma: the cmov XOR formula reduces to selection on mask ∈ {0,1}. *)
  Lemma cmov_xor_identity (x y m : Naive.word 64)
    (Hm : m = word.of_Z 0 \/ m = word.of_Z 1) :
    word.xor x (word.and (word.xor x y) (word.opp m)) =
    (if word.eqb m (word.of_Z 0) then x else y).
  Proof.
    destruct Hm as [Hm|Hm]; subst m.
    - (* mask = 0 *)
      rewrite Properties.word.eqb_eq by reflexivity.
      apply Properties.word.unsigned_inj.
      rewrite word.unsigned_xor, word.unsigned_and.
      rewrite word.unsigned_opp. rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite (Z.mod_0_l (2^64)) by (cbv; congruence).
      replace (-0) with 0 by Lia.lia.
      rewrite (Z.mod_0_l (2^64)) by (cbv; congruence).
      rewrite Z.land_0_r. rewrite Z.lxor_0_r.
      ZnWords.
    - (* mask = 1 *)
      replace (word.eqb (word.of_Z 1) (word.of_Z 0)) with false.
      2:{ symmetry. apply Properties.word.eqb_ne. intro Heq.
          apply (f_equal word.unsigned) in Heq.
          rewrite !word.unsigned_of_Z in Heq. cbv in Heq. discriminate. }
      apply Properties.word.unsigned_inj.
      rewrite word.unsigned_xor, word.unsigned_and.
      rewrite word.unsigned_opp, word.unsigned_of_Z.
      rewrite word.unsigned_xor.
      cbv [word.wrap].
      change (- (1 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 64).
      rewrite Z.land_ones by Lia.lia.
      rewrite !Z.mod_mod by Lia.lia.
      assert (Hxor_bd : 0 <= Z.lxor (word.unsigned x) (word.unsigned y) < 2^64).
      { split.
        - apply Z.lxor_nonneg.
          split; intros _; apply Properties.word.unsigned_range.
        - pose proof (Properties.word.unsigned_range x) as Hx.
          pose proof (Properties.word.unsigned_range y) as Hy.
          assert (Hxor_nonneg : 0 <= Z.lxor (word.unsigned x) (word.unsigned y)).
          { apply Z.lxor_nonneg. split; intros _; [apply Hy|apply Hx]. }
          destruct (Z.eq_dec (Z.lxor (word.unsigned x) (word.unsigned y)) 0)
            as [Hxor0|Hxor0]; [Lia.lia|].
          apply Z.log2_lt_pow2; [Lia.lia|].
          apply Z.le_lt_trans with
            (m := Z.max (Z.log2 (word.unsigned x)) (Z.log2 (word.unsigned y))).
          { apply Z.log2_lxor; Lia.lia. }
          apply Z.max_lub_lt.
          + destruct (Z.eq_dec (word.unsigned x) 0) as [Hx0|Hx0].
            * rewrite Hx0. cbv. reflexivity.
            * apply Z.log2_lt_pow2; Lia.lia.
          + destruct (Z.eq_dec (word.unsigned y) 0) as [Hy0|Hy0].
            * rewrite Hy0. cbv. reflexivity.
            * apply Z.log2_lt_pow2; Lia.lia. }
      rewrite Z.mod_small with (a := Z.lxor (word.unsigned x) (word.unsigned y))
        by exact Hxor_bd.
      rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l.
      apply Z.mod_small. apply Properties.word.unsigned_range.
  Qed.

  (** [cmov_5felems(out, src, mask)] performs the constant-time
      assignment [out := if mask=0 then out else src] over a 200-byte
      buffer (5 felems × 40 bytes = 25 × 8-byte words).

      Algorithm: for each 64-bit word position [i], compute
      [m := 0 - mask] (yields 0 if mask=0, else 2^64-1) and write
      [out[i] := out[i] xor ((out[i] xor src[i]) and m)].
      Since mask ∈ {0, 1}, this resolves to:
        - mask=0: [out[i] xor 0 = out[i]]    (preserves out)
        - mask=1: [out[i] xor (out[i] xor src[i]) = src[i]]  (copies src). *)
  Definition cmov_5felems := func! (out, src, mask) {
    m = $0 - mask;
    i = $0;
    while (i < $200) {
      x = load(out + i);
      y = load(src + i);
      store(out + i, x ^ ((x ^ y) & m));
      i = i + $8
    }
  }.

  (** Byte-level spec: no FElem layer needed because [cmov_5felems]
      treats the buffer as opaque bytes. The [src] block stays
      untouched in either branch; [out] either keeps its bytes
      (mask=0) or takes [src]'s bytes (mask=1). *)
  Instance spec_of_cmov_5felems : spec_of "cmov_5felems" :=
    fnspec! "cmov_5felems" out_ptr src_ptr mask / out src R,
    { requires tr mem :=
        Datatypes.length out = 200%nat /\
        Datatypes.length src = 200%nat /\
        (mask = word.of_Z 0 \/ mask = word.of_Z 1) /\
        ((out$@out_ptr) ⋆ (src$@src_ptr) ⋆ R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let result := if word.eqb mask (word.of_Z 0) then out else src in
        ((result$@out_ptr) ⋆ (src$@src_ptr) ⋆ R)%sep mem' }.

  Lemma cmov_5felems_correct : program_logic_goal_for_function! cmov_5felems.
  Proof.
    repeat straightline.
    (* Set up the loop invariant. n ∈ [0, 25] tracks remaining iterations;
       k = 25 - n is the number of words already processed. *)
    pose (inv := fun (n : nat) (tr' : Semantics.trace)
                       (m_l : @Interface.map.rep _ _ BasicC64Semantics.mem)
                       (loc : @Interface.map.rep _ _ BasicC64Semantics.locals) =>
      exists (out' : list Byte.byte) (iw : Naive.word 64),
        (n <= 25)%nat /\
        Datatypes.length out' = 200%nat /\
        word.unsigned iw = Z.of_nat (8 * (25 - n)) /\
        List.firstn (8 * (25 - n)) out' =
          List.firstn (8 * (25 - n))
            (if word.eqb mask (word.of_Z 0) then out else src) /\
        List.skipn (8 * (25 - n)) out' = List.skipn (8 * (25 - n)) out /\
        Interface.map.get loc "out" = Some out_ptr /\
        Interface.map.get loc "src" = Some src_ptr /\
        Interface.map.get loc "mask" = Some mask /\
        Interface.map.get loc "m" = Some (word.opp mask) /\
        Interface.map.get loc "i" = Some iw /\
        ((out'$@out_ptr) ⋆ (src$@src_ptr) ⋆ R)%sep m_l /\
        tr = tr').
    eapply (Loops.while_localsmap (measure:=nat) inv Nat.lt_wf_0 25%nat).
    (* 3 goals: entry condition, body, postcondition (when n=0). *)
    { (* Entry: invariant at n=25 (no words processed yet). *)
      subst inv; cbv beta.
      exists out, (word.of_Z 0).
      replace (8 * (25 - 25))%nat with 0%nat by Lia.lia.
      ssplit.
      - Lia.lia.
      - assumption.
      - ZnWords.
      - reflexivity.
      - reflexivity.
      - (* "out": peel 4 puts (i, m, mask, src), then put_same matches "out". *)
        subst l1 l0 l.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      - subst l1 l0 l.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      - subst l1 l0 l.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_diff by congruence.
        apply map.get_put_same.
      - (* "m": stored value word.sub(0,mask) is convertible to word.opp mask. *)
        subst l1 l0 m.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same.
        f_equal.
      - subst l1 i. apply map.get_put_same.
      - ecancel_assumption.
      - reflexivity. }
    { (* Body+exit: forall n. assuming inv n, prove the conditional. *)
      intros n tr_l m_l loc_l Hinv.
      subst inv; cbv beta in Hinv.
      destruct Hinv as (out' & iw & Hn_le & Hlen' & Hiw_val & Hpref & Hsuf
                        & Hl_out & Hl_src & Hl_mask & Hl_m & Hl_i & Hsep & Htreq).
      eexists. split.
      { (* Evaluate `i < 200`: pick br = ltu iw 200 *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal WeakestPrecondition.get dlet.dlet].
        eexists; split. { exact Hl_i. }
        cbv [Semantics.interp_binop]. reflexivity. }
      cbv [Markers.split]. split.
      - (* Body case (br ≠ 0): n > 0, then execute c2 (load+load+store+inc),
           preserve inv with v' = pred n. *)
        intros Hbr_nz.
        apply Properties.word.if_nonzero in Hbr_nz.
        rewrite word.unsigned_ltu in Hbr_nz. apply Z.ltb_lt in Hbr_nz.
        rewrite word.unsigned_of_Z in Hbr_nz. cbv [word.wrap] in Hbr_nz.
        destruct n as [|n']; [exfalso|].
        { (* n=0 contradicts Hbr_nz: iw = 200 *)
          remember (word.unsigned iw) as u eqn:Hu.
          assert (Hbr' : u < 200 mod 2^64) by (rewrite Hu; exact Hbr_nz).
          Lia.lia. }
        (* n = S n': Step 1 — Set offset and split out' into pref ++ middle ++ suf. *)
        set (offset := (8 * (25 - S n'))%nat).
        assert (Hoff_lt : (offset + 8 <= 200)%nat) by (subst offset; Lia.lia).
        assert (Hsplit_out' : (out' = List.firstn offset out' ++ List.firstn 8 (List.skipn offset out') ++ List.skipn (offset + 8) out')%list).
        { rewrite <- (List.firstn_skipn offset out') at 1.
          f_equal.
          rewrite <- (List.firstn_skipn 8 (List.skipn offset out')) at 1.
          f_equal. rewrite skipn_skipn. f_equal. Lia.lia. }
        (* Step 2 — Split Hsep using sep_eq_of_list_word_at_app twice.
           Result: Hsep contains the 3 chunks (pref, middle, suf) as separate
           sep clauses + (src + R). *)
        rewrite Hsplit_out' in Hsep at 1.
        seprewrite_in (SeparationMemory.sep_eq_of_list_word_at_app out_ptr
                         (List.firstn offset out')
                         (List.firstn 8 (List.skipn offset out') ++ List.skipn (offset + 8) out')%list
                         (Z.of_nat offset)) Hsep.
        { rewrite List.firstn_length, Hlen'. Lia.lia. }
        { rewrite !List.app_length, !List.firstn_length, !List.skipn_length, Hlen'.
          cbv [Bitwidth64.BW64]. Lia.lia. }
        seprewrite_in (SeparationMemory.sep_eq_of_list_word_at_app
                         (word.add out_ptr (word.of_Z (Z.of_nat offset)))
                         (List.firstn 8 (List.skipn offset out'))
                         (List.skipn (offset + 8) out') 8) Hsep.
        { rewrite List.firstn_length, List.skipn_length, Hlen'. Lia.lia. }
        { rewrite !List.firstn_length, !List.skipn_length, Hlen'.
          subst offset. cbv [Bitwidth64.BW64]. Lia.lia. }
        (* Hsep now: middle$@(out_ptr+offset) ⋆ suf$@(out_ptr+offset+8) ⋆
                     pref$@out_ptr ⋆ src$@src_ptr ⋆ R. *)
        (* Step 2.5: Hiw_eq bridges iw and word.of_Z (Z.of_nat offset).
           Note: straightline applies Hiw_eq via `subst iw` automatically,
           so the rewrite Hiw_eq step in the load tactic is unnecessary. *)
        assert (Hiw_eq : iw = word.of_Z (Z.of_nat offset)).
        { apply Properties.word.unsigned_inj. rewrite Hiw_val.
          rewrite word.unsigned_of_Z. cbv [word.wrap]. rewrite Z.mod_small.
          - reflexivity.
          - subst offset. cbv [Bitwidth64.BW64]. Lia.lia. }
        (* Step 3: discharge dexpr `load(out+i)` using load_Z_of_sep on middle. *)
        repeat straightline.
        eexists. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.literal WeakestPrecondition.get
               WeakestPrecondition.load dlet.dlet].
          eexists; split. { exact Hl_out. }
          eexists; split. { exact Hl_i. }
          cbv [Semantics.interp_binop].
          eexists; split.
          { unfold Memory.load.
            erewrite SeparationMemory.load_Z_of_sep with
              (bs := List.firstn 8 (List.skipn offset out')) (n := 8%nat).
            - reflexivity.
            - apply BasicC64Semantics.mapok.
            - ecancel_assumption_impl.
            - rewrite List.firstn_length, List.skipn_length, Hlen'. Lia.lia.
            - cbv [Bitwidth64.BW64]. Lia.lia. }
          reflexivity. }
        (* Step 4: discharge load(src+i). Same pattern after splitting src. *)
        assert (Hsplit_src : (src = List.firstn offset src ++ List.firstn 8 (List.skipn offset src) ++ List.skipn (offset + 8) src)%list).
        { rewrite <- (List.firstn_skipn offset src) at 1.
          f_equal.
          rewrite <- (List.firstn_skipn 8 (List.skipn offset src)) at 1.
          f_equal. rewrite skipn_skipn. f_equal. Lia.lia. }
        rewrite Hsplit_src in Hsep at 1.
        seprewrite_in (SeparationMemory.sep_eq_of_list_word_at_app src_ptr
                         (List.firstn offset src)
                         (List.firstn 8 (List.skipn offset src) ++ List.skipn (offset + 8) src)%list
                         (Z.of_nat offset)) Hsep.
        { rewrite List.firstn_length, H0. Lia.lia. }
        { rewrite !List.app_length, !List.firstn_length, !List.skipn_length, H0.
          cbv [Bitwidth64.BW64]. Lia.lia. }
        seprewrite_in (SeparationMemory.sep_eq_of_list_word_at_app
                         (word.add src_ptr (word.of_Z (Z.of_nat offset)))
                         (List.firstn 8 (List.skipn offset src))
                         (List.skipn (offset + 8) src) 8) Hsep.
        { rewrite List.firstn_length, List.skipn_length, H0. Lia.lia. }
        { rewrite !List.firstn_length, !List.skipn_length, H0.
          subst offset. cbv [Bitwidth64.BW64]. Lia.lia. }
        repeat straightline.
        eexists. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.literal WeakestPrecondition.get
               WeakestPrecondition.load dlet.dlet].
          eexists; split. { subst l. rewrite map.get_put_diff by congruence. exact Hl_src. }
          eexists; split. { subst l. rewrite map.get_put_diff by congruence. exact Hl_i. }
          cbv [Semantics.interp_binop].
          eexists; split.
          { unfold Memory.load.
            erewrite SeparationMemory.load_Z_of_sep with
              (bs := List.firstn 8 (List.skipn offset src)) (n := 8%nat).
            - reflexivity.
            - apply BasicC64Semantics.mapok.
            - ecancel_assumption_impl.
            - rewrite List.firstn_length, List.skipn_length, H0. Lia.lia.
            - cbv [Bitwidth64.BW64]. Lia.lia. }
          reflexivity. }
        (* Steps 5a/5b: Address + value dexpr discharge.
           Step 5a (address): committed via subst l0 l + map.get_put_diff chain.
           Step 5b (value): the nested `x ^ ((x ^ y) & m)` dexpr was verified
           PIECEWISE in MCP but needs careful state shifts that resist a
           single block (after first eexists, the goal-shape differs from
           what MCP saw mid-proof). Saved as plan comment instead. *)
        repeat straightline.
        subst l0 l.
        (* Step 5a: address dexpr `out + i`. WORKS in file. *)
        eexists. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.literal WeakestPrecondition.get
               WeakestPrecondition.load dlet.dlet].
          eexists; split. { rewrite map.get_put_diff by congruence.
                            rewrite map.get_put_diff by congruence. exact Hl_out. }
          eexists; split. { rewrite map.get_put_diff by congruence.
                            rewrite map.get_put_diff by congruence. exact Hl_i. }
          cbv [Semantics.interp_binop]. reflexivity. }
        (* Step 5b: value dexpr `x ^ ((x ^ y) & m)`.
           Structure: outer xor unfolds to (outer-x lookup, then expr for inner)
           — the inner ((x^y) & m) needs ANOTHER cbv to flatten to (x, y, m). *)
        eexists. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.literal WeakestPrecondition.get
               WeakestPrecondition.load dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence. apply map.get_put_same. } (* outer x *)
          cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.literal WeakestPrecondition.get
               WeakestPrecondition.load dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence. apply map.get_put_same. } (* inner x *)
          eexists; split.
          { apply map.get_put_same. }                                          (* y *)
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hl_m. }              (* m *)
          reflexivity. }
        (* Step 5c: apply uncurried_store_Z_of_sep with explicit R frame.
           The xor expression is the value being stored; uncurried form
           returns m' satisfying the new sep predicate. *)
        unfold WeakestPrecondition.store, Memory.store.
        edestruct (SeparationMemory.uncurried_store_Z_of_sep
                    (word.add out_ptr iw) 8%nat
                    (List.firstn 8 (List.skipn offset out'))
                    (word.unsigned
                       (word.xor
                         (word.of_Z (LittleEndianList.le_combine
                                       (List.firstn 8 (List.skipn offset out'))))
                         (word.and
                           (word.xor
                             (word.of_Z (LittleEndianList.le_combine
                                           (List.firstn 8 (List.skipn offset out'))))
                             (word.of_Z (LittleEndianList.le_combine
                                           (List.firstn 8 (List.skipn offset src)))))
                           (word.opp mask))))
                    (sepclause_of_map ((List.firstn 8 (List.skipn offset src))$@(word.add src_ptr (word.of_Z (Z.of_nat offset))))
                     ⋆ sepclause_of_map ((List.skipn (offset + 8) src)$@(word.add (word.add src_ptr (word.of_Z (Z.of_nat offset))) (word.of_Z 8)))
                     ⋆ sepclause_of_map ((List.firstn offset src)$@src_ptr)
                     ⋆ sepclause_of_map ((List.skipn (offset + 8) out')$@(word.add (word.add out_ptr (word.of_Z (Z.of_nat offset))) (word.of_Z 8)))
                     ⋆ sepclause_of_map ((List.firstn offset out')$@out_ptr) ⋆ R)%sep
                    m_l)
          as [m' [Hstore_eq Hsep']].
        { ssplit.
          - ecancel_assumption_impl.
          - rewrite List.firstn_length, List.skipn_length, Hlen'. Lia.lia.
          - cbv [Bitwidth64.BW64]. Lia.lia. }
        (* Now: m', Hstore_eq, Hsep' (new memory has le_split bytes at offset).
           Step 6: provide m' to discharge the WP store predicate. *)
        eexists. split. { exact Hstore_eq. }
        (* Step 7: advance through `i = i + 8` set explicitly via cmd_body
           unfold (BLS12_MSM pattern). Locals at this point have "x" and "y"
           on top of loc_l (from the two loads), so "i" lookup needs
           2 map.get_put_diff + exact Hl_i. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            exact Hl_i. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* Step 8: provide v' = n' and prove inv n'. *)
        set (new_middle := LittleEndianList.le_split 8
          (word.unsigned
            (word.xor
              (word.of_Z (LittleEndianList.le_combine
                            (List.firstn 8 (List.skipn offset out'))))
              (word.and
                (word.xor
                  (word.of_Z (LittleEndianList.le_combine
                                (List.firstn 8 (List.skipn offset out'))))
                  (word.of_Z (LittleEndianList.le_combine
                                (List.firstn 8 (List.skipn offset src)))))
                (word.opp mask))))).
        set (out'' := (List.firstn offset out'
                       ++ new_middle
                       ++ List.skipn (offset + 8) out')%list).
        exists n'. split; [|Lia.lia].
        exists out'', (word.add iw (word.of_Z 8)).
        ssplit.
        + (* 1. (n' <= 25)%nat *)
          Lia.lia.
        + (* 2. length out'' = 200%nat *)
          subst out''. unfold new_middle. rewrite !List.app_length.
          rewrite List.firstn_length, List.skipn_length, Hlen'.
          rewrite LittleEndianList.length_le_split.
          subst offset. cbv [Bitwidth64.BW64]. Lia.lia.
        + (* 3. word.unsigned (iw + 8) = Z.of_nat (8 * (25 - n')) *)
          rewrite word.unsigned_add. rewrite Hiw_val.
          rewrite word.unsigned_of_Z. cbv [word.wrap].
          rewrite Z.mod_small.
          * replace (8 * (25 - n'))%nat with (8 * (25 - S n') + 8)%nat by Lia.lia.
            rewrite Nat2Z.inj_add. Lia.lia.
          * cbv [Bitwidth64.BW64]. subst offset. Lia.lia.
        + (* 4. firstn invariant: case-split on H1 (mask=0 or 1).
             Mask=0 case: VERIFIED in MCP iter 43 (~30 LoC).
             Mask=1 case: similar structure, admitted for now. *)
          destruct H1 as [Hm0 | Hm1]; subst mask.
          { (* mask = word.of_Z 0 *)
            rewrite Properties.word.eqb_eq by reflexivity.
            rewrite Properties.word.eqb_eq in Hpref by reflexivity.
            subst offset out''.
            replace (8 * (25 - n'))%nat with (8 * (25 - S n') + 8)%nat by Lia.lia.
            rewrite List.firstn_app, List.length_firstn, Hlen'.
            rewrite Nat.min_l by Lia.lia.
            replace (8 * (25 - S n') + 8 - 8 * (25 - S n'))%nat with 8%nat by Lia.lia.
            rewrite List.firstn_firstn.
            rewrite Nat.min_r by Lia.lia.
            rewrite List.firstn_app.
            unfold new_middle. rewrite LittleEndianList.length_le_split.
            replace (8 - 8)%nat with 0%nat by Lia.lia.
            rewrite List.firstn_O. rewrite List.app_nil_r.
            rewrite List.firstn_all2 with (n := 8%nat)
              by (rewrite LittleEndianList.length_le_split; reflexivity).
            rewrite Hpref.
            rewrite (cmov_xor_identity _ _ (word.of_Z 0)) by (left; reflexivity).
            rewrite Properties.word.eqb_eq by reflexivity.
            rewrite word.unsigned_of_Z. cbv [word.wrap].
            rewrite Z.mod_small.
            2: { pose proof (LittleEndianList.le_combine_bound
                              (List.firstn 8 (List.skipn (8 * (25 - S n')) out'))) as Hbnd.
                 rewrite List.length_firstn, List.length_skipn, Hlen' in Hbnd.
                 replace (Init.Nat.min 8 (200 - 8 * (25 - S n')))%nat with 8%nat in Hbnd by Lia.lia.
                 replace (8 * Z.of_nat 8) with 64 in Hbnd by Lia.lia.
                 Lia.lia. }
            rewrite (LittleEndianList.split_le_combine' _ 8%nat).
            2: { rewrite List.length_firstn, List.length_skipn, Hlen'. Lia.lia. }
            rewrite Hsuf.
            rewrite (firstn_skipn_comm 8 (8 * (25 - S n')) out).
            replace (List.firstn (8 * (25 - S n')) out)
              with (List.firstn (8 * (25 - S n'))
                     (List.firstn (8 * (25 - S n') + 8) out)).
            2: { rewrite List.firstn_firstn. f_equal. Lia.lia. }
            rewrite firstn_skipn. reflexivity. }
          { (* mask = word.of_Z 1 — VERIFIED in MCP iter 44 *)
            replace (word.eqb (word.of_Z 1) (word.of_Z 0)) with false.
            2: { symmetry. apply Properties.word.eqb_ne. intro Heq.
                 apply (f_equal word.unsigned) in Heq.
                 rewrite !word.unsigned_of_Z in Heq. cbv in Heq. discriminate. }
            replace (word.eqb (word.of_Z 1) (word.of_Z 0)) with false in Hpref.
            2: { symmetry. apply Properties.word.eqb_ne. intro Heq.
                 apply (f_equal word.unsigned) in Heq.
                 rewrite !word.unsigned_of_Z in Heq. cbv in Heq. discriminate. }
            subst offset out''.
            replace (8 * (25 - n'))%nat with (8 * (25 - S n') + 8)%nat by Lia.lia.
            rewrite List.firstn_app, List.length_firstn, Hlen'.
            rewrite Nat.min_l by Lia.lia.
            replace (8 * (25 - S n') + 8 - 8 * (25 - S n'))%nat with 8%nat by Lia.lia.
            rewrite List.firstn_firstn.
            rewrite Nat.min_r by Lia.lia.
            rewrite List.firstn_app.
            unfold new_middle. rewrite LittleEndianList.length_le_split.
            replace (8 - 8)%nat with 0%nat by Lia.lia.
            rewrite List.firstn_O. rewrite List.app_nil_r.
            rewrite List.firstn_all2 with (n := 8%nat)
              by (rewrite LittleEndianList.length_le_split; reflexivity).
            rewrite Hpref.
            rewrite (cmov_xor_identity _ _ (word.of_Z 1)) by (right; reflexivity).
            replace (word.eqb (word.of_Z 1) (word.of_Z 0)) with false.
            2: { symmetry. apply Properties.word.eqb_ne. intro Heq.
                 apply (f_equal word.unsigned) in Heq.
                 rewrite !word.unsigned_of_Z in Heq. cbv in Heq. discriminate. }
            rewrite word.unsigned_of_Z. cbv [word.wrap].
            rewrite Z.mod_small.
            2: { pose proof (LittleEndianList.le_combine_bound
                              (List.firstn 8 (List.skipn (8 * (25 - S n')) src))) as Hbnd.
                 rewrite List.length_firstn, List.length_skipn, H0 in Hbnd.
                 replace (Init.Nat.min 8 (200 - 8 * (25 - S n')))%nat with 8%nat in Hbnd by Lia.lia.
                 replace (8 * Z.of_nat 8) with 64 in Hbnd by Lia.lia.
                 Lia.lia. }
            rewrite (LittleEndianList.split_le_combine' _ 8%nat).
            2: { rewrite List.length_firstn, List.length_skipn, H0. Lia.lia. }
            rewrite (firstn_skipn_comm 8 (8 * (25 - S n')) src).
            replace (List.firstn (8 * (25 - S n')) src)
              with (List.firstn (8 * (25 - S n'))
                     (List.firstn (8 * (25 - S n') + 8) src)).
            2: { rewrite List.firstn_firstn. f_equal. Lia.lia. }
            rewrite firstn_skipn. reflexivity. }
        + (* 5. skipn invariant: skipn (8*(25-n')) out'' = skipn (8*(25-n')) out.
             Proof verified in MCP (iter 33). Strategy: 8*(25-n') = offset+8;
             out'' = pref ++ new_middle ++ suf where |pref|=offset, |new_middle|=8.
             Decompose via skipn_app twice + skipn_skipn + Hsuf. *)
          subst offset out''.
          replace (8 * (25 - n'))%nat with (8 * (25 - S n') + 8)%nat by Lia.lia.
          rewrite List.skipn_app, List.length_firstn, Hlen'.
          rewrite Nat.min_l by Lia.lia.
          replace (8 * (25 - S n') + 8 - 8 * (25 - S n'))%nat with 8%nat by Lia.lia.
          rewrite (List.skipn_all2 (List.firstn (8 * (25 - S n')) out'))
            by (rewrite List.length_firstn, Hlen'; Lia.lia).
          cbn [List.app].
          rewrite List.skipn_app.
          unfold new_middle. rewrite LittleEndianList.length_le_split.
          replace (8 - 8)%nat with 0%nat by Lia.lia.
          cbn [List.skipn].
          replace (8 * (25 - S n') + 8)%nat with (8 + 8 * (25 - S n'))%nat by Lia.lia.
          rewrite <- ! List.skipn_skipn.
          rewrite Hsuf. reflexivity.
        + (* 6. map.get loc "out" — skip "i","y","x" then exact Hl_out *)
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          exact Hl_out.
        + (* 7. map.get loc "src" *)
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          exact Hl_src.
        + (* 8. map.get loc "mask" *)
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          exact Hl_mask.
        + (* 9. map.get loc "m" *)
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_put_diff by congruence.
          exact Hl_m.
        + (* 10. map.get loc "i" — fresh put for "i" by the i+=8 set *)
          apply map.get_put_same.
        + (* 11. sep predicate via iff1ToEq trick:
             Convert each iff1 to a functional equation via `iff1ToEq`, then use
             standard `rewrite` (no Proper instance needed). *)
          subst out''. rewrite Hsplit_src at 1.
          epose proof (SeparationMemory.sep_eq_of_list_word_at_app out_ptr
                         (List.firstn offset out')
                         (new_middle ++ List.skipn (offset + 8) out')%list
                         (Z.of_nat offset)) as Hm1.
          specialize (Hm1 ltac:(rewrite List.length_firstn, Hlen';
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          specialize (Hm1 ltac:(rewrite !List.length_app, List.length_firstn,
                                !List.length_skipn, Hlen';
                                unfold new_middle;
                                rewrite LittleEndianList.length_le_split;
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          apply iff1ToEq in Hm1.
          epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                         (word.add out_ptr (word.of_Z (Z.of_nat offset)))
                         new_middle (List.skipn (offset + 8) out') 8) as Hm2.
          specialize (Hm2 ltac:(unfold new_middle;
                                rewrite LittleEndianList.length_le_split; reflexivity)).
          specialize (Hm2 ltac:(unfold new_middle;
                                rewrite LittleEndianList.length_le_split,
                                  List.length_skipn, Hlen';
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          apply iff1ToEq in Hm2.
          epose proof (SeparationMemory.sep_eq_of_list_word_at_app src_ptr
                         (List.firstn offset src)
                         (List.firstn 8 (List.skipn offset src) ++
                          List.skipn (offset + 8) src)%list
                         (Z.of_nat offset)) as Hm3.
          specialize (Hm3 ltac:(rewrite List.length_firstn, H0;
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          specialize (Hm3 ltac:(rewrite !List.length_app, !List.length_firstn,
                                !List.length_skipn, H0;
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          apply iff1ToEq in Hm3.
          epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                         (word.add src_ptr (word.of_Z (Z.of_nat offset)))
                         (List.firstn 8 (List.skipn offset src))
                         (List.skipn (offset + 8) src) 8) as Hm4.
          specialize (Hm4 ltac:(rewrite List.length_firstn, List.length_skipn, H0;
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          specialize (Hm4 ltac:(rewrite !List.length_firstn,
                                !List.length_skipn, H0;
                                cbv [Bitwidth64.BW64]; Lia.lia)).
          apply iff1ToEq in Hm4.
          rewrite Hm1, Hm2, Hm3, Hm4.
          ecancel_assumption_impl.
        + (* 12. tr equality. Htreq was likely subst'd by straightline
             (Htreq : tr = tr_l → subst tr_l replaces all tr_l with tr).
             Goal becomes tr = tr (no IO ops in body), so reflexivity. *)
          reflexivity.
        (* Original full plan kept for reference:

         === Step 5a: Address dexpr for `out + i` ===
         repeat straightline.
         eexists. split.
         { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
                WeakestPrecondition.literal WeakestPrecondition.get
                WeakestPrecondition.load dlet.dlet].
           eexists; split. { subst l0 l. rewrite map.get_put_diff by congruence.
                             rewrite map.get_put_diff by congruence. exact Hl_out. }
           eexists; split. { subst l0 l. rewrite map.get_put_diff by congruence.
                             rewrite map.get_put_diff by congruence. exact Hl_i. }
           cbv [Semantics.interp_binop]. reflexivity. }

         === Step 5b: Value dexpr for `x ^ ((x ^ y) & m)` ===
         eexists. split.
         { cbv [WeakestPrecondition.expr ... ].
           eexists; split. { subst l0 l. rewrite map.get_put_diff by congruence.
                             apply map.get_put_same. }                              (* x *)
           eexists; split.
           { eexists; split. { subst l0 l. rewrite map.get_put_diff by congruence.
                               apply map.get_put_same. }                            (* x again, inner *)
             eexists; split. { subst l0. apply map.get_put_same. }                  (* y = put_same on l0 *)
             cbv [Semantics.interp_binop]. reflexivity. }
           eexists; split. { subst l0 l.
                             rewrite map.get_put_diff by congruence.
                             rewrite map.get_put_diff by congruence. exact Hl_m. } (* m, after 2 puts *)
           cbv [Semantics.interp_binop]. reflexivity. }

         === Step 5c: Apply uncurried_store_Z_of_sep ===
         The `store` predicate unfolds to `exists m', Memory.store ... = Some m' /\ post m'`.
         Memory.store sz m a v = store_Z m a (bytes_per sz) (word.unsigned v).
         With sz = access_size.word, bytes_per = 8.
         Apply (e.g. via edestruct):
           SeparationMemory.uncurried_store_Z_of_sep with
             a := word.add out_ptr iw, n := 8%nat,
             _bs := List.firstn 8 (List.skipn offset out'),
             z := word.unsigned <the XOR value>,
             m := m_l.
         Side conditions:
         - sep precondition for the middle of out': ecancel_assumption_impl.
         - length: rewrite firstn_length, skipn_length, Hlen'. Lia.lia.
         - bound: cbv [Bitwidth64.BW64]. Lia.lia.
         Result: m', store_eq, Hsep' for new memory with le_split bytes.
         Continuation: exists m', split. { exact Hstore_eq. } (* now post m' *).

         === Step 6: Re-merge into out''$@out_ptr ===
         Define new_middle := le_split 8 (word.unsigned <XOR value>).
         Define out'' := List.firstn offset out' ++ new_middle ++ List.skipn (offset+8) out'.
         Use sep_eq_of_list_word_at_app TWICE (in reverse direction) to combine:
           new_middle$@(out_ptr+offset) ⋆ suf$@(out_ptr+offset+8) ⋆ pref$@out_ptr
           = (pref ++ new_middle ++ suf)$@out_ptr = out''$@out_ptr.
         Then assert Hsep_new : (out''$@out_ptr ⋆ src$@src_ptr ⋆ R)%sep m'.
         (The src split needs to be re-merged similarly to recover src$@src_ptr.)

         === Step 7: Set i = i + 8 ===
         repeat straightline (advances through cmd.set).
         New locals: l1 := map.put l0 "i" (word.add iw (word.of_Z 8)).

         === Step 8: exists v' := n', prove inv n' ===
         exists n'. unshelve eexists out'', (word.add iw (word.of_Z 8)).
         ssplit.
         - (S n' <= 25) → (n' <= 25): Lia.lia.
         - length out'' = 200: from concatenation lengths.
         - word.unsigned (iw + 8) = 8 * (25 - n')
           Use Hiw_val + word.unsigned_add. Show 8 * (25 - n') = 8 * (24 - n') + 8.
         - firstn (8*(25-n')) out'' = firstn ... (if mask=0 then out else src).
           THIS IS THE ALGEBRAIC HEART:
           - 8*(25-n') = offset + 8.
           - firstn (offset+8) out'' = firstn (offset+8) (pref ++ new_middle ++ suf).
             Since length pref = offset, this is pref ++ firstn 8 new_middle = pref ++ new_middle.
           - pref = firstn offset out' = firstn offset (if ...).
           - new_middle = le_split 8 (word.unsigned (xor x (and (xor x y) (opp mask)))).
             KEY identity: word.xor a (word.and (word.xor a b) c) =
               if c = 0 then a else if c = -1 then b else mixed.
             For c = word.opp mask:
               * mask = 0 → opp 0 = 0 → expression = a (= x).
                 le_split 8 (word.unsigned x) = le_split 8 (le_combine middle) = middle (round-trip).
                 So new_middle = middle = firstn 8 (skipn offset out') = firstn 8 (skipn offset (if mask=0 then out)) (from Hpref + Hsplit_out').
               * mask = 1 → opp 1 = 2^64 - 1 (all 1s in unsigned form).
                 (xor x y) & all1 = xor x y. Then xor x (xor x y) = y.
                 So expression = y = src_middle.
                 le_split 8 (word.unsigned y) = src_middle.
                 = firstn 8 (skipn offset src).
           - Combined: pref ++ new_middle = (firstn offset (if mask=0 then out else src)) ++ (firstn 8 (skipn offset (if mask=0 then out else src))) = firstn (offset+8) (if mask=0 then out else src).
           Lemmas needed:
           - LittleEndianList.le_split_le_combine: le_split n (le_combine bs) = bs when length bs = n.
           - word.opp_0 / unsigned_opp_eq for opp 0 = 0 and opp 1.
           - Properties.word.xor_and_or or specific bitwise identities.
         - skipn (8*(25-n')) out'' = skipn ... out: similar; suf is unchanged.
         - map.get for "out", "src", "mask", "m", "i": after subst l0 l1,
           rewrite map.get_put_diff chain + apply map.get_put_same.
         - sep predicate: ecancel_assumption_impl on the recombined Hsep_new.
         - tr = tr (preserved).
         - n' < S n': Lia.lia.

         Estimated total LoC for steps 5-8: ~250-350 LoC, plus ~50 LoC for
         the algebraic XOR identities in step 8 (might pose as separate Lemma).
       *)
      - intros Hbr_zero.
        apply Properties.word.if_zero in Hbr_zero.
        rewrite word.unsigned_ltu in Hbr_zero. apply Z.ltb_ge in Hbr_zero.
        rewrite word.unsigned_of_Z in Hbr_zero. cbv [word.wrap] in Hbr_zero.
        (* Hbr_zero now: 200 mod 2^64 <= word.unsigned iw *)
        destruct n; [|exfalso].
        + (* n = 0 case: out' has length 200, firstn 200 = if-mask *)
          cbn [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].
          ssplit; [reflexivity | symmetry; assumption | ].
          replace (8 * (25 - 0))%nat with 200%nat in Hpref by Lia.lia.
          rewrite (List.firstn_all2 (n:=200) out') in Hpref by (rewrite Hlen'; Lia.lia).
          rewrite (List.firstn_all2 (n:=200)
                     (if word.eqb mask (word.of_Z 0) then out else src)) in Hpref.
          2: { destruct (word.eqb mask (word.of_Z 0)); Lia.lia. }
          rewrite <- Hpref. ecancel_assumption.
        + (* n = S _: contradict via Hbr_zero + Hiw_val.
              The two `word.unsigned iw`s have different implicit args
              (typeclass mismatch); rewrite Hiw_val in Hbr_zero fails.
              Workaround: `remember` introduces `u` from Hiw_val's side,
              then `assert` restates Hbr_zero with `u` via
              `rewrite Hu; exact Hbr_zero` — the rewrite pulls out the
              right `word.unsigned iw` instance from Hbr_zero's type. *)
          remember (word.unsigned iw) as u eqn:Hu.
          assert (Hbr' : 200 mod 2^64 <= u) by (rewrite Hu; exact Hbr_zero).
          Lia.lia.
    }
    (* Plan:
       After straightline expands the function call + the two initial
       sets (m = 0 - mask; i = 0), we reach the while loop goal.

       Apply Loops.while_localsmap with measure = nat counting from 25
       down to 0, well-foundedness via Nat.lt_wf_0.

       Loop invariant inv (n: nat) tr mem locals :=
         exists (k : nat) iw mw,
           (n + k = 25)%nat /\
           map.get locals "out" = Some out_ptr /\
           map.get locals "src" = Some src_ptr /\
           map.get locals "mask" = Some mask /\
           map.get locals "m" = Some mw /\
           map.get locals "i" = Some iw /\
           word.unsigned iw = Z.of_nat (8 * k) /\
           mw = word.opp mask /\
           tr = original_tr /\
           ( exists out',
             Datatypes.length out' = 200%nat /\
             firstn (8 * k) out' = firstn (8 * k)
               (if word.eqb mask (word.of_Z 0) then out else src) /\
             skipn (8 * k) out' = skipn (8 * k) out /\
             ((out'$@out_ptr) ⋆ (src$@src_ptr) ⋆ R)%sep mem ).

       Entry: k=0, out'=out (so firstn 0 out' = firstn 0 _ trivially).
       Body: at iteration with measure (S n), k advances by 1.
       Exit: n=0, k=25, so out' = if mask=0 then out else src (by firstn/skipn). *)
  Qed.

End CMov5Felems.
