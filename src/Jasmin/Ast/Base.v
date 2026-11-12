(** * Words, bytes and memories: bedrock2 (coqutil) against Jasmin. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory.
From Stdlib Require Import ZArith Lia String List.
Require coqutil.Word.Interface coqutil.Word.Properties coqutil.Byte.
Require coqutil.Word.LittleEndianList coqutil.Map.Interface coqutil.Map.Memory.
Set SsrOldRewriteGoalsOrder.

Module CW := coqutil.Word.Interface.word.
Module CWP := coqutil.Word.Properties.word.

Local Open Scope Z_scope.

Section W.
  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Local Notation w64 := (@CW.rep 64 W).

  (** A bedrock2 word as a Jasmin u64. *)
  Definition jw (v : w64) : u64 := wrepr U64 (CW.unsigned v).

  Lemma wbase64 : wbase U64 = 2 ^ 64.
  Proof. reflexivity. Qed.

  Lemma wunsigned_jw v : wunsigned (jw v) = CW.unsigned v.
  Proof.
    rewrite /jw wunsigned_repr_small //; rewrite wbase64.
    exact: CWP.unsigned_range.
  Qed.

  Lemma jw_inj a b : jw a = jw b -> a = b.
  Proof. move=> h; apply: CWP.unsigned_inj; by rewrite -!wunsigned_jw h. Qed.

  Lemma jw_wrap z : wrepr U64 (CW.wrap z) = wrepr U64 z.
  Proof. by rewrite /CW.wrap -wbase64 wrepr_mod. Qed.

  Lemma jw_of_Z z : jw (CW.of_Z z) = wrepr U64 z.
  Proof. by rewrite /jw CW.unsigned_of_Z jw_wrap. Qed.

  Lemma jw_add a b : jw (CW.add a b) = (jw a + jw b)%R.
  Proof. by rewrite /jw CW.unsigned_add jw_wrap wrepr_add. Qed.

  Lemma jw_sub a b : jw (CW.sub a b) = (jw a - jw b)%R.
  Proof. by rewrite /jw CW.unsigned_sub jw_wrap wrepr_sub. Qed.

  Lemma jw_mul a b : jw (CW.mul a b) = (jw a * jw b)%R.
  Proof. by rewrite /jw CW.unsigned_mul jw_wrap wrepr_mul. Qed.

  Lemma wunsigned_inj' (x y : u64) : wunsigned x = wunsigned y -> x = y.
  Proof. exact: wunsigned_inj. Qed.

  Lemma jw_and a b : jw (CW.and a b) = wand (jw a) (jw b).
  Proof.
    apply: wunsigned_inj; rewrite wunsigned_jw CWP.unsigned_and_nowrap.
    by rewrite /wunsigned /wand word.urepr_wand -!/(wunsigned _) !wunsigned_jw.
  Qed.

  Lemma jw_or a b : jw (CW.or a b) = wor (jw a) (jw b).
  Proof.
    apply: wunsigned_inj; rewrite wunsigned_jw CWP.unsigned_or_nowrap.
    by rewrite /wunsigned /wor word.urepr_wor -!/(wunsigned _) !wunsigned_jw.
  Qed.

  Lemma jw_xor a b : jw (CW.xor a b) = wxor (jw a) (jw b).
  Proof.
    apply: wunsigned_inj; rewrite wunsigned_jw CWP.unsigned_xor_nowrap.
    by rewrite /wunsigned /wxor word.urepr_wxor -!/(wunsigned _) !wunsigned_jw.
  Qed.

  Lemma jw_mulhuu a b : jw (CW.mulhuu a b) = high_bits U64 (wunsigned (jw a) * wunsigned (jw b)).
  Proof.
    rewrite high_bits_wbase !wunsigned_jw /jw CW.unsigned_mulhuu jw_wrap wbase64; reflexivity.
  Qed.

  Lemma jw_sru a k : 0 <= k < 64 ->
    jw (CW.sru a (CW.of_Z k)) = wshr (jw a) k.
  Proof.
    move=> hk; apply: wunsigned_inj.
    have hu : CW.unsigned (CW.of_Z (word:=W) k) = k.
    { rewrite CW.unsigned_of_Z /CW.wrap Z.mod_small //. split; [lia|].
      apply: (Z.lt_le_trans _ 64); [lia|]. by apply: (Z.pow_le_mono_r 2 6 64) => //; lia. }
    rewrite wunsigned_jw CWP.unsigned_sru_nowrap hu; last lia.
    rewrite /wshr Z.min_r; last by rewrite /wsize_bits /=; lia.
    have hm : word.modulus (wsize_size_minus_1 U64).+1 = 2 ^ 64 by reflexivity.
    rewrite /wunsigned word.mkwordK -/(wunsigned _) wunsigned_jw hm.
    have [h0 h1] := CWP.unsigned_range a.
    have hle : Z.shiftr (CW.unsigned a) k <= CW.unsigned a.
    { rewrite Z.shiftr_div_pow2; [|lia].
      apply: Z.div_le_upper_bound; first by apply: Z.pow_pos_nonneg; lia.
      have : 1 <= 2 ^ k by apply: (Z.pow_le_mono_r 2 0 k); lia.
      nia. }
    have hnn : 0 <= Z.shiftr (CW.unsigned a) k by apply Z.shiftr_nonneg; lia.
    rewrite Z.mod_small //; lia.
  Qed.

  Lemma jw_slu a k : 0 <= k < 64 ->
    jw (CW.slu a (CW.of_Z k)) = wshl (jw a) k.
  Proof.
    move=> hk; apply: wunsigned_inj.
    have hu : CW.unsigned (CW.of_Z (word:=W) k) = k.
    { rewrite CW.unsigned_of_Z /CW.wrap Z.mod_small //. split; [lia|].
      apply: (Z.lt_le_trans _ 64); [lia|]. by apply: (Z.pow_le_mono_r 2 6 64) => //; lia. }
    rewrite wunsigned_jw CW.unsigned_slu hu; last lia.
    rewrite /wshl Z.min_r; last by rewrite /wsize_bits /=; lia.
    have hm : word.modulus (wsize_size_minus_1 U64).+1 = 2 ^ 64 by reflexivity.
    by rewrite /wunsigned word.mkwordK -/(wunsigned _) wunsigned_jw hm.
  Qed.

  Lemma jw_ltu a b : CW.ltu a b = wlt Unsigned (jw a) (jw b).
  Proof. by rewrite CW.unsigned_ltu /wlt -!/(wunsigned _) !wunsigned_jw. Qed.

  Lemma jw_eqb a b : CW.eqb a b = (jw a == jw b).
  Proof.
    rewrite CW.unsigned_eqb -!wunsigned_jw.
    case: eqP => [->|hne]; first by rewrite Z.eqb_refl.
    by apply/Z.eqb_spec => /wunsigned_inj.
  Qed.

  Lemma jw_opp a : jw (CW.opp a) = (0 - jw a)%R.
  Proof. by rewrite /jw CW.unsigned_opp jw_wrap -(Z.sub_0_l (CW.unsigned a)) wrepr_sub wrepr0. Qed.

  Lemma jw0 : jw (CW.of_Z 0) = 0%R.
  Proof. by rewrite jw_of_Z wrepr0. Qed.
  Lemma jw1 : jw (CW.of_Z 1) = 1%R.
  Proof. by rewrite jw_of_Z wrepr1. Qed.
End W.

(** ** Bytes and memories *)
Require bedrock2.Memory bedrock2.Syntax.
From Jasmin Require Import arch_decl x86_decl.

Section M.
  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Local Notation w64 := (@CW.rep 64 W).
  Context {Mem : coqutil.Map.Interface.map.map w64 coqutil.Byte.byte}
          {Mem_ok : coqutil.Map.Interface.map.ok Mem}.
  #[local] Existing Instance x86_decl.
  Local Notation pd := (@arch_pd _ _ _ _ _ x86_decl).
  #[local] Existing Instance arch_pd.

  Lemma size_length {A} (l : list A) : size l = length l.
  Proof. by elim: l => //= _ l ->. Qed.

  Lemma nth_nth {A} (d : A) (l : list A) (i : nat) : seq.nth d l i = List.nth i l d.
  Proof. by elim: l i => [|x l ih] [|i] //=. Qed.

  Definition jb (b : coqutil.Byte.byte) : u8 := wrepr U8 (coqutil.Byte.byte.unsigned b).

  Lemma wunsigned_jb b : wunsigned (jb b) = coqutil.Byte.byte.unsigned b.
  Proof.
    rewrite /jb wunsigned_repr_small //.
    have := coqutil.Byte.byte.unsigned_range b; rewrite (_ : wbase U8 = 256) //.
  Qed.

  Lemma wcat_r_jb (l : list coqutil.Byte.byte) :
    word.wcat_r [seq jb b | b <- l] = coqutil.Word.LittleEndianList.le_combine l.
  Proof.
    elim: l => [|b l ih] //.
    cbn [word.wcat_r seq.map coqutil.Word.LittleEndianList.le_combine].
    have h := wunsigned_jb b; rewrite /wunsigned in h.
    by rewrite ih h.
  Qed.

  Lemma decode_jb (l : list coqutil.Byte.byte) :
    LE.decode U64 [seq jb b | b <- l] = wrepr U64 (coqutil.Word.LittleEndianList.le_combine l).
  Proof. by rewrite /LE.decode /make_vec wcat_r_jb. Qed.

  Lemma encode_jw (v : w64) :
    LE.encode (jw v) = [seq jb b | b <- coqutil.Word.LittleEndianList.le_split 8 (CW.unsigned v)].
  Proof.
    have h1 : size (LE.encode (jw v)) =
      size [seq jb b | b <- coqutil.Word.LittleEndianList.le_split 8 (CW.unsigned v)].
    { by rewrite LE.size_encode size_map size_length coqutil.Word.LittleEndianList.length_le_split. }
    have h2 : size (LE.encode (jw v)) = Z.to_nat (wsize_size U64).
    { by rewrite LE.size_encode. }
    apply: (LE.decode_inj h1 h2).
    rewrite LE.decodeK decode_jb coqutil.Word.LittleEndianList.le_combine_split.
    rewrite /jw Z.mod_small //.
    exact: CWP.unsigned_range v.
  Qed.

  Lemma wread8_jw (v : w64) (i : nat) : (i < 8)%nat ->
    LE.wread8 (jw v) (Z.of_nat i) =
      jb (List.nth i (coqutil.Word.LittleEndianList.le_split 8 (CW.unsigned v)) Init.Byte.x00).
  Proof.
    move=> hi; rewrite /LE.wread8 encode_jw Nat2Z.id.
    rewrite (nth_map Init.Byte.x00); last by rewrite size_length coqutil.Word.LittleEndianList.length_le_split.
    by rewrite nth_nth.
  Qed.
  Local Notation get := coqutil.Map.Interface.map.get.

  Definition pt (w : u64) : pointer := w.
  Definition jp (a : w64) : pointer := pt (jw a).

  (** Every byte of the bedrock2 memory is readable in the Jasmin memory, with the same value. *)
  Definition mem_rel (m : @coqutil.Map.Interface.map.rep _ _ Mem) (jm : low_memory.mem) : Prop :=
    forall a b, get m a = Some b -> read jm Aligned (jp a) U8 = ok (jb b).

  Lemma jw_add_of_Z (a : w64) (i : Z) : jw (CW.add a (CW.of_Z i)) = (jw a + wrepr U64 i)%R.
  Proof. by rewrite jw_add jw_of_Z. Qed.

  Lemma bytes_per_word8 : bedrock2.Memory.bytes_per (width:=64) Syntax.access_size.word = 8%nat.
  Proof. reflexivity. Qed.

  Lemma unsigned_le_combine8 (bs : list coqutil.Byte.byte) : length bs = 8%nat ->
    CW.unsigned (CW.of_Z (word:=W) (coqutil.Word.LittleEndianList.le_combine bs)) =
      coqutil.Word.LittleEndianList.le_combine bs.
  Proof.
    move=> hl; rewrite CW.unsigned_of_Z /CW.wrap Z.mod_small //.
    have := coqutil.Word.LittleEndianList.le_combine_bound bs; rewrite hl; exact.
  Qed.

  Lemma mem_rel_load {m jm a v} :
    mem_rel m jm -> bedrock2.Memory.load Syntax.access_size.word m a = Some v ->
    read jm Unaligned (jp a) U64 = ok (jw v).
  Proof.
    move=> hrel; rewrite /bedrock2.Memory.load /coqutil.Map.Memory.load_Z bytes_per_word8.
    case hb: (coqutil.Map.Memory.load_bytes m a 8) => [bs|] //= [<-].
    have hlen := coqutil.Map.Memory.length_load_bytes _ _ _ _ hb.
    rewrite (@read8_read _ _ _ _ jm Unaligned (jp a) U64 (jw (CW.of_Z (coqutil.Word.LittleEndianList.le_combine bs)))) //.
    move=> al' i hi.
    have hi' : (0 <= i < 8)%Z by move: hi; rewrite /wsize_size.
    pose n := Z.to_nat i.
    have hn : (n < 8)%coq_nat by rewrite /n; lia.
    have hget := coqutil.Map.Memory.nth_error_load_bytes _ _ _ _ hb _ hn.
    have hin : i = Z.of_nat n by rewrite /n Z2Nat.id //; lia.
    case hnth : (List.nth_error bs n) hget => [bn|] hget; last first.
    { exfalso; apply: (proj2 (List.nth_error_Some bs n)); [rewrite hlen; exact hn | exact hnth]. }
    rewrite (read8_alignment Aligned) addE.
    have -> : (jp a + wrepr Uptr i)%R = jp (CW.add a (CW.of_Z i)) by rewrite /jp jw_add_of_Z.
    rewrite (hrel _ bn); last by rewrite hin hget.
    rewrite hin wread8_jw; last by apply/ltP.
    rewrite unsigned_le_combine8 // -hlen coqutil.Word.LittleEndianList.split_le_combine.
    by rewrite (List.nth_error_nth bs n _ hnth).
  Qed.

  (** The Jasmin memory outside the image of the bedrock2 domain. *)
  Definition outside (m : @coqutil.Map.Interface.map.rep _ _ Mem) (p : pointer) : Prop :=
    forall a, jp a = p -> get m a = None.

  Lemma jp_sub (k a : w64) : sub (jp k) (jp a) = CW.unsigned (CW.sub k a).
  Proof. by rewrite subE /jp -jw_sub wunsigned_jw. Qed.

  Lemma mem_rel_valid {m jm a} : mem_rel m jm -> get m a <> None -> validw jm Aligned (jp a) U8.
  Proof.
    move=> hrel; case h: (get m a) => [b|] // _.
    exact: (readV (hrel _ _ h)).
  Qed.

  Lemma mem_rel_store {m jm a v m'} :
    mem_rel m jm -> bedrock2.Memory.store Syntax.access_size.word m a v = Some m' ->
    exists jm', [/\ write jm Unaligned (jp a) (jw v) = ok jm', mem_rel m' jm',
      (forall k, get m' k = None <-> get m k = None) &
      (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hrel; rewrite /bedrock2.Memory.store /coqutil.Map.Memory.store_Z bytes_per_word8.
    rewrite /coqutil.Map.Memory.store_bytes coqutil.Word.LittleEndianList.length_le_split.
    case hb: (coqutil.Map.Memory.load_bytes m a 8) => [bs0|] // [<-].
    set bs := coqutil.Word.LittleEndianList.le_split 8 (CW.unsigned v).
    have hlen0 := coqutil.Map.Memory.length_load_bytes _ _ _ _ hb.
    have hin : forall i, (i < 8)%coq_nat -> get m (CW.add a (CW.of_Z (Z.of_nat i))) <> None.
    { move=> i hi; have := coqutil.Map.Memory.nth_error_load_bytes _ _ _ _ hb _ hi.
      move=> <-; apply/List.nth_error_Some; lia. }
    have hval : validw jm Unaligned (jp a) U64.
    { apply/validwP; split => // k hk.
      have hk' : (0 <= k < 8)%Z by move: hk; rewrite /wsize_size.
      rewrite (validw8_alignment Aligned) addE.
      have -> : (jp a + wrepr Uptr k)%R = jp (CW.add a (CW.of_Z k)) by rewrite /jp jw_add_of_Z.
      apply: (mem_rel_valid hrel).
      have hk8 : (Z.to_nat k < 8)%coq_nat by lia.
      have := hin (Z.to_nat k) hk8; by rewrite Z2Nat.id; [|lia]. }
    have [jm' hw] := elimT (writeV (jw v) jm Unaligned (jp a)) hval.
    exists jm'; split; first exact hw.
    { move=> k b; rewrite /coqutil.Map.Memory.unchecked_store_bytes coqutil.Map.Properties.map.get_putmany_dec.
      rewrite coqutil.Map.OfListWord.map.get_of_list_word_at.
      rewrite (write_read8 hw) /= jp_sub.
      have [hu0 hu1] := CWP.unsigned_range (CW.sub k a).
      case: (ZltP (CW.unsigned (CW.sub k a)) 8) => hlt.
      { have hlt' : (Z.to_nat (CW.unsigned (CW.sub k a)) < length bs)%coq_nat.
        { rewrite /bs coqutil.Word.LittleEndianList.length_le_split; lia. }
        case hn: (List.nth_error bs _) => [b'|]; last by move: hn; move/List.nth_error_None; lia.
        move=> [<-]; rewrite (_ : (0 <=? _)%Z = true); last by apply/Z.leb_le.
        rewrite /=.
        rewrite -(Z2Nat.id (CW.unsigned (CW.sub k a))) // wread8_jw; last by apply/ltP; lia.
        by rewrite -/bs (List.nth_error_nth _ _ _ hn).
      }
      { have hge : (length bs <= Z.to_nat (CW.unsigned (CW.sub k a)))%coq_nat.
        { rewrite /bs coqutil.Word.LittleEndianList.length_le_split; lia. }
        rewrite (proj2 (List.nth_error_None _ _) hge) => hk.
        rewrite andbF; exact: hrel.
      }
    }
    { move=> k; rewrite /coqutil.Map.Memory.unchecked_store_bytes coqutil.Map.Properties.map.get_putmany_dec.
      rewrite coqutil.Map.OfListWord.map.get_of_list_word_at.
      case hn: (List.nth_error bs _) => [b'|]; last by [].
      split => // hnone; exfalso.
      have hlt : (Z.to_nat (CW.unsigned (CW.sub k a)) < 8)%coq_nat.
      { have := proj1 (List.nth_error_Some bs (Z.to_nat (CW.unsigned (CW.sub k a)))).
        rewrite hn /bs coqutil.Word.LittleEndianList.length_le_split; apply => //. }
      apply: (hin _ hlt).
      have hnn : 0 <= CW.unsigned (CW.sub k a) by have [? ?] := CWP.unsigned_range (CW.sub k a); lia.
      rewrite Z2Nat.id //.
      rewrite CW.of_Z_unsigned (_ : CW.add a (CW.sub k a) = k) //.
      apply: CWP.unsigned_inj; rewrite CW.unsigned_add CW.unsigned_sub /CW.wrap Zplus_mod_idemp_r.
      rewrite (_ : CW.unsigned a + (CW.unsigned k - CW.unsigned a) = CW.unsigned k); last by ring.
      by rewrite Z.mod_small //; apply: CWP.unsigned_range.
    }
    { move=> p hout; rewrite (write_read8 hw) /=.
      have [i hi] : exists i, sub p (jp a) = i by eexists.
      rewrite hi.
      case: ZleP => h0 //=; case: ZltP => h1 //=; exfalso.
      have hp : p = jp (CW.add a (CW.of_Z i)).
      { rewrite /jp jw_add_of_Z -/(jp a) -hi subE wrepr_unsigned.
        by rewrite GRing.addrC GRing.subrK. }
      have hi8 : (Z.to_nat i < 8)%coq_nat by move: h1; rewrite /wsize_size; lia.
      have h1' := hin (Z.to_nat i) hi8; rewrite Z2Nat.id // in h1'.
      exact: h1' (hout _ (esym hp)).
    }
  Qed.
End M.
