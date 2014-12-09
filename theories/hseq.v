Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype.
Require Import tuple bigop finfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Variable I : eqType.

Section Basic.

Variables (T_ : I -> Type) (idx : seq I).

Record hseq : predArgType :=
  HSeq {hsval :> seq {i : I & T_ i}; _ : map tag hsval == idx}.

Definition hstags of hseq := idx.

Canonical hseq_subType := [subType for hsval].

End Basic.

Definition hseq_eqMixin (T_ : I -> eqType) idx :=
  [eqMixin of hseq T_ idx by <:].
Canonical hseq_eqType (T_ : I -> eqType) idx :=
  EqType (hseq T_ idx) (hseq_eqMixin T_ idx).

Lemma tags_hseq T_ idx (hs : hseq T_ idx) : map tag hs = idx.
Proof. exact: (eqP (valP hs)). Qed.

End Def.

Definition hseq_choiceMixin (I : choiceType) (T_ : I -> choiceType) idx :=
  [choiceMixin of hseq T_ idx by <:].
Canonical hseq_choiceType (I : choiceType) (T_ : I -> choiceType) idx :=
  ChoiceType (hseq T_ idx) (hseq_choiceMixin T_ idx).
Definition hseq_countMixin (I : countType) (T_ : I -> countType) idx :=
  [countMixin of hseq T_ idx by <:].
Canonical hseq_countType (I : countType) (T_ : I -> countType) idx :=
  CountType (hseq T_ idx) (hseq_countMixin T_ idx).
Canonical hseq_subCountType (I : countType) (T_ : I -> countType) idx :=
  [subCountType of hseq T_ idx].

Module Type FinHSeqSig.
Section FinHSeqSig.
Variables (I : finType) (T_ : I -> finType) (idx : seq I).
Parameter enum : seq (hseq T_ idx).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = foldr muln 1 [seq #|T_ i| | i <- idx].
End FinHSeqSig.
End FinHSeqSig.

Module FinHSeq.
Section FinHSeq.
Variables (I : finType) (T_ : I -> finType) (idx : seq I).

Definition enum : seq (hseq T_ idx) :=
  let extend i e :=
      flatten (codom (fun x : T_ i => map (cons (Tagged T_ x)) e)) in
  pmap insub (foldr extend [::[::]] idx).

Lemma enumP : Finite.axiom enum.
Proof.
case=> /= hs Phs.
rewrite -(count_map _ (pred1 hs)) (pmap_filter (@insubK _ _ _)).
rewrite count_filter -(@eq_count _ (pred1 hs)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
elim: idx hs Phs => [|i idx' IH] [|[i' x] s] //= /eqP [Hi {IH}/eqP/IH].
rewrite {}Hi {i'} in x *; move: (foldr _ _ _) => eidx IH.
transitivity (x \in T_ i : nat)=> //.
rewrite -mem_enum codomE.
elim: (fintype.enum (T_ i)) (enum_uniq (T_ i))=> //= y e IHe /andP[/negPf ney].
rewrite count_cat count_map inE /preim /= {1}/eq_op /= eq_sym => {IHe}/IHe->.
rewrite -tag_eqE /tag_eq eqxx /= tagged_asE.
by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IH).
Qed.

Lemma size_enum : size enum = foldr muln 1 [seq #|T_ i| | i <- idx].
Proof.
rewrite /= size_pmap_sub; elim: idx=> [|i idx' /= <-] //=.
rewrite cardE /codom /image_mem; move: (foldr _ _ _) => e.
elim: (fintype.enum (T_ i)) => //= x xs IHxs.
rewrite count_cat {}IHxs count_map mulSn /preim /=; congr addn.
by apply: eq_count=> s /=; rewrite eqE /= eqxx.
Qed.

End FinHSeq.
End FinHSeq.

Section UseFinHSeq.

Variables (I : finType) (T_ : I -> finType) (idx : seq I).

Definition hseq_finMixin := FinMixin (@FinHSeq.enumP I T_ idx).
Canonical hseq_finType := Eval hnf in FinType (hseq T_ idx) hseq_finMixin.
Canonical hseq_subFinType := [subFinType of hseq T_ idx].

End UseFinHSeq.

(* FIXME: find a better name for this *)
Definition mkhseq (I : eqType) T_ (idx : seq I) (hs : hseq T_ idx)
                  (mkHs : map tag hs == idx -> hseq T_ idx) :=
  mkHs (let: HSeq _ hsP := hs return map tag hs == idx in hsP).

Lemma mkhseqE (I : eqType) T_ (idx : seq I) (hs : hseq T_ idx) :
  mkhseq (fun Phs => @HSeq I T_ idx hs Phs) = hs.
Proof. by case: hs. Qed.

Notation "[ 'hseq' 'of' hs ]" :=
  (mkhseq (fun hsP => @HSeq _ _ _ hs hsP))
  (at level 0, format "[ 'hseq'  'of'  hs ]") : form_scope.

Notation "[ 'hseq' ]" := [hseq of [::]]
  (at level 0, format "[ 'hseq' ]") : form_scope.

Notation "[ 'hseq' x ; .. ; y ]" :=
  [hseq of Tagged _ x :: .. [:: Tagged _ y] ..]
  (at level 0, format "[ 'hseq' '[' x ; '/' .. ; '/' y ']' ]") : form_scope.

Section HIdx.

Section Def.

Variable (I : eqType) (i : I) (idx : seq I).

Record hidx := HIdx {
  hival :> 'I_(size idx);
  _ : tnth (in_tuple idx) hival == i
}.

Canonical hidx_subType := [subType for hival].
Definition hidx_eqMixin := [eqMixin of hidx by <:].
Canonical hidx_eqType := EqType hidx hidx_eqMixin.
Definition hidx_choiceMixin := [choiceMixin of hidx by <:].
Canonical hidx_choiceType := ChoiceType hidx hidx_choiceMixin.
Definition hidx_countMixin := [countMixin of hidx by <:].
Canonical hidx_countType := CountType hidx hidx_countMixin.
Canonical hidx_subCountType := [subCountType of hidx].
Definition hidx_finMixin := [finMixin of hidx by <:].
Canonical hidx_finType := FinType hidx hidx_finMixin.
Canonical hidx_subFinType := [subFinType of hidx].

Lemma card_hidx : #|{: hidx}| = count (pred1 i) idx.
Proof.
rewrite card_sub -sum1_card big_mkcond /=.
pose f (x : 'I_(size idx)) := nth i idx x == i : nat.
rewrite (eq_big_seq f) /= {}/f; last first.
  by move=> i' _; rewrite /= inE (tnth_nth i).
elim: idx => /= [|i' idx' <-]; first by rewrite big_ord0.
by rewrite big_mkcond /= big_ord_recl /= -big_mkcond /=.
Qed.

Lemma tuple_of_hseq_proof T_ (hs : hseq T_ idx) : size hs == size idx.
Proof. by rewrite -[in X in _ == X](eqP (valP hs)) size_map. Qed.
Canonical tuple_of_hseq T_ (hs : hseq T_ idx) := Tuple (tuple_of_hseq_proof hs).

Lemma hnth_proof T_ (hs : hseq T_ idx) (n : hidx) :
  tag (tnth [tuple of hs] n) = i.
Proof.
case: hs n => [t /= Ht] [n /= /eqP <-] /=.
rewrite (tnth_nth i) -[in X in nth _ X _](eqP Ht).
by rewrite -tnth_map /= (tnth_nth i).
Qed.

Definition hnth T_ (hs : hseq T_ idx) (n : hidx) : T_ i :=
  eq_rect _ T_ (tagged (tnth [tuple of hs] n)) _ (hnth_proof hs n).

End Def.

Definition hidx0 {I : eqType} {i : I} {idx : seq I} : hidx i (i :: idx) :=
  HIdx (eqxx _ : tnth (in_tuple (i :: idx)) (ord0 : 'I_(size idx).+1) == i).

Definition hshead (I : eqType) (T_ : I -> Type) i idx (hs : hseq T_ (i :: idx))
                  : T_ i :=
  hnth hs hidx0.

End HIdx.

Notation "[ 'hnth' hs i ]" :=
  (let i' := @Ordinal (size (hstags hs)) i (erefl true) in
   hnth hs (@HIdx _ _ (hstags hs) i' (eqxx (tnth (in_tuple (hstags hs)) i'))))
  (at level 0, hs, i at level 8, format "[ 'hnth'  hs  i ]") : form_scope.

Section SeqHSeq.

Variables (I : eqType) (T_ : I -> Type) (idx : seq I).

Canonical nil_hseq (I : eqType) (T_ : I -> Type) :=
  @HSeq I T_ [::] [::] isT.

Lemma cons_hseqP i (x : T_ i) (hs : hseq T_ idx) :
  map tag (Tagged T_ x :: hs) == i :: idx.
Proof. by rewrite /= tags_hseq. Qed.
Canonical cons_hseq i (x : T_ i) (hs : hseq T_ idx) :=
  @HSeq _ _ (i :: idx) _ (cons_hseqP x hs).

Lemma cat_hseqP idx' (hs : hseq T_ idx) (hs' : hseq T_ idx') :
  map tag (hs ++ hs') == idx ++ idx'.
Proof. by rewrite map_cat !tags_hseq. Qed.
Canonical cat_hseq idx' hs (hs' : hseq T_ idx') :=
  HSeq (cat_hseqP hs hs').

Lemma behead_hseqP (hs : hseq T_ idx) : map tag (behead hs) == behead idx.
Proof. by rewrite -behead_map tags_hseq. Qed.
Canonical behead_hseq hs := HSeq (behead_hseqP hs).

End SeqHSeq.

Lemma hseq_nil (I : eqType) (T_ : I -> Type) :
  all_equal_to ([hseq of [::]] : hseq T_ [::]).
Proof. by move=> [[|??] Phs]; apply: val_inj=> //=. Qed.

CoInductive hseq_cons_spec (I : eqType) (T_ : I -> Type) i idx
  : hseq T_ (i :: idx) -> Type :=
  HSeqConsSpec x (hs : hseq T_ idx)
  : hseq_cons_spec [hseq of Tagged T_ x :: hs].

Lemma hseqP (I : eqType) (T_ : I -> Type) i idx (hs : hseq T_ (i :: idx))
  : hseq_cons_spec hs.
Proof.
case: hs => [[|[i' x] s] // Phs].
have Hi : i' = i by case/andP: Phs => [/eqP Hi _].
rewrite {}Hi {i'} in x Phs *.
have Ps : map tag s == idx by move: (eqP Phs) => /= [->].
pose hs := HSeq Ps.
rewrite (_ : @HSeq _ _ (i :: idx) _ Phs = [hseq of Tagged T_ x :: hs]) //.
by apply: val_inj.
Qed.

Lemma hsheadE (I : eqType) (T_ : I -> Type) i idx
              (x : T_ i) (hs : hseq T_ idx) :
  hshead [hseq of Tagged T_ x :: hs] = x.
Proof. by rewrite /hshead /= /hnth eq_axiomK /=. Qed.

Lemma hseq_eta (I : eqType) (T_ : I -> Type) i idx :
  forall hs : hseq T_ (i :: idx),
    hs = [hseq of Tagged T_ (hshead hs) :: behead hs].
Proof.
by move=> hs; case/hseqP: hs => x hs; rewrite hsheadE /=; apply: val_inj.
Qed.

Lemma hmap_proof (I : eqType) (T_ S_ : I -> Type) (idx : seq I)
                 (f : forall i, T_ i -> S_ i) (hs : hseq T_ idx) :
  map tag (map (fun t => Tagged S_ (f (tag t) (tagged t))) hs) == idx.
Proof. by rewrite -map_comp /funcomp tags_hseq. Qed.

Definition hmap (I : eqType) (T_ S_ : I -> Type) (idx : seq I)
                (f : forall i, T_ i -> S_ i) (hs : hseq T_ idx) :=
  HSeq (hmap_proof f hs).

Lemma hmapK (I : eqType) T_ S_ idx
            (f : forall i : I, T_ i -> S_ i)
            (g : forall i : I, S_ i -> T_ i) :
  (forall i, cancel (f i) (g i)) ->
  cancel (hmap f : hseq T_ idx -> _) (hmap g).
Proof.
by move=> Hfg hs; apply: val_inj; apply: mapK=> - [i x] /=; rewrite Hfg.
Qed.

Fixpoint split_tuple T ns :
  (sumn ns).-tuple T -> hseq (fun n => n.-tuple T) ns :=
  match ns with
  | [::] => fun t => [hseq of [::]]
  | n :: ns' =>
    fun t =>
      let t1 := [tuple of take n t] in
      let ts := [tuple of drop n t] in
      [hseq of Tagged _ (tcast (minn_idPl (leq_addr (sumn ns') n)) t1) ::
                        split_tuple (tcast (addKn n (sumn ns')) ts)]
  end.

Fixpoint merge_tuple T ns :
  hseq (fun n => n.-tuple T) ns -> (sumn ns).-tuple T :=
  match ns with
  | [::] =>
    fun hs => [tuple]
  | n :: ns' =>
    fun hs => [tuple of hshead hs ++ merge_tuple [hseq of behead hs]]
  end.

Lemma merge_tupleK T ns : cancel (@merge_tuple T ns) (@split_tuple T ns).
Proof.
elim: ns => [|n ns IH] hs //=; first by rewrite hseq_nil [in RHS]hseq_nil.
case/hseqP: hs=> t hs /=; rewrite hsheadE /=.
apply: val_inj=> /=; congr cons.
  congr Tagged.
  set t' := [tuple of take _ _]; move: (minn_idPl _)=> E.
  have : val t' = val t by rewrite /t' /= take_size_cat //= size_tuple.
  by move: (E) t'; rewrite {}E=> E t'; rewrite tcast_id; apply: val_inj.
set t' := [tuple of drop _ _]; move: (addKn _ _) => E.
suff -> : tcast E t' = merge_tuple hs by rewrite IH.
have : val t' = val (merge_tuple hs).
  rewrite /t' /= drop_size_cat // ?size_tuple // mkhseqE //=.
  by congr merge_tuple; apply: val_inj.
by move: (E) t'; rewrite {}E=> E t'; rewrite tcast_id; apply: val_inj.
Qed.

Lemma split_tupleK T ns : cancel (@split_tuple T ns) (@merge_tuple T ns).
Proof.
elim: ns => [|n ns IH] /= t //=; first by rewrite [in RHS]tuple0.
have H : forall m (E : m = n) t', val (tcast E t') = val t'.
  by move=> T' m E; move: (E); rewrite {}E => E t'; rewrite tcast_id.
rewrite hsheadE; apply: val_inj=> /=; rewrite !{}H /=.
rewrite -[in RHS](cat_take_drop n t); congr cat.
rewrite -[drop n t]/(val [tuple of drop n t]).
move: (addKn _ _) [tuple of drop n t] => E; move: (E); rewrite {}E=> E t'.
by rewrite tcast_id -[in RHS](IH t') /=; congr merge_tuple; apply: val_inj.
Qed.
