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
  let extend i e := flatten (codom (fun x : T_ i => map (cons (Tagged T_ x)) e)) in
  pmap insub (foldr extend [::[::]] idx).

Lemma enumP : Finite.axiom enum.
Proof.
case=> /= hs Phs; rewrite -(count_map _ (pred1 hs)) (pmap_filter (@insubK _ _ _)).
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

Notation "[ 'hseq' 'of' hs ]" :=
  (mkhseq (fun hsP => @HSeq _ _ _ hs hsP))
  (at level 0, format "[ 'hseq'  'of'  hs ]") : form_scope.

Section HIdx.

Section Def.

Variable (I : eqType) (i : I) (idx : seq I).

Record hidx := HIdx {hival :> 'I_(size idx); _ : nth i idx hival == i}.

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
rewrite card_sub -sum1_card.
elim: idx => /= [|i' idx' <-]; first by rewrite big_ord0.
by rewrite big_mkcond /= big_ord_recl /= !inE /= -big_mkcond /=.
Qed.

Lemma tuple_of_hseq_proof T_ (hs : hseq T_ idx) : size hs == size idx.
Proof. by rewrite -[in X in _ == X](eqP (valP hs)) size_map. Qed.
Canonical tuple_of_hseq T_ (hs : hseq T_ idx) := Tuple (tuple_of_hseq_proof hs).

Lemma hnth_proof T_ (hs : hseq T_ idx) (n : hidx) : tag (tnth [tuple of hs] n) = i.
Proof.
case: hs n => [t /= Ht] [n /= /eqP <-] /=.
rewrite -[in X in nth _ X _](eqP Ht).
by rewrite -tnth_map /= (tnth_nth i).
Qed.

Definition hnth T_ (hs : hseq T_ idx) (n : hidx) : T_ i :=
  eq_rect _ T_ (tagged (tnth [tuple of hs] n)) _ (hnth_proof hs n).

End Def.

End HIdx.

Section SeqHSeq.

Variables (I : eqType) (T_ : I -> Type) (idx : seq I).

Lemma cons_hseqP i (x : T_ i) (hs : hseq T_ idx) :
  map tag (Tagged T_ x :: hs) == i :: idx.
Proof. by rewrite /= tags_hseq. Qed.

Canonical cons_hseq i (x : T_ i) (hs : hseq T_ idx) :=
  @HSeq _ _ (i :: idx) _ (cons_hseqP x hs).

Check (fun i (x : T_ i) (hs : hseq T_ idx) =>
         [hseq of Tagged T_ x :: hs]).

End SeqHSeq.
