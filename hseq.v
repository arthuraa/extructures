Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype.
Require Import tuple bigop finfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HSeq.

Section Def.

Variable I : eqType.

Section Basic.

Variables (T_ : I -> Type) (idx : seq I).

Record hseq : predArgType :=
  HSeq {hsval :> (size idx).-tuple {i : I & T_ i}; _ : map tag hsval == idx}.

Canonical hseq_subType := [subType for hsval].

End Basic.

Definition hseq_eqMixin (T_ : I -> eqType) idx :=
  [eqMixin of hseq T_ idx by <:].
Canonical hseq_eqType (T_ : I -> eqType) idx :=
  EqType (hseq T_ idx) (hseq_eqMixin T_ idx).

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
Definition hseq_finMixin (I : finType) (T_ : I -> finType) idx :=
  [finMixin of hseq T_ idx by <:].
Canonical hseq_finType (I : finType) (T_ : I -> finType) idx :=
  FinType (hseq T_ idx) (hseq_finMixin T_ idx).
Canonical hseq_subFinType (I : finType) (T_ : I -> finType) idx :=
  [subFinType of hseq T_ idx].

Lemma card_hseq (I : finType) (T_ : I -> finType) (idx : seq I) :
  #|hseq T_ idx| = foldr muln 1 [seq #|T_ i| | i <- idx].
Proof.
rewrite card_sub; elim: idx=> [|i idx IH] /=.
  by rewrite (@eq_card1 _ [tuple]) // => x /=; rewrite !inE tuple0.
pose X := {i' : I & T_ i'}.
have -> : #|T_ i| = #|[pred x : X | tag x == i]|.
  pose in_X (t : T_ i) := Tagged T_ t.
  have in_X_inj : injective in_X.
    move=> x y /eqP; rewrite /in_X -tag_eqE /tag_eq /= tagged_asE.
    by case/andP => [_ /eqP].
  rewrite -(card_image in_X_inj); apply: eq_card=> x; rewrite !inE.
  apply/(sameP idP)/(iffP idP).
    case: x => [i' x] /= /eqP Hi'; rewrite {}Hi' {i'} in x *.
    by rewrite mem_image //.
  by move: x => _ /imageP [x Hx ->]; rewrite eqxx.
rewrite -{}IH -cardX /=.
pose f (t : (size idx).+1.-tuple X) := (thead t, [tuple of behead t]).
have f_inj : injective f.
  move=> t1 t2 /=; case/tupleP: t1=> [x1 t1]; case/tupleP: t2=> [x2 t2] /=.
  by rewrite /f !theadE=> - [-> E]; apply: val_inj=> /=; rewrite E.
rewrite -(card_image f_inj); apply: eq_card=> - [x t] /=; rewrite !inE /=.
have -> : (x, t) = f [tuple of x :: t].
  by rewrite /f /= theadE; congr pair; apply: val_inj.
by rewrite mem_image.
Qed.

End HSeq.

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

Lemma hnth_proof T_ (hs : hseq T_ idx) (n : hidx) : tag (tnth hs n) = i.
Proof.
case: hs n => [t /= /eqP Ht] [n /= /eqP <-] /=.
rewrite -{2}Ht -(@tnth_nth _ _ _ [tuple of [seq tag i | i <- t]]).
by rewrite tnth_map.
Qed.

Definition hnth T_ (hs : hseq T_ idx) (n : hidx) : T_ i :=
  eq_rect _ T_ (tagged (tnth hs n)) _ (hnth_proof hs n).

End Def.

End HIdx.
