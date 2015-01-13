Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice fintype seq.
Require Import div ssralg finalg zmodp bigop tuple finfun binomial.
Require Import ssrint intdiv.
Require Import hseq ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Some of the Ssreflect constructions require 1 != 0 (e.g. the
zmodType structure). To go around this limitation while allowing for
the maximum flexibility, we add a type of non-zero natural numbers. *)

Structure non_zero : Type := NonZero {
  nat_of_non_zero :> nat;
  _ : nat_of_non_zero != 0
}.

Canonical non_zero_subType := [subType for nat_of_non_zero].
Definition non_zero_eqMixin := [eqMixin of non_zero by <:].
Canonical non_zero_eqType := Eval hnf in EqType non_zero non_zero_eqMixin.
Definition non_zero_choiceMixin := [choiceMixin of non_zero by <:].
Canonical non_zero_choiceType :=
  Eval hnf in ChoiceType non_zero non_zero_choiceMixin.
Definition non_zero_countMixin := [countMixin of non_zero by <:].
Canonical non_zero_countType :=
  Eval hnf in CountType non_zero non_zero_countMixin.
Canonical non_zero_subCountType :=
  Eval hnf in [subCountType of non_zero].
Definition non_zero_ordMixin := [ordMixin of non_zero by <:].
Canonical non_zero_ordType :=
  Eval hnf in OrdType non_zero non_zero_ordMixin.

Canonical non_zero_succn n := @NonZero n.+1 erefl.

Section Def.

Variable k : nat.

CoInductive word : predArgType := Word of 'I_(2 ^ k).

Definition ord_of_word (w : word) := let: Word i := w in i.

Local Coercion ord_of_word : word >-> ordinal.

Canonical word_subType := [newType for ord_of_word].
Definition word_eqMixin := [eqMixin of word by <:].
Canonical word_eqType := Eval hnf in EqType word word_eqMixin.
Definition word_choiceMixin := [choiceMixin of word by <:].
Canonical word_choiceType := Eval hnf in ChoiceType word word_choiceMixin.
Definition word_countMixin := [countMixin of word by <:].
Canonical word_countType := Eval hnf in CountType word word_countMixin.
Canonical word_subCountType := Eval hnf in [subCountType of word].
Definition word_finMixin := [finMixin of word by <:].
Canonical word_finType := Eval hnf in FinType word word_finMixin.
Canonical word_subFinType := Eval hnf in [subFinType of word].
Definition word_ordMixin := [ordMixin of word by <:].
Canonical word_ordType := Eval hnf in OrdType word word_ordMixin.

Lemma card_word : #|{: word}| = 2 ^ k.
Proof. by rewrite card_sub eq_cardT // -cardT card_ord. Qed.

Lemma exp2_gt0 : 0 < 2 ^ k.
Proof. by rewrite expn_gt0. Qed.

Definition as_word (n : int) :=
  Word (Ordinal (ltn_pmod `|modz n (2 ^ k)%N| exp2_gt0)).

Lemma as_wordK (n : nat) : n < 2 ^ k -> val (as_word n) = n :> nat.
Proof. by move=> ub; rewrite /= modz_nat absz_nat modn_mod modn_small //. Qed.

(* Signed conversion to integers *)
Definition int_of_word (w : word) : int :=
  if w < 2 ^ k.-1 then w
  else (w - 2 ^ k)%Z.

Definition addw (w1 w2 : word) := as_word (w1 + w2)%N.
Definition oppw (w : word) := as_word (2 ^ k - w)%N.
Definition mulw (w1 w2 : word) := as_word (w1 * w2)%N.
Definition subw (w1 w2 : word) := addw w1 (oppw w2).
Definition shlw (w1 w2 : word) := as_word (w1 * 2 ^ w2)%N.

Definition zerow := as_word 0.
Definition onew := as_word 1.
Definition monew := oppw onew.

Lemma onew_zero : (onew == zerow) = (k == 0).
Proof.
rewrite -!val_eqE /=; case: k => [|k'] //=.
rewrite expnS !modz_nat !absz_nat !mod0n modn_mod modn_small //.
by rewrite -{1}[2]/(2 * 2 ^ 0) leq_pmul2l // leq_exp2l.
Qed.

Lemma valwK (w : word) : as_word w = w.
Proof.
by do 2!apply: val_inj; rewrite /= modz_nat absz_nat modn_mod modn_small.
Qed.

Lemma add0w : left_id zerow addw.
Proof. by move=> w; rewrite /addw /= !mod0z mod0n valwK. Qed.

Lemma addNw : left_inverse zerow oppw addw.
Proof.
move=> w; do 2!apply: val_inj.
by rewrite /= !modz_nat !absz_nat /= !modnDml subnK ?modnn ?mod0n // ltnW.
Qed.

Lemma addwA : associative addw.
Proof.
move=> x y z; do 2!apply: val_inj.
by rewrite /= !modz_nat !absz_nat /= !modn_mod !modnDml modnDmr addnA.
Qed.

Lemma addwC : commutative addw.
Proof. by move=> x y; do 2!apply: val_inj; rewrite /= addnC. Qed.

Definition word_zmodMixin := ZmodMixin addwA addwC add0w addNw.
Canonical word_zmodType := ZmodType word word_zmodMixin.
Canonical word_finZmodType := Eval hnf in [finZmodType of word].
Canonical word_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of word for +%R].
Canonical word_finGroupType := Eval hnf in [finGroupType of word for +%R].

Lemma mul1w : left_id onew mulw.
Proof.
move=> w; do 2!apply: val_inj.
by rewrite /= /mulw !modz_nat !absz_nat !modn_mod modnMml mul1n modn_small.
Qed.

Lemma mulwC : commutative mulw.
Proof. by move=> w1 w2; rewrite /mulw mulnC. Qed.

Lemma mulw1 : right_id onew mulw.
Proof. by move=> w; rewrite mulwC mul1w. Qed.

Lemma mulwA : associative mulw.
Proof.
move=> w1 w2 w3; do 2!apply: val_inj.
by rewrite /= /mulw !modz_nat !absz_nat !modn_mod modnMml modnMmr mulnA.
Qed.

Lemma mulw_addr : right_distributive mulw addw.
Proof.
move=> w1 w2 w3; do 2!apply: val_inj.
by rewrite /= /mulw !modz_nat !absz_nat !modn_mod modnMmr modnDm mulnDr.
Qed.

Lemma mulw_addl : left_distributive mulw addw.
Proof.
by move=> w1 w2 w3; rewrite -!(mulwC w3) mulw_addr.
Qed.

Definition bits_of_word (w : word) :=
  locked [ffun i : 'I_k => odd (val w %/ 2 ^ i)].

Definition word_of_bits (bs : {ffun pred 'I_k}) :=
  as_word (\sum_(i < k) bs i * 2 ^ i)%N.

Lemma word_of_bitsK : cancel word_of_bits bits_of_word.
Proof.
have Hsum2 : forall N (f : pred 'I_N), \sum_(i < N) f i * 2 ^ i < 2 ^ N.
  move=> N f.
  rewrite -[2 ^ N]prednK ?expn_gt0 // predn_exp mul1n ltnS leq_sum // => i _.
  by case: (f i); rewrite // ?mul1n ?mul0n leqnn.
move=> bs; apply/ffunP=> - [i Hi].
rewrite /bits_of_word /word_of_bits -lock ffunE /= !modz_nat !absz_nat.
rewrite modn_mod modn_small; last first.
  by apply: Hsum2.
have Hl : k = i.+1 + (k - i.+1) by rewrite subnKC //.
rewrite {}Hl in bs Hi *.
rewrite big_split_ord big_ord_recr /=.
pose f i' := bs (rshift i.+1 i') * 2 ^ i' * 2 ^ i.+1.
rewrite [in X in _ + _ + X](eq_big_seq f); last first.
  by move=> i' _; rewrite /= expnD [in X in _ * X]mulnC mulnA.
rewrite -big_distrl /= expnS mulnA.
rewrite !divnDr ?mulnK ?dvdn_mull ?dvdnn ?expn_gt0 //.
rewrite divn_small; last by apply: Hsum2.
rewrite add0n odd_add odd_mul andbF addbF oddb.
by apply: f_equal; apply: val_inj.
Qed.

Lemma word_of_bits_inj : injective word_of_bits.
Proof. exact: can_inj word_of_bitsK. Qed.

Lemma bits_of_wordK : cancel bits_of_word word_of_bits.
Proof.
have := (inj_card_bij word_of_bits_inj).
rewrite card_word card_ffun card_bool card_ord=> /(_ erefl) Hbij.
have [inv Hinv Hinv'] := (Hbij).
move: (bij_can_eq Hbij word_of_bitsK Hinv) => H w.
by rewrite H Hinv'.
Qed.

Lemma bits_of_word_inj : injective bits_of_word.
Proof. exact: can_inj bits_of_wordK. Qed.

Definition negw w := word_of_bits [ffun i => ~~ bits_of_word w i].

Lemma negwK : involutive negw.
Proof.
move=> w; rewrite /negw word_of_bitsK.
by apply: (canLR bits_of_wordK); apply/ffunP=> i; rewrite !ffunE negbK.
Qed.

Lemma bits_zero : bits_of_word zerow = [ffun _ => false].
Proof.
apply: (canLR word_of_bitsK); do 2!apply: val_inj=> /=.
rewrite (eq_big_seq (fun i : 'I_k => 0)); last by move=> i; rewrite /= ffunE.
by rewrite sum_nat_const muln0.
Qed.

Lemma bits_one : bits_of_word onew = [ffun i : 'I_k => 0 == i].
Proof.
apply: (canLR word_of_bitsK); do 2!apply: val_inj=> /=.
case: k=> [|k']; first by rewrite big_ord0 expn0 modn1.
rewrite big_ord_recl (eq_big_seq (fun i : 'I_(k') => 0)).
  by rewrite sum_nat_const muln0 addn0 ffunE.
by move=> i _; rewrite /= ffunE.
Qed.

Lemma bits_mone : bits_of_word monew = [ffun _ => true].
Proof.
apply: (canLR word_of_bitsK).
rewrite -(GRing.add0r monew) /monew; apply: (canLR (GRing.subrK (oppw onew))).
rewrite GRing.opprK.
do 2!apply: val_inj=> /=.
rewrite !modz_nat !absz_nat !modn_mod.
rewrite (eq_big_seq (fun i : 'I_k => 2 ^ i)); last first.
  by move=> i _; rewrite /= ffunE mul1n.
have -> : (\sum_(i < k) 2 ^ i) = (2 ^ k).-1 by rewrite predn_exp /= mul1n.
rewrite [in _ + _]modn_small ?prednK ?expn_gt0 //.
have [->|Hn0] := altP (k =P 0); first by rewrite !expn0 /= modn1.
rewrite [in _ + _]modn_small -1?[in X in X < _](expn0 2) ?ltn_exp2l ?lt0n //.
by rewrite addn1 prednK ?expn_gt0 // modnn mod0n.
Qed.

Lemma negw_zero : negw zerow = monew.
Proof.
rewrite /negw; apply: (canLR bits_of_wordK).
rewrite bits_mone bits_zero.
by apply/ffunP=> i; rewrite !ffunE.
Qed.

Section Bitwise2.

Variable op : bool -> bool -> bool.

Definition bitwise2 w1 w2 :=
  word_of_bits [ffun i => op (bits_of_word w1 i) (bits_of_word w2 i)].

Lemma bitwise2C : commutative op -> commutative bitwise2.
Proof.
move=> opC w1 w2; congr word_of_bits; apply/ffunP=> i.
by rewrite 2!ffunE opC.
Qed.

Lemma bitwise2A : associative op -> associative bitwise2.
Proof.
move=> opA w1 w2 w3; congr word_of_bits; apply/ffunP=> i.
by rewrite /bitwise2 !word_of_bitsK !ffunE /= opA.
Qed.

Lemma idem_bitwise2 : idempotent op -> idempotent bitwise2.
Proof.
move=> opbb w; apply: bits_of_word_inj; apply/ffunP=> i.
by rewrite /bitwise2 /= word_of_bitsK ffunE opbb.
Qed.

Lemma id_bitwise2 b w :
  left_id b op ->
  bits_of_word w = [ffun=> b] ->
  left_id w bitwise2.
Proof.
move=> Hid /(canRL bits_of_wordK) -> {w} w; rewrite /bitwise2 word_of_bitsK.
by apply: (canLR bits_of_wordK); apply/ffunP=> i; rewrite /= !ffunE Hid.
Qed.

End Bitwise2.

Definition andw := bitwise2 andb.
Definition orw := bitwise2 orb.
Definition xorw := bitwise2 addb.

Lemma andwC : commutative andw.
Proof. exact: bitwise2C andbC. Qed.

Lemma andwA : associative andw.
Proof. exact: bitwise2A andbA. Qed.

Lemma andww : idempotent andw.
Proof. exact: idem_bitwise2 andbb. Qed.

Lemma andN1w : left_id monew andw.
Proof. exact: id_bitwise2 andTb bits_mone. Qed.

Lemma andwN1 : right_id monew andw.
Proof. by move=> w; rewrite andwC andN1w. Qed.

Lemma orwC : commutative orw.
Proof. exact: bitwise2C orbC. Qed.

Lemma orwA : associative orw.
Proof. exact: bitwise2A orbA. Qed.

Lemma orww : idempotent orw.
Proof. exact: idem_bitwise2 orbb. Qed.

Lemma or0w : left_id zerow orw.
Proof. exact: id_bitwise2 orFb bits_zero. Qed.

Lemma orw0 : right_id zerow orw.
Proof. by move=> w; rewrite orwC or0w. Qed.

Lemma xorwC : commutative xorw.
Proof. exact: bitwise2C addbC. Qed.

Lemma xorwA : associative xorw.
Proof. exact: bitwise2A addbA. Qed.

Lemma xor0w : left_id zerow xorw.
Proof. exact: id_bitwise2 addFb bits_zero. Qed.

Lemma xorw0 : right_id zerow xorw.
Proof. by move=> w; rewrite xorwC xor0w. Qed.

Section Order.

Local Open Scope ord_scope.

Lemma leqw_mone w : w <= monew.
Proof.
case: w=> [] /=; do 3!rewrite /Ord.leq /=.
case: k=> [|k' n].
  by rewrite expn0=> n; rewrite ord1.
rewrite !modz_nat !absz_nat !modn_mod.
rewrite !modn_small; try by rewrite -{1}(expn1 2) leq_exp2l.
  have := (leq_sub2r 1 (valP n)); rewrite subn1 //=.
by rewrite subn1 prednK ?leqnn // expn_gt0.
Qed.

Lemma leqw_zero w : zerow <= w.
Proof.
do 3!rewrite /Ord.leq /=.
by rewrite !modz_nat !absz_nat !modn_mod mod0n.
Qed.

End Order.

End Def.

Arguments onew {_}.
Arguments zerow {_}.
Arguments monew {_}.
Arguments as_word {_} _.
Arguments addw {_} _ _.
Arguments subw {_} _ _.
Arguments mulw {_} _ _.
Arguments oppw {_} _.
Arguments shlw {_} _ _.
Arguments andw {_} _ _.
Arguments orw {_} _ _.
Arguments xorw {_} _ _.

Delimit Scope word_scope with w.
Notation "+%w" := addw.
Notation "-%w" := oppw.
Notation "x + y" := (addw x y) : word_scope.
Notation "x - y" := (subw x y) : word_scope.
Notation "x * y" := (mulw x y) : word_scope.
Notation "- x" := (oppw x) : word_scope.
Notation "0" := (zerow) : word_scope.
Notation "1" := (onew) : word_scope.

Section NonZero.

Variable k : non_zero.

Lemma onewN0 : 1%w != 0%w :> word k.
Proof. by rewrite onew_zero (valP k). Qed.

Definition word_ringMixin :=
  RingMixin (@mulwA k) (@mul1w k) (@mulw1 k)
            (@mulw_addl k) (@mulw_addr k) onewN0.

Canonical word_ringType :=
  Eval hnf in RingType (word k) word_ringMixin.

End NonZero.

Definition swcast {k k'} (w : word k) : word k' :=
  as_word (val w).

Section Splitting.

Variable ks : seq nat.

Definition wunpack (w : word (sumn ks)) : hseq word ks :=
  let t := tcast (card_ord (sumn ks)) (val (bits_of_word w)) in
  let word_of_tuple k t' :=
      word_of_bits (Finfun (tcast (esym (card_ord k)) t')) in
  hmap word_of_tuple (split_tuple t).

Definition wpack (ws : hseq word ks) : word (sumn ks) :=
  let tuple_of_word k w :=
      tcast (card_ord k) (val (bits_of_word w)) in
  let t := tcast (esym (card_ord (sumn ks)))
                 (merge_tuple (hmap tuple_of_word ws)) in
  word_of_bits (Finfun t).

Lemma wpackK : cancel wpack wunpack.
Proof.
move=> ws; rewrite /wunpack /wpack /= word_of_bitsK /= tcastKV.
rewrite merge_tupleK hmapK // => i w; rewrite tcastK /=.
by apply: (canLR (@bits_of_wordK i)); case: (bits_of_word _).
Qed.

Lemma wunpackK : cancel wunpack wpack.
Proof.
move=> w; rewrite /wunpack /wpack /= hmapK ?split_tupleK ?tcastK.
  by apply: (canLR (@bits_of_wordK _)); case: (bits_of_word _).
by move=> i w'; rewrite word_of_bitsK /= tcastKV.
Qed.

End Splitting.

Definition wcast k1 k2 (p : k1 = k2) (w : word k1) : word k2 :=
  eq_rect k1 word w k2 p.

Lemma wcast_id k (eq_kk : k = k) w : wcast eq_kk w = w.
Proof. by rewrite eq_axiomK. Qed.

Lemma wcastK k1 k2 (eq_k1k2 : k1 = k2) :
  cancel (wcast eq_k1k2) (wcast (esym eq_k1k2)).
Proof.
move: (eq_k1k2) (esym _); rewrite -{}eq_k1k2 {k2}=> eq_kk eq_kk'.
by rewrite !eq_axiomK.
Qed.

Lemma wcastKV k1 k2 (eq_k1k2 : k1 = k2) :
  cancel (wcast (esym eq_k1k2)) (wcast eq_k1k2).
Proof.
move: (eq_k1k2) (esym _); rewrite -{}eq_k1k2 {k2}=> eq_kk eq_kk'.
by rewrite !eq_axiomK.
Qed.

Lemma wcast_trans k1 k2 k3 (eq_k1k2 : k1 = k2) (eq_k2k3 : k2 = k3) :
  wcast (etrans eq_k1k2 eq_k2k3) =1 wcast eq_k2k3 \o wcast eq_k1k2.
Proof.
move: (eq_k1k2) (eq_k2k3) (etrans _ _); rewrite -{}eq_k2k3 -{}eq_k1k2 {k2 k3}.
by move=> ???; rewrite !eq_axiomK.
Qed.
