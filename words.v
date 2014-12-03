Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice fintype seq.
Require Import div ssralg finalg zmodp bigop tuple finfun binomial.
Require Import BinNums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Variable k : nat.

CoInductive word : predArgType := Word of 'I_(2 ^ k).

Definition ord_of_word (w : word) := let: Word i := w in i.

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

Lemma card_word : #|{: word}| = 2 ^ k.
Proof. by rewrite card_sub eq_cardT // -cardT card_ord. Qed.

Lemma exp2_gt0 : 0 < 2 ^ k.
Proof. by rewrite expn_gt0. Qed.

Definition as_word (n : nat) := Word (Ordinal (ltn_pmod n exp2_gt0)).

Definition addw (w1 w2 : word) := as_word (val w1 + val w2).
Definition oppw (w : word) := as_word (2 ^ k - val w).
Definition mulw (w1 w2 : word) := as_word (val w1 * val w2).

Definition zerow := as_word 0.
Definition onew := as_word 1.
Definition monew := oppw onew.

Lemma valwK (w : word) : as_word (val w) = w.
Proof. by apply: val_inj; apply: val_inj; rewrite /= modn_small. Qed.

Lemma add0w : left_id zerow addw.
Proof. by move=> w; rewrite /addw /= mod0n valwK. Qed.

Lemma addNw : left_inverse zerow oppw addw.
Proof.
  by move=> w; do 2!apply: val_inj;
  rewrite /= modnDml subnK ?modnn ?mod0n // ltnW.
Qed.

Lemma addwA : associative addw.
Proof.
by move=> x y z; do 2!apply: val_inj; rewrite /= modnDml modnDmr addnA.
Qed.

Lemma addwC : commutative addw.
Proof. by move=> x y; do 2!apply: val_inj; rewrite /= addnC. Qed.

Definition word_zmodMixin := ZmodMixin addwA addwC add0w addNw.
Canonical word_zmodType := ZmodType word word_zmodMixin.
Canonical word_finZmodType := Eval hnf in [finZmodType of word].
Canonical word_baseFinGroupType := Eval hnf in [baseFinGroupType of word for +%R].
Canonical word_finGroupType := Eval hnf in [finGroupType of word for +%R].

Lemma mul1w : left_id onew mulw.
Proof.
  by move=> w; do 2!apply: val_inj; rewrite /= /mulw modnMml mul1n modn_small.
Qed.

Lemma mulwC : commutative mulw.
Proof. by move=> w1 w2; rewrite /mulw mulnC. Qed.

Lemma mulw1 : right_id onew mulw.
Proof. by move=> w; rewrite mulwC mul1w. Qed.

Lemma mulwA : associative mulw.
Proof.
  move=> w1 w2 w3; do 2!apply: val_inj.
  by rewrite /= /mulw modnMml modnMmr mulnA.
Qed.

Lemma mulw_addr : right_distributive mulw addw.
Proof.
  move=> w1 w2 w3; do 2!apply: val_inj.
  by rewrite /= /mulw modnMmr modnDm mulnDr.
Qed.

Lemma mulw_addl : left_distributive mulw addw.
Proof.
  by move=> w1 w2 w3; rewrite -!(mulwC w3) mulw_addr.
Qed.

Definition bits_of_word (w : word) :=
  locked [ffun i : 'I_k => odd (val w %/ 2 ^ i)].

Definition word_of_bits (bs : {ffun pred 'I_k}) :=
  as_word (\sum_(i < k) bs i * 2 ^ i).

Lemma word_of_bitsK : cancel word_of_bits bits_of_word.
Proof.
have Hsum2 : forall N (f : pred 'I_N), \sum_(i < N) f i * 2 ^ i < 2 ^ N.
  move=> N f.
  rewrite -[2 ^ N]prednK ?expn_gt0 // predn_exp mul1n ltnS leq_sum // => i _.
  by case: (f i); rewrite // ?mul1n ?mul0n leqnn.
move=> bs; apply/ffunP=> - [i Hi].
rewrite /bits_of_word /word_of_bits -lock ffunE /= modn_small; last by apply: Hsum2.
have Hl : k = i.+1 + (k - i.+1) by rewrite subnKC //.
rewrite {}Hl in bs Hi *.
rewrite big_split_ord big_ord_recr /=.
rewrite [in X in _ + _ + X](eq_big_seq (fun i' => bs (rshift i.+1 i') * 2 ^ i' * 2 ^ i.+1)); last first.
  by move=> i' _; rewrite /= expnD [in X in _ * X]mulnC mulnA.
rewrite -big_distrl /= expnS mulnA !divnDr ?mulnK ?dvdn_mull ?dvdnn ?expn_gt0 //.
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
rewrite (eq_big_seq (fun i : 'I_k => 2 ^ i)); last by move=> i _; rewrite /= ffunE mul1n.
have -> : (\sum_(i < k) 2 ^ i) = (2 ^ k).-1 by rewrite predn_exp /= mul1n.
rewrite [in _ + _]modn_small ?prednK ?expn_gt0 //.
have [->|Hn0] := altP (k =P 0); first by rewrite !expn0 /= modn1.
rewrite [in _ + _]modn_small -1?[in X in X < _](expn0 2) ?ltn_exp2l // ?lt0n //.
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

End Def.


Section Pos.

Variable n : nat.

Local Coercion bits : word >-> tuple_of.

Definition onew : word n.+1 := Word [tuple of true :: nseq n false].

Definition oppw (w : word n.+1) :=
  addw onew (Word [tuple of map negb w]).

Lemma oppwK : left_inverse zerow oppw addw



Definition casen (n : N) : option (bool * N) :=
  if n is Npos p then
    match p with
    | xI p => Some (true, Npos p)
    | xO p => Some (false, Npos p)
    | xH => Some (true, N0)
    end
  else None.

Definition consn (b : bool) (n : N) : N :=
  if b then
    if n is Npos p then Npos (xI p)
    else Npos xH
  else
    if n is Npos p then Npos (xO p)
    else N0.

Fixpoint sizep (p : positive) : nat :=
  match p with
  | xI p
  | xO p => (sizep p).+1
  | xH => 0
  end.

Definition sizen (n : N) : nat :=
  if n is Npos p then (sizep p).+1
  else 0.

Fixpoint truncaten s n :=
  if s is s.+1 then
    if n is Npos p then
      match p with
      | xI p => if truncaten s (Npos p) is Npos p' then Npos (xI p')
                else Npos xH
      | xO p => if truncaten s (Npos p) is Npos p' then Npos (xO p')
                else N0
      | xH => Npos xH
      end
    else N0
  else N0.

Lemma sizen_truncate s n :
  sizen (truncaten s n) <= s.
Proof.
  elim: s n => [|s IH] [|[p|p|]] //=.
    by case: {IH p} (truncaten s (Npos p)) (IH (Npos p)) => [|p] //.
  by case: {IH p} (truncaten s (Npos p)) (IH (Npos p)) => [|p] //.
Qed.

Fixpoint inc s n : N :=
  if s is s.+1 then
    if casen n is Some (b, n') then
      if b then consn false (inc s n')
      else consn true n'
    else 1%N
  else N0.

Lemma sizen_inc s n :
  sizen n <= s ->
  sizen (inc s n) <= s.
Proof.
  elim: s n => [|s IH] [|[p|p|]] //.
    move=> /(IH (Npos p)) {IH} /=.
    by case: (inc s _).
  by case s.
Qed.

Definition addc s c n : N :=
  if c then inc s n else n.

Lemma addc_cons s c b n :
  addc s.+1 c (consn b n) =
  consn (c (+) b) (addc s (c && b) n).
Proof.
  case: c => //=.
  by case: b n => [] [|[p|p|]] //.
Qed.

Lemma sizen_addc s c n :
  sizen n <= s ->
  sizen (addc s c n) <= s.
Proof.
  case: c => //=.
  exact: sizen_inc.
Qed.

Fixpoint add_aux s c n m : N :=
  if s is s'.+1 then
    match casen n, casen m with
    | Some (bn, n), Some (bm, m) =>
      consn (c (+) bn (+) bm) (add_aux s' (2 <= c + bn + bm) n m)
    | Some _, None => addc s c n
    | None, Some _ => addc s c m
    | None, None => if c then Npos xH else N0
    end
  else N0.

Definition add s n m : N :=
  add_aux s false n m.

Fixpoint add' s n m : N :=
  if s is s.+1 then
    match casen n, casen m with
    | None, _ => m
    | Some _, None => n
    | Some (bn, n), Some (bm, m) =>
      consn (bn (+) bm) (addc s (bn && bm) (add' s n m))
    end
  else N0.

Lemma add_auxE s c n m :
  add_aux s c n m =
  addc s c (add s n m).
Proof.
  rewrite /add.
  elim: s c n m => [|s IH] /= c n m; first by case: c.
  case: (casen n) => [[bn n']|];
  case: (casen m) => [[bm m']|] //=.
  case: c => //.
  rewrite addc_cons addbA andTb. congr consn.
  rewrite addSn add0n ltnS addn_gt0 !lt0b IH (IH (1 < _)).
  case: bn bm => [] [] //=.
Qed.

Lemma add'E s : add s =2 add' s.
Proof.
  rewrite /add.
  elim: s => [|s IH] // n m /=.
  case En: (casen n) => [[bn n']|];
  case Em: (casen m) => [[bm m']|] //=.
    rewrite add_auxE -IH.
    by case: bn bm {En Em} => [] [].
  by case: m Em => [|[]].
Qed.

Lemma sizen_case n :
  sizen n = if casen n is Some (_, n') then (sizen n').+1
            else 0.
Proof. by case: n => [|[p|p|]]. Qed.

Lemma sizen_cons b n s :
  (sizen (consn b n) <= s.+1) = (sizen n <= s).
Proof. by case: n b => [|[p|p|]] []. Qed.

Lemma sizen_add s c n m :
  sizen n <= s ->
  sizen m <= s ->
  sizen (add_aux s c n m) <= s.
Proof.
  elim: s c n m => [|s IH] c n m //=.
  rewrite 2!sizen_case.
  case En: (casen n) => [[bn n']|];
  case Em: (casen m) => [[bm m']|] //=.
  - by rewrite sizen_cons; apply: IH.
  - move=> H _; apply: sizen_addc.
    by rewrite sizen_case En.
  - move=> _ H; apply: sizen_addc.
    by rewrite sizen_case Em.
  by case: c.
Qed.

Lemma add_auxC s c : commutative (add_aux s c).
Proof.
  elim: s c => [|s IH] c n m //=.
  case: (casen n) (casen m) => [[bn n']|] [[bm m']|] //=.
  by rewrite IH -!addbA (addbC bn) -!addnA (addnC bn).
Qed.

Structure word n := Word {
  bits :> N;
  _ : sizen bits <= n
}.

Lemma word_size n (w : word n) : sizen w <= n.
Proof. by case: w. Qed.

Canonical word_subType n := [subType for @bits n].

Definition word_eqMixin n := [eqMixin of word n by <:].
Canonical word_eqType n := Eval hnf in EqType (word n) (word_eqMixin n).

Definition addw n (w1 w2 : word n) : word n :=
  Word (sizen_add false (word_size w1) (word_size w2)).

Lemma addwC n : commutative (@addw n).
Proof.
  move=> w1 w2.
  apply: val_inj => /=.
  exact: add_auxC.
Qed.
