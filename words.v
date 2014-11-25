Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import BinNums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
