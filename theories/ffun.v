From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.

From extructures Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Section FFun.

Variables (T : ordType) (S : eqType) (def : T -> S).

Local Notation wf f :=
  (all (fun x => f x != Some (def x)) (domm f)).

Record ffun := FFun {
  ffval : {fmap T -> S};
  _     : wf ffval;
}.
Arguments FFun _ _ : clear implicits.

Canonical ffun_subType := [subType for ffval].

Implicit Types (f g : ffun) (x : T) (y : S).

Definition appf f x :=
  if val f x is Some y then y else def x.

Coercion appf : ffun >-> Funclass.

Lemma eq_ffun f g : f =1 g <-> f = g.
Proof.
split=> [e|-> //]; apply/val_inj/eq_fmap=> x.
move/(_ x): e; rewrite /appf.
case efx: (val f x)=> [y1|]; case egx: (val g x)=> [y2|] // e.
- congruence.
- have {}xP: x \in domm (val f) by rewrite mem_domm efx.
  by move: (allP (valP f) _ xP); rewrite efx e eqxx.
- have {}xP: x \in domm (val g) by rewrite mem_domm egx.
  by move: (allP (valP g) _ xP); rewrite egx e eqxx.
Qed.

Definition supp f := domm (val f).

Lemma mem_supp f x : (x \in supp f) = (f x != def x).
Proof.
rewrite /appf /supp mem_domm.
case efx: (val f x)=> [y|]; last by rewrite eqxx.
have xP: x \in domm (val f) by rewrite mem_domm efx.
by move: (allP (valP f) _ xP); rewrite efx => ->.
Qed.

Lemma suppPn f x : reflect (f x = def x) (x \notin supp f).
Proof. rewrite mem_supp negbK; exact/eqP. Qed.

Lemma emptyf_subproof : wf (@emptym T S).
Proof. by rewrite domm0. Qed.

Definition emptyf := FFun emptym emptyf_subproof.

Lemma emptyfE x : emptyf x = def x.
Proof. by []. Qed.

Lemma supp0 : supp emptyf = fset0.
Proof. exact/domm0. Qed.

Definition upd_def f x y :=
  if def x == y then remm (val f) x
  else setm (val f) x y.

Lemma upd_subproof f x y : wf (upd_def f x y).
Proof.
rewrite /upd_def; apply/allP=> x'.
case: (altP eqP)=> [e|ne].
- rewrite domm_rem; case/fsetD1P=> ne /(allP (valP f)).
  by rewrite remmE (negbTE ne).
- rewrite domm_set in_fsetU1 setmE.
  by case: eqP=> [-> _|_ /(allP (valP f))]; rewrite // eq_sym.
Qed.

Definition upd f x y := FFun (upd_def f x y) (upd_subproof f x y).

Lemma updE f x1 y x2 :
  upd f x1 y x2 = if x2 == x1 then y else f x2.
Proof.
rewrite /appf /= /upd_def; case: (altP (def x1 =P y)) => ey.
  rewrite remmE; case: (altP (x2 =P x1)) => ex //; congruence.
by rewrite setmE; case: (altP (x2 =P x1)) => ex.
Qed.

End FFun.
