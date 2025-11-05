From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.

From extructures Require Import ord fset fmap.

(******************************************************************************)
(*   Given a function def : T -> S, the type ffun def is the type of          *)
(* finitely supported functions of type T -> S. That is, f agrees with def    *)
(* on all but finitely many inputs.  The type T must be an instance of        *)
(* ordType, and S must be an eqType.                                          *)
(*                                                                            *)
(*        supp f == the finite set of inputs where f differs from def         *)
(*   mkffun f xs == the finite function defined by                            *)
(*                      mkffun f xs x = if x \in xs then f x else def x       *)
(*     mkffunm m == complete a finite map m with def outside of the domain    *)
(*                  of m                                                      *)
(*        emptyf == the finite function with empty support; i.e. that agrees  *)
(*                  with def everywhere                                       *)
(*     upd f x y == override the value of f at x to be y                      *)
(*     updfm f m == override the values of f with the finite map m            *)
(*      mapf g f == compose the finite function f with g : S -> R; the result *)
(*                  has type ffun (g \o def)                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Section FFun.

Context {T : ordType} {S : eqType} {def : T -> S}.

Local Notation wf f :=
  (all (fun x => f x != Some (def x)) (domm f)).

Record ffun := FFun {
  ffval : {fmap T -> S};
  _     : wf ffval;
}.
Arguments FFun _ _ : clear implicits.

HB.instance Definition _ := [isSub of ffun for ffval].

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

Lemma mem_suppN f x : (x \notin supp f) = (f x == def x).
Proof. by rewrite mem_supp negbK. Qed.

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

Definition mkffun (fb : T -> S) (xs : seq T) :=
  foldr (fun x f => upd f x (fb x)) emptyf xs.

Lemma mkffunE fb xs x :
  mkffun fb xs x = if x \in xs then fb x else def x.
Proof.
elim: xs=> [|x' xs IH] //=; rewrite inE updE IH.
by case: eqP => [<-|_].
Qed.

Lemma supp_mkffun fb xs :
  supp (mkffun fb xs) = fset [seq x <- xs | fb x != def x].
Proof.
apply/eq_fset=> x; rewrite mem_supp in_fset mem_filter mkffunE.
by rewrite andbC; case: ifP=> //; rewrite eqxx.
Qed.

Lemma supp_mkffun_sub fb (X : {fset T}) : supp (mkffun fb X) `<=` X.
Proof.
by apply/fsubsetP => x; rewrite supp_mkffun in_fset mem_filter; case/andP.
Qed.

Definition updfm f (xs : {fmap T -> S}) : ffun :=
  mkffun (fun v => if xs v is Some x then x else f v)
         (supp f `|` domm xs).

Lemma updfmE f xs x :
  updfm f xs x = if xs x is Some y then y else f x.
Proof.
rewrite /updm mkffunE in_fsetU orbC mem_domm.
case e: (xs x)=> [y|] //=.
by case: ifPn=> // /suppPn ->.
Qed.

Definition mkffunm (m : {fmap T -> S}) : ffun :=
  mkffun (fun x => odflt (def x) (m x)) (domm m).

Lemma mkffunmE m x : mkffunm m x = odflt (def x) (m x).
Proof. by rewrite /mkffunm mkffunE mem_domm; case: (m x). Qed.

Lemma val_mkffun (f : T -> S) (X : {fset T}) :
  ffval (mkffun f X) =
  mkfmapfp (fun x => if f x == def x then None else Some (f x)) X.
Proof.
apply/eq_fmap=> x; rewrite mkfmapfpE.
move: (mkffunE f X x); rewrite /appf /=.
set ff := mkffun f X; case e: (ffval ff x) => [y|].
- have xdomm: x \in domm (ffval ff) by rewrite mem_domm e.
  move/allP/(_ _ xdomm): (valP ff); rewrite /= e => yP ey.
  move: yP; rewrite {}ey; case: ifP; last by rewrite eqxx.
  rewrite inj_eq; last exact: Some_inj.
  by move=> _ /negbTE ->.
- by case: ifP=> // _ ->; rewrite eqxx.
Qed.

End FFun.

Arguments ffun {T S} def.
Arguments suppPn {T S def f x}.

Section Mapping.

Variables (T : ordType) (S R : eqType) (def : T -> S).

Definition mapf (g : S -> R) (f : ffun def) : ffun (g \o def) :=
  mkffun (g \o f) (supp f).

Lemma mapfE (g : S -> R) (f : ffun def) x :
  mapf g f x = g (f x).
Proof.
rewrite /mapf mkffunE mem_supp /=.
by case: eqP=> //= ->.
Qed.

Lemma val_mapf (g : S -> R) :
  injective g ->
  forall f : ffun def, ffval (mapf g f) = mapm g (ffval f).
Proof.
move=> g_inj f; apply/eq_fmap=> x.
rewrite /mapf val_mkffun mkfmapfpE mapmE mem_supp /= /appf /=.
rewrite inj_eq //.
case e: (ffval f x)=> [y|] /=; last by rewrite eqxx.
have xdomm: x \in domm (ffval f) by rewrite mem_domm e.
move/allP/(_ _ xdomm): (valP f); rewrite e.
rewrite inj_eq; last exact: Some_inj.
by move=> /negbTE ->.
Qed.

End Mapping.

HB.instance Definition _ T (S : eqType) def :=
  [Equality of @ffun T S def by <:].
#[hnf] HB.instance Definition _ T (S : choiceType) def :=
  [Choice of @ffun T S def by <:].
#[hnf] HB.instance Definition _ T (S : ordType) def :=
  [Ord of @ffun T S def by <:].
