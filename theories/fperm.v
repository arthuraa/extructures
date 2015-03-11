Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.path MathComp.bigop.

Require Import ord partmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FPerm.

Section Def.

Variables (T : ordType).

Local Open Scope ord_scope.

Definition axiom (f : {partmap T -> T}) :=
  let xs := domm f in
  injectivem f &&
  all (fun x => let y := odflt x (f x) in (y \in xs) && (y != x)) xs.

Record fperm_type := FPerm {
  fpval : {partmap T -> T};
  _ : axiom fpval
}.
Definition fperm_of of phant T := fperm_type.
Identity Coercion type_of_fperm_of : fperm_of >-> fperm_type.

End Def.

Module Exports.

Notation "{ 'fperm' T }" := (@fperm_of _ (Phant T))
  (at level 0, format "{ 'fperm'  T }") : type_scope.
Canonical fperm_subType T := [subType for @fpval T].
Definition fperm_eqMixin T := [eqMixin of fperm_type T by <:].
Canonical fperm_eqType T :=
  Eval hnf in EqType (fperm_type T) (fperm_eqMixin T).

End Exports.

End FPerm.

Export FPerm.Exports.

Delimit Scope fperm_scope with fperm.

Definition fun_of_fperm T (s : FPerm.fperm_type T) x :=
  if val s x is Some y then y else x.

Coercion fun_of_fperm : FPerm.fperm_type >-> Funclass.

Section Operations.

Variable T : ordType.

Implicit Types (s : {fperm T}) (x : T).

Local Open Scope fset_scope.

Lemma fperm_inj s : injective s.
Proof.
move=> x y; rewrite /fun_of_fperm.
case ex: (val s x) => [x'|]; case ey: (val s y) => [y'|] //.
- move=> ?; subst y'; move: (andP (valP s)).1 => /injectivemP/(_ x).
  by rewrite mem_domm ex=> /(_ erefl y (esym ey)).
- move=> ?; subst x'; move: (andP (valP s)).2 => /allP/(_ x).
  by rewrite mem_domm ex /= mem_domm ey /= => /(_ erefl).
move=> ?; subst y'; move: (andP (valP s)).2 => /allP/(_ y).
by rewrite mem_domm ey /= mem_domm ex /= => /(_ erefl).
Qed.

Definition fperm_one : {fperm T} := @FPerm.FPerm T emptym erefl.

Lemma fperm1 x : fperm_one x = x.
Proof. by []. Qed.

Definition supp s := domm (val s).

Lemma imfset_supp s : s @: supp s = supp s.
Proof.
apply/eqP; rewrite eqEfsize; apply/andP; split.
  apply/fsubsetP=> x /imfsetP [y Py -> {x}].
  move/allP/(_ _ Py): (andP (valP s)).2=> /=.
  rewrite /fun_of_fperm /=; case: (val s y)=> [z|] //=.
  by case/andP.
suff /eqP -> : size (s @: domm (val s)) == size (domm (val s)).
  by rewrite leqnn.
by apply/imfset_injP=> ????; apply: fperm_inj.
Qed.

Lemma mem_supp s x : (x \in supp s) = (s x != x).
Proof.
rewrite /supp mem_domm /fun_of_fperm.
case s_x: (val s x)=> [y|] //=; last by rewrite eqxx.
apply/esym.
have x_in_s : x \in domm (val s) by rewrite mem_domm s_x.
by move: (allP (andP (valP s)).2 _ x_in_s); rewrite s_x /= => /andP [].
Qed.

Lemma fperm_supp s x : (s x \in supp s) = (x \in supp s).
Proof.
rewrite -{1}imfset_supp; apply/(sameP idP)/(iffP idP).
  by apply: mem_imfset.
by case/imfsetP=> x' hx' /fperm_inj ->.
Qed.

Lemma imfset_supp_sub s X : fsubset (supp s) X -> s @: X = X.
Proof.
move=> h_sub; apply/eq_fset=> x; have h_im_sub := imfsetS s h_sub.
have [in_supp|nin_supp] := boolP (x \in supp s).
  rewrite (fsubsetP _ _ h_sub _ in_supp); move/fsubsetP: h_im_sub; apply.
  by rewrite imfset_supp.
move: nin_supp; rewrite mem_supp negbK =>/eqP ex.
apply/(sameP idP)/(iffP idP); first by rewrite -{2}ex; apply: mem_imfset.
case/imfsetP=> [y Py ey]; rewrite {2}ey in ex.
by move/fperm_inj in ex; rewrite ex.
Qed.

Section Build.

Variables (f : T -> T) (X : {fset T}).

Hypothesis stable : f @: X = X.

Lemma fperm_subproof : FPerm.axiom (filterm (fun x y => x != y)
                                            (mkpartmapf f X)).
Proof.
have f_inj: {in X &, injective f}.
  by apply/imfset_injP; rewrite stable.
apply/andP; split.
  apply/injectivemP=> x1; rewrite mem_domm !filtermE !mkpartmapfE.
  have [hx1|] //= := boolP (x1 \in X).
  have [efx1|efx1 _ x2] //= := altP (x1 =P f x1).
  rewrite filtermE mkpartmapfE.
  have [hx2|] //= := boolP (x2 \in X).
  by have [efx2|efx2 []] //= := altP (x2 =P f x2); eauto.
apply/allP=> x /=; rewrite !mem_domm filtermE mkpartmapfE.
have [x_in_X|] //= := boolP (x \in X).
have [??|nfx _] //= := altP (x =P f x).
rewrite filtermE mkpartmapfE /= -stable (mem_imfset f x_in_X) /=.
rewrite (eq_sym _ x) nfx andbT; have [efx|] //= := altP (_ =P f (f x)).
rewrite -(negbTE nfx) {nfx}; apply/eqP.
suff fx_in_X: f x \in X by apply: f_inj x_in_X fx_in_X efx.
by rewrite -stable (mem_imfset _ x_in_X).
Qed.

Definition fperm : {fperm T} := FPerm.FPerm fperm_subproof.

Lemma fpermE x : fperm x = if x \in X then f x else x.
Proof.
rewrite /fun_of_fperm /fperm /= filtermE mkpartmapfE.
have [x_in_X|] //= := boolP (x \in X).
by have [<-|] := altP (x =P f x).
Qed.

End Build.

Section Inverse.

Variable s : {fperm T}.

Local Notation inv_def := (fun x => odflt x (fpick (pred1 x \o s) (supp s))).

Lemma fperm_inv_subproof : inv_def @: supp s = supp s.
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  move=> x_in_supp; apply/imfsetP; exists (s x).
    by rewrite -imfset_supp (mem_imfset _ x_in_supp).
  case: fpickP=> [y' /= /eqP/esym e _|/(_ _ x_in_supp) /=].
    exact: fperm_inj e.
  by rewrite eqxx.
by case/imfsetP=> [y Py -> {x}]; case: fpickP.
Qed.

Definition fperm_inv := fperm fperm_inv_subproof.

Lemma fpermK : cancel s fperm_inv.
Proof.
move=> x; rewrite fpermE; case: ifPn=> [x_in_supp|].
  rewrite fperm_supp in x_in_supp.
  case: fpickP => [y /= /eqP/esym /fperm_inj-> //|/(_ _ x_in_supp) /=].
  by rewrite eqxx.
by rewrite fperm_supp mem_supp negbK=> /eqP.
Qed.

Lemma fpermKV : cancel fperm_inv s.
Proof.
move=> x; rewrite fpermE; case: ifPn=> [x_in_supp|].
  case: fpickP=> [x' /= /eqP/esym -> //|/=].
  rewrite -imfset_supp in x_in_supp; case/imfsetP: x_in_supp=> [x' Px' ->].
  by move/(_ _ Px'); rewrite eqxx.
by rewrite mem_supp negbK => /eqP.
Qed.

Lemma supp_inv : supp fperm_inv = supp s.
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  by rewrite !mem_supp; apply: contra => /eqP {1}<-; rewrite fpermKV eqxx.
by rewrite !mem_supp; apply: contra=> /eqP {1}<-; rewrite fpermK eqxx.
Qed.

Lemma fperm_suppV x : (fperm_inv x \in supp s) = (x \in supp s).
Proof. by rewrite -{1}supp_inv fperm_supp supp_inv. Qed.

End Inverse.

Lemma fperm_mul_subproof s1 s2 :
  (s1 \o s2) @: (supp s1 :|: supp s2) = supp s1 :|: supp s2.
Proof.
by rewrite imfset_comp !imfset_supp_sub // ?fsubsetUr // fsubsetUl.
Qed.

Definition fperm_mul s1 s2 := fperm (fperm_mul_subproof s1 s2).

Lemma fpermM s1 s2 : fperm_mul s1 s2 =1 s1 \o s2.
Proof.
move=> x; rewrite fpermE; have [|nin_supp] //= := boolP (x \in _).
rewrite in_fsetU negb_or !mem_supp !negbK in nin_supp.
by case/andP: nin_supp=> [/eqP h1 /eqP ->]; rewrite h1.
Qed.

Lemma eq_fperm s1 s2 : s1 =1 s2 <-> s1 = s2.
Proof.
split; last congruence.
have Pval: forall s x, val s x != Some x.
  move=> {s1 s2} s x; apply/eqP=> Px.
  have Px': x \in domm (val s) by rewrite mem_domm Px.
  by move: (allP (andP (valP s)).2 x Px') => {Px'} /=; rewrite Px /= eqxx andbF.
move=> Ps1s2; apply/val_inj/eq_partmap => x.
move: (Ps1s2 x); rewrite /fun_of_fperm.
case Ps1: (val s1 x)=> [y1|] //; case Ps2: (val s2 x)=> [y2|] //.
- by move=> ->.
- by move=> ? {Ps2}; subst y1; move: (Pval s1 x); rewrite Ps1 eqxx.
by move=> ? {Ps1}; subst y2; move: (Pval s2 x); rewrite Ps2 eqxx.
Qed.

Lemma fperm_mul1s : left_id fperm_one fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM. Qed.

Lemma fperm_muls1 : right_id fperm_one fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM. Qed.

Lemma fperm_mulK : right_inverse fperm_one fperm_inv fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM /= fpermKV. Qed.

Lemma fperm_mulKV : left_inverse fperm_one fperm_inv fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM /= fpermK. Qed.

Lemma fperm_mulA : associative fperm_mul.
Proof. by move=> s1 s2 s3; apply/eq_fperm=> x; rewrite !fpermM /= !fpermM. Qed.

End Operations.

Arguments fperm_one {_}.
Prenex Implicits fperm_inv fperm_mul.
