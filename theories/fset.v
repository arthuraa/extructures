Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.path.

Require Import ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FSet.

Section Def.

Variables (T : ordType).

Local Open Scope ord_scope.

Record fset_type := FSet {
  fsval : seq T;
  _ : sorted (@Ord.lt T) fsval
}.
Definition fset_of of phant T := fset_type.
Identity Coercion type_of_fset_of : fset_of >-> fset_type.

End Def.

Module Exports.

Notation "{ 'fset' T }" := (@fset_of _ (Phant T))
  (at level 0, format "{ 'fset'  T }") : type_scope.
Coercion fsval : fset_type >-> seq.
Canonical fset_subType T := [subType for @fsval T].
Definition fset_eqMixin T := [eqMixin of fset_type T by <:].
Canonical fset_eqType T :=
  Eval hnf in EqType (fset_type T) (fset_eqMixin T).

End Exports.

End FSet.

Export FSet.Exports.

Delimit Scope fset_scope with fset.

(* Redefine the partmap constructor with a different signature, in
order to keep types consistent. *)
Definition fset (T : ordType) s Ps : {fset T} :=
  @FSet.FSet T s Ps.

Section Operations.

Variables (T : ordType).

Implicit Type s : {fset T}.

Local Open Scope ord_scope.

Fixpoint fsetU1' (s : seq T) x : seq T :=
  if s is x' :: s' then
    if x < x' then x :: s
    else if x == x' then s
    else x' :: fsetU1' s' x
  else [:: x].

Lemma fsetU1_proof s x : sorted (@Ord.lt T) (fsetU1' s x).
Proof.
have E: forall s : seq T, fsetU1' s x =i x :: s.
  elim=> {s} // x' s /= IH x''; rewrite ![in X in X = _]fun_if /= !inE.
  rewrite IH inE.
  case: (Ord.ltgtP x x') => // H; try by bool_congr.
  by rewrite H orbA orbb.
case: s; elim=> // x' s /= IH Ps.
move: (order_path_min (@Ord.lt_trans T) Ps) => lb.
rewrite ![in X in is_true X]fun_if /= path_min_sorted; last exact: (allP lb).
rewrite (path_sorted Ps); case: Ord.ltgtP=> [x_x'//|x_x'|_ //] /=.
rewrite path_min_sorted ?(IH (path_sorted Ps)) //=; apply/allP.
by rewrite !(eq_all_r (E s)) {E} /= lb andbT.
Qed.

Definition fsetU1 s x := fset (fsetU1_proof s x).

Definition mem_fset s :=
  [pred x : T | x \in val s].

Canonical mem_fset_predType := mkPredType mem_fset.

End Operations.

Notation "x |: s" := (fsetU1 s x) : fset_scope.

Section Properties.

Variables (T : ordType).
Local Open Scope ord_scope.
Local Open Scope fset_scope.

Implicit Types (s : {fset T}) (x y : T).

Lemma eq_fseq s1 s2 : s1 =i s2 -> s1 = s2.
Proof.
case: s1 s2 => [s1 Ps1] [s2 Ps2] /= E; apply/val_inj=> /=.
have anti: antisymmetric (@Ord.lt T).
  move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  exact: Ord.anti_leq (introT andP (conj xy yx)).
have {E} E := E : s1 =i s2; apply: (eq_sorted _ _ Ps1 Ps2) => //.
  exact: Ord.lt_trans.
apply: uniq_perm_eq => //; [move: Ps1|move: Ps2]; apply/sorted_uniq => //;
by [apply: Ord.ltxx|apply: Ord.lt_trans].
Qed.

Lemma in_fsetU1 x y s : x \in y |: s = (x == y) || (x \in s).
Proof.
case: s => s Ps; rewrite !inE /=; elim: s Ps => [|z s IH /=] // Ps.
rewrite /= !inE /= ![in LHS]fun_if !inE.
case: (Ord.ltgtP y z) =>[//|z_lt_y |<-].
  by rewrite IH ?(path_sorted Ps) //; bool_congr.
by rewrite orbA orbb.
Qed.

End Properties.
