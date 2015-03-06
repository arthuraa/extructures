Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice.

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
  let xs := unzip1 f in
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

Definition fperm (T : ordType) (m : {partmap T -> T}) (Pm : FPerm.axiom m)
                 : {fperm T} :=
  FPerm.FPerm Pm.

Section Operations.

Variable T : ordType.

Implicit Types (s : {fperm T}) (x : T).

Lemma fperm_mul_subproof s1 s2 :
  FPerm.axiom (mkpartmap (pmap (fun p => if s1 p.2 == p.1 then None
                                         else Some (p.1, s1 p.2))
                               (val s2))).
Proof.
admit.
Qed.

Definition fperm_mul s1 s2 := fperm (fperm_mul_subproof s1 s2).

Definition fperm_inv_subproof s :
  FPerm.axiom (mkpartmap (map (fun p => (p.2, p.1)) (val s))).
Proof.
admit.
Qed.

Definition fpcycle s x :=
  let fix loop y n :=
    if n is n'.+1 then
      y :: if s y == x then [::]
           else loop (s y) n'
    else [:: y] in
  mkfset (loop x (size (val s))).

End Operations.

Section Properties.

Variables (T : ordType).
Local Open Scope ord_scope.
Local Open Scope fperm_scope.

Implicit Types (s : {fperm T}) (x y : T).

Lemma eq_fperm s1 s2 : s1 =1 s2 -> s1 = s2.
Proof.
have Pval: forall s x, val s x != Some x.
  move=> {s1 s2} s x; apply/eqP=> Px.
  have Px': x \in unzip1 (val s).
    by apply/mapP; exists (x, x)=> //; apply/getm_in.
  by move: (allP (valP s) x Px') => {Px'} /=; rewrite Px /= eqxx andbF.
move=> Ps1s2; apply/val_inj/eq_partmap => x.
move: (Ps1s2 x); rewrite /fun_of_fperm.
case Ps1: (val s1 x)=> [y1|] //; case Ps2: (val s2 x)=> [y2|] //.
- by move=> ->.
- by move=> ? {Ps2}; subst y1; move: (Pval s1 x); rewrite Ps1 eqxx.
by move=> ? {Ps1}; subst y2; move: (Pval s2 x); rewrite Ps2 eqxx.
Qed.

End Properties.
