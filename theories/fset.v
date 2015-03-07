Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.path MathComp.bigop.

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

Definition fset0 := @fset T [::] erefl.

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

Definition fsetU s1 s2 := foldr (fun x s => fsetU1 s x) s2 s1.

Definition fsubset s1 s2 := fsetU s1 s2 == s2.

Definition mkfset xs := foldr (fun x s => fsetU1 s x) fset0 xs.

Definition mem_fset s :=
  [pred x : T | x \in val s].

Canonical mem_fset_predType := mkPredType mem_fset.

End Operations.

Arguments fset0 {_}.
Prenex Implicits fsetU1 fsetU mkfset.

Notation "x |: s" := (fsetU1 s x) : fset_scope.
Notation "s1 :|: s2" := (fsetU s1 s2) : fset_scope.

Section Properties.

Variables (T : ordType).
Local Open Scope ord_scope.
Local Open Scope fset_scope.

Implicit Types (s : {fset T}) (x y : T) (xs : seq T).

Lemma eq_fset s1 s2 : s1 =i s2 -> s1 = s2.
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

Lemma in_fset0 x : x \in fset0 = false.
Proof. by []. Qed.

Lemma in_fsetU1 x y s : x \in y |: s = (x == y) || (x \in s).
Proof.
case: s => s Ps; rewrite !inE /=; elim: s Ps => [|z s IH /=] // Ps.
rewrite /= !inE /= ![in LHS]fun_if !inE.
case: (Ord.ltgtP y z) =>[//|z_lt_y |<-].
  by rewrite IH ?(path_sorted Ps) //; bool_congr.
by rewrite orbA orbb.
Qed.

Lemma size_fsetU1 s x : size (x |: s) = (x \notin s) + size s.
Proof.
rewrite /fsetU1 /= [in RHS]inE /=; move: (valP s)=>/=; move: (s : seq _).
elim{s} => [|x' xs IH] //=.
rewrite inE negb_or; case: Ord.ltgtP=> //=.
  move=> xx' hxs {IH}; suff -> : x \notin xs by [].
  apply/negP=> /(allP (order_path_min (@Ord.lt_trans T) hxs)).
  by rewrite Ord.ltNge (Ord.ltW xx').
move=> x'x hxs; move: IH => /(_ (path_sorted hxs)) ->.
by rewrite addnS.
Qed.

Lemma in_fsetU x s1 s2 : (x \in s1 :|: s2) = (x \in s1) || (x \in s2).
Proof.
case: s1=> [/= s1 Ps1]; rewrite /fsetU !inE /= {Ps1}.
by elim: s1=> [|y s1 IH] //=; rewrite in_fsetU1 IH inE; bool_congr.
Qed.

Lemma fsetUP x s1 s2 : reflect (x \in s1 \/ x \in s2) (x \in s1 :|: s2).
Proof. by rewrite in_fsetU; apply/orP. Qed.

Lemma fsetUC : commutative (@fsetU T).
Proof. by move=> s1 s2; apply/eq_fset=> x; rewrite !in_fsetU orbC. Qed.

Lemma fsetUA : associative (@fsetU T).
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !in_fsetU orbA.
Qed.

Lemma fset0U : left_id fset0 (@fsetU T).
Proof. by []. Qed.

Lemma fsetU0 : right_id fset0 (@fsetU T).
Proof. by move=> s; rewrite fsetUC fset0U. Qed.

Lemma fsetUid : idempotent (@fsetU T).
Proof. by move=> s; apply/eq_fset=> x; rewrite in_fsetU orbb. Qed.

Lemma fsubsetP s1 s2 : reflect {subset s1 <= s2} (fsubset s1 s2).
Proof.
apply/(iffP idP)=> [/eqP <- x|hs1s2]; first by rewrite in_fsetU => ->.
apply/eqP/eq_fset=> x; rewrite in_fsetU.
have [/hs1s2|//] //= := boolP (x \in s1).
Qed.

Lemma fsubsetUl s1 s2 : fsubset s1 (s1 :|: s2).
Proof. by rewrite /fsubset fsetUA fsetUid. Qed.

Lemma fsubsetUr s1 s2 : fsubset s2 (s1 :|: s2).
Proof. by rewrite fsetUC fsubsetUl. Qed.

Lemma in_mkfset x xs : (x \in mkfset xs) = (x \in xs).
Proof. by elim: xs => [|x' xs IH] //=; rewrite in_fsetU1 IH inE. Qed.

Lemma mkfset_cons x xs : mkfset (x :: xs) = x |: mkfset xs.
Proof. by []. Qed.

Lemma uniq_fset s : uniq s.
Proof. exact: (sorted_uniq (@Ord.lt_trans T) (@Ord.ltxx T) (valP s)). Qed.

Lemma size_mkfset xs : size (mkfset xs) <= size xs.
Proof.
have fsub: {subset mkfset xs <= xs} by move=> x; rewrite in_mkfset.
exact: (uniq_leq_size (uniq_fset _) fsub).
Qed.

Lemma uniq_size_mkfset xs : uniq xs = (size xs == size (mkfset xs)).
Proof. exact: (uniq_size_uniq (uniq_fset _) (fun x => in_mkfset x _)). Qed.

End Properties.

Section setOpsAlgebra.

Import Monoid.

Variable T : ordType.

Canonical fsetU_monoid := Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical fsetU_comoid := ComLaw (@fsetUC T).

End setOpsAlgebra.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@fsetU _/fset0]_(i <- r | P) F%fset) : fset_scope.
Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@fsetU _/fset0]_(i <- r) F%fset) : fset_scope.
Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@fsetU _/fset0]_(m <= i < n | P%B) F%fset) : fset_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@fsetU _/fset0]_(m <= i < n) F%fset) : fset_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P%B) F%fset) : fset_scope.
Notation "\bigcup_ i F" :=
  (\big[@fsetU _/fset0]_i F%fset) : fset_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@fsetU _/fset0]_(i : t | P%B) F%fset) (only parsing): fset_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@fsetU _/fset0]_(i : t) F%fset) (only parsing) : fset_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@fsetU _/fset0]_(i < n | P%B) F%fset) : fset_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@fsetU _/fset0]_ (i < n) F%fset) : fset_scope.
Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@fsetU _/fset0]_(i in A | P%B) F%fset) : fset_scope.
Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@fsetU _/fset0]_(i in A) F%fset) : fset_scope.

Section BigSetOps.

Variable T : ordType.
Variable I : finType.

Implicit Types (U : pred T) (P : pred I) (F :  I -> {fset T}).

Local Open Scope fset_scope.

Lemma bigcup_sup j P F : P j -> fsubset (F j) (\bigcup_(i | P i) F i).
Proof. by move=> Pj; rewrite (bigD1 j) //= fsubsetUl. Qed.

Lemma bigcupP x P F :
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
apply/(iffP idP)=> [|[i Pi]]; last first.
  apply: fsubsetP x; exact: bigcup_sup.
by elim/big_rec: _ => [|i _ Pi _ /fsetUP[|//]]; [rewrite inE | exists i].
Qed.

End BigSetOps.

Section Image.

Variables T S : ordType.

Implicit Type s : {fset T}.

Definition imfset (f : T -> S) s := mkfset (map f s).

End Image.

Notation "f @: s" := (imfset f s) (at level 24) : fset_scope.

Prenex Implicits imfset.

Section CardImage.

Local Open Scope fset_scope.

Variables T S : ordType.

Implicit Types (s : {fset T}) (f : T -> S).

Lemma size_imfset f s : size (f @: s) <= size s.
Proof.
by rewrite /imfset (leq_trans (size_mkfset (map f s))) // size_map.
Qed.

Lemma imfset_injP f s : reflect {in s &, injective f} (size (f @: s) == size s).
Proof.
case: s => [s Ps] /=; rewrite /imfset /=.
suff h: reflect {in s &, injective f}
                (size (mkfset [seq f i | i <- s]) == size s).
  by apply/(iffP h); move=> {h} h x1 x2; rewrite ?inE /=; apply: h.
elim: s Ps => [|x s IH] Ps; first by constructor.
rewrite map_cons mkfset_cons size_fsetU1 /=; apply/(iffP idP).
  have [hin|hnin] := boolP (_ \in _).
    rewrite add0n=> /eqP hs.
    suff: size (mkfset (map f s)) < (size s).+1 by rewrite -hs ltnn.
    by rewrite ltnS (leq_trans (size_mkfset (map f s))) // size_map leqnn.
    rewrite add1n eqSS => /IH hinj x1 x2.
    rewrite !inE=> /orP [/eqP ?|x1_in_s] /orP [/eqP ?|x2_in_s].
    - by subst x1 x2.
    - subst x1=> h; apply/eqP; apply: contraNT hnin => _.
      by rewrite h in_mkfset; apply/mapP; exists x2.
    - subst x2=> h; apply/eqP; apply: contraNT hnin => _.
      by rewrite -h in_mkfset; apply/mapP; exists x1.
    rewrite /= in Ps; move/path_sorted in Ps; move/(_ Ps) in hinj.
    by apply: hinj x1_in_s x2_in_s.
move=> hinj; have [hin|hnin] /= := boolP (_ \in _).
  move: hin; rewrite in_mkfset; move/mapP=> [y Py Px].
  move: {hinj}(hinj x y); rewrite !inE eqxx Py orbT /= => /(_ erefl erefl Px).
  move=> ?; subst y.
  move: Ps => /= /(order_path_min (@Ord.lt_trans T))/allP/(_ _ Py).
  by rewrite Ord.ltxx.
rewrite eqSS; apply/IH; first by apply: path_sorted.
by move=> y z Py Pz; apply: hinj; rewrite inE ?Py ?Pz orbT.
Qed.

End CardImage.
