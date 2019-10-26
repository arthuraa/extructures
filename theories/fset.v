From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path bigop tuple.

Require Import ord.

(******************************************************************************)
(*   This file defines a type {fset T} of finite sets over an ordType T.      *)
(* This is a subtype of seq T: we represent a set as a sorted list of set     *)
(* elements, allowing us to show extensional equality: two sets are equal if  *)
(* they have the same elements (cf. eq_fset).                                 *)
(*                                                                            *)
(*   These definitions and notations are largely similar to the finset        *)
(* library of the Mathematical Components distribution.                       *)
(*                                                                            *)
(*          fset s == the set of elements contained in the sequence s.        *)
(*         x \in s == {fset T} coerces into a collective predicate.           *)
(*                    Membership is computed like for sequences.              *)
(*          size s == the cardinality of s, defined by converting it to a     *)
(*                    sequence.                                               *)
(*           fset0 == the empty set.                                          *)
(*         fset1 x == the singleton set that contains x.                      *)
(* fset_filter p s == remove the elements of s that do not satisfy the        *)
(*                    predicate p : T -> bool.                                *)
(*       s1 :|: s2 == the union of s1 and s2.                                 *)
(*          x |: s == notation for fset1 x :|: s.                             *)
(*       s1 :&: s2 == the intersection of s1 and s2.                          *)
(*       s1 :\: s2 == remove all elements of s2 from s1.                      *)
(*          s :\ x == notation for s :\: fset1 x.                             *)
(* fdisjoint s1 s2 == the sets s1 and s2 are disjoint.                        *)
(*   fsubset s1 s2 == s1 is a subset of s2.                                   *)
(*          f @: s == the image of s by f: the set containing all elements of *)
(*                    the form f x, where x \in s.                            *)
(*      powerset s == set of all subsets of s.                                *)
(*                                                                            *)
(*   We provide lemmas and notations for big versions of idempotent           *)
(* operations (in the sense of the bigop library) indexed by sets, as well as *)
(* a \bigcup form for taking the union of a family of sets.  We do not        *)
(* a \bigcap operation for computing intersections because it does not have a *)
(* neutral element: most types are infinite, but ours sets are merely finite. *)
(******************************************************************************)

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

Lemma fset_subproof (s : seq T) :
  sorted (@Ord.lt T) (sort (@Ord.leq T) (undup s)).
Proof.
move: (undup s) (undup_uniq s)=> {s} s.
move/permPl/perm_uniq: (perm_sort (@Ord.leq T) s)=> <- u_s.
move: {s} (sort _ _) u_s (sort_sorted (@Ord.leq_total T) s)=> [|x s] //=.
case/andP; elim: s x => //= x' s IH x; rewrite inE negb_or Ord.leq_eqVlt.
rewrite eq_sym=> /andP [/negbTE -> /= _] /andP [nin u_s] /andP [-> /=].
exact: IH.
Qed.

End Def.

Module Exports.

Definition fset_of (T : ordType) & phant T := fset_type T.
Identity Coercion fset_of_fset : fset_of >-> fset_type.

Notation "{ 'fset' T }" := (@fset_of _ (Phant T))
  (at level 0, format "{ 'fset'  T }") : type_scope.
Coercion fsval : fset_type >-> seq.

Section Instances.

Variable T : ordType.

Canonical fset_subType := [subType for @fsval T].
Definition fset_eqMixin := [eqMixin of fset_type T by <:].
Canonical fset_eqType :=
  Eval hnf in EqType (fset_type T) fset_eqMixin.
Definition fset_choiceMixin :=
  [choiceMixin of fset_type T by <:].
Canonical fset_choiceType :=
  Eval hnf in ChoiceType (fset_type T) fset_choiceMixin.
Definition fset_ordMixin := [ordMixin of fset_type T by <:].
Canonical fset_ordType :=
  Eval hnf in OrdType (fset_type T) fset_ordMixin.

Canonical fset_of_subType := Eval hnf in [subType of {fset T}].
Canonical fset_of_eqType := Eval hnf in [eqType of {fset T}].
Canonical fset_of_choiceType := Eval hnf in [choiceType of {fset T}].
Canonical fset_of_ordType := Eval hnf in [ordType of {fset T}].

End Instances.

End Exports.

End FSet.

Export FSet.Exports.

Delimit Scope fset_scope with fset.

Lemma fset_key : unit. Proof. exact: tt. Qed.
Definition fset (T : ordType) : seq T -> {fset T} :=
  locked_with fset_key
              (fun (s : seq T) =>
                 @FSet.FSet T _ (FSet.fset_subproof s)).

Prenex Implicits fset.

Section Basics.

Variable T : ordType.
Local Open Scope ord_scope.

Definition pred_of_fset (s : {fset T}) :=
  [pred x : T | x \in val s].
Canonical fset_predType := PredType pred_of_fset.

Lemma in_fset s x : (x \in fset s) = (x \in s).
Proof. by rewrite [fset]unlock inE /= mem_sort mem_undup. Qed.

Implicit Type s : {fset T}.

Definition fset0 := @FSet.FSet T [::] erefl : {fset T}.
Definition fset1 x := @FSet.FSet T [:: x] erefl : {fset T}.
Definition fsetU s1 s2 := fset (val s1 ++ val s2).
Definition fset_filter P s := fset [seq x <- s | P x].
Definition fsetI s1 s2 := fset_filter (mem s1) s2.
Definition fsetD s1 s2 := fset_filter [pred x | x \notin s2] s1.
Definition fsubset s1 s2 := fsetU s1 s2 == s2.
Definition fdisjoint s1 s2 := fsetI s1 s2 == fset0.

End Basics.

Arguments fset0 {_}.
Prenex Implicits fsetU fsetI fsubset.

Notation "s1 :|: s2" := (fsetU s1 s2) : fset_scope.
Notation "x |: s" := (fsetU (fset1 x) s) : fset_scope.
Notation "s1 :&: s2" := (fsetI s1 s2) : fset_scope.
Notation "s1 :\: s2" := (fsetD s1 s2) : fset_scope.
Notation "s :\ x" := (fsetD s (fset1 x)) : fset_scope.
Notation "[ 'fset' a1 ; .. ; an ]" := (fsetU (fset1 a1) .. (fsetU (fset1 an) fset0) .. )
  (at level 0, format "[ 'fset'  a1 ;  .. ;  an ]") : fset_scope.

Section Properties.

Variables (T : ordType).
Local Open Scope fset_scope.

Implicit Types (s : {fset T}) (x y : T) (xs : seq T).

Lemma all_fset P xs : all P (fset xs) = all P xs.
Proof.
apply/(sameP allP)/(iffP allP)=> h x; first by rewrite in_fset; eauto.
by move/(_ x): h; rewrite in_fset.
Qed.

Lemma has_fset P xs : has P (fset xs) = has P xs.
Proof.
apply/(sameP hasP)/(iffP hasP)=> - [x x_in Px]; exists x=> //;
by rewrite ?in_fset // -in_fset.
Qed.

Lemma eq_fset s1 s2 : s1 =i s2 <-> s1 = s2.
Proof.
split; last congruence.
case: s1 s2 => [s1 Ps1] [s2 Ps2] /= E; apply/val_inj=> /=.
have anti: antisymmetric (@Ord.lt T).
  move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  exact: Ord.anti_leq (introT andP (conj xy yx)).
rewrite -[s1 =i s2]/(_) in E; apply: (eq_sorted _ _ Ps1 Ps2) => //.
  exact: Ord.lt_trans.
apply: uniq_perm => //; [move: Ps1|move: Ps2]; apply/sorted_uniq => //;
by [apply: Ord.ltxx|apply: Ord.lt_trans].
Qed.

Lemma fsvalK : cancel val (@fset T).
Proof. by move=> X; apply/eq_fset=> x; rewrite in_fset. Qed.

Lemma fset0E : @fset0 T = fset [::].
Proof. by apply/eq_fset=> x; rewrite in_fset. Qed.

Lemma fset1E x : fset1 x = fset [:: x].
Proof. by apply/eq_fset=> x'; rewrite in_fset. Qed.

Lemma in_fset0 x : x \in fset0 = false.
Proof. by []. Qed.

Lemma in_fset1 x y : x \in fset1 y = (x == y).
Proof. by rewrite /= inE. Qed.

Lemma fset1P x y : reflect (x = y) (x \in fset1 y).
Proof. by rewrite in_fset1; apply/eqP. Qed.

Lemma in_fsetU x s1 s2 : (x \in s1 :|: s2) = (x \in s1) || (x \in s2).
Proof. by rewrite /fsetU in_fset mem_cat. Qed.

Lemma in_fsetU1 x y s : x \in y |: s = (x == y) || (x \in s).
Proof. by rewrite in_fsetU in_fset1. Qed.

Lemma fset_cat xs ys : fset (xs ++ ys) = fset xs :|: fset ys.
Proof. by apply/eq_fset=> x; rewrite in_fsetU !in_fset mem_cat. Qed.

Lemma all_fsetU P s1 s2 : all P (s1 :|: s2) = all P s1 && all P s2.
Proof. by rewrite /fsetU all_fset all_cat. Qed.

Lemma in_fset2 x y z : x \in [fset y; z] = (x == y) || (x == z).
Proof. by rewrite !in_fsetU1 in_fset0 orbF. Qed.

Lemma fset21 x y : x \in [fset x; y].
Proof. by rewrite in_fset2 eqxx. Qed.

Lemma fset22 x y : y \in [fset x; y].
Proof. by rewrite in_fset2 eqxx orbT. Qed.

Lemma fset2P x y z : reflect (x = y \/ x = z) (x \in [fset y; z]).
Proof.
rewrite in_fset2; apply/(iffP idP).
  by case/orP=> [/eqP->|/eqP->]; auto.
by case=> [->|->]; rewrite eqxx ?orbT.
Qed.
Arguments fset2P [_ _ _].

CoInductive fset_spec : {fset T} -> Type :=
| FSetSpec0 : fset_spec fset0
| FSetSpecS x s of x \notin s : fset_spec (x |: s).

(* FIXME: This name is inconsistent with MathComp *)

Lemma fsetP s : fset_spec s.
Proof.
case: s=> [[|x xs] /= Pxs]; first by rewrite eq_axiomK; apply: FSetSpec0.
have Pxs' := path_sorted Pxs.
set s' : {fset T} := FSet.FSet Pxs'; set s : {fset T} := FSet.FSet _.
have x_nin_s : x \notin s'.
  apply/negP=> /(allP (order_path_min (@Ord.lt_trans T) Pxs)).
  by rewrite Ord.ltxx.
suff ->: s = x |: s' by apply: FSetSpecS.
by apply/eq_fset=> x'; rewrite in_fsetU1 !inE.
Qed.

Lemma fset_rect (P : {fset T} -> Type) :
  P fset0 ->
  (forall x s, x \notin s -> P s -> P (x |: s)) ->
  forall s, P s.
Proof.
move=> H0 HS []; elim=> [|/= x xs IH] Pxs; first by rewrite eq_axiomK.
move: IH => /(_ (path_sorted Pxs)).
set s : {fset T} := FSet.FSet _; set s' : {fset T} := FSet.FSet _ => Ps.
have x_nin_s : x \notin s.
  apply/negP=> /(allP (order_path_min (@Ord.lt_trans T) Pxs)).
  by rewrite Ord.ltxx.
suff ->: s' = x |: s by eauto.
by apply/eq_fset=> x'; rewrite in_fsetU1 !inE.
Qed.

Definition fset_ind (P : {fset T} -> Prop) :
  P fset0 ->
  (forall x s, x \notin s -> P s -> P (x |: s)) ->
  forall s, P s := @fset_rect P.

Lemma fsetU1P x y s : reflect (x = y \/ x \in s) (x \in y |: s).
Proof. by rewrite in_fsetU1; apply/predU1P. Qed.

Lemma fsetUP x s1 s2 : reflect (x \in s1 \/ x \in s2) (x \in s1 :|: s2).
Proof. by rewrite in_fsetU; apply/orP. Qed.

Lemma fsetUC : commutative (@fsetU T).
Proof. by move=> s1 s2; apply/eq_fset=> x; rewrite !in_fsetU orbC. Qed.

Lemma fsetUA : associative (@fsetU T).
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !in_fsetU orbA.
Qed.

Lemma fset0U : left_id fset0 (@fsetU T).
Proof. by move=> s; apply/eq_fset=> x; rewrite in_fsetU in_fset0. Qed.

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
Arguments fsubsetP [_ _].

Lemma fsubsetxx s : fsubset s s.
Proof. by apply/fsubsetP. Qed.

Lemma fsubset_trans : transitive (@fsubset T).
Proof.
by move=> s1 s2 s3 /fsubsetP ? /fsubsetP ?; apply/fsubsetP=> x; eauto.
Qed.

Lemma fsubsetUl s1 s2 : fsubset s1 (s1 :|: s2).
Proof. by rewrite /fsubset fsetUA fsetUid. Qed.

Lemma fsubsetUr s1 s2 : fsubset s2 (s1 :|: s2).
Proof. by rewrite fsetUC fsubsetUl. Qed.

Lemma fsubU1set x s1 s2 :
  fsubset (x |: s1) s2 = (x \in s2) && (fsubset s1 s2).
Proof.
apply/(sameP idP)/(iffP idP).
  case/andP=> [hx /fsubsetP hs1]; apply/fsubsetP=> x'.
  by rewrite in_fsetU1=> /orP [/eqP ->|hx']; eauto.
move/fsubsetP=> h; apply/andP; split.
  by apply: h; rewrite in_fsetU1 eqxx.
by apply/fsubsetP=> x' hx'; apply: h; rewrite in_fsetU1 hx' orbT.
Qed.

Lemma fsubUset s1 s2 s3 :
  fsubset (s1 :|: s2) s3 = (fsubset s1 s3 && fsubset s2 s3).
Proof.
apply/(sameP idP)/(iffP idP).
  case/andP=> [/fsubsetP hs1 /fsubsetP hs2]; apply/fsubsetP=> x.
  by rewrite in_fsetU=> /orP [hx|hx]; eauto.
by move/fsubsetP=> h; apply/andP; split; apply/fsubsetP=> x hx; apply: h;
rewrite in_fsetU hx ?orbT.
Qed.

Lemma fsubsetU s1 s2 s3 :
  fsubset s1 s2 || fsubset s1 s3 -> fsubset s1 (s2 :|: s3).
Proof.
by case/orP=> [/fsubsetP h | /fsubsetP h]; apply/fsubsetP=> x hx;
rewrite in_fsetU h /= ?orbT.
Qed.

Lemma fsetUS s1 s2 s3 :
  fsubset s1 s2 -> fsubset (s3 :|: s1) (s3 :|: s2).
Proof.
rewrite fsubUset fsubsetUl /= => sub; rewrite fsubsetU //.
by rewrite sub orbT.
Qed.

Lemma fsetSU s1 s2 s3 :
  fsubset s1 s2 -> fsubset (s1 :|: s3) (s2 :|: s3).
Proof. by rewrite !(fsetUC _ s3); apply: fsetUS. Qed.

Lemma fsetUSS s1 s2 s3 s4 :
  fsubset s1 s2 -> fsubset s3 s4 ->
  fsubset (s1 :|: s3) (s2 :|: s4).
Proof.
by move=> P1 P2; rewrite (fsubset_trans (fsetSU _ P1)) // fsetUS.
Qed.

Lemma fsub1set x s1 : fsubset (fset1 x) s1 = (x \in s1).
Proof.
apply/(sameP fsubsetP)/(iffP idP); last by [apply; rewrite in_fset1].
by move=> x_in x' /fset1P ->.
Qed.

Lemma fset_cons x xs : fset (x :: xs) = x |: fset xs.
Proof. by apply/eq_fset=> x'; rewrite in_fset in_fsetU1 inE in_fset. Qed.

Lemma uniq_fset s : uniq s.
Proof. exact: (sorted_uniq (@Ord.lt_trans T) (@Ord.ltxx T) (valP s)). Qed.

Lemma in_fset_filter P s x : (x \in fset_filter P s) = P x && (x \in s).
Proof. by rewrite /fset_filter in_fset mem_filter. Qed.

Lemma in_fsetI x s1 s2 : (x \in s1 :&: s2) = (x \in s1) && (x \in s2).
Proof. by rewrite in_fset_filter. Qed.

Lemma fsetIP x s1 s2 : reflect (x \in s1 /\ x \in s2) (x \in s1 :&: s2).
Proof. by rewrite in_fsetI; apply/andP. Qed.

Lemma fsetIC : commutative (@fsetI T).
Proof. by move=> s1 s2; apply/eq_fset=> x; rewrite !in_fsetI andbC. Qed.

Lemma fsetIA : associative (@fsetI T).
Proof. by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !in_fsetI andbA. Qed.

Lemma fsetIid : idempotent (@fsetI T).
Proof. by move=> s; apply/eq_fset=> x; rewrite !in_fsetI andbb. Qed.

Lemma fset0I : left_zero (@fset0 T) fsetI.
Proof. by move=> s; apply/eq_fset=> x; rewrite in_fsetI !in_fset0. Qed.

Lemma fsetI0 : right_zero (@fset0 T) fsetI.
Proof. by move=> s; apply/eq_fset=> x; rewrite in_fsetI andbF. Qed.

Lemma fsetUIl : left_distributive (@fsetU T) fsetI.
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !(in_fsetU,in_fsetI) !orb_andl.
Qed.

Lemma fsetUIr : right_distributive (@fsetU T) fsetI.
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !(in_fsetU,in_fsetI) !orb_andr.
Qed.

Lemma fsetIUl : left_distributive (@fsetI T) fsetU.
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !(in_fsetU,in_fsetI) !andb_orl.
Qed.

Lemma fsetIUr : right_distributive (@fsetI T) fsetU.
Proof.
by move=> s1 s2 s3; apply/eq_fset=> x; rewrite !(in_fsetU,in_fsetI) !andb_orr.
Qed.

Lemma fsubsetIl s1 s2 : fsubset (s1 :&: s2) s1.
Proof. by apply/fsubsetP=> x /fsetIP []. Qed.

Lemma fsubsetIr s1 s2 : fsubset (s1 :&: s2) s2.
Proof. by apply/fsubsetP=> x /fsetIP []. Qed.

Lemma fsubsetI s1 s2 s3 :
  fsubset s1 (s2 :&: s3) = (fsubset s1 s2) && (fsubset s1 s3).
Proof.
apply/(sameP idP)/(iffP idP).
  move=> /andP [/fsubsetP h2 /fsubsetP h3]; apply/fsubsetP=> x hx.
  by apply/fsetIP; eauto.
by move=> /fsubsetP=> h; apply/andP; split; apply/fsubsetP=> x /h/fsetIP [??].
Qed.

Lemma fsubIset s1 s2 s3 :
  fsubset s1 s3 || fsubset s2 s3 -> fsubset (s1 :&: s2) s3.
Proof.
by case/orP=> [/fsubsetP h|/fsubsetP h]; apply/fsubsetP=> x /fsetIP[]; eauto.
Qed.

Lemma fsetIS s1 s2 s3 :
  fsubset s1 s2 -> fsubset (s3 :&: s1) (s3 :&: s2).
Proof.
by rewrite fsubsetI fsubsetIl /= => sub; rewrite fsubIset // sub orbT.
Qed.

Lemma fsetSI s1 s2 s3 :
  fsubset s1 s2 -> fsubset (s1 :&: s3) (s2 :&: s3).
Proof. by rewrite 2!(fsetIC _ s3); apply: fsetIS. Qed.

Lemma fsetISS s1 s2 s3 s4 :
  fsubset s1 s2 -> fsubset s3 s4 ->
  fsubset (s1 :&: s3) (s2 :&: s4).
Proof.
move=> sub1 sub2; rewrite (fsubset_trans (fsetIS _ sub2)) //.
by rewrite fsetSI.
Qed.

Lemma fsetIidPl s1 s2 : reflect (s1 :&: s2 = s1) (fsubset s1 s2).
Proof.
apply: (iffP fsubsetP) => [sAB | <- x /fsetIP[] //].
apply/eq_fset=> x; rewrite in_fsetI; apply: andb_idr; exact: sAB.
Qed.

Lemma fsetIidPr s1 s2 : reflect (s1 :&: s2 = s2) (fsubset s2 s1).
Proof. rewrite fsetIC; exact: fsetIidPl. Qed.

Lemma fsetUidPl s1 s2 : reflect (s1 :|: s2 = s1) (fsubset s2 s1).
Proof. by rewrite /fsubset fsetUC; apply: eqP. Qed.

Lemma fsetUidPr s1 s2 : reflect (s1 :|: s2 = s2) (fsubset s1 s2).
Proof. exact: eqP. Qed.

Lemma fset1I x s : fset1 x :&: s = if x \in s then fset1 x else fset0.
Proof.
apply/eq_fset=> x'; rewrite 2!fun_if in_fsetI in_fset1.
by case: eqP=> [->|]; case: ifP=> //=.
Qed.

Lemma fdisjointC : commutative (@fdisjoint T).
Proof. by move=> s1 s2; rewrite /fdisjoint fsetIC. Qed.

Lemma fdisjointP s1 s2 : reflect (forall x, x \in s1 -> x \notin s2)
                                 (fdisjoint s1 s2).
Proof.
apply/(iffP eqP)=> [e x h1|].
  apply/negP=> h2; have: x \in s1 :&: s2 by apply/fsetIP; split.
  by rewrite e in_fset0.
move=> dis; apply/eq_fset=> x; rewrite in_fset0 in_fsetI.
by have [h|//] := boolP (x \in s1); rewrite (negbTE (dis _ h)).
Qed.

Lemma fdisjoint_trans s1 s2 s3 :
  fsubset s1 s2 -> fdisjoint s2 s3 -> fdisjoint s1 s3.
Proof.
by move=> /fsubsetP sub /fdisjointP dis; apply/fdisjointP=> x /sub; eauto.
Qed.

Lemma fdisjoint0s s : fdisjoint fset0 s.
Proof. by rewrite /fdisjoint fset0I. Qed.

Lemma fdisjoints0 s : fdisjoint s fset0.
Proof. by rewrite fdisjointC fdisjoint0s. Qed.

Lemma fdisjoints1 s x : fdisjoint s (fset1 x) = (x \notin s).
Proof.
apply/fdisjointP; have [ins|nins] /= := boolP (x \in s).
  by move/(_ _ ins)/fset1P.
by move=> x' ins'; apply: contra nins=> /fset1P <-.
Qed.

Lemma fdisjoint1s s x : fdisjoint (fset1 x) s = (x \notin s).
Proof. by rewrite fdisjointC fdisjoints1. Qed.

Lemma in_fsetD x s1 s2 : (x \in s1 :\: s2) = (x \notin s2) && (x \in s1).
Proof. by rewrite in_fset_filter. Qed.

Lemma in_fsetD1 x s y : (x \in s :\ y) = (x != y) && (x \in s).
Proof. by rewrite in_fsetD in_fset1. Qed.

Lemma fsetDP x s1 s2 : reflect (x \in s1 /\ x \notin s2) (x \in s1 :\: s2).
Proof. rewrite in_fsetD andbC; exact: andP. Qed.

Lemma fsubDset s1 s2 s3 : fsubset (s1 :\: s2) s3 = fsubset s1 (s2 :|: s3).
Proof.
apply/fsubsetP/fsubsetP=> [h x in1|h x ];
move/(_ x): h; rewrite in_fsetD in_fsetU.
  by rewrite in1 andbT -implyNb=> /implyP.
by move=> h /andP [nin2 in1]; move: nin2; apply: implyP; rewrite implyNb; auto.
Qed.

Lemma fsubD1set s1 x s2 : fsubset (s1 :\ x) s2 = fsubset s1 (x |: s2).
Proof.
by apply/fsubsetP/fsubsetP=> h x';
move/(_ x'): h; rewrite in_fsetD1 in_fsetU1; case: eqP.
Qed.

Lemma fsetID s1 s2 : s1 :&: s2 :|: s1 :\: s2 = s1.
Proof.
apply/eq_fset=> x; rewrite in_fsetU in_fsetI in_fsetD.
by rewrite (andbC _ (x \in s1)) -andb_orr orbN andbT.
Qed.

Lemma fsetDUl : left_distributive (@fsetD T) (@fsetU T).
Proof.
move=> s1 s2 s3; apply/eq_fset=> x; rewrite !(in_fsetU, in_fsetD).
by rewrite andb_orr.
Qed.

Lemma fsetDUr s1 s2 s3 : s1 :\: (s2 :|: s3) = (s1 :\: s2) :&: (s1 :\: s3).
Proof.
apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetU, in_fsetI).
rewrite negb_or (andbC (x \notin s3)) andbA.
rewrite -[in RHS](andbA (x \notin s2)) andbb -!andbA; congr andb.
exact: andbC.
Qed.

Lemma fsetDIl s1 s2 s3 : (s1 :&: s2) :\: s3 = (s1 :\: s3) :&: (s2 :\: s3).
Proof.
by apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetI); case: (x \notin s3).
Qed.

Lemma fsetIDA s1 s2 s3 : s1 :&: (s2 :\: s3) = (s1 :&: s2) :\: s3.
Proof.
by apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetI); bool_congr.
Qed.

Lemma fsetIDAC s1 s2 s3 : (s1 :\: s2) :&: s3 = (s1 :&: s3) :\: s2.
Proof.
by apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetI) andbA.
Qed.

Lemma fsetDIr s1 s2 s3 : s1 :\: (s2 :&: s3) = (s1 :\: s2) :|: (s1 :\: s3).
Proof.
apply/eq_fset=> x.
by rewrite !(in_fsetD, in_fsetU, in_fsetI) negb_and andb_orl.
Qed.

Lemma fsetDDl s1 s2 s3 : (s1 :\: s2) :\: s3 = s1 :\: (s2 :|: s3).
Proof.
by apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetU) negb_or; bool_congr.
Qed.

Lemma fsetDDr s1 s2 s3 : s1 :\: (s2 :\: s3) = (s1 :\: s2) :|: (s1 :&: s3).
Proof.
apply/eq_fset=> x; rewrite !(in_fsetD, in_fsetU, in_fsetI) negb_and negbK.
by rewrite orbC andb_orl; do !bool_congr.
Qed.

Lemma fsetSD s1 s2 s3 : fsubset s1 s2 -> fsubset (s1 :\: s3) (s2 :\: s3).
Proof.
move=> /fsubsetP sub; apply/fsubsetP=> x /fsetDP [/sub ??].
by apply/fsetDP; split.
Qed.

Lemma fsetDS s1 s2 s3 : fsubset s1 s2 -> fsubset (s3 :\: s2) (s3 :\: s1).
Proof.
move=> /fsubsetP sub; apply/fsubsetP=> x /fsetDP [hin hnin].
by apply/fsetDP; split=> //; apply: contra hnin; apply: sub.
Qed.

Lemma fdisjoint_fsetI0 s1 s2 : fdisjoint s1 s2 -> s1 :&: s2 = fset0.
Proof. by move=> ?; apply/eqP. Qed.

Definition fpick P s := ohead (fset_filter P s).

CoInductive fpick_spec (P : pred T) s : option T -> Type :=
| FPickSome x of P x & x \in s : fpick_spec P s (Some x)
| FPickNone of (forall x, x \in s -> ~~ P x) : fpick_spec P s None.

Lemma fpickP P s : fpick_spec P s (fpick P s).
Proof.
rewrite /fpick; case E: (val (fset_filter P s))=> [|x xs] /=.
  constructor=> x x_in_s; apply/negP => Px.
  by move: (in_fset_filter P s x); rewrite inE E Px x_in_s.
move: (in_fset_filter P s x); rewrite inE E inE eqxx /=.
by case/esym/andP=> ??; constructor.
Qed.

Lemma sizes0 : size (@fset0 T) = 0.
Proof. by []. Qed.

Lemma sizes1 x : size (fset1 x) = 1.
Proof. by []. Qed.

Lemma sizesU s1 s2 : fdisjoint s1 s2 -> size (s1 :|: s2) = size s1 + size s2.
Proof.
move=> dis /=; apply/eqP; move: (size_undup (s1 ++ s2)).
rewrite /fsetU [fset]unlock size_sort leq_eqVlt ltn_size_undup cat_uniq.
rewrite !uniq_fset /= andbT orbC -implybE size_cat=> /implyP; apply.
by apply/hasPn=> x; apply: contraTN; move/fdisjointP: dis; apply.
Qed.

Lemma sizesU1 x s : size (x |: s) = (x \notin s) + size s.
Proof.
have [|x_nin] := boolP (x \in s).
  by rewrite -fsub1set => /fsetUidPr ->.
by rewrite sizesU // fdisjointC fdisjoints1.
Qed.

Lemma sizesD1 x s : size s = (x \in s) + size (s :\ x).
Proof.
rewrite -[in LHS](fsetID s (fset1 x)) sizesU fsetIC.
  by rewrite fset1I 2![in LHS]fun_if //=.
apply/fdisjointP=> x' /fsetIP [/fset1P -> x_in].
by rewrite in_fsetD in_fset1 eqxx.
Qed.

Lemma size_fset xs : size (fset xs) <= size xs.
Proof.
have fsub: {subset fset xs <= xs} by move=> x; rewrite in_fset.
exact: (uniq_leq_size (uniq_fset _) fsub).
Qed.

Lemma uniq_size_fset xs : uniq xs = (size xs == size (fset xs)).
Proof. exact: (uniq_size_uniq (uniq_fset _) (fun x => in_fset xs x)). Qed.

Lemma fsubset_leq_size s1 s2 : fsubset s1 s2 -> size s1 <= size s2.
Proof.
elim/fset_ind: s1 s2 => [|x s1 Px IH] s2; first by rewrite leq0n.
rewrite fsubU1set sizesU1 (sizesD1 x s2) Px add1n.
case/andP=> [-> ]; rewrite ltnS=> /fsubsetP hs1s2.
apply: IH; apply/fsubsetP=> x' Hx'; rewrite in_fsetD1 hs1s2 // andbT.
by apply: contra Px=> /eqP <-.
Qed.

Lemma sizes_eq0 s : (size s == 0) = (s == fset0).
Proof.
case: s / fsetP=> [|x s Px] //; rewrite sizesU1 Px /= add1n eqE /=.
by apply/esym/negbTE/eqP=> h; move: (in_fset0 x); rewrite -h in_fsetU1 eqxx.
Qed.

Lemma fset0Pn s : reflect (exists x, x \in s) (s != fset0).
Proof.
rewrite -val_eqE; case: s => [[|x xs] Pxs] /=; constructor.
  by case=> x; rewrite inE /=.
by exists x; rewrite inE eqxx.
Qed.

Lemma fsubset_sizeP s1 s2 :
  size s1 = size s2 -> reflect (s1 = s2) (fsubset s1 s2).
Proof.
elim/fset_rect: s1 s2=> [|x s1 Px IH] s2.
  rewrite sizes0 => /esym/eqP; rewrite sizes_eq0=> /eqP ->.
  by rewrite fsubsetxx; constructor.
rewrite sizesU1 Px add1n fsubU1set => h_size.
apply/(iffP idP)=> [/andP [x_in_s2 hs1s2]|].
  have ->: s2 = x |: s2 :\ x.
    apply/eq_fset=> x'; rewrite in_fsetU1 in_fsetD1 orb_andr orbN /=.
    by have [->|] := altP (x' =P x).
  congr fsetU; apply: IH.
    by move: h_size; rewrite (sizesD1 x s2) x_in_s2 add1n=> - [?].
  apply/fsubsetP=> x' x'_in_s1; rewrite in_fsetD1 (fsubsetP hs1s2) //.
  by rewrite andbT; apply: contraTN x'_in_s1 => /eqP ->.
move=> hs2; rewrite -{}hs2 {s2} in h_size *.
by rewrite in_fsetU1 eqxx /= fsubsetUr.
Qed.

Lemma eqEfsubset s1 s2 : (s1 == s2) = (fsubset s1 s2) && (fsubset s2 s1).
Proof.
apply/(sameP idP)/(iffP idP)=> [|/eqP ->]; last by rewrite fsubsetxx.
case/andP=> [/fsubsetP s1s2 /fsubsetP s2s1]; apply/eqP/eq_fset=> x.
by apply/(sameP idP)/(iffP idP); eauto.
Qed.

Lemma eqEfsize s1 s2 : (s1 == s2) = (fsubset s1 s2) && (size s2 <= size s1).
Proof.
apply/(sameP idP)/(iffP idP)=> [/andP [hsub hsize]|/eqP ->]; last first.
  by rewrite fsubsetxx leqnn.
apply/eqP/fsubset_sizeP=> //; apply/eqP; rewrite eqn_leq hsize andbT.
by apply: fsubset_leq_size.
Qed.

Lemma fsub0set s : fsubset fset0 s.
Proof. by rewrite /fsubset fset0U. Qed.

Lemma fsubset0 s : (fsubset s fset0) = (s == fset0).
Proof. by rewrite eqEfsize sizes0 andbT. Qed.

Lemma fsubset1 x s : fsubset s (fset1 x) = (s == fset1 x) || (s == fset0).
Proof.
rewrite eqEfsize /= -sizes_eq0 orbC andbC.
by case: posnP => // /eqP; rewrite sizes_eq0 => /eqP ->; rewrite fsub0set.
Qed.

Lemma fsetU_eq0 s1 s2 : (s1 :|: s2 == fset0) = (s1 == fset0) && (s2 == fset0).
Proof. by rewrite -!fsubset0 fsubUset. Qed.

Lemma fdisjointUl s1 s2 s3 :
  fdisjoint (s1 :|: s2) s3 = (fdisjoint s1 s3) && (fdisjoint s2 s3).
Proof.
by rewrite /fdisjoint fsetIUl -fsubset0 fsubUset 2!fsubset0.
Qed.

Lemma fdisjointUr s1 s2 s3 :
  fdisjoint s1 (s2 :|: s3) = (fdisjoint s1 s2) && (fdisjoint s1 s3).
Proof.
by rewrite /fdisjoint fsetIUr -fsubset0 fsubUset 2!fsubset0.
Qed.

Lemma fset0D s : fset0 :\: s = fset0.
Proof. by apply/eq_fset=> x; rewrite in_fsetD andbF. Qed.

Lemma fsetD0 s : s :\: fset0 = s.
Proof. by apply/eq_fset=> x; rewrite in_fsetD. Qed.

Lemma fsetDv s : s :\: s = fset0.
Proof.
by apply/eqP; rewrite -fsubset0; apply/fsubsetP=> x; rewrite in_fsetD andNb.
Qed.

Lemma fsetDidPl s1 s2 : reflect (s1 :\: s2 = s1) (fdisjoint s1 s2).
Proof.
apply/(iffP idP).
  by move=> /fdisjoint_fsetI0 dis; rewrite -[LHS]fset0U -dis fsetID.
by move=> dis; rewrite /fdisjoint -dis fsetIDAC -fsetIDA fsetDv fsetI0 eqxx.
Qed.

End Properties.

Arguments fsubsetP {_} [_ _].
Arguments fset2P {_} [_ _].

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

Local Open Scope fset_scope.

Section General.

Variable T : ordType.
Variable I : eqType.

Implicit Types (U : pred T) (P : pred I) (F :  I -> {fset T}).

Lemma bigcup_sup j s P F :
  j \in s -> P j -> fsubset (F j) (\bigcup_(i <- s | P i) F i).
Proof.
elim: s=> [|j' s IH] //=; rewrite inE=> /orP [/eqP <-|]; rewrite big_cons.
  by move=> ->; rewrite fsubsetUl.
case: ifP => // _ /IH {IH} IH /IH {IH} IH.
by rewrite (fsubset_trans IH) // fsubsetUr.
Qed.

CoInductive bigcup_spec x (s : seq I) P F : Prop :=
| BigCupSpec i of i \in s & P i & x \in F i.

Lemma bigcupP x s P F :
  reflect (bigcup_spec x s P F) (x \in \bigcup_(i <- s | P i) F i).
Proof.
apply/(iffP idP)=> [|[i Ps Pi]]; last first.
  apply: fsubsetP x; exact: bigcup_sup.
elim: s=> [|i s IH]; first by rewrite big_nil.
rewrite big_cons; case: ifP=> [Pi /fsetUP [x_in|]|_].
- by apply: BigCupSpec; eauto; rewrite inE eqxx.
- case/IH=> [i' i'_in Pi' x_in]; apply: BigCupSpec; eauto.
  by rewrite inE i'_in orbT.
case/IH=> [i' i'_in Pi' x_in]; apply: BigCupSpec; eauto.
by rewrite inE i'_in orbT.
Qed.

End General.

Section Finite.

Variable T : ordType.
Variable I : finType.

Implicit Types (U : pred T) (P : pred I) (F :  I -> {fset T}).

Lemma bigcup_fin_sup j P F :
  P j -> fsubset (F j) (\bigcup_(i | P i) F i).
Proof. by apply: bigcup_sup; rewrite mem_index_enum. Qed.

Lemma bigcup_finP x P F :
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
apply/(iffP (bigcupP _ _ _ _))=> [[i _ Pi x_in]|[i Pi x_in]]; eauto.
by econstructor; eauto.
Qed.

End Finite.

End BigSetOps.

Section Image.

Variables T S : ordType.

Implicit Type s : {fset T}.

Local Open Scope fset_scope.

Definition imfset (f : T -> S) s := fset (map f s).

Local Notation "f @: s" := (imfset f s) (at level 24).

Lemma imfsetP f s x :
  reflect (exists2 y, y \in s & x = f y) (x \in f @: s).
Proof.
apply/(iffP idP).
  rewrite /imfset in_fset=> /mapP [y Py ->].
  by eexists; eauto.
move=> [y Py {x}->]; rewrite /imfset in_fset.
by apply/mapP; eauto.
Qed.
Arguments imfsetP [_ _ _].

Lemma eq_imfset f1 f2 : f1 =1 f2 -> imfset f1 =1 imfset f2.
Proof.
move=> h_f s; apply/eq_fset=> x.
by apply/(sameP idP)/(iffP idP)=> /imfsetP [y Py ->]; apply/imfsetP;
eexists; eauto.
Qed.

Lemma eq_in_imfset f1 f2 s : {in s, f1 =1 f2} -> f1 @: s = f2 @: s.
Proof.
move=> h_f; apply/eq_fset=> x.
apply/(sameP idP)/(iffP idP)=> /imfsetP [y Py ->]; apply/imfsetP;
eexists; eauto.
by apply/esym/h_f.
Qed.

Lemma mem_imfset f x s : x \in s -> f x \in f @: s.
Proof. by move=> Px; apply/imfsetP; eauto. Qed.

Lemma imfset0 f : f @: fset0 = fset0.
Proof. by rewrite /imfset [fset]unlock /=; apply/val_inj. Qed.

Lemma imfset1 f x : f @: fset1 x = fset1 (f x).
Proof. by apply/eq_fset=> y; rewrite in_fset1 /imfset in_fset /= inE. Qed.

Lemma imfsetU f s1 s2 : f @: (s1 :|: s2) = f @: s1 :|: f @: s2.
Proof.
apply/eq_fset=> y; apply/(sameP idP)/(iffP idP)=> [/fsetUP|/imfsetP].
  move=> [|] => /imfsetP [x' x'_in_s ->{y}]; apply/imfsetP;
  exists x'=> //; apply/fsetUP; eauto.
by move=> [y' /fsetUP [?|?] -> {y}]; apply/fsetUP; [left|right]; apply/imfsetP;
eauto.
Qed.

Lemma imfsetU1 f x s : f @: (x |: s) = f x |: f @: s.
Proof. by rewrite imfsetU imfset1. Qed.

Lemma imfsetI f s1 s2 :
  {in s1 & s2, injective f} -> f @: (s1 :&: s2) = f @: s1 :&: f @: s2.
Proof.
move=> inj; apply/eq_fset=> x; apply/imfsetP/fsetIP.
  case=> [{x} x x_in ->]; case/fsetIP: x_in=> [x_in1 x_in2].
  by apply/andP; rewrite ?mem_imfset.
case=> [/imfsetP [y1 y1_in ->] /imfsetP [y2 y2_in]] e.
by exists y1; rewrite // in_fsetI y1_in /= (inj _ _ y1_in y2_in e).
Qed.

Lemma imfset_fset f xs : f @: fset xs = fset [seq f x | x <- xs].
Proof.
apply/eq_fset=> x; rewrite in_fset.
apply/(sameP imfsetP)/(iffP mapP).
- by case=> {x} x xin ->; exists x; rewrite ?in_fset.
- by case=> {x} x xin ->; exists x; rewrite -1?in_fset.
Qed.

Lemma imfset_eq0 f X : (f @: X == fset0) = (X == fset0).
Proof.
apply/(sameP idP)/(iffP idP)=> [/eqP ->|]; first by rewrite imfset0.
apply: contraTT; case/fset0Pn=> x xX; apply/fset0Pn; exists (f x).
by rewrite mem_imfset.
Qed.

End Image.

Notation "f @: s" := (imfset f s) (at level 24) : fset_scope.

Prenex Implicits imfset.
Arguments imfsetP {_ _} [_ _ _].

Section ImageProps.

Local Open Scope fset_scope.

Variables T S R : ordType.

Implicit Types (s : {fset T}) (f : T -> S) (g : S -> R).

Lemma imfset_id s : id @: s = s.
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  by move=> x_in; apply/imfsetP; eauto.
by case/imfsetP=> [/= ? ? ->].
Qed.

Lemma imfset_comp f g s : (g \o f) @: s = g @: (f @: s).
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  case/imfsetP=> [y /imfsetP [z Pz ->] ->].
  by apply/imfsetP; eauto.
case/imfsetP=> [y /= Py ->]; apply/imfsetP; exists (f y)=> //.
exact: mem_imfset.
Qed.

Lemma imfsetK f f_inv : cancel f f_inv -> cancel (imfset f) (imfset f_inv).
Proof.
move=> fK s; apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  move=> x_in; apply/imfsetP; exists (f x); first by apply mem_imfset.
  by rewrite fK.
case/imfsetP=> [y /imfsetP [z Pz ->] ->].
by rewrite fK.
Qed.

Lemma imfset_inj f : injective f -> injective (imfset f).
Proof.
move=> f_inj s1 s2 e; apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  by move=> /(mem_imfset f); rewrite -{}e=> /imfsetP [y Py /f_inj ->].
by move=> /(mem_imfset f); rewrite {}e=> /imfsetP [y Py /f_inj ->].
Qed.

Lemma imfsetS f s1 s2 : fsubset s1 s2 -> fsubset (f @: s1) (f @: s2).
Proof.
move/fsubsetP=> h_sub; apply/fsubsetP=> x /imfsetP [y /h_sub Py ->].
by apply: mem_imfset.
Qed.

Lemma mem_imfset_can f f_inv x s :
  cancel f f_inv -> cancel f_inv f -> (x \in f @: s) = (f_inv x \in s).
Proof.
move=> fK fKV; apply/(sameP idP)/(iffP idP).
  by move=> h_x; apply/imfsetP; eexists; eauto.
by case/imfsetP=> [y Py ->]; rewrite fK.
Qed.

Lemma mem_imfset_inj f y s :
  injective f -> (f y \in f @: s) = (y \in s).
Proof.
move=> f_inj; apply/(sameP imfsetP)/(iffP idP); first by eauto.
by move=> [y' Py' /f_inj ->].
Qed.

Lemma size_imfset f s : size (f @: s) <= size s.
Proof.
by rewrite /imfset (leq_trans (size_fset (map f s))) // size_map.
Qed.

Lemma imfset_injP f s :
  reflect {in s &, injective f} (size (f @: s) == size s).
Proof.
elim/fset_rect: s => [|x s Px IH]; first by rewrite imfset0 eqxx; constructor.
rewrite imfsetU1 !sizesU1 Px add1n /=; apply/(iffP idP).
  have [hin|hnin] /= := boolP (f x \in _).
    by rewrite add0n=> /eqP him; move: (size_imfset f s); rewrite him ltnn.
  rewrite add1n eqSS
    => /IH hinj y1 y2 /fsetU1P[->{y1}|hy1] /fsetU1P[->{y2}|hy2] //=;
    last by eauto.
    by move=> hfx; rewrite hfx (mem_imfset f hy2) in hnin.
  by move=> hfx; rewrite -hfx (mem_imfset f hy1) in hnin.
move=> hinj; have /IH/eqP ->: {in s &, injective f}.
  by move=> y1 y2 hy1 hy2 /=; apply:hinj; apply/fsetU1P; auto.
suff ->: f x \notin f @: s by [].
apply: contra Px=> /imfsetP [x' Px' hfx']; suff -> : x = x' by [].
by apply: hinj _ _ hfx'; apply/fsetU1P; auto.
Qed.

End ImageProps.

Section Powerset.

Local Open Scope fset_scope.

Variable T : ordType.
Implicit Types (x : T) (s : {fset T}).

Definition powerset s :=
  fset [seq fset (mask (val m) s) |
        m : (size s).-tuple bool <- enum predT].

Lemma powersetE s1 s2 : (s1 \in powerset s2) = fsubset s1 s2.
Proof.
rewrite /powerset in_fset; apply/(sameP mapP)/(iffP idP).
  move=> /fsubsetP s12.
  exists [tuple of [seq x \in s1 | x <- in_tuple s2]].
    by rewrite mem_enum.
  apply/eq_fset => x; rewrite in_fset -filter_mask mem_filter /=.
  by have [/s12|] := boolP (x \in s1).
case=> m _ -> {s1}; apply/fsubsetP => x; rewrite in_fset; exact: mem_mask.
Qed.

Lemma powersetS s1 s2 : fsubset (powerset s1) (powerset s2) = fsubset s1 s2.
Proof.
apply/(sameP fsubsetP)/(iffP idP).
  move=> sub s3; rewrite !powersetE => sub'; exact: fsubset_trans sub.
move/(_ s1); rewrite !powersetE; apply; exact: fsubsetxx.
Qed.

Lemma powerset0 : powerset fset0 = fset1 fset0.
Proof.
by apply/eq_fset=> s; rewrite powersetE fsubset0 in_fset1.
Qed.

Lemma powerset1 x : powerset (fset1 x) = [fset fset1 x; fset0].
Proof.
by apply/eq_fset=> s; rewrite in_fset2 powersetE fsubset1.
Qed.

End Powerset.

Section BigOpIdempotent.

Variables (R : Type) (idx : R).
Local Notation "1" := idx.

Variable op : Monoid.com_law 1.
Local Notation "*%M" := op (at level 0).
Local Notation "x * y" := (op x y).

Hypothesis opxx : idempotent op.

Local Open Scope fset_scope.

Section Basic.

Variables (I : ordType) (J : Type).
Variables (F : I -> R) (G : J -> {fset I}).

Lemma big_idem_fsetU1 i0 s :
  \big[*%M/1]_(i <- i0 |: s) F i = F i0 * \big[*%M/1]_(i <- s) F i.
Proof.
have e: i0 |: s =i i0 :: s.
  by move=> i; rewrite in_fsetU1 [in RHS]inE.
by rewrite (eq_big_idem _ _ _ e) /= ?big_cons.
Qed.

Lemma big_idem_fsetU s1 s2 :
  \big[*%M/1]_(i <- s1 :|: s2) F i =
  (\big[*%M/1]_(i <- s1) F i) * (\big[*%M/1]_(i <- s2) F i).
Proof.
elim/fset_ind: s1 => [|i s1 _ IH]; first by rewrite big_nil 2!Monoid.mul1m.
by rewrite -fsetUA !big_idem_fsetU1 // IH Monoid.mulmA.
Qed.

Lemma big_idem_bigcup s :
  \big[*%M/1]_(i <- \bigcup_(j <- s) G j) F i
  = \big[*%M/1]_(j <- s) \big[*%M/1]_(i <- G j) F i.
Proof.
elim: s => [|j s IH]; first by rewrite 3!big_nil.
by rewrite 2!big_cons big_idem_fsetU IH.
Qed.

End Basic.

Section Image.

Variables (I J : ordType).
Variables (F : I -> R) (G : J -> I).

Lemma big_idem_imfset s :
  \big[*%M/1]_(i <- G @: s) F i
  = \big[*%M/1]_(i <- s) F (G i).
Proof.
elim/fset_ind: s => [|j s _ IH]; first by rewrite imfset0 2!big_nil.
by rewrite imfsetU1 2!big_idem_fsetU1 IH.
Qed.

End Image.

End BigOpIdempotent.

Section BigOpUnion.

(* Specialize previous lemmas to unions *)

Variables (I J R : ordType) (F : I -> {fset R}) (G : J -> {fset I}).

Local Open Scope fset_scope.

Lemma bigcup_fsetU1 i0 s :
  \bigcup_(i <- i0 |: s) F i = F i0 :|: \bigcup_(i <- s) F i.
Proof. apply: big_idem_fsetU1; exact: fsetUid. Qed.

Lemma bigcup_fsetU s1 s2 :
  \bigcup_(i <- s1 :|: s2) F i =
  (\bigcup_(i <- s1) F i) :|: (\bigcup_(i <- s2) F i).
Proof. apply: big_idem_fsetU; exact: fsetUid. Qed.

Lemma bigcup_bigcup s :
  \bigcup_(i <- \bigcup_(j <- s) G j) F i =
  \bigcup_(j <- s) \bigcup_(i <- G j) F i.
Proof. apply: big_idem_bigcup; exact: fsetUid. Qed.

End BigOpUnion.
