From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype generic_quotient.

Require Import void.

(******************************************************************************)
(*   Class of types with a decidable total order relation.  Its main purpose  *)
(* is to supply an interface for aggregate structures (sets, maps) that       *)
(* support extensional equality and executable operations; accordingly, it    *)
(* sticks to basic constructions and results.                                 *)
(*                                                                            *)
(*        ordType == a type with a total order relation.                      *)
(*   Ord.axioms r == the relation r is a total order.                         *)
(*    OrdMixin ax == the mixin of the ordered class, where ax is a proof that *)
(*                   a relation is a total order.                             *)
(*         x <= y == order relation of an ordType (Ord.leq in prefix form).   *)
(*          x < y == strict ordering.                                         *)
(*                                                                            *)
(*   These notations are delimited by the %ord key, and are not open by       *)
(* default, to avoid conflicts with the standard ordering of nat.  Ternary    *)
(* variants such as x <= y <= z are also available.                           *)
(*   Currently, ord is defined as a subclass of choice, in order to simplify  *)
(* the class hierarchy while supporting the use of generic quotients on       *)
(* things that involve ordTypes, in particular finite maps.                   *)
(*   In addition to instances for basic types such as bool, nat, seq, and     *)
(* quotients, this file provides infrastructure for defining some derived     *)
(* instances.                                                                 *)
(*                                                                            *)
(*       PcanOrdMixin fK == the mixin for T, given f : T -> S and g with S    *)
(*                          an ordType and fK : pcancel f g.                  *)
(*        CanOrdMixin fK == the mixin for T, given f : T -> S and g with S    *)
(*                          an ordType and fK : cancel f g.                   *)
(*        InjOrdMixin fI == the mixin for T, given f : T -> S with S          *)
(*                          an ordType and fI : injective f.                  *)
(* [ordMixin of T by <:] == the mixin for T, assuming that it was             *)
(*                          declared as the subtype of some ordType S.        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Interface of types with an order relation. *)

Delimit Scope ord_scope with ord.

Module Ord.

Module Total.

Section ClassDef.

Record axioms T (leq : rel T) := Ax {
  _ : reflexive leq;
  _ : transitive leq;
  _ : antisymmetric leq;
  _ : total leq
}.

Record mixin_of T := Mixin {
  leq : rel T;
  _   : axioms leq
}.

Record class_of T := Class {base : Choice.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Choice.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation ordType := type.
Notation ordMixin := mixin_of.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T m _ _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.

End Total.

Export Total.Exports.

Definition leq T := Total.leq (Total.class T).
Definition lt (T : ordType) (x y : T) := leq x y && (x != y).

Notation "x <= y" := (leq x y) : ord_scope.
Notation "x < y" := (lt x y) : ord_scope.
Notation "x <= y <= z" := (leq x y && leq y z) : ord_scope.
Notation "x <= y <  z" := (leq x y && lt  y z) : ord_scope.
Notation "x <  y <= z" := (lt  x y && leq y z) : ord_scope.
Notation "x <  y <  z" := (lt  x y && lt  y z) : ord_scope.

Section Theory.

Local Open Scope ord_scope.

Variable T : ordType.
Implicit Types x y : T.

Lemma leqxx : reflexive (@leq T).
Proof. by case: T => ? [? [? []]]. Qed.

Lemma leq_trans : transitive (@leq T).
Proof. by case: T => ? [? [? []]]. Qed.

Lemma anti_leq : antisymmetric (@leq T).
Proof. by case: T => ? [? [? []]]. Qed.

Lemma leq_total : total (@leq T).
Proof. by case: T => [? [? [? []]]]. Qed.

Lemma eq_leq x y : x = y -> x <= y.
Proof. by move=> ->; rewrite leqxx. Qed.

Lemma ltW (x y : T) : x < y -> x <= y.
Proof. by case/andP. Qed.

Lemma ltxx (x : T) : (x < x) = false.
Proof. by rewrite /lt eqxx andbF. Qed.

Lemma lt_trans : transitive (@lt T).
Proof.
move=> y x z /= /andP [lxy exy] /andP [lyz eyz].
rewrite /lt (@leq_trans y) //=.
apply: contra eyz; move=> /eqP exz; move: (@anti_leq x y).
by rewrite -{}exz {z} in lyz * => -> //; apply/andP; split.
Qed.

Lemma eq_op_leq (x y : T) : (x == y) = (x <= y <= x).
Proof.
apply/(sameP idP)/(iffP idP); first by move=> /anti_leq ->.
by move=> /eqP ->; rewrite leqxx.
Qed.

Lemma leq_eqVlt (x y : T) : (x <= y) = (x == y) || (x < y).
Proof.
rewrite /lt; have [<-{y}|] /= := altP (_ =P _); first by rewrite leqxx.
by rewrite andbT.
Qed.

Lemma lt_neqAle (x y : T) : (x < y) = (x != y) && (x <= y).
Proof. by rewrite /lt andbC. Qed.

Lemma leqNgt x y : (x <= y) = ~~ (y < x).
Proof.
rewrite /lt.
have [lxy|] := boolP (x <= y).
  have [lyx|gyx] //= := boolP (y <= x).
  rewrite negbK (@anti_leq x y) ?eqxx //.
  by rewrite lxy lyx.
have [->{y}|nyx gyx] /= := altP (y =P x).
  by rewrite leqxx.
by move: (leq_total x y); rewrite (negbTE gyx) /= => ->.
Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x).
Proof. by rewrite leqNgt negbK. Qed.

CoInductive compare_ord x y : bool -> bool -> bool -> Set :=
| CompareOrdLt of x < y : compare_ord x y true false false
| CompareOrdGt of y < x : compare_ord x y false true false
| CompareOrdEq of x = y : compare_ord x y false false true.

Lemma ltgtP x y : compare_ord x y (x < y) (y < x) (x == y).
Proof.
rewrite lt_neqAle.
have [<- {y}|Hne] //= := altP (_ =P _).
  by rewrite ltxx; constructor.
rewrite ltNge; have [Hl|Hg] := boolP (x <= y); constructor=> //.
  by rewrite /lt Hl.
by rewrite ltNge.
Qed.

End Theory.

End Ord.

Export Ord.Total.Exports.

Notation "x <= y" := (Ord.leq x y) : ord_scope.
Notation "x < y" := (Ord.lt x y) : ord_scope.
Notation "x <= y <= z" := (Ord.leq x y && Ord.leq y z) : ord_scope.
Notation "x <= y <  z" := (Ord.leq x y && Ord.lt  y z) : ord_scope.
Notation "x <  y <= z" := (Ord.lt  x y && Ord.leq y z) : ord_scope.
Notation "x <  y <  z" := (Ord.lt  x y && Ord.lt  y z) : ord_scope.

Definition nat_ordMixin :=
  OrdMixin (Ord.Total.Ax leqnn leq_trans anti_leq leq_total).
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Section ProdOrd.

Variables T S : ordType.
Local Open Scope ord_scope.

(* For products, we use lexicographic ordering. *)

Definition prod_leq : rel (T * S) :=
  [rel p1 p2 |
   if p1.1 == p2.1 then p1.2 <= p2.2
   else p1.1 <= p2.1].

Lemma prod_leqP : Ord.Total.axioms prod_leq.
Proof.
rewrite /prod_leq; split.
- by move=> ?; rewrite /= eqxx Ord.leqxx.
- move=> p1 p2 p3; rewrite /=.
  have [->|H21] := altP (p2.1 =P _).
    have [_|//] := altP (_ =P _).
    by apply Ord.leq_trans.
  have [<-|H13] := altP (p1.1 =P _).
    by rewrite (negbTE H21).
  have [<-|H23] := altP (_ =P _).
    move=> {H13} l21 l12; rewrite (@Ord.anti_leq _ p1.1 p2.1) ?eqxx // in H21.
    by rewrite l12 l21.
  by apply Ord.leq_trans.
- move=> [x1 y1] [x2 y2]; rewrite /= eq_sym.
  have [/eqP -> /Ord.anti_leq -> //|Hne /Ord.anti_leq E] := ifP.
  by rewrite E eqxx in Hne.
move=> p1 p2; rewrite /Ord.leq /= eq_sym.
by case: ifP=> ?; apply: Ord.leq_total.
Qed.

Definition prod_ordMixin := OrdMixin prod_leqP.
Canonical prod_ordType :=
  Eval hnf in OrdType (T * S) prod_ordMixin.

End ProdOrd.

Section SeqOrd.

Variable T : ordType.
Local Open Scope ord_scope.

Fixpoint seq_leq (s1 s2 : seq T) :=
  match s1, s2 with
  | x1 :: s1, x2 :: s2 =>
    if x1 == x2 then seq_leq s1 s2 else x1 <= x2
  | [::], _ => true
  | _ :: _, _ => false
  end.

Lemma seq_leqP : Ord.Total.axioms seq_leq.
Proof.
split.
- by elim=> [|x s IH] //=; rewrite eqxx.
- elim=> [|x1 s1 IH] [|x2 s2] [|x3 s3] //=.
  have [->|H21] := altP (_ =P _).
    have [_|//] := altP (_ =P _).
    by apply IH.
  have [<-|H13] := altP (_ =P _).
    by rewrite (negbTE H21).
  have [<-|H23] := altP (_ =P _).
    move=> l21 l12 {H13}; rewrite (@Ord.anti_leq _ x1 x2) ?eqxx // in H21.
    by rewrite l21 l12.
  by apply Ord.leq_trans.
- elim=> [|x1 s1 IH] [|x2 s2] //=.
  rewrite /= eq_sym.
  have [-> /IH -> //|Hne /Ord.anti_leq E] := altP (_ =P _).
  by rewrite E eqxx in Hne.
elim=> [|x1 s1 IH] [|x2 s2] //=.
rewrite /= eq_sym.
by have [_|Hne] := altP (_ =P _); auto; apply Ord.leq_total.
Qed.

Definition seq_ordMixin := OrdMixin seq_leqP.
Canonical seq_ordType :=
  Eval hnf in OrdType (seq T) seq_ordMixin.

End SeqOrd.

Section SumOrd.

Variables (T S : ordType).
Local Open Scope ord_scope.

Definition sum_leq (x y : T + S) :=
  match x, y with
  | inl x, inl y => x <= y
  | inr x, inr y => x <= y
  | inl _, inr _ => true
  | inr _, inl _ => false
  end.

Lemma sum_leqP : Ord.Total.axioms sum_leq.
Proof.
split.
- by case=> [x|y] /=; rewrite Ord.leqxx.
- by case=> [x1|y1] [x2|y2] [x3|y3] //=; apply: Ord.leq_trans.
- by case=> [x1|y1] [x2|y2] //= => /Ord.anti_leq ->.
by case=> [x1|y1] [x2|y2] //=; apply: Ord.leq_total.
Qed.

Definition sum_ordMixin := OrdMixin sum_leqP.
Canonical sum_ordType :=
  Eval hnf in OrdType (T + S) sum_ordMixin.

End SumOrd.

Section OptionOrd.

Variables (T : ordType).
Local Open Scope ord_scope.

Definition option_leq (x y : option T) :=
  match x, y with
  | Some x, Some y => x <= y
  | None, _ => true
  | Some _, None => false
  end.

Lemma option_leqP : Ord.Total.axioms option_leq.
Proof.
split.
- by case=> [x|] //=; rewrite Ord.leqxx.
- by case=> [x1|] [x2|] [x3|] //=; apply: Ord.leq_trans.
- by case=> [x1|] [x2|] //= => /Ord.anti_leq ->.
by case=> [x1|] [x2|] //=; apply: Ord.leq_total.
Qed.

Definition option_ordMixin := OrdMixin option_leqP.
Canonical option_ordType :=
  Eval hnf in OrdType (option T) option_ordMixin.

End OptionOrd.

Section TransferOrdType.

Variables (T : Type) (eT : ordType) (f : T -> eT).
Local Open Scope ord_scope.

Local Notation le := (fun x y => f x <= f y).

Lemma inj_ordP : injective f -> Ord.Total.axioms le.
Proof.
move=> f_inj; split.
- by move=> x; rewrite /= Ord.leqxx.
- by move=> x y z /=; exact: Ord.leq_trans.
- by move=> x y /= /Ord.anti_leq /f_inj.
by move=> x y; exact: Ord.leq_total.
Qed.

Definition InjOrdMixin f_inj := OrdMixin (inj_ordP f_inj).

Definition PcanOrdMixin g (fK : pcancel f g) :=
  InjOrdMixin (pcan_inj fK).

Definition CanOrdMixin g (fK : cancel f g) :=
  InjOrdMixin (can_inj fK).

End TransferOrdType.

Section SubOrdType.

Variables (T : ordType) (P : pred T) (sT : subType P).
Local Open Scope ord_scope.

Definition sub_ordMixin := @InjOrdMixin _ _ (@val T P sT) val_inj.
Canonical sub_ordType := Eval hnf in OrdType sT sub_ordMixin.

Lemma val_ordE (u v : sT) : (val u <= val v) = (u <= v).
Proof. by []. Qed.

End SubOrdType.

Notation "[ 'ordMixin' 'of' T 'by' <: ]" :=
    (sub_ordMixin _ : Ord.Total.mixin_of T)
  (at level 0, format "[ 'ordMixin'  'of'  T  'by'  <: ]") : form_scope.

Definition ordinal_ordMixin n := [ordMixin of 'I_n by <:].
Canonical ordinal_ordType n :=
  Eval hnf in OrdType 'I_n (ordinal_ordMixin n).

Lemma bool_leqP : Ord.Total.axioms implb.
Proof. split; by do ![case=> //]. Qed.

Definition bool_ordMixin := OrdMixin bool_leqP.
Canonical bool_ordType := Eval hnf in OrdType bool bool_ordMixin.

Definition unit_leq (x y : unit) := true.

Lemma unit_leqP : Ord.Total.axioms unit_leq.
Proof. split; by do ![case]. Qed.

Definition unit_ordMixin := OrdMixin unit_leqP.
Canonical unit_ordType := Eval hnf in OrdType unit unit_ordMixin.

Definition void_ordMixin := PcanOrdMixin (of_voidK unit).
Canonical void_ordType := Eval hnf in OrdType void void_ordMixin.

Section Tagged.

Variables (I : ordType) (T_ : I -> ordType).
Implicit Types u v : {x : I & T_ x}.

Local Open Scope ord_scope.

Definition tag_leq u v :=
  (tag u < tag v) || (tag u == tag v) && (tagged u <= tagged_as u v).

Definition tag_leqP : Ord.Total.axioms tag_leq.
Proof.
rewrite /tag_leq; split.
- by move=> [i x] /=; rewrite Ord.ltxx eqxx tagged_asE Ord.leqxx.
- move=> [i2 x2] [i1 x1] [i3 x3] /=.
  case: Ord.ltgtP x2=> [i1i2 x2 _|?|<- {i2} x2] //=.
    case: Ord.ltgtP x3=> [i2i3 x3 _|?|<- {i3} x3] //=; last by rewrite i1i2.
    by rewrite (Ord.lt_trans i1i2 i2i3).
  case: Ord.ltgtP x3=> //= <- {i3} x3; rewrite !tagged_asE.
  exact: Ord.leq_trans.
- move=> [i1 x1] [i2 x2] /=; rewrite [i2 == i1]eq_sym.
  case: Ord.ltgtP x2=> //= i1i2; rewrite -{}i1i2 {i2} => x2.
  by rewrite !tagged_asE => /Ord.anti_leq ->.
move=> [i1 x1] [i2 x2] /=; rewrite [i2 == i1]eq_sym.
by case: Ord.ltgtP x2 => //= <- {i2} x2; rewrite !tagged_asE Ord.leq_total.
Qed.

Definition tag_ordMixin := OrdMixin tag_leqP.
Canonical tag_ordType := Eval hnf in OrdType {i : I & T_ i} tag_ordMixin.

End Tagged.

Section EquivQuotOrd.

Local Open Scope quotient_scope.

Variable T : ordType.
Variable e : equiv_rel T.

Definition equivQuotient_ordMixin :=
  CanOrdMixin (@reprK _ [quotType of {eq_quot e}]).
Canonical equivQuotient_ordType :=
  OrdType {eq_quot e} equivQuotient_ordMixin.

End EquivQuotOrd.
