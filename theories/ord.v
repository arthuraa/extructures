Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Interface of types with an order relation. *)

Delimit Scope ord_scope with ord.

Module Ord.

Module Partial.

Section ClassDef.

Record mixin_of T := Mixin {
  leq : rel T;
  _ : reflexive leq;
  _ : transitive leq;
  _ : antisymmetric leq
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation partOrdType := type.
Notation partOrdMixin := mixin_of.
Notation PartOrdMixin := Mixin.
Notation PartOrdType T m := (@pack T m _ _ id).
Notation "[ 'partOrdType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'partOrdType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'partOrdType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'partOrdType'  'of'  T ]") : form_scope.
End Exports.

End Partial.
Export Partial.Exports.

Definition leq T := Partial.leq (Partial.class T).
Definition lt (T : partOrdType) (x y : T) := leq x y && (x != y).

Notation "x <= y" := (leq x y) : ord_scope.
Notation "x < y" := (lt x y) : ord_scope.
Notation "x <= y <= z" := (leq x y && leq y z) : ord_scope.
Notation "x <= y <  z" := (leq x y && lt  y z) : ord_scope.
Notation "x <  y <= z" := (lt  x y && leq y z) : ord_scope.
Notation "x <  y <  z" := (lt  x y && lt  y z) : ord_scope.

Section PartialTheory.

Local Open Scope ord_scope.

Variable T : partOrdType.
Implicit Types x y : T.

Lemma leqxx : reflexive (@leq T).
Proof. by case: T => ? [? []]. Qed.

Lemma leq_trans : transitive (@leq T).
Proof. by case: T => ? [? []]. Qed.

Lemma anti_leq : antisymmetric (@leq T).
Proof. by case: T => ? [? []]. Qed.

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

End PartialTheory.

Module Total.

Section ClassDef.

Inductive mixin_of (T : partOrdType) := Mixin of total (@leq T).

Record class_of T := Class {
  base : Partial.class_of T;
  mixin : mixin_of (Partial.Pack base T)
}.
Local Coercion base : class_of >-> Partial.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Partial.Pack T b0 T)) :=
  fun b bT & phant_id (Partial.class bT) b =>
  fun m & phant_id m0 m => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition partOrdType := @Partial.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Partial.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion partOrdType : type >-> Partial.type.
Canonical partOrdType.
Notation ordType := type.
Notation ordMixin := mixin_of.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.

End Total.
Export Total.Exports.

Section TotalTheory.

Variable T : ordType.
Implicit Types x y : T.

Local Open Scope ord_scope.

Lemma leq_total : total (@leq T).
Proof. by case: T => [? [? []]]. Qed.

Lemma leqNgt x y : (x <= y) = ~~ (y < x).
Proof.
rewrite /lt.
have [lxy|] := boolP (x <= y).
  have [lyx|gyx] //= := boolP (y <= x).
  rewrite negbK (@anti_leq _ x y) ?eqxx //.
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

End TotalTheory.

End Ord.

Export Ord.Partial.Exports Ord.Total.Exports.

Notation "x <= y" := (Ord.leq x y) : ord_scope.
Notation "x < y" := (Ord.lt x y) : ord_scope.
Notation "x <= y <= z" := (Ord.leq x y && Ord.leq y z) : ord_scope.
Notation "x <= y <  z" := (Ord.leq x y && Ord.lt  y z) : ord_scope.
Notation "x <  y <= z" := (Ord.lt  x y && Ord.leq y z) : ord_scope.
Notation "x <  y <  z" := (Ord.lt  x y && Ord.lt  y z) : ord_scope.

Definition nat_partOrdMixin := PartOrdMixin leqnn leq_trans anti_leq.
Canonical nat_partOrdType := Eval hnf in PartOrdType nat nat_partOrdMixin.
Definition nat_ordMixin := OrdMixin leq_total.
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Section ProdPartOrd.

Variables T S : partOrdType.
Local Open Scope ord_scope.

(* For products, we use lexicographic ordering. *)

Definition prod_leq : rel (T * S) :=
  [rel p1 p2 |
   if p1.1 == p2.1 then p1.2 <= p2.2
   else p1.1 <= p2.1].

Lemma prod_leq_refl : reflexive prod_leq.
Proof. by move=> ?; rewrite /prod_leq /= eqxx Ord.leqxx. Qed.

Lemma prod_leq_trans : transitive prod_leq.
Proof.
move=> p1 p2 p3; rewrite /prod_leq /=.
have [->|H21] := altP (p2.1 =P _).
  have [_|//] := altP (_ =P _).
  by apply Ord.leq_trans.
have [<-|H13] := altP (p1.1 =P _).
  by rewrite (negbTE H21).
have [<-|H23] := altP (_ =P _).
  move=> {H13} l21 l12; rewrite (@Ord.anti_leq _ p1.1 p2.1) ?eqxx // in H21.
  by rewrite l12 l21.
by apply Ord.leq_trans.
Qed.

Lemma anti_prod_leq : antisymmetric prod_leq.
Proof.
move=> [x1 y1] [x2 y2]; rewrite /prod_leq /= eq_sym.
have [-> /Ord.anti_leq -> //|Hne /Ord.anti_leq E] := altP (x2 =P _).
by rewrite E eqxx in Hne.
Qed.

Definition prod_partOrdMixin :=
  PartOrdMixin prod_leq_refl prod_leq_trans anti_prod_leq.
Canonical prod_partOrdType :=
  Eval hnf in PartOrdType (T * S) prod_partOrdMixin.

End ProdPartOrd.

Section ProdOrd.

Variables T S : ordType.
Local Open Scope ord_scope.

Lemma prod_leq_total : total (@Ord.leq [partOrdType of T * S]).
Proof.
move=> p1 p2; rewrite /Ord.leq /= /prod_leq /= eq_sym.
by have [_|Hne] := altP (p2.1 =P _); apply Ord.leq_total.
Qed.

Definition prod_ordMixin := OrdMixin prod_leq_total.
Canonical prod_ordType := Eval hnf in OrdType (T * S) prod_ordMixin.

End ProdOrd.

Section SeqPartOrd.

Variable T : partOrdType.
Local Open Scope ord_scope.

Fixpoint seq_leq (s1 s2 : seq T) :=
  match s1, s2 with
  | x1 :: s1, x2 :: s2 =>
    if x1 == x2 then seq_leq s1 s2 else x1 <= x2
  | [::], _ => true
  | _ :: _, _ => false
  end.

Lemma seq_leq_refl : reflexive seq_leq.
Proof. by elim=> [|x s IH] //=; rewrite eqxx. Qed.

Lemma seq_leq_trans : transitive seq_leq.
Proof.
elim=> [|x1 s1 IH] [|x2 s2] [|x3 s3] //=.
have [->|H21] := altP (_ =P _).
  have [_|//] := altP (_ =P _).
  by apply IH.
have [<-|H13] := altP (_ =P _).
  by rewrite (negbTE H21).
have [<-|H23] := altP (_ =P _).
  move=> l21 l12 {H13}; rewrite (@Ord.anti_leq _ x1 x2) ?eqxx // in H21.
  by rewrite l21 l12.
by apply Ord.leq_trans.
Qed.

Lemma anti_seq_leq : antisymmetric seq_leq.
Proof.
elim=> [|x1 s1 IH] [|x2 s2] //=.
rewrite /= eq_sym.
have [-> /IH -> //|Hne /Ord.anti_leq E] := altP (_ =P _).
by rewrite E eqxx in Hne.
Qed.

Definition seq_partOrdMixin :=
  PartOrdMixin seq_leq_refl seq_leq_trans anti_seq_leq.
Canonical seq_partOrdType :=
  Eval hnf in PartOrdType (seq T) seq_partOrdMixin.

End SeqPartOrd.

Section SeqOrd.

Variable T : ordType.

Lemma seq_leq_total : total (@seq_leq T).
Proof.
elim=> [|x1 s1 IH] [|x2 s2] //=.
rewrite /= eq_sym.
by have [_|Hne] := altP (_ =P _); auto; apply Ord.leq_total.
Qed.

Definition seq_ordMixin := OrdMixin seq_leq_total.
Canonical seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.

End SeqOrd.

Section TransferPartOrdType.

Variables (T : Type) (eT : partOrdType) (f : T -> eT).
Local Open Scope ord_scope.

Local Notation le := (fun x y => f x <= f y).

Lemma inj_ord_refl : reflexive le.
Proof. by move=> x; rewrite /= Ord.leqxx. Qed.

Lemma inj_ord_trans : transitive le.
Proof. by move=> x y z /=; exact: Ord.leq_trans. Qed.

Lemma inj_ord_anti : injective f -> antisymmetric le.
Proof. by move=> f_inj x y /= /Ord.anti_leq /f_inj. Qed.

Definition InjPartOrdMixin f_inj :=
  PartOrdMixin inj_ord_refl inj_ord_trans (inj_ord_anti f_inj).

Definition PcanPartOrdMixin g (fK : pcancel f g) :=
  InjPartOrdMixin (pcan_inj fK).

Definition CanPartOrdMixin g (fK : cancel f g) :=
  InjPartOrdMixin (can_inj fK).

End TransferPartOrdType.

Section SubPartOrdType.

Variables (T : partOrdType) (P : pred T) (sT : subType P).
Local Open Scope ord_scope.

Definition sub_partOrdMixin := @InjPartOrdMixin _ _ (@val T P sT) val_inj.
Canonical sub_partOrdType := Eval hnf in PartOrdType sT sub_partOrdMixin.

Lemma val_pordE (u v : sT) : (val u <= val v) = (u <= v).
Proof. by []. Qed.

End SubPartOrdType.

Notation "[ 'partOrdMixin' 'of' T 'by' <: ]" :=
    (sub_partOrdMixin _ : Ord.Partial.mixin_of T)
  (at level 0, format "[ 'partOrdMixin'  'of'  T  'by'  <: ]") : form_scope.

Section TransferOrdType.

Variables (T : eqType) (eT : ordType) (f : T -> eT).
Local Open Scope ord_scope.

Section Inj.

Hypothesis f_inj : injective f.

Let T_partOrdType := PartOrdType T (InjPartOrdMixin f_inj).

Lemma inj_ord_total : total (@Ord.leq T_partOrdType).
Proof. by move=> x y; exact: Ord.leq_total. Qed.

Definition InjOrdMixin := OrdMixin inj_ord_total.

End Inj.

Definition PcanOrdMixin g (fK : pcancel f g) := InjOrdMixin (pcan_inj fK).

Definition CanOrdMixin g (fK : cancel f g) := InjOrdMixin (can_inj fK).

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
    (sub_ordMixin _ : Ord.Total.mixin_of [partOrdType of T])
  (at level 0, format "[ 'ordMixin'  'of'  T  'by'  <: ]") : form_scope.

Definition ordinal_partOrdMixin n := [partOrdMixin of 'I_n by <:].
Canonical ordinal_partOrdType n :=
  Eval hnf in PartOrdType 'I_n (ordinal_partOrdMixin n).
Definition ordinal_ordMixin n := [ordMixin of 'I_n by <:].
Canonical ordinal_ordType n := Eval hnf in OrdType 'I_n (ordinal_ordMixin n).

Lemma nat_of_boolK : cancel nat_of_bool (eq_op 1).
Proof. by case. Qed.

Definition bool_partOrdMixin := CanPartOrdMixin nat_of_boolK.
Canonical bool_partOrdType := Eval hnf in PartOrdType bool bool_partOrdMixin.
Definition bool_ordMixin := CanOrdMixin nat_of_boolK.
Canonical bool_ordType := Eval hnf in OrdType bool bool_ordMixin.
