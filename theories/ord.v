Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Interface of types with a total order. *)

Delimit Scope ord_scope with ord.

Module Ord.

Section ClassDef.

Definition axioms T (r : rel T) :=
  [/\ reflexive r ,
      transitive r ,
      antisymmetric r &
      total r ].

Structure mixin_of T := Mixin {
  ord_op : rel T;
  _ : axioms ord_op
}.

Structure class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b  => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation OrdMixin := Mixin.
Notation ordType := type.
Notation OrdType T m := (@pack T m _ _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0) : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0) : form_scope.
End Exports.

Section Projections.

Variable (T : ordType).

Definition leq := Ord.ord_op (Ord.mixin (Ord.class T)).

Lemma leqxx : reflexive leq.
Proof. by rewrite /leq; case: T => ? [] ? [] ? []. Qed.

Lemma leq_trans : transitive leq.
Proof. by rewrite /leq; case: T => ? [] ? [] ? []. Qed.

Lemma anti_leq : antisymmetric leq.
Proof. by rewrite /leq; case: T => ? [] ? [] ? []. Qed.

Lemma leq_total : total leq.
Proof. by rewrite /leq; case: T => ? [] ? [] ? []. Qed.

End Projections.

Local Notation "x <= y" := (leq x y) : ord_scope.
Local Notation "x < y" := (~~ (leq y x)) : ord_scope.
Local Notation "x <= y <= z" := (leq x y && leq y z) : ord_scope.

Section Theory.

Local Open Scope ord_scope.

Variable (T : ordType).

Lemma eq_leq (x y : T) : x = y -> x <= y.
Proof. by move=> ->; rewrite leqxx. Qed.

Lemma ltW (x y : T) : x < y -> x <= y.
Proof. by move=> x_y; move: (leq_total y x); rewrite (negbTE x_y). Qed.

Lemma ltxx (x : T) : (x < x) = false.
Proof. by rewrite leqxx. Qed.

Lemma lt_trans : transitive [rel x y : T | x < y].
Proof.
move=> y x z /= /ltW x_y; apply: contra=> z_x.
exact: leq_trans z_x x_y.
Qed.

Lemma eq_op_leq (x y : T) : (x == y) = (x <= y <= x).
Proof.
apply/(sameP idP)/(iffP idP); first by move=> /anti_leq ->.
by move=> /eqP ->; rewrite leqxx.
Qed.

Lemma leq_eqVlt (x y : T) : (x <= y) = (x == y) || (x < y).
Proof.
apply/(sameP idP)/(iffP idP).
  case/orP=> [/eqP ->|]; first by rewrite leqxx.
  by apply/implyP; rewrite implyNb leq_total.
apply/implyP.
rewrite implybE orbA orbC orbA -negb_and -implybE.
by apply/implyP=> /anti_leq ->.
Qed.

Lemma lt_neqAle (x y : T) : (x < y) = (x != y) && (x <= y).
Proof. by rewrite leq_eqVlt negb_or negbK eq_sym. Qed.

CoInductive compare_ord (x y : T) : bool -> bool -> bool -> Set :=
| CompareOrdLt of x < y : compare_ord x y true false false
| CompareOrdGt of y < x : compare_ord x y false true false
| CompareOrdEq of x = y : compare_ord x y false false true.

Lemma ltgtP x y : compare_ord x y (x < y) (y < x) (x == y).
Proof.
rewrite lt_neqAle.
have [<- {y}|Hne] //= := altP (_ =P _).
  by rewrite leqxx; constructor.
have [Hl|Hg] := boolP (x <= y); constructor=> //.
by rewrite lt_neqAle Hne Hl.
Qed.

End Theory.

End Ord.

Export Ord.Exports.

Notation "x <= y" := (Ord.leq x y) : ord_scope.
Notation "x < y" := (~~ (Ord.leq y x)) : ord_scope.
Notation "x <= y <= z" := (Ord.leq x y && Ord.leq y z) : ord_scope.

Lemma nat_ordP : Ord.axioms leq.
Proof. exact: And4 leqnn leq_trans anti_leq leq_total. Qed.

Definition nat_ordMixin := OrdMixin nat_ordP.
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Section ProdOrd.

Variables T S : ordType.
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
  by rewrite Ord.leq_eqVlt (negbTE H21) /= => /negbTE ->.
by apply Ord.leq_trans.
Qed.

Lemma anti_prod_leq : antisymmetric prod_leq.
Proof.
move=> [x1 y1] [x2 y2]; rewrite /prod_leq /= eq_sym.
have [-> /Ord.anti_leq -> //|Hne /Ord.anti_leq E] := altP (x2 =P _).
by rewrite E eqxx in Hne.
Qed.

Lemma prod_leq_total : total prod_leq.
Proof.
move=> p1 p2; rewrite /prod_leq /= eq_sym.
by have [_|Hne] := altP (p2.1 =P _); apply Ord.leq_total.
Qed.

Definition prod_ordMixin := OrdMixin (And4 prod_leq_refl prod_leq_trans
                                           anti_prod_leq prod_leq_total).
Canonical prod_ordType := Eval hnf in OrdType (T * S) prod_ordMixin.

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
  by rewrite Ord.leq_eqVlt (negbTE H21) /= => /negbTE ->.
by apply Ord.leq_trans.
Qed.

Lemma anti_seq_leq : antisymmetric seq_leq.
Proof.
elim=> [|x1 s1 IH] [|x2 s2] //=.
rewrite /= eq_sym.
have [-> /IH -> //|Hne /Ord.anti_leq E] := altP (_ =P _).
by rewrite E eqxx in Hne.
Qed.

Lemma seq_leq_total : total seq_leq.
Proof.
elim=> [|x1 s1 IH] [|x2 s2] //=.
rewrite /= eq_sym.
by have [_|Hne] := altP (_ =P _); auto; apply Ord.leq_total.
Qed.

Definition seq_ordMixin := OrdMixin (And4 seq_leq_refl seq_leq_trans
                                          anti_seq_leq seq_leq_total).
Canonical seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.

End SeqOrd.

Section TransferOrdType.

Variables (T : Type) (eT : ordType) (f : T -> eT).
Local Open Scope ord_scope.

Lemma inj_ordAxiom : injective f -> Ord.axioms (fun x y => f x <= f y).
Proof.
move=> f_inj.
split.
- move=> *; exact: Ord.leqxx.
- move=> x y z /=; exact: Ord.leq_trans.
- by move=> x y /= /Ord.anti_leq; auto.
move=> x y /=; exact: Ord.leq_total.
Qed.

Definition InjOrdMixin f_inj := OrdMixin (inj_ordAxiom f_inj).

Definition PcanEqMixin g (fK : pcancel f g) := InjOrdMixin (pcan_inj fK).

Definition CanEqMixin g (fK : cancel f g) := InjOrdMixin (can_inj fK).

End TransferOrdType.

Section SubOrdType.

Variables (T : ordType) (P : pred T) (sT : subType P).
Local Open Scope ord_scope.

Local Notation ev_ax := (fun T v => @Ord.axioms T (fun x y => v x <= v y)).
Lemma val_ordP : ev_ax sT val. Proof. exact: inj_ordAxiom val_inj. Qed.

Definition sub_ordMixin := OrdMixin val_ordP.
Canonical sub_ordType := Eval hnf in OrdType sT sub_ordMixin.

Lemma val_ordE (u v : sT) : (val u <= val v) = (u <= v).
Proof. by []. Qed.

End SubOrdType.

Notation "[ 'ordMixin' 'of' T 'by' <: ]" :=
    (sub_ordMixin _ : Ord.mixin_of T)
  (at level 0, format "[ 'ordMixin'  'of'  T  'by'  <: ]") : form_scope.

Definition ordinal_ordMixin n := [ordMixin of 'I_n by <:].
Canonical ordinal_ordType n := Eval hnf in OrdType 'I_n (ordinal_ordMixin n).
