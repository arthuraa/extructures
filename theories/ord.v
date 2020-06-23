From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype generic_quotient
  tuple.

From void Require Import void.

From deriving Require base.
From deriving Require Import deriving.

From Coq Require Import ZArith NArith Ascii String.

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
(*         x <  y == strict ordering.                                         *)
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

Declare Scope ord_scope.
Delimit Scope ord_scope with ord.

Module Ord.

Section ClassDef.

Record axioms T (r : rel T) := Ax {
  _ : reflexive r;
  _ : transitive r;
  _ : antisymmetric r;
  _ : total r
}.

Record mixin_of T := Mixin {
  op : rel T;
  _  : axioms op
}.

Record class_of T := Class {base : Choice.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.

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

Definition leq T := op (class T).
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

Export Ord.Exports.

Notation "x <= y" := (Ord.leq x y) : ord_scope.
Notation "x < y" := (Ord.lt x y) : ord_scope.
Notation "x <= y <= z" := (Ord.leq x y && Ord.leq y z) : ord_scope.
Notation "x <= y <  z" := (Ord.leq x y && Ord.lt  y z) : ord_scope.
Notation "x <  y <= z" := (Ord.lt  x y && Ord.leq y z) : ord_scope.
Notation "x <  y <  z" := (Ord.lt  x y && Ord.lt  y z) : ord_scope.

Arguments Ord.leq {_}.
Arguments Ord.lt {_}.

Definition nat_ordMixin :=
  OrdMixin (Ord.Ax leqnn leq_trans anti_leq leq_total).
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Module DerOrdType.

Import base.

Local Notation arg_class := (arg_class Ord.sort).
Local Notation arg_inst := (arg_inst Ord.sort).
Local Notation arity_inst := (arity_inst Ord.sort).
Local Notation sig_inst := (sig_inst Ord.sort).

Section OrdType.

Variable (Σ : sig_inst).
Let F := IndF.functor Σ.
Variable (T : initAlgEqType F).

Definition leq_branch As (cAs : hlist arg_class As) :
  hlist (type_of_arg (T * (T -> bool))) As ->
  hlist (type_of_arg T)                 As ->
  bool :=
  @arity_rec
    _ _ (fun a => hlist (type_of_arg (T * (T -> bool))) a -> hlist (type_of_arg T) a -> bool)
    (fun _ _ => true)
    (fun R As rec x y =>
       if x.(hd) == y.(hd) then rec x.(tl) y.(tl) else (x.(hd) <= y.(hd))%ord)
    (fun   As rec x y =>
       if x.(hd).1 == y.(hd) then rec x.(tl) y.(tl) else x.(hd).2 y.(hd)) As cAs.

Definition leq : T -> T -> bool :=
  rec (fun args1 =>
         case
           (fun args2 =>
              match leq_fin (IndF.constr args2) (IndF.constr args1) with
              | inl e =>
                leq_branch
                  (hnth (sig_inst_class Σ) (IndF.constr args1))
                  (IndF.args args1)
                  (cast (hlist (type_of_arg T) \o @nth_fin _ _) e (IndF.args args2))
              | inr b => ~~ b
              end)).

Lemma leqP : Ord.axioms leq.
Proof.
have anti: antisymmetric leq.
  elim/indP=> [[xi xargs]] y.
  rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
  rewrite /leq !recE -[rec _]/(leq) /= !caseE /=.
  case ie: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e|b].
    case: xi / e {ie} xargs=> xargs _ /=; rewrite leq_finii /= => h.
    congr (Roll (IndF.Cons _))=> /=.
    elim/arity_ind: {yi} (nth_fin yi) / (hnth _ _) xargs yargs h
        => [[] []|R As cAs IH|As cAs IH] //=.
      case=> [x xargs] [y yargs] /=.
      rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH ->|yx] //.
      by move=> /Ord.anti_leq e; rewrite e eqxx in yx.
    case=> [[x xP] xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH ->|yx /xP e] //.
    by rewrite e eqxx in yx.
  case: (leq_fin xi yi) (leq_nat_of_fin xi yi)=> [e|b'].
    by rewrite e leq_finii in ie.
  move=> <- <-.
  have ne: nat_of_fin yi != nat_of_fin xi.
    by apply/eqP=> /nat_of_fin_inj e; rewrite e leq_finii in ie.
    by case: ltngtP ne.
split=> //.
- elim/indP=> [[i args]].
  rewrite /leq recE /= -[rec _]/(leq) caseE leq_finii /=.
  elim/arity_ind: {i} _ / (hnth _ _) args=> [[]|R As cAs IH|As cAs IH] //=.
    by case=> [x args]; rewrite /= eqxx.
  by case=> [[x xP] args] /=; rewrite eqxx.
- move=> y x z; elim/indP: x y z=> [[xi xargs]] y z.
  rewrite -(unrollK y) -(unrollK z).
  move: (unroll y) (unroll z)=> {y z} [yi yargs] [zi zargs].
  rewrite /leq !recE /= -[rec _]/(leq) !caseE /=.
  case: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e _|b] //.
    case: xi / e xargs=> /= xargs.
    case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|b] //.
      case: yi / e xargs yargs => xargs yargs /=.
      elim/arity_ind: {zi} _ / (hnth _ _) xargs yargs zargs => [//|R|] As cAs IH /=.
        case=> [x xargs] [y yargs] [z zargs] /=.
        case: (altP (_ =P _)) => [<-|xy].
          case: ifP=> // /eqP _; exact: IH.
        case: (altP (_ =P _)) => [<-|yz]; first by rewrite (negbTE xy).
        case: (altP (_ =P _)) => [<-|xz]; last exact: Ord.leq_trans.
        move=> c1 c2; suffices e: x = y by rewrite e eqxx in xy.
        by have /andP/Ord.anti_leq := conj c1 c2.
      case=> [[x xP] xargs] [y yargs] [z zargs] /=.
      case: (altP (x =P y))=> [<-|xy].
        case: (altP (x =P z))=> [_|//]; exact: IH.
      case: (altP (x =P z))=> [<-|yz].
        rewrite eq_sym (negbTE xy)=> le1 le2.
        suffices e : x = y by rewrite e eqxx in xy.
        by apply: anti; rewrite le1.
      case: (altP (_ =P _))=> [<-|_] //; exact: xP.
  move=> <- {b} ei.
  case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|_ <-].
    case: yi / e yargs ei=> /= yargs.
    by rewrite leq_nat_of_fin; case: (leq_fin zi xi).
  case: (leq_fin zi xi) (leq_nat_of_fin zi xi)=> [e|_ <-].
    by case: xi / e ei xargs; rewrite -ltnNge => /ltnW ->.
  move: ei; rewrite -!ltnNge; exact: ltn_trans.
- elim/indP=> [[xi xargs]] y.
  rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
  rewrite /leq !recE /= -[rec _]/(leq) !caseE /= (leq_fin_swap xi yi).
  case: (leq_fin yi xi)=> [e|[] //].
  case: xi / e xargs=> /= xargs.
  elim/arity_ind: {yi} _ / (hnth _ _) xargs yargs=> [[] []|R|] //= As cAs IH.
    case=> [x xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP eqP)=> [{y} _|]; first exact: IH.
    by rewrite Ord.leq_total.
  case=> /= [[x xP] xargs] [y yargs] /=.
  by rewrite eq_sym; case: (altP eqP).
Qed.

End OrdType.

End DerOrdType.

Ltac derive_ordMixin T :=
  let sT_ind := eval hnf in [the indType _ of T by @Ind.sort _] in
  match sT_ind with @Ind.Pack ?Σ _ ?cT_ind =>
  let cT_ind := eval red in cT_ind in
  let sT_ind := constr:(@Ind.Pack Σ T cT_ind) in
  let sT_ind := constr:(IndF.initAlgType sT_ind) in
  let sT_eq  := eval hnf in [eqType of T] in
  let bT_eq  := constr:(Equality.class sT_eq) in
  let sΣ     := eval hnf in [the sig_inst Ord.sort of Σ by @sig_inst_sort _ _] in
  let cΣ     := eval hnf in (sig_inst_class sΣ) in
  let cΣ     := eval deriving_compute in cΣ in
  let sΣ     := constr:(@SigInst _ Ord.sort Σ cΣ) in
  let sT_ind_eq := constr:(InitAlgEqType bT_eq (InitAlg.class sT_ind)) in
  let op     := constr:(@DerOrdType.leq sΣ sT_ind_eq) in
  let op     := eval cbv delta [DerOrdType.leq DerOrdType.leq_branch] in op in
  let op     := eval deriving_compute in op in
  let op     := eval simpl in op in
  exact (@OrdMixin _ op (@DerOrdType.leqP sΣ sT_ind_eq))
  end.

Notation "[ 'derive' 'ordMixin' 'for' T ]" :=
  (ltac:(derive_ordMixin T))
  (at level 0) : form_scope.

Section BasicInstances.

Variables T S : ordType.

Definition prod_ordMixin := [derive ordMixin for (T * S)%type].
Canonical prod_ordType := Eval hnf in OrdType (T * S) prod_ordMixin.
Definition sum_ordMixin := [derive ordMixin for (T + S)%type].
Canonical sum_ordType := Eval hnf in OrdType (T + S) sum_ordMixin.
Definition option_ordMixin := [derive ordMixin for option T].
Canonical option_ordType := Eval hnf in OrdType (option T) option_ordMixin.
Definition seq_ordMixin := [derive ordMixin for seq T].
Canonical seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.
Definition void_ordMixin := [derive ordMixin for void].
Canonical void_ordType := Eval hnf in OrdType void void_ordMixin.
Definition comparison_ordMixin := [derive ordMixin for comparison].
Canonical comparison_ordType :=
  Eval hnf in OrdType comparison comparison_ordMixin.
Definition bool_ordMixin := [derive ordMixin for bool].
Canonical bool_ordType := Eval hnf in OrdType bool bool_ordMixin.
Definition unit_ordMixin := [derive ordMixin for unit].
Canonical unit_ordType := Eval hnf in OrdType unit unit_ordMixin.
Definition ascii_ordMixin := [derive ordMixin for ascii].
Canonical ascii_ordType := Eval hnf in OrdType ascii ascii_ordMixin.
Definition string_ordMixin := [derive ordMixin for string].
Canonical string_ordType := Eval hnf in OrdType string string_ordMixin.
(* NB: These instances use a different ordering than the standard numeric one. *)
Definition positive_ordMixin := [derive ordMixin for positive].
Canonical positive_ordType := Eval hnf in OrdType positive positive_ordMixin.
Definition N_ordMixin := [derive ordMixin for N].
Canonical N_ordType := Eval hnf in OrdType N N_ordMixin.
Definition Z_ordMixin := [derive ordMixin for Z].
Canonical Z_ordType := Eval hnf in OrdType Z Z_ordMixin.

End BasicInstances.

Section TransferOrdType.

Variables (T : Type) (eT : ordType) (f : T -> eT).
Local Open Scope ord_scope.

Local Notation le := (fun x y => f x <= f y).

Lemma inj_ordP : injective f -> Ord.axioms le.
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
    (sub_ordMixin _ : Ord.mixin_of T)
  (at level 0, format "[ 'ordMixin'  'of'  T  'by'  <: ]") : form_scope.

Definition sig_ordMixin (T : ordType) (P : pred T) : ordMixin {x | P x} :=
  sub_ordMixin _.
Canonical sig_ordType (T : ordType) (P : pred T) :=
  Eval hnf in OrdType {x | P x} (sig_ordMixin P).

Definition ordinal_ordMixin n := [ordMixin of 'I_n by <:].
Canonical ordinal_ordType n :=
  Eval hnf in OrdType 'I_n (ordinal_ordMixin n).

Section Tagged.

Variables (I : ordType) (T_ : I -> ordType).
Implicit Types u v : {x : I & T_ x}.

Local Open Scope ord_scope.

Definition tag_leq u v :=
  (tag u < tag v) || (tag u == tag v) && (tagged u <= tagged_as u v).

Definition tag_leqP : Ord.axioms tag_leq.
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

Section TreeOrdType.

Variable T : ordType.

Implicit Types t : GenTree.tree T.

Fixpoint tree_leq t1 t2 :=
  match t1, t2 with
  | GenTree.Leaf x1, GenTree.Leaf x2   => (x1 <= x2)%ord
  | GenTree.Leaf x1, _                 => true
  | GenTree.Node n1 s1, GenTree.Leaf _ => false
  | GenTree.Node n1 s1, GenTree.Node n2 s2 =>
    let fix loop s1 s2 {struct s1} :=
      match s1, s2 with
      | [::], _ => true
      | t1 :: s1, [::] => false
      | t1 :: s1, t2 :: s2 =>
        if t1 == t2 then loop s1 s2 else tree_leq t1 t2
      end in
    (n1 < n2) ||
    (n1 == n2) && loop s1 s2
  end.

Lemma tree_leqP : Ord.axioms tree_leq.
Proof.
have anti: antisymmetric tree_leq.
  elim=> [x1|n1 s1 IH] [x2|n2 s2] //= => [/Ord.anti_leq ->|] //.
  have [l21|l12] /= := leqP n2 n1.
    case: eqP=> [->|] //; rewrite eqxx ltnn /= => H.
    rewrite (_ : s1 = s2) //.
    elim: s1 s2 IH H {l21 n1 n2} => [|t1 s1 IH] [|t2 s2] //=.
    case=> anti_t1 {}/IH IH.
    by rewrite [t2 == _]eq_sym; case: eqP=> [-> /IH ->|_ /anti_t1] //.
  by rewrite gtn_eqF //= ltnNge ltnW //=.
split=> //.
- elim=> [x|n s IH] //=; first exact: Ord.leqxx.
  apply/orP; right; rewrite eqxx /=.
  elim: s IH {n}=> /= [|t s IHs [-> /IHs ->]] //.
  by rewrite eqxx.
- elim=> [x2|n2 s2 IH] [x1|n1 s1] [x3|n3 s3] //=.
    exact: Ord.leq_trans.
  case/orP=> [e12|].
    case/orP=> [e23|]; first by rewrite (ltn_trans e12 e23).
    by case/andP=> [/eqP <-]; rewrite e12.
  case/andP=> [/eqP <- e12].
  case/orP=> [->|/andP [-> e23]] //=.
  apply/orP; right.
  elim: s2 s1 s3 IH e12 e23=> [|t2 s2 IH] [|t1 s1] [|t3 s3] //=.
  case=> t2_trans {}/IH IH.
  case: ifPn => [/eqP <-|ne12]; first by case: eqP; eauto.
  case: ifPn => [/eqP <-|ne23]; first by rewrite (negbTE ne12).
  move: ne12 ne23; case: (t1 =P t3) => [<-|]; last by eauto.
  move=> ne _ l12 l21; move: (anti t1 t2) ne; rewrite l12 l21.
  by move=> /(_ erefl) ->; rewrite eqxx.
- elim=> [x1|n1 s1 IH] [x2|n2 s2] //=; first exact: Ord.leq_total.
  case: ltngtP=> //= _.
  elim: s1 s2 IH {n1 n2}=> [|t1 s1 IH] [|t2 s2] //= [total_t1 {}/IH IH].
  by rewrite [t2 == _]eq_sym; case: (t1 =P t2)=> //.
Qed.

Definition tree_ordMixin := OrdMixin tree_leqP.
Canonical tree_ordType := Eval hnf in OrdType (GenTree.tree T) tree_ordMixin.

End TreeOrdType.

Definition tuple_ordMixin (T : ordType) (n : nat) :=
  [ordMixin of n.-tuple T by <:].
Canonical tuple_ordType (T : ordType) (n : nat) :=
  Eval hnf in OrdType (n.-tuple T) (tuple_ordMixin T n).
