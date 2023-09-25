From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype generic_quotient
  tuple.

From deriving Require base.
From deriving Require Import deriving.

From Coq Require Import ZArith NArith Ascii String.
(******************************************************************************)
(*   Class of types with a decidable total order relation.  Its main purpose  *)
(* is to supply an interface for aggregate structures (sets, maps) that       *)
(* support extensional equality and executable operations; accordingly, it    *)
(* sticks to basic constructions and results.                                 *)
(*                                                                            *)
(*       hasOrd T == a structure of a total order relation on T               *)
(*   hasOrd.Build == the constructor of hasOrd                                *)
(*        ordType == a type with a total order relation.                      *)
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
(*           PcanHasOrd fK == the mixin for T, given f : T -> S and g with S  *)
(*                            an ordType and fK : pcancel f g.                *)
(*            CanHasOrd fK == the mixin for T, given f : T -> S and g with S  *)
(*                            an ordType and fK : cancel f g.                 *)
(*            InjHasOrd fI == the mixin for T, given f : T -> S with S        *)
(*                            an ordType and fI : injective f.                *)
(*        [Ord of T by <:] == if T is a subType of S : ordType, this defines  *)
(*                            an order structure on T inherited from S        *)
(*   [derive hasOrd for T] == derive an hasOrd mixin for T automatically,     *)
(*                            assuming that T is an instance of indType       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Interface of types with a total order relation. *)

Declare Scope ord_scope.
Delimit Scope ord_scope with ord.

HB.mixin Record hasOrd T := {
  leq : rel T;
  leqxx : reflexive leq;
  leq_trans : transitive leq;
  anti_leq : antisymmetric leq;
  leq_total : total leq;
}.

Module Ord.

#[short(type="ordType")]
HB.structure Definition Ord := {T of hasOrd T & Choice T}.

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

Lemma eq_leq x y : x = y -> x <= y.
Proof. by move=> ->; rewrite leqxx. Qed.

Lemma ltW (x y : T) : x < y -> x <= y.
Proof. by case/andP. Qed.

Lemma ltxx (x : T) : (x < x) = false.
Proof. by rewrite /lt eqxx andbF. Qed.

Lemma lt_trans : transitive (@lt T).
Proof.
move=> y x z /= /andP [lxy exy] /andP [lyz eyz].
rewrite /lt (@leq_trans _ y) //=.
apply: contra eyz; move=> /eqP exz; move: (@anti_leq _ x y).
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

End Theory.

Module Exports.
HB.reexport.
End Exports.

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

HB.instance Definition _ :=
  hasOrd.Build nat leqnn leq_trans anti_leq leq_total.

Module DerOrdType.

Import base.

Section OrdType.

Variable (T : indChoiceType).
Notation n := (Ind.Def.n T).
Notation D := (Ind.Def.decl T).
Notation arg_class  := (arg_class  Ord.Ord.sort).
Notation arg_inst   := (arg_inst   n Ord.Ord.sort).
Notation arity_inst := (arity_inst n Ord.Ord.sort).
Notation sig_inst   := (sig_inst   n Ord.Ord.sort).
Notation decl_inst  := (decl_inst  n Ord.Ord.sort).
Variable (sT : forall i, sig_class Ord.Ord.sort (D i)).

Import IndF.

Definition leq_branch As (cAs : hlist' arg_class As) :
  hlist' (type_of_arg (T *F (fun i => T i -> bool))) As ->
  hlist' (type_of_arg T)                             As ->
  bool :=
  @arity_rec
    _ _ _
   (fun a => hlist' (type_of_arg (T *F (fun i => T i -> bool))) a ->
             hlist' (type_of_arg T) a ->
             bool)
    (fun _ _ => true)
    (fun R As rec x y =>
       if x.(hd) == y.(hd) then rec x.(tl) y.(tl) else (x.(hd) <= y.(hd))%ord)
    (fun j As rec x y =>
       if x.(hd).1 == y.(hd) then rec x.(tl) y.(tl) else x.(hd).2 y.(hd)) As cAs.

Definition leq : forall i, T i -> T i -> bool :=
  rec  (fun i args1 =>
  case (fun   args2 =>
          match leq_fin (IndF.constr args2) (IndF.constr args1) with
          | inl e =>
            leq_branch
              (hnth (sT i) (IndF.constr args1))
              (IndF.args args1)
              (cast (hlist' (type_of_arg T) \o @nth_fin _ _) e (IndF.args args2))
          | inr b => ~~ b
          end)).

Lemma refl' i : reflexive (@leq i).
Proof.
elim/indP: i / => i [j args].
rewrite /leq recE /= -/leq caseE leq_finii /=.
elim/arity_ind: {j} _ / (hnth _ _) args=> [[]|R As cAs IH|j As cAs IH] //=.
  case=> [x args]; rewrite /= eqxx; exact: IH.
by case=> [[x xP] args] /=; rewrite eqxx; exact: IH.
Qed.

Lemma anti' i : antisymmetric (@leq i).
Proof.
elim/indP: i / => i [xi xargs] y.
rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
rewrite /leq !recE -/leq /= !caseE /=.
case ie: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e|b].
  case: xi / e {ie} xargs=> xargs _ /=; rewrite leq_finii /= => h.
  congr (Roll (IndF.Cons _))=> /=.
  elim/arity_ind: {yi} (nth_fin yi) / (hnth _ _) xargs yargs h
      => [[] []|R As cAs IH|j As cAs IH] //=.
    case=> [x xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH <-|yx] //.
    by move=> /Ord.anti_leq e; rewrite e eqxx in yx.
  case=> [[x xP] xargs] [y yargs] /=.
  rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH <-|yx /xP e] //.
  by rewrite e eqxx in yx.
case: (leq_fin xi yi) (leq_nat_of_fin xi yi)=> [e|b'].
  by rewrite e leq_finii in ie.
move=> <- <-.
have ne: nat_of_fin yi != nat_of_fin xi.
  by apply/eqP=> /nat_of_fin_inj e; rewrite e leq_finii in ie.
  by case: ltngtP ne.
Qed.

Lemma trans' i : transitive (@leq i).
Proof.
move=> y x z; elim/indP: i / x y z => i' [xi xargs] y z.
rewrite -(unrollK y) -(unrollK z).
move: (unroll y) (unroll z)=> {y z} [yi yargs] [zi zargs].
rewrite /leq !recE /= -/leq !caseE /=.
case: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e _|b] //.
  case: xi / e xargs=> /= xargs.
  case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|b] //.
    case: yi / e xargs yargs => xargs yargs /=.
    elim/arity_ind: {zi} _ / (hnth _ _) xargs yargs zargs
                    => [//|R|j] As cAs IH /=.
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
      by apply: anti'; rewrite le1.
    case: (altP (_ =P _))=> [<-|_] //; exact: xP.
move=> <- {b} ei.
case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|_ <-].
  case: yi / e yargs ei=> /= yargs.
  by rewrite leq_nat_of_fin; case: (leq_fin zi xi).
case: (leq_fin zi xi) (leq_nat_of_fin zi xi)=> [e|_ <-].
  by case: xi / e ei xargs; rewrite -ltnNge => /ltnW ->.
move: ei; rewrite -!ltnNge; exact: ltn_trans.
Qed.

Lemma total' i : total (@leq i).
Proof.
elim/indP: i / => i [xi xargs] y.
rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
rewrite /leq !recE /= -/leq !caseE /= (leq_fin_swap xi yi).
case: (leq_fin yi xi)=> [e|[] //].
case: xi / e xargs=> /= xargs.
elim/arity_ind: {yi} _ / (hnth _ _) xargs yargs=> [[] []|R|j] //= As cAs IH.
  case=> [x xargs] [y yargs] /=.
  rewrite eq_sym; case: (altP eqP)=> [{y} _|]; first exact: IH.
  by rewrite Ord.leq_total.
case=> /= [[x xP] xargs] [y yargs] /=.
by rewrite eq_sym; case: (altP eqP)=> ?; [apply: IH|apply: xP].
Qed.

Definition mixin_for i op (p : @leq i = op) :=
  @hasOrd.Build (T i) op
    (cast (@reflexive (T i)) p (@refl' i))
    (cast (@transitive (T i)) p (@trans' i))
    (cast (@antisymmetric (T i)) p (@anti' i))
    (cast (@total (T i)) p (@total' i)).

End OrdType.

Definition pack_for T :=
  [infer indType of T with Ord.Ord.sort as sT n Ts' D cD in
   fun (Ts : lift_class Choice.sort n) =>
   fun & phant_id Ts' (untag_sort Ts) =>
   fun T_choice & phant_id (lift_class_proj Choice.class Ts) T_choice =>
   let T_ind_choice := @IndChoiceType _ _ _ T_choice sT in
   fun cD' & phant_id cD cD' =>
   @mixin_for T_ind_choice cD' (Ind.idx sT)].

End DerOrdType.

Notation "[ 'derive' 'nored' 'hasOrd' 'for' T ]" :=
  (@DerOrdType.pack_for T _ id _ _ _ _ _ _ id _ id _ id _ id _ id _ id _ erefl)
  (at level 0) : form_scope.

Ltac derive_hasOrd T :=
  let pack :=
    constr:(@DerOrdType.pack_for T _ id _ _ _ _ _ _ id _ id _ id _ id _ id _ id) in
  match type of pack with
  | forall op, ?leq = op -> _ =>
    let leq := eval unfold DerOrdType.leq, DerOrdType.leq_branch in leq in
    let leq := eval deriving_compute in leq in
    exact (pack leq erefl : hasOrd T)
  end.

Notation "[ 'derive' 'hasOrd' 'for' T ]" :=
  (ltac:(derive_hasOrd T))
  (at level 0, format "[ 'derive'  'hasOrd'  'for'  T ]") : form_scope.

Ltac derive_lazy_hasOrd T :=
  let pack :=
    constr:(@DerOrdType.pack_for T _ id _ _ _ _ _ _ id _ id _ id _ id _ id _ id) in
  match type of pack with
  | forall op, ?leq = op -> _ =>
    let leq := eval unfold DerOrdType.leq, DerOrdType.leq_branch in leq in
    let leq := eval deriving_lazy in leq in
    exact (pack leq erefl : hasOrd T)
  end.

Notation "[ 'derive' 'lazy' 'hasOrd' 'for' T ]" :=
  (ltac:(derive_hasOrd T))
  (at level 0, format "[ 'derive'  'lazy'  'hasOrd'  'for'  T ]") : form_scope.

#[deprecated(since="extructures 0.4.0",
      note="Use [derive nored hasOrd for _] instead")]
Notation "[ 'derive' 'nored' 'ordMixin' 'for' T ]" :=
  ([derive nored hasOrd for T])
  (at level 0) : form_scope.
#[deprecated(since="extructures 0.4.0",
      note="Use [derive hasOrd for _] instead")]
Notation "[ 'derive' 'ordMixin' 'for' T ]" :=
  ([derive hasOrd for T])
  (at level 0) : form_scope.
#[deprecated(since="extructures 0.4.0",
      note="Use [derive lazy hasOrd for _] instead")]
Notation "[ 'derive' 'lazy' 'ordMixin' 'for' T ]" :=
  ([derive lazy hasOrd for T])
  (at level 0) : form_scope.

Section BasicInstances.

Variables T S : ordType.

Definition prod_hasOrd := [derive hasOrd for (T * S)%type].
HB.instance Definition _ := prod_hasOrd.
Definition sum_hasOrd := [derive hasOrd for (T + S)%type].
HB.instance Definition _ := sum_hasOrd.
Definition option_hasOrd := [derive hasOrd for option T].
HB.instance Definition _ := option_hasOrd.
Definition seq_hasOrd := [derive hasOrd for seq T].
HB.instance Definition _ := seq_hasOrd.
Definition void_hasOrd := [derive hasOrd for void].
HB.instance Definition _ := void_hasOrd.
Definition comparison_hasOrd := [derive hasOrd for comparison].
HB.instance Definition _ := comparison_hasOrd.
Definition bool_hasOrd := [derive hasOrd for bool].
HB.instance Definition _ := bool_hasOrd.
Definition unit_hasOrd := [derive hasOrd for unit].
HB.instance Definition _ := unit_hasOrd.
Definition ascii_hasOrd := [derive hasOrd for ascii].
HB.instance Definition _ := ascii_hasOrd.
Definition string_hasOrd := [derive hasOrd for string].
HB.instance Definition _ := string_hasOrd.
(* NB: These instances use a different ordering than the standard numeric one. *)
Definition positive_hasOrd := [derive hasOrd for positive].
HB.instance Definition _ := positive_hasOrd.
Definition N_hasOrd := [derive hasOrd for N].
HB.instance Definition _ := N_hasOrd.
Definition Z_hasOrd := [derive hasOrd for Z].
HB.instance Definition _ := Z_hasOrd.

End BasicInstances.

Section TransferOrdType.

Variables (T : Type) (eT : ordType) (f : T -> eT).
Local Open Scope ord_scope.

Local Notation le := (fun x y => f x <= f y).

Lemma inj_le_refl : reflexive le.
Proof. by move=> x; rewrite /= Ord.leqxx. Qed.

Lemma inj_le_trans : transitive le.
Proof. by move=> x y z /=; exact: Ord.leq_trans. Qed.

Lemma inj_le_anti : injective f -> antisymmetric le.
Proof. by move=> f_inj x y /= /Ord.anti_leq /f_inj. Qed.

Lemma inj_le_total : total le.
Proof. by move=> x y; exact: Ord.leq_total. Qed.

Definition InjHasOrd (f_inj : injective f) : hasOrd (inj_type f_inj) :=
  hasOrd.Build (inj_type f_inj)
    inj_le_refl inj_le_trans (inj_le_anti f_inj) inj_le_total.

Definition PcanHasOrd g (fK : pcancel f g) : hasOrd (pcan_type fK) :=
  InjHasOrd (pcan_inj fK).

Definition CanHasOrd g (fK : cancel f g) : hasOrd (can_type fK) :=
  InjHasOrd (can_inj fK).

End TransferOrdType.

#[deprecated(since="extructures 0.4.0", note="Use InjHasOrd")]
Notation InjOrdMixin := InjHasOrd.
#[deprecated(since="extructures 0.4.0", note="Use PcanHasOrd")]
Notation PcanOrdMixin := PcanHasOrd.
#[deprecated(since="extructures 0.4.0", note="Use CanHasOrd")]
Notation CanOrdMixin := CanHasOrd.

(* FIXME: This is not generating an instance for inj_type... *)
HB.instance Definition _ (T : choiceType) (S : ordType) (f : T -> S)
  (f_inj : injective f) : hasOrd (inj_type f_inj) :=
  InjHasOrd f_inj.
HB.instance Definition _ (T : choiceType) (S : ordType) (f : T -> S) g
  (fK : pcancel f g) :=
  PcanHasOrd fK.
HB.instance Definition _ (T : choiceType) (S : ordType) (f : T -> S) g
  (fK : cancel f g) :=
  CanHasOrd fK.
HB.instance Definition _ (S : ordType) (P : pred S) (T : subType P) : hasOrd (sub_type T) :=
  PcanHasOrd (@valK _ _ T).

Notation "[ 'Ord' 'of' T 'by' <: ]" := (Ord.Ord.copy T%type (sub_type T%type))
  (at level 0, format "[ 'Ord'  'of'  T  'by'  <: ]") : form_scope.
#[deprecated(since="extructures 0.4.0", note="Use [Ord of _ by <:] instead")]
Notation "[ 'ordMixin' 'of' T 'by' <: ]" := [Ord of T by <:]
  (at level 0, format "[ 'ordMixin'  'of'  T  'by'  <: ]") : form_scope.

(* FIXME: Why is this generating an instance of eqtype? *)
HB.instance Definition _ (T : ordType) (P : pred T) :=
  [Ord of {x | P x} by <:].
HB.instance Definition _ (n : nat) :=
  [Ord of 'I_n by <:].

Section Tagged.

Variables (I : ordType) (T_ : I -> ordType).
Implicit Types u v : {x : I & T_ x}.

Local Open Scope ord_scope.

Definition tag_leq u v :=
  (tag u < tag v) || (tag u == tag v) && (tagged u <= tagged_as u v).

Lemma tag_leq_refl : reflexive tag_leq.
Proof.
rewrite /tag_leq.
by move=> [i x] /=; rewrite Ord.ltxx eqxx tagged_asE Ord.leqxx.
Qed.

Lemma tag_leq_trans : transitive tag_leq.
Proof.
rewrite /tag_leq.
move=> [i2 x2] [i1 x1] [i3 x3] /=.
case: Ord.ltgtP x2=> [i1i2 x2 _|?|<- {i2} x2] //=.
  case: Ord.ltgtP x3=> [i2i3 x3 _|?|<- {i3} x3] //=; last by rewrite i1i2.
  by rewrite (Ord.lt_trans i1i2 i2i3).
case: Ord.ltgtP x3=> //= <- {i3} x3; rewrite !tagged_asE.
exact: Ord.leq_trans.
Qed.

Lemma tag_leq_anti : antisymmetric tag_leq.
Proof.
rewrite /tag_leq.
move=> [i1 x1] [i2 x2] /=; rewrite [i2 == i1]eq_sym.
case: Ord.ltgtP x2=> //= i1i2; rewrite -{}i1i2 {i2} => x2.
by rewrite !tagged_asE => /Ord.anti_leq ->.
Qed.

Lemma tag_leq_total : total tag_leq.
Proof.
rewrite /tag_leq.
move=> [i1 x1] [i2 x2] /=; rewrite [i2 == i1]eq_sym.
by case: Ord.ltgtP x2 => //= <- {i2} x2; rewrite !tagged_asE Ord.leq_total.
Qed.

HB.instance Definition _ :=
  hasOrd.Build {i : I & T_ i} tag_leq_refl tag_leq_trans
               tag_leq_anti tag_leq_total.

End Tagged.

Section EquivQuotOrd.

Local Open Scope quotient_scope.

Variable T : ordType.
Variable e : equiv_rel T.

HB.instance Definition _ :=
  Ord.Ord.copy {eq_quot e} (can_type (@reprK _ {eq_quot e})).

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

Lemma tree_leq_anti : antisymmetric tree_leq.
Proof.
elim=> [x1|n1 s1 IH] [x2|n2 s2] //= => [/Ord.anti_leq ->|] //.
have [l21|l12] /= := leqP n2 n1.
  case: eqP=> [->|] //; rewrite eqxx ltnn /= => H.
  rewrite (_ : s1 = s2) //.
  elim: s1 s2 IH H {l21 n1 n2} => [|t1 s1 IH] [|t2 s2] //=.
  case=> anti_t1 {}/IH IH.
  by rewrite [t2 == _]eq_sym; case: eqP=> [-> /IH ->|_ /anti_t1] //.
by rewrite gtn_eqF //= ltnNge ltnW //=.
Qed.

Lemma tree_leq_refl : reflexive tree_leq.
Proof.
elim=> [x|n s IH] //=; first exact: Ord.leqxx.
apply/orP; right; rewrite eqxx /=.
elim: s IH {n}=> /= [|t s IHs [-> /IHs ->]] //.
by rewrite eqxx.
Qed.

Lemma tree_leq_trans : transitive tree_leq.
Proof.
elim=> [x2|n2 s2 IH] [x1|n1 s1] [x3|n3 s3] //=.
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
move=> ne _ l12 l21; move: (@tree_leq_anti t1 t2) ne; rewrite l12 l21.
by move=> /(_ erefl) ->; rewrite eqxx.
Qed.

Lemma tree_leq_total : total tree_leq.
Proof.
elim=> [x1|n1 s1 IH] [x2|n2 s2] //=; first exact: Ord.leq_total.
case: ltngtP=> //= _.
elim: s1 s2 IH {n1 n2}=> [|t1 s1 IH] [|t2 s2] //= [total_t1 {}/IH IH].
by rewrite [t2 == _]eq_sym; case: (t1 =P t2)=> //.
Qed.

HB.instance Definition _ :=
  hasOrd.Build (GenTree.tree T) tree_leq_refl tree_leq_trans
               tree_leq_anti tree_leq_total.
End TreeOrdType.

HB.instance Definition _ (T : ordType) (n : nat) :=
  Ord.Ord.copy (n.-tuple T) (sub_type (n.-tuple T)).
