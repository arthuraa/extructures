Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.fintype.

Require Import MathComp.tuple MathComp.bigop.

Require Import ord fset partmap fperm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive name : Type := Name of nat.

Definition nat_of_name (n : name) := let: Name n := n in n.

Canonical name_newType := Eval hnf in [newType for nat_of_name].
Definition name_eqMixin := [eqMixin of name by <:].
Canonical name_eqType := Eval hnf in EqType name name_eqMixin.
Definition name_partOrdMixin := [partOrdMixin of name by <:].
Canonical name_partOrdType := Eval hnf in PartOrdType name name_partOrdMixin.
Definition name_ordMixin := [ordMixin of name by <:].
Canonical name_ordType := Eval hnf in OrdType name name_ordMixin.

Definition fresh (ns : {fset name}) : name :=
  locked (Name (foldr maxn 0 [seq nat_of_name n | n <- ns]).+1).

Lemma freshP ns : fresh ns \notin ns.
Proof.
suff ub: forall n, n \in ns -> nat_of_name n < nat_of_name (fresh ns).
  by apply/negP=> /ub; rewrite ltnn.
move=> [n] /=; rewrite /fresh; unlock=> /=; rewrite ltnS inE /=.
elim: {ns} (val ns)=> [|[n'] ns IH] //=.
rewrite inE=> /orP [/eqP[<-]{n'} |/IH h]; first exact: leq_maxl.
by rewrite (leq_trans h) // leq_maxr.
Qed.

Module Nominal.

Section ClassDef.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Record mixin_of T := Mixin {
  action : {fperm name} -> T -> T;
  free_names : T -> {fset name};
  _ : forall s1 s2 x, action s1 (action s2 x) = action (s1 * s2) x;
  _ : forall s x, supp s :&: free_names x = fset0 -> action s x = x
}.

Record class_of T := Class {base : Ord.Total.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Ord.Total.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Ord.Total.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition ordType := @Ord.Total.Pack cT class xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Ord.Total.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion ordType : type >-> Ord.Total.type.
Canonical ordType.
Notation nominalType := type.
Notation nominalMixin := mixin_of.
Notation NominalMixin := Mixin.
Notation NominalType T m := (@pack T m _ _ id).
Notation "[ 'nominalType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'nominalType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'nominalType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'nominalType'  'of'  T ]") : form_scope.
End Exports.

End Nominal.
Export Nominal.Exports.

Definition action (T : nominalType) :=
  Nominal.action (Nominal.class T).

Definition free_names (T : nominalType) :=
  Nominal.free_names (Nominal.class T).

Section NominalTheory.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable T : nominalType.

Implicit Types (s : {fperm name}) (x : T).

Lemma actionD s1 s2 x : action s1 (action s2 x) = action (s1 * s2) x.
Proof. by case: T s1 s2 x=> [? [? []] ?]. Qed.

Lemma free_namesP s x : supp s :&: free_names x = fset0 -> action s x = x.
Proof. by case: T s x=> [? [? []] ?]. Qed.

Lemma action1 x : action 1 x = x.
Proof. by apply: free_namesP; rewrite fset0I. Qed.

Lemma actionK s : cancel (@action T s) (@action T s^-1).
Proof. by move=> x; rewrite actionD fperm_mulVs action1. Qed.

Lemma actionKV s : cancel (@action T s^-1) (action s).
Proof. by move=> x; rewrite actionD fperm_mulsV action1. Qed.

End NominalTheory.

Prenex Implicits actionD action1 actionK actionKV.

Section NameNominal.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (s : {fperm name}) (n : name).

Definition name_action s n := s n.

Definition name_free_names n := fset1 n.

Lemma name_actionD s1 s2 x :
  name_action s1 (name_action s2 x) = name_action (s1 * s2) x.
Proof. by rewrite /name_action /= fpermM. Qed.

Lemma name_free_namesP s n :
  supp s :&: name_free_names n = fset0 -> name_action s n = n.
Proof.
rewrite /name_action /name_free_names=> h_dis; apply/suppPn/negP=> hn.
suff: n \in supp s :&: fset1 n by rewrite h_dis in_fset0.
by rewrite in_fsetI hn in_fset1 /=.
Qed.

Definition name_nominalMixin :=
  NominalMixin name_actionD name_free_namesP.
Canonical name_nominalType := Eval hnf in NominalType name name_nominalMixin.

Lemma free_namesnP n' n : reflect (n' = n) (n' \in free_names n).
Proof. rewrite in_fset1; exact/eqP. Qed.

End NameNominal.

Section TrivialNominalType.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : ordType).

Implicit Types (s : {fperm name}) (x : T).

Definition trivial_action s x := x.

Definition trivial_free_names x := fset0 : {fset name}.

Lemma trivial_actionD s1 s2 x :
  trivial_action s1 (trivial_action s2 x) = trivial_action (s1 * s2) x.
Proof. by []. Qed.

Lemma trivial_free_namesP s x :
  supp s :&: trivial_free_names x = fset0 -> trivial_action s x = x.
Proof. by []. Qed.

End TrivialNominalType.

Notation TrivialNominalMixin T :=
  (NominalMixin (@trivial_actionD [ordType of T])
                (@trivial_free_namesP [ordType of T])).

Definition unit_nominalMixin := TrivialNominalMixin unit.
Canonical unit_nominalType := Eval hnf in NominalType unit unit_nominalMixin.

Definition bool_nominalMixin := TrivialNominalMixin bool.
Canonical bool_nominalType := Eval hnf in NominalType bool bool_nominalMixin.

Definition nat_nominalMixin := TrivialNominalMixin nat.
Canonical nat_nominalType := Eval hnf in NominalType nat nat_nominalMixin.

Section Instances.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T S : nominalType).

Implicit Type (s : {fperm name}).

Section ProdNominalType.

Implicit Type (p : T * S).

Definition prod_action s p := (action s p.1, action s p.2).

Definition prod_free_names p := free_names p.1 :|: free_names p.2.

Lemma prod_actionD s1 s2 p :
  prod_action s1 (prod_action s2 p) = prod_action (s1 * s2) p.
Proof.
by case: p => [x y]; rewrite /prod_action /= !actionD.
Qed.

Lemma prod_free_namesP s p :
  supp s :&: prod_free_names p = fset0 -> prod_action s p = p.
Proof.
case: p=> x y; move/eqP.
by rewrite /prod_action/prod_free_names fsetIUr fsetU_eq0 /=
  => /andP [/eqP/free_namesP -> /eqP/free_namesP ->].
Qed.

Definition prod_nominalMixin := NominalMixin prod_actionD prod_free_namesP.
Canonical prod_nominalType :=
  Eval hnf in NominalType (T * S) prod_nominalMixin.

End ProdNominalType.

Section SeqNominalType.

Implicit Type (xs : seq T).

Definition seq_action s xs := map (action s) xs.

Definition seq_free_names xs := \bigcup_(x <- xs) free_names x.

Lemma seq_actionD s1 s2 xs :
  seq_action s1 (seq_action s2 xs) = seq_action (s1 * s2) xs.
Proof. by rewrite /seq_action -map_comp (eq_map (@actionD T s1 s2)). Qed.

Lemma seq_free_namesP s xs :
  supp s :&: seq_free_names xs = fset0 ->
  seq_action s xs = xs.
Proof.
move=> h.
have {h} h: forall x, x \in xs -> supp s :&: free_names x = fset0.
  move=> x x_in_xs; apply/eqP; rewrite -fsubset0 -{}h.
  apply/fsubsetP=> n /fsetIP [n_in_supp n_in_fv]; apply/fsetIP; split=> //.
  rewrite /seq_free_names /=; move: {n_in_supp} n n_in_fv; apply/fsubsetP.
  move: x_in_xs; rewrite -[x \in xs]/(x \in in_tuple xs)=> /tnthP [i ->].
  by rewrite big_tnth; apply: bigcup_sup.
by rewrite /seq_action -[in RHS](map_id xs);
apply/eq_in_map=> x /h/free_namesP.
Qed.

Definition seq_nominalMixin := NominalMixin seq_actionD seq_free_namesP.
Canonical seq_nominalType := Eval hnf in NominalType (seq T) seq_nominalMixin.

Lemma free_namessP n xs :
  reflect (exists2 x, x \in xs & n \in free_names x) (n \in free_names xs).
Proof.
rewrite {2}/free_names/=/seq_free_names; apply/(iffP idP).
  rewrite big_tnth=> /bigcupP [i _]; eexists; eauto.
  exact/mem_tnth.
move=> [x /(tnthP (in_tuple xs)) [i {x}->]].
by rewrite big_tnth; move: n; apply/fsubsetP/bigcup_sup.
Qed.

End SeqNominalType.

Section SumNominalType.

Implicit Types (x y : T + S).

Definition sum_action s x :=
  match x with
  | inl x => inl (action s x)
  | inr x => inr (action s x)
  end.

Definition sum_free_names x :=
  match x with
  | inl x => free_names x
  | inr x => free_names x
  end.

Lemma sum_actionD s1 s2 x :
  sum_action s1 (sum_action s2 x) = sum_action (s1 * s2) x.
Proof. by case: x=> [x|x] //=; rewrite actionD. Qed.

Lemma sum_free_namesP s x :
  supp s :&: sum_free_names x = fset0 ->
  sum_action s x = x.
Proof. by case: x=> [x|x] //= => /free_namesP ->. Qed.

Definition sum_nominalMixin := NominalMixin sum_actionD sum_free_namesP.
Canonical sum_nominalType := Eval hnf in NominalType (T + S) sum_nominalMixin.

End SumNominalType.

Section OptionNominalType.

Implicit Type x : option S.

Definition option_action s x :=
  match x with
  | Some x => Some (action s x)
  | None => None
  end.

Definition option_free_names x :=
  match x with
  | Some x => free_names x
  | None => fset0
  end.

Lemma option_actionD s1 s2 x :
  option_action s1 (option_action s2 x) = option_action (s1 * s2) x.
Proof. by case: x=> [x|] //=; rewrite actionD. Qed.

Lemma option_free_namesP s x :
  supp s :&: option_free_names x = fset0 ->
  option_action s x = x.
Proof. by case: x=> [x|] //= => /free_namesP ->. Qed.

Definition option_nominalMixin :=
  NominalMixin option_actionD option_free_namesP.
Canonical option_nominalType :=
  Eval hnf in NominalType (option S) option_nominalMixin.

End OptionNominalType.

Section PartMapNominalType.

Implicit Type (m : {partmap T -> S}).

Definition partmap_action s m :=
  mkpartmapfp (fun x => action s (m (action s^-1 x)))
              (action s @: domm m).

Definition partmap_free_names m :=
  (\bigcup_(x <- domm m) free_names x)
  :|: \bigcup_(x <- domm (invm m)) free_names x.

Lemma partmap_actionD s1 s2 m :
  partmap_action s1 (partmap_action s2 m) = partmap_action (s1 * s2) m.
Proof.
apply/eq_partmap=> x; rewrite /partmap_action.
set m1 := mkpartmapfp _ (action s2 @: domm m).
have domm_m1: domm m1 = action s2 @: domm m.
  apply/eq_fset=> y; apply/(sameP idP)/(iffP idP).
    case/imfsetP=> [{y} y Py ->]; apply/dommP.
    case/dommP: (Py)=> [v m_y].
    exists (action s2 v); rewrite /m1 mkpartmapfpE (mem_imfset (action s2) Py).
    by rewrite actionK m_y.
  by move/dommP=> [v]; rewrite mkpartmapfpE; case: ifP.
rewrite domm_m1 -imfset_comp (imfset_eq (actionD _ _)).
congr getm; apply/eq_mkpartmapfp=> y; rewrite mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s2) (actionKV s2)) actionD.
rewrite -fperm_inv_mul mem_domm; case e: (m (action _ y)) => [z|] //=.
by rewrite actionD.
Qed.

Lemma partmap_free_namesP s m :
  supp s :&: partmap_free_names m = fset0 ->
  partmap_action s m = m.
Proof.
move=> h_dis.
have {h_dis} h_sub:
  forall ns, fsubset ns (partmap_free_names m) -> supp s :&: ns = fset0.
  move=> ns h; apply/eqP; rewrite -fsubset0 -{}h_dis fsubsetI fsubsetIl /=.
  by rewrite (fsubset_trans (fsubsetIr _ ns)).
have dom_const: forall x v, m x = Some v -> action s x = x /\ action s v = v.
  move=> x v m_x; split; apply: free_namesP; apply: h_sub.
    have {m_x} /seq_tnthP [i ->]: x \in domm m by rewrite mem_domm m_x.
    rewrite /partmap_free_names big_tnth; apply/fsubsetU/orP; left.
    exact: bigcup_sup.
  have {m_x} /seq_tnthP [/= i ->]: v \in domm (invm m) by apply/invmP; eauto.
  rewrite /partmap_free_names [in X in _ :|: X]big_tnth; apply/fsubsetU/orP.
  right; exact: bigcup_sup.
apply/eq_partmap=> x {h_sub}; rewrite /partmap_action mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s) (actionKV s)).
rewrite mem_domm; case m_sx: (m _)=> [v|] //=.
  move: (dom_const _ _ m_sx); rewrite actionKV=> - [->].
  by rewrite m_sx=> {2}<-.
case m_x: (m x)=> [v|] //=.
move: (dom_const _ _ m_x)=> [hx _].
by rewrite -{}hx actionK m_x in m_sx.
Qed.

Definition partmap_nominalMixin :=
  NominalMixin partmap_actionD partmap_free_namesP.
Canonical partmap_nominalType :=
  Eval hnf in NominalType {partmap T -> S} partmap_nominalMixin.

Lemma actionmE s m x : action s m x = action s (m (action s^-1 x)).
Proof.
rewrite {1}/action /=/partmap_action mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s) (actionKV s)) mem_domm.
by case: (m (action _ _)).
Qed.

CoInductive partmap_free_names_spec n m : Prop :=
| PMFreeNamesKey k v of m k = Some v & n \in free_names k
| PMFreeNamesVal k v of m k = Some v & n \in free_names v.

Lemma free_namesmP n m :
  reflect (partmap_free_names_spec n m) (n \in free_names m).
Proof.
rewrite /free_names/=/partmap_free_names; apply/(iffP idP).
  case/fsetUP; rewrite big_tnth=> /bigcupP [i _].
    move: (mem_tnth i (in_tuple (domm m)))=> /dommP [v Pv].
    by apply: PMFreeNamesKey.
  move: (mem_tnth i (in_tuple (domm (invm m))))=> /invmP [x m_x].
  by apply: PMFreeNamesVal.
case=> [k v m_k n_in|k v m_k n_in]; apply/fsetUP.
  have /(tnthP (in_tuple (domm m))) [i i_in]: k \in domm m.
    by rewrite mem_domm m_k.
  left; rewrite big_tnth; apply/bigcupP.
  by rewrite {}i_in in n_in; eexists; eauto.
have /(tnthP (in_tuple (domm (invm m)))) [i i_in]: v \in domm (invm m).
  by apply/invmP; eauto.
right; rewrite big_tnth; apply/bigcupP.
by rewrite {}i_in in n_in; eexists; eauto.
Qed.

End PartMapNominalType.

End Instances.

Section TransferNominalType.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : ordType) (S : nominalType) (f : T -> S) (g : S -> T).

Hypothesis fK : cancel f g.
Hypothesis gK : cancel g f.

Definition bij_action s x := g (action s (f x)).

Definition bij_free_names x := free_names (f x).

Lemma bij_actionD s1 s2 x :
  bij_action s1 (bij_action s2 x) = bij_action (s1 * s2) x.
Proof. by rewrite /bij_action /= gK actionD. Qed.

Lemma bij_free_namesP s x :
  supp s :&: bij_free_names x = fset0 -> bij_action s x = x.
Proof.
by rewrite /bij_free_names /bij_action=> /free_namesP ->; rewrite fK.
Qed.

Definition BijNominalMixin := NominalMixin bij_actionD bij_free_namesP.

End TransferNominalType.
