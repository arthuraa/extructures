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
  names : T -> {fset name};
  _ : forall s1 s2 x, action s1 (action s2 x) = action (s1 * s2) x;
  _ : forall n n' x,
        n \notin names x -> n' \notin names x -> action (fperm2 n n') x = x;
  _ : forall n n' x,
        n \in names x -> action (fperm2 n n') x = x -> n' \in names x
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

Definition names (T : nominalType) :=
  Nominal.names (Nominal.class T).

Section NominalTheory.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable T : nominalType.

Implicit Types (s : {fperm name}) (x : T).

Lemma actionD s1 s2 x : action s1 (action s2 x) = action (s1 * s2) x.
Proof. by case: T s1 s2 x=> [? [? []] ?]. Qed.

Lemma namesTeq n n' x :
  n \in names x -> action (fperm2 n n') x = x -> n' \in names x.
Proof. by case: T n n' x=> [? [? []] ?]. Qed.

Lemma namesNNE n n' x :
  n \notin names x -> n' \notin names x ->
  action (fperm2 n n') x = x.
Proof. by case: T n n' x=> [? [? []] ?]. Qed.

Lemma mem_names n x (X : {fset name}) :
  (forall n', n' \notin X -> action (fperm2 n n') x != x) ->
  n \in names x.
Proof.
move/(_ (fresh (names x :|: X)))=> h; move: (freshP (names x :|: X)).
rewrite in_fsetU negb_or=> /andP [P /h {h}].
by apply: contraNT=> Pn; apply/eqP; rewrite namesNNE.
Qed.

Lemma action1 x : action 1 x = x.
Proof. by rewrite -(fperm2xx (fresh (names x))) namesNNE // freshP. Qed.

Lemma actionK s : cancel (@action T s) (@action T s^-1).
Proof. by move=> x; rewrite actionD fperm_mulVs action1. Qed.

Lemma actionKV s : cancel (@action T s^-1) (action s).
Proof. by move=> x; rewrite actionD fperm_mulsV action1. Qed.

Lemma action_inj s : injective (@action T s).
Proof. exact: (can_inj (actionK s)). Qed.

Lemma namesP n x :
  reflect (forall n', action (fperm2 n n') x = x -> n' \in names x)
          (n \in names x).
Proof.
apply/(iffP idP); first by move=> n_in n'; apply namesTeq.
by apply; rewrite fperm2xx action1.
Qed.

Lemma names_disjointE s x : fdisjoint (supp s) (names x) -> action s x = x.
Proof.
elim/fperm2_rect: s=> [|n n' s Pn Pn' IH]; first by rewrite action1.
have [->|neq dis] := altP (n =P n'); first by rewrite fperm2xx fperm_mul1s.
have n_nin: n \notin names x.
  move/fdisjointP: dis; apply; rewrite mem_supp fpermM /= (suppPn _ _ Pn).
  by rewrite fperm2L eq_sym.
have n'_nin := (fdisjointP _ _ dis _ Pn').
have {dis} /IH dis: fdisjoint (supp s) (names x).
  apply/fdisjointP=> n'' Pn''; move/fdisjointP: dis; apply.
  rewrite mem_supp fpermM /=; case: fperm2P; last by rewrite -mem_supp.
    by rewrite -fperm_supp in Pn''; move=> e; rewrite e (negbTE Pn) in Pn''.
  by move=> _; apply: contra Pn=> /eqP ->.
by rewrite -actionD dis namesNNE.
Qed.

Lemma eq_in_action s1 s2 x :
  {in names x, s1 =1 s2} ->
  action s1 x = action s2 x.
Proof.
move=> e; apply: (canRL (actionKV s2)); rewrite actionD.
apply/names_disjointE/fdisjointP=> n; rewrite mem_supp fpermM /=.
by rewrite (can2_eq (fpermKV s2) (fpermK _)); apply/contra=> /e ->.
Qed.

Lemma names_action s x : names (action s x) = s @: names x.
Proof.
apply/(canRL (imfsetK (fpermKV s))); apply/eq_fset=> n.
rewrite (mem_imfset_can _ _ (fpermKV s) (fpermK s)).
apply/(sameP idP)/(iffP idP)=> Pn.
  apply/(@mem_names _ _ (names x :|: supp s))=> n'.
  rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
  rewrite actionD -n'_fix -fperm2J fperm_mulsKV -actionD.
  rewrite (inj_eq (@action_inj s)); apply: contra n'_fresh=> /eqP.
  by apply/namesTeq.
apply/(@mem_names _ _ (names (action s x) :|: supp s))=> n'.
rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
rewrite -(inj_eq (@action_inj s)) actionD -(fperm_mulsKV s (_ * _)).
rewrite fperm2J n'_fix -actionD; apply: contra n'_fresh=> /eqP.
by apply/namesTeq.
Qed.

End NominalTheory.

Prenex Implicits actionD action1 actionK actionKV action_inj.

Section NameNominal.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (s : {fperm name}) (n : name).

Definition name_action s n := s n.

Definition name_names n := fset1 n.

Lemma name_actionD s1 s2 x :
  name_action s1 (name_action s2 x) = name_action (s1 * s2) x.
Proof. by rewrite /name_action /= fpermM. Qed.

Lemma name_namesNNE n n' n'' :
  n \notin name_names n'' -> n' \notin name_names n'' ->
  name_action (fperm2 n n') n'' = n''.
Proof.
by rewrite /name_names /name_action !in_fset1 !(eq_sym _ n''); apply: fperm2D.
Qed.

Lemma name_namesTeq n n' n'' :
  n \in name_names n'' -> name_action (fperm2 n n') n'' = n'' ->
  n' \in name_names n''.
Proof.
rewrite /name_action /name_names=> /fset1P <-{n''}; rewrite in_fset1.
by rewrite fperm2L=> ->.
Qed.

Definition name_nominalMixin :=
  NominalMixin name_actionD name_namesNNE name_namesTeq.
Canonical name_nominalType := Eval hnf in NominalType name name_nominalMixin.

Lemma actionnE s n : action s n = s n. Proof. by []. Qed.

Lemma namesnP n' n : reflect (n' = n) (n' \in names n).
Proof. rewrite in_fset1; exact/eqP. Qed.

End NameNominal.

Section TrivialNominalType.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : ordType).

Implicit Types (s : {fperm name}) (x : T).

Definition trivial_action s x := x.

Definition trivial_names x := fset0 : {fset name}.

Lemma trivial_actionD s1 s2 x :
  trivial_action s1 (trivial_action s2 x) = trivial_action (s1 * s2) x.
Proof. by []. Qed.

Lemma trivial_namesNNE n n' x :
  n \notin trivial_names x -> n' \notin trivial_names x ->
  trivial_action (fperm2 n n') x = x.
Proof. by []. Qed.

Lemma trivial_namesTeq n n' x :
  n \in trivial_names x ->
  trivial_action (fperm2 n n') x = x ->
  n' \in trivial_names x.
Proof. by []. Qed.

End TrivialNominalType.

Notation TrivialNominalMixin T :=
  (NominalMixin (@trivial_actionD [ordType of T])
                (@trivial_namesNNE [ordType of T])
                (@trivial_namesTeq [ordType of T])).

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

Definition prod_names p := names p.1 :|: names p.2.

Lemma prod_actionD s1 s2 p :
  prod_action s1 (prod_action s2 p) = prod_action (s1 * s2) p.
Proof.
by case: p => [x y]; rewrite /prod_action /= !actionD.
Qed.

Lemma prod_namesNNE n n' p :
  n \notin prod_names p -> n' \notin prod_names p ->
  prod_action (fperm2 n n') p = p.
Proof.
by case: p=> x y /=; rewrite /prod_action/prod_names /= 2!in_fsetU 2!negb_or=>
  /andP [??] /andP [??]; rewrite 2?namesNNE.
Qed.

Lemma prod_namesTeq n n' p :
  n \in prod_names p ->
  prod_action (fperm2 n n') p = p ->
  n' \in prod_names p.
Proof.
by case: p=> [x y]; rewrite /prod_names !in_fsetU /prod_action /=
  => /orP /= [h_in|h_in] [??]; apply/orP; [left|right];
eauto using namesTeq.
Qed.

Definition prod_nominalMixin :=
  NominalMixin prod_actionD prod_namesNNE prod_namesTeq.
Canonical prod_nominalType :=
  Eval hnf in NominalType (T * S) prod_nominalMixin.

Lemma actionpE s p : action s p = (action s p.1, action s p.2).
Proof. by []. Qed.

End ProdNominalType.

Section SeqNominalType.

Implicit Type (xs : seq T).

Definition seq_action s xs := map (action s) xs.

Definition seq_names xs := \bigcup_(x <- xs) names x.

Lemma seq_actionD s1 s2 xs :
  seq_action s1 (seq_action s2 xs) = seq_action (s1 * s2) xs.
Proof. by rewrite /seq_action -map_comp (eq_map (@actionD T s1 s2)). Qed.

Lemma seq_namesNNE n n' xs :
  n \notin seq_names xs -> n' \notin seq_names xs ->
  seq_action (fperm2 n n') xs = xs.
Proof.
move=> h1 h2.
have h: forall n x, n \notin seq_names xs -> x \in xs -> n \notin names x.
  move=> {n n' h1 h2} n x Pn /seq_tnthP [i ->]; apply: contra Pn.
  by rewrite /seq_names big_tnth; move: n; apply/fsubsetP/bigcup_sup.
rewrite /seq_action -[in RHS](map_id xs); apply/eq_in_map=> x Px.
by apply namesNNE; eauto.
Qed.

Lemma seq_namesTeq n n' xs :
  n \in seq_names xs ->
  seq_action (fperm2 n n') xs = xs ->
  n' \in seq_names xs.
Proof.
rewrite /seq_names big_tnth => /bigcupP [i _ Pin e].
suff e': action (fperm2 n n') (tnth (in_tuple xs) i) = tnth (in_tuple xs) i.
  by move: {e e'} n' (namesTeq Pin e'); apply/fsubsetP/bigcup_sup.
rewrite (tnth_nth (tnth (in_tuple xs) i)) /=.
by move: {Pin} i (tnth _ _)=> [i Pi] /= x; rewrite -{2}e {e} (nth_map x).
Qed.

Definition seq_nominalMixin :=
  NominalMixin seq_actionD seq_namesNNE seq_namesTeq.
Canonical seq_nominalType := Eval hnf in NominalType (seq T) seq_nominalMixin.

Lemma actionsE s xs : action s xs = [seq action s x | x <- xs].
Proof. by []. Qed.

Lemma namessP n xs :
  reflect (exists2 x, x \in xs & n \in names x) (n \in names xs).
Proof.
rewrite {2}/names/=/seq_names; apply/(iffP idP).
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

Definition sum_names x :=
  match x with
  | inl x => names x
  | inr x => names x
  end.

Lemma sum_actionD s1 s2 x :
  sum_action s1 (sum_action s2 x) = sum_action (s1 * s2) x.
Proof. by case: x=> [x|x] //=; rewrite actionD. Qed.

Lemma sum_namesNNE n n' x :
  n \notin sum_names x -> n' \notin sum_names x ->
  sum_action (fperm2 n n') x = x.
Proof. by case: x=> [x|x] //= => /namesNNE h /h ->. Qed.

Lemma sum_namesTeq n n' x :
  n \in sum_names x ->
  sum_action (fperm2 n n') x = x ->
  n' \in sum_names x.
Proof. by case: x=> [x|x] /namesTeq Pin [/Pin ?]. Qed.

Definition sum_nominalMixin :=
  NominalMixin sum_actionD sum_namesNNE sum_namesTeq.
Canonical sum_nominalType := Eval hnf in NominalType (T + S) sum_nominalMixin.

End SumNominalType.

Section OptionNominalType.

Implicit Type x : option S.

Definition option_action s x := omap (action s) x.

Definition option_names x :=
  match x with
  | Some x => names x
  | None => fset0
  end.

Lemma option_actionD s1 s2 x :
  option_action s1 (option_action s2 x) = option_action (s1 * s2) x.
Proof. by case: x=> [x|] //=; rewrite actionD. Qed.

Lemma option_namesNNE n n' x :
  n \notin option_names x -> n' \notin option_names x ->
  option_action (fperm2 n n') x = x.
Proof. by case: x=> [x|] //= => /namesNNE h /h ->. Qed.

Lemma option_namesTeq n n' x :
  n \in option_names x ->
  option_action (fperm2 n n') x = x ->
  n' \in option_names x.
Proof. by case: x=> [x /namesTeq P [/P e]|]. Qed.

Definition option_nominalMixin :=
  NominalMixin option_actionD option_namesNNE option_namesTeq.
Canonical option_nominalType :=
  Eval hnf in NominalType (option S) option_nominalMixin.

Lemma actionoE s x : action s x = omap (action s) x.
Proof. by []. Qed.

End OptionNominalType.

Section SetNominalType.

Variable T' : nominalType.

Implicit Type X : {fset T'}.

Definition fset_action s X := action s @: X.

Definition fset_names X :=
  \bigcup_(x <- X) names x.

Lemma fset_actionD s1 s2 X :
  fset_action s1 (fset_action s2 X) = fset_action (s1 * s2) X.
Proof.
by rewrite /fset_action -imfset_comp; apply/eq_imfset/actionD.
Qed.

Lemma fset_namesNNE n n' X :
  n \notin fset_names X -> n' \notin fset_names X ->
  fset_action (fperm2 n n') X = X.
Proof.
move=> Pn Pn'; rewrite -[in RHS](imfset_id X).
apply: eq_in_imfset=> x x_in; apply: names_disjointE.
apply/fdisjointP=> n'' /(fsubsetP _ _ (fsubset_supp_fperm2 n n')).
have sub: fsubset (names x) (fset_names X).
  case/seq_tnthP: x_in=> [/= i ->]; rewrite /fset_names big_tnth.
  by apply/bigcup_sup.
by case/fset2P=> ->; [move: Pn|move: Pn']; apply: contra; [move: n|move: n'];
apply/fsubsetP.
Qed.

Lemma fset_namesTeq n n' X :
  n \in fset_names X ->
  fset_action (fperm2 n n') X = X ->
  n' \in fset_names X.
Proof.
rewrite /fset_names /fset_action big_tnth => /bigcupP [i _ Pi] e.
have {i Pi} [x x_in Pn] : exists2 x, x \in X & n \in names x.
  by eexists; eauto; apply: mem_tnth.
move: x_in Pn; rewrite -{1}e => /imfsetP [y Py ->]; rewrite names_action.
rewrite (mem_imfset_can _ _ (fpermK _) (fpermKV _)) fperm2V fperm2L.
by case/seq_tnthP: Py=> {y} [y ->]; move: {e} n'; apply/fsubsetP/bigcup_sup.
Qed.

Definition fset_nominalMixin :=
  NominalMixin fset_actionD fset_namesNNE fset_namesTeq.
Canonical fset_nominalType :=
  Eval hnf in NominalType {fset T'} fset_nominalMixin.

Lemma actionfsE s X : action s X = action s @: X.
Proof. by []. Qed.

Lemma namesfsE X : names X = \bigcup_(x <- X) names x.
Proof. by []. Qed.

Lemma namesfsP n X : reflect (exists2 x, x \in X & n \in names x)
                             (n \in names X).
Proof.
rewrite namesfsE big_tnth; apply/(iffP (bigcupP _ _ _)).
  by move=> [i _ Pi]; eexists; eauto; apply/mem_tnth.
by case=> [x /seq_tnthP [/= i ->]]; eexists; eauto.
Qed.

Lemma namesfsPn n X : reflect (forall x, x \in X -> n \notin names x)
                              (n \notin names X).
Proof.
apply/(iffP idP).
  by move=> Pn x Px; apply: contra Pn=> Pn; apply/namesfsP; eauto.
by move=> P; apply/namesfsP=> - [x /P/negbTE ->].
Qed.

End SetNominalType.

Section PartMapNominalType.

Implicit Type (m : {partmap T -> S}).

Definition partmap_action s m :=
  mkpartmapfp (fun x => action s (m (action s^-1 x)))
              (action s @: domm m).

Definition partmap_names m :=
  names (domm m) :|: names (domm (invm m)).

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
rewrite domm_m1 -imfset_comp (eq_imfset (actionD _ _)).
congr getm; apply/eq_mkpartmapfp=> y; rewrite mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s2) (actionKV s2)) actionD.
rewrite -fperm_inv_mul mem_domm; case e: (m (action _ y)) => [z|] //=.
by rewrite actionD.
Qed.

Lemma partmap_namesNNE n n' m :
  n \notin partmap_names m -> n' \notin partmap_names m ->
  partmap_action (fperm2 n n') m = m.
Proof.
rewrite /partmap_names 2!in_fsetU 2!negb_or
  => /andP[/namesfsPn hn1 /namesfsPn hn2]
     /andP[/namesfsPn hn1' /namesfsPn hn2'].
apply/eq_partmap=> x; rewrite mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK _) (actionKV _)) fperm2V mem_domm.
case e: (m x)=> [y|].
  have x_def: x \in domm m by rewrite mem_domm e.
  rewrite namesNNE; eauto; rewrite e /= actionoE /=.
  have y_def: y \in domm (invm m) by apply/invmP; eauto.
  by rewrite namesNNE; eauto.
case e': (m _)=> [y|] //=.
have x_def: action (fperm2 n n') x \in domm m by rewrite mem_domm e'.
rewrite -(actionK (fperm2 n n') x) fperm2V namesNNE in e; eauto.
by rewrite e in e'.
Qed.

Let partmap_names_dom s m :
  domm (partmap_action s m) = action s @: domm m.
Proof.
apply/eq_fset=> n; rewrite (mem_imfset_can _ _ (actionK _) (actionKV _)).
apply/(sameP (dommP _ _))/(iffP (dommP _ _)).
admit. admit.
Qed.

Let partmap_names_codom s m :
  domm (invm (partmap_action s m)) = action s @: domm (invm m).
Proof.
admit.
Qed.

(*

rewrite actionfsE.  imfsetU; congr fsetU.
  apply/eq_fset=> n''; apply/(sameP (namesfsP _ _)).
  rewrite (mem_imfset_can _ _ (actionK _) (actionKV _)) fperm2V.
  apply/(iffP (namesfsP _ _ )).
    move=> [x /dommP [y Px] Pn'']; exists (action (fperm2 n n') x).
      rewrite mem_domm mkpartmapfpE (mem_imfset_inj _ _ (@action_inj _ _)).
      by rewrite mem_domm Px /= actionK Px.
    rewrite names_action (mem_imfset_can _ _ (actionK _) (actionKV _)).
    by rewrite fperm2V.
*)

Lemma partmap_namesTeq n n' m :
  n \in partmap_names m ->
  partmap_action (fperm2 n n') m = m ->
  n' \in partmap_names m.
Proof.
move=> Pn e.
rewrite -{}e (_ : partmap_names _ = action (fperm2 n n') (partmap_names m)).
  rewrite -{1}(fperm2L n n') -actionnE actionfsE.
  by rewrite (mem_imfset_inj _ _ (@action_inj _ _)).
rewrite /partmap_names actionfsE imfsetU partmap_names_dom names_action.
by rewrite partmap_names_codom names_action.
Qed.

Definition partmap_nominalMixin :=
  NominalMixin partmap_actionD partmap_namesNNE partmap_namesTeq.
Canonical partmap_nominalType :=
  Eval hnf in NominalType {partmap T -> S} partmap_nominalMixin.

Lemma actionmE s m k : action s m k = action s (m (action s^-1 k)).
Proof.
rewrite {1}/action /=/partmap_action mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s) (actionKV s)) mem_domm.
by case: (m (action _ _)).
Qed.

Lemma actionm_set s m k v :
  action s (setm m k v) = setm (action s m) (action s k) (action s v).
Proof.
apply/eq_partmap=> k'; rewrite !actionmE !setmE.
rewrite -{1}(actionK s k) (can_eq (actionKV s)).
have [_{k'}|] //= := altP (k' =P _).
by rewrite actionmE.
Qed.

Lemma actionm_rem s m k :
  action s (remm m k) = remm (action s m) (action s k).
Proof.
apply/eq_partmap=> k'; rewrite !actionmE !remmE.
rewrite -{1}(actionK s k) (can_eq (actionKV s)).
have [_{k'}|] //= := altP (k' =P _).
by rewrite actionmE.
Qed.

CoInductive partmap_names_spec n m : Prop :=
| PMFreeNamesKey k v of m k = Some v & n \in names k
| PMFreeNamesVal k v of m k = Some v & n \in names v.

Lemma namesmP n m :
  reflect (partmap_names_spec n m) (n \in names m).
Proof.
rewrite /names/=/partmap_names; apply/(iffP idP).
  case/fsetUP; rewrite !namesfsE big_tnth=> /bigcupP [i _].
    move: (mem_tnth i (in_tuple (domm m)))=> /dommP [v Pv].
    by apply: PMFreeNamesKey.
  move: (mem_tnth i (in_tuple (domm (invm m))))=> /invmP [x m_x].
  by apply: PMFreeNamesVal.
case=> [k v m_k n_in|k v m_k n_in]; apply/fsetUP.
  have /(tnthP (in_tuple (domm m))) [i i_in]: k \in domm m.
    by rewrite mem_domm m_k.
  left; rewrite namesfsE big_tnth; apply/bigcupP.
  by rewrite {}i_in in n_in; eexists; eauto.
have /(tnthP (in_tuple (domm (invm m)))) [i i_in]: v \in domm (invm m).
  by apply/invmP; eauto.
right; rewrite namesfsE big_tnth; apply/bigcupP.
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

Definition bij_names x := names (f x).

Lemma bij_actionD s1 s2 x :
  bij_action s1 (bij_action s2 x) = bij_action (s1 * s2) x.
Proof. by rewrite /bij_action /= gK actionD. Qed.

Lemma bij_namesNNE n n' x :
  n \notin bij_names x -> n' \notin bij_names x ->
  bij_action (fperm2 n n') x = x.
Proof.
by rewrite /bij_names /bij_action=> ? ?; rewrite namesNNE //.
Qed.

Lemma bij_namesTeq n n' x :
  n \in bij_names x -> bij_action (fperm2 n n') x = x ->
  n' \in bij_names x.
Proof.
rewrite /bij_names /bij_action=> Pn h; apply: namesTeq=> //.
by apply: (canRL gK).
Qed.

Definition BijNominalMixin :=
  NominalMixin bij_actionD bij_namesNNE bij_namesTeq.

End TransferNominalType.
