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
  _ : forall s x, supp s :&: free_names x = fset0 -> action s x = x;
  _ : forall n n' x,
        n \in free_names x -> n' \notin free_names x ->
        action (fperm2 n n') x <> x
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

Lemma free_namesP2 n1 n2 x :
  n1 \notin free_names x ->
  n2 \notin free_names x ->
  action (fperm2 n1 n2) x = x.
Proof.
move=> h1 h2; apply/free_namesP; rewrite supp_fperm2 fun_if if_arg fset0I.
case: (_ == _)=> //; apply/eqP; rewrite -fsubset0; apply/fsubsetP=> n.
by case/fsetIP=> [/fset2P []->]; rewrite in_fset0; apply: contraTT.
Qed.

Lemma free_names_min n n' x :
  n \in free_names x -> n' \notin free_names x ->
  action (fperm2 n n') x <> x.
Proof. by case: T n n' x=> [? [? []] ?]. Qed.

Lemma free_names_fin n x (X : {fset name}) :
  (forall n', n' \notin X -> action (fperm2 n n') x != x) ->
  n \in free_names x.
Proof.
move/(_ (fresh (free_names x :|: X)))=> h.
move: (freshP (free_names x :|: X)).
rewrite in_fsetU negb_or=> /andP [P /h {h}].
by apply: contraNT=> Pn; apply/eqP; rewrite free_namesP2.
Qed.

Lemma action1 x : action 1 x = x.
Proof. by apply: free_namesP; rewrite fset0I. Qed.

Lemma actionK s : cancel (@action T s) (@action T s^-1).
Proof. by move=> x; rewrite actionD fperm_mulVs action1. Qed.

Lemma actionKV s : cancel (@action T s^-1) (action s).
Proof. by move=> x; rewrite actionD fperm_mulsV action1. Qed.

Lemma action_inj s : injective (@action T s).
Proof. exact: (can_inj (actionK s)). Qed.

Lemma mem_free_names n x :
  reflect (forall n', action (fperm2 n n') x = x -> n' \in free_names x)
          (n \in free_names x).
Proof.
apply/(iffP idP).
  by move=> n_in n' /eqP; apply: contraTT=> n'_nin; apply/eqP/free_names_min.
by apply; rewrite fperm2xx action1.
Qed.

Lemma eq_in_action s1 s2 x :
  {in free_names x, s1 =1 s2} ->
  action s1 x = action s2 x.
Proof.
move=> e; apply: (canRL (actionKV s2)); rewrite actionD.
apply/free_namesP/eqP; rewrite -fsubset0; apply/fsubsetP=> n.
rewrite in_fsetI mem_supp in_fset0=> /andP [neq is_free].
apply: contraNT neq => _; apply/eqP; rewrite fpermM /= (e _ is_free).
by rewrite fpermK.
Qed.

Lemma free_names_action s x :
  free_names (action s x) = s @: free_names x.
Proof.
apply/(canRL (imfsetK (fpermKV s))); apply/eq_fset=> n.
rewrite (mem_imfset_can _ _ (fpermKV s) (fpermK s)).
apply/(sameP idP)/(iffP idP)=> Pn.
  apply/(@free_names_fin _ _ (free_names x :|: supp s))=> n'.
  rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
  rewrite actionD -n'_fix -fperm2J fperm_mulsKV -actionD.
  by rewrite (inj_eq (@action_inj s)); apply/eqP/free_names_min.
apply/(@free_names_fin _ _ (free_names (action s x) :|: supp s))=> n'.
rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
rewrite -(inj_eq (@action_inj s)) actionD -(fperm_mulsKV s (_ * _)).
by rewrite fperm2J n'_fix -actionD; apply/eqP/free_names_min.
Qed.

End NominalTheory.

Prenex Implicits actionD action1 actionK actionKV action_inj.

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

Lemma name_free_names_min n n' n'' :
  n \in name_free_names n'' -> n' \notin name_free_names n'' ->
  name_action (fperm2 n n') n'' <> n''.
Proof.
rewrite /name_free_names=> /fset1P <- {n''}; rewrite in_fset1=> /eqP.
by rewrite /name_action fperm2E /= eqxx=> e.
Qed.

Definition name_nominalMixin :=
  NominalMixin name_actionD name_free_namesP name_free_names_min.
Canonical name_nominalType := Eval hnf in NominalType name name_nominalMixin.

Lemma actionnE s n : action s n = s n. Proof. by []. Qed.

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

Lemma trivial_free_names_min n n' x :
  n \in trivial_free_names x ->
  n' \notin trivial_free_names x ->
  trivial_action (fperm2 n n') x <> x.
Proof. by rewrite in_fset0. Qed.

End TrivialNominalType.

Notation TrivialNominalMixin T :=
  (NominalMixin (@trivial_actionD [ordType of T])
                (@trivial_free_namesP [ordType of T])
                (@trivial_free_names_min [ordType of T])).

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

Lemma prod_free_names_min n n' p :
  n \in prod_free_names p ->
  n' \notin prod_free_names p ->
  prod_action (fperm2 n n') p <> p.
Proof.
by case: p=> [x y]; rewrite !in_fsetU negb_or /prod_action
  => /orP /= [h_in /andP[h_nin _]|h_in /andP [_ h_nin]] [? ?];
apply: (free_names_min h_in h_nin).
Qed.

Definition prod_nominalMixin :=
  NominalMixin prod_actionD prod_free_namesP prod_free_names_min.
Canonical prod_nominalType :=
  Eval hnf in NominalType (T * S) prod_nominalMixin.

Lemma actionpE s p : action s p = (action s p.1, action s p.2).
Proof. by []. Qed.

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

Lemma seq_free_names_min n n' xs :
  n \in seq_free_names xs ->
  n' \notin seq_free_names xs ->
  seq_action (fperm2 n n') xs <> xs.
Proof.
rewrite /seq_free_names big_tnth => /bigcupP [i _ Pin Pnin].
suff Pnin' : n' \notin free_names (tnth (in_tuple xs) i).
  move=> e; apply: (free_names_min Pin Pnin')=> {Pin Pnin Pnin'}.
  rewrite (tnth_nth (tnth (in_tuple xs) i)) /=.
  by move: i (tnth _ _)=> [i Pi] /= x; rewrite -{2}e {e} (nth_map x).
by apply: contra Pnin; move: n'; apply/fsubsetP/bigcup_sup.
Qed.

Definition seq_nominalMixin :=
  NominalMixin seq_actionD seq_free_namesP seq_free_names_min.
Canonical seq_nominalType := Eval hnf in NominalType (seq T) seq_nominalMixin.

Lemma actionsE s xs : action s xs = [seq action s x | x <- xs].
Proof. by []. Qed.

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

Lemma sum_free_names_min n n' x :
  n \in sum_free_names x ->
  n' \notin sum_free_names x ->
  sum_action (fperm2 n n') x <> x.
Proof. by case: x=> [x|x] /free_names_min Pin /Pin {Pin} e' [e]. Qed.

Definition sum_nominalMixin :=
  NominalMixin sum_actionD sum_free_namesP sum_free_names_min.
Canonical sum_nominalType := Eval hnf in NominalType (T + S) sum_nominalMixin.

End SumNominalType.

Section OptionNominalType.

Implicit Type x : option S.

Definition option_action s x := omap (action s) x.

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

Lemma option_free_names_min n n' x :
  n \in option_free_names x ->
  n' \notin option_free_names x ->
  option_action (fperm2 n n') x <> x.
Proof. by case: x=> [x /free_names_min P /P e [?]|]. Qed.

Definition option_nominalMixin :=
  NominalMixin option_actionD option_free_namesP option_free_names_min.
Canonical option_nominalType :=
  Eval hnf in NominalType (option S) option_nominalMixin.

Lemma actionoE s x : action s x = omap (action s) x.
Proof. by []. Qed.

End OptionNominalType.

Section SetNominalType.

Variable T' : nominalType.

Implicit Type X : {fset T'}.

Definition fset_action s X := action s @: X.

Definition fset_free_names X :=
  \bigcup_(x <- X) free_names x.

Lemma fset_actionD s1 s2 X :
  fset_action s1 (fset_action s2 X) = fset_action (s1 * s2) X.
Proof.
by rewrite /fset_action -imfset_comp; apply/eq_imfset/actionD.
Qed.

Lemma fset_free_namesP s X :
  supp s :&: fset_free_names X = fset0 ->
  fset_action s X = X.
Proof.
move=> h_dis; rewrite -[in RHS](imfset_id X).
apply: eq_in_imfset=> x x_in; apply: free_namesP.
apply/eqP; rewrite -fsubset0 -{}h_dis fsubsetI fsubsetIl /=.
rewrite (fsubset_trans (fsubsetIr _ _)) // /fset_free_names big_tnth.
by move/seq_tnthP: x_in=> [i ->]; apply/bigcup_sup.
Qed.

Lemma fset_free_names_min n n' X :
  n \in fset_free_names X ->
  n' \notin fset_free_names X ->
  fset_action (fperm2 n n') X <> X.
Proof.
move=> n_free n'_fresh eX.
have {n'_fresh} n'_fresh: forall x, x \in X -> n' \notin free_names x.
  move=> x /seq_tnthP [i ->]; apply: contra n'_fresh.
  rewrite /fset_free_names big_tnth /=; move: n' {eX}.
  by apply/fsubsetP/bigcup_sup.
have {n_free} [x x_in n_free]: exists2 x, x \in X & n \in free_names x.
  move: n_free; rewrite /fset_free_names big_tnth /=; move/bigcupP=> [i _ Pi].
  by eexists; eauto; apply/mem_tnth.
move: x_in; rewrite -{}eX; case/imfsetP=> y /n'_fresh {n'_fresh} n'_fresh.
move=> /(canLR (actionK _)); rewrite fperm2V=> Py; move/negP: n'_fresh; apply.
rewrite -{}Py free_names_action (mem_imfset_can _ _ (actionK _) (actionKV _)).
by rewrite fperm2V actionnE fperm2R.
Qed.

Definition fset_nominalMixin :=
  NominalMixin fset_actionD fset_free_namesP fset_free_names_min.
Canonical fset_nominalType :=
  Eval hnf in NominalType {fset T'} fset_nominalMixin.

Lemma free_namesfsE X : free_names X = \bigcup_(x <- X) free_names x.
Proof. by []. Qed.

End SetNominalType.

Section PartMapNominalType.

Implicit Type (m : {partmap T -> S}).

Definition partmap_action s m :=
  mkpartmapfp (fun x => action s (m (action s^-1 x)))
              (action s @: domm m).

Definition partmap_free_names m :=
  free_names (domm m) :|: free_names (domm (invm m)).

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
    rewrite /partmap_free_names free_namesfsE big_tnth; apply/fsubsetU/orP.
    left; exact: bigcup_sup.
  have {m_x} /seq_tnthP [/= i ->]: v \in domm (invm m) by apply/invmP; eauto.
  rewrite /partmap_free_names !free_namesfsE [in X in _ :|: X]big_tnth.
  apply/fsubsetU/orP; right; exact: bigcup_sup.
apply/eq_partmap=> x {h_sub}; rewrite /partmap_action mkpartmapfpE.
rewrite (mem_imfset_can _ _ (actionK s) (actionKV s)).
rewrite mem_domm; case m_sx: (m _)=> [v|] //=.
  move: (dom_const _ _ m_sx); rewrite actionKV=> - [->].
  by rewrite m_sx=> {2}<-.
case m_x: (m x)=> [v|] //=.
move: (dom_const _ _ m_x)=> [hx _].
by rewrite -{}hx actionK m_x in m_sx.
Qed.

Lemma partmap_free_names_min n n' m :
  n \in partmap_free_names m ->
  n' \notin partmap_free_names m ->
  partmap_action (fperm2 n n') m <> m.
Proof.
move=> n_free n'_fresh; apply/eqP; apply: contraNN n'_fresh=> /eqP <-.
case/fsetUP: n_free=> [n_free|n_free]; apply/fsetUP; [left|right].
  rewrite (_ : domm _ = action (fperm2 n n') (domm m)); last first.
    rewrite domm_mkpartmapfp; apply/eq_fset=> x; rewrite in_mkfset.
    rewrite mem_filter (mem_imfset_can _ _ (actionK _) (actionKV _)).
    by rewrite mem_domm; case: (m _).
  rewrite free_names_action (mem_imfset_can _ _ (actionK _) (actionKV _)).
  by rewrite fperm2V actionnE fperm2R.
rewrite (_ : domm _ = action (fperm2 n n') (domm (invm m))); last first.
  apply/eq_fset=> y; rewrite (mem_imfset_can _ _ (actionK _) (actionKV _)).
  apply/(sameP idP)/(iffP idP).
    move/invmP=> [x Px]; apply/invmP; exists (action (fperm2 n n') x).
    rewrite mkpartmapfpE actionK (mem_imfset_inj _ _ (@action_inj _ _)).
    by rewrite mem_domm Px /= actionoE /= actionKV.
  case/invmP=> [x Px]; apply/invmP; exists (action (fperm2 n n') x).
  move: Px; rewrite mkpartmapfpE (mem_imfset_can _ _ (actionK _) (actionKV _)).
  rewrite mem_domm; case e: (m (action _ x))=> [?|] //=; rewrite actionoE /=.
  by move=> [<-]; rewrite -{1}fperm2V e actionK.
rewrite free_names_action (mem_imfset_can _ _ (actionK _) (actionKV _)).
by rewrite fperm2V actionnE fperm2R.
Qed.

Definition partmap_nominalMixin :=
  NominalMixin partmap_actionD partmap_free_namesP partmap_free_names_min.
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

CoInductive partmap_free_names_spec n m : Prop :=
| PMFreeNamesKey k v of m k = Some v & n \in free_names k
| PMFreeNamesVal k v of m k = Some v & n \in free_names v.

Lemma free_namesmP n m :
  reflect (partmap_free_names_spec n m) (n \in free_names m).
Proof.
rewrite /free_names/=/partmap_free_names; apply/(iffP idP).
  case/fsetUP; rewrite !free_namesfsE big_tnth=> /bigcupP [i _].
    move: (mem_tnth i (in_tuple (domm m)))=> /dommP [v Pv].
    by apply: PMFreeNamesKey.
  move: (mem_tnth i (in_tuple (domm (invm m))))=> /invmP [x m_x].
  by apply: PMFreeNamesVal.
case=> [k v m_k n_in|k v m_k n_in]; apply/fsetUP.
  have /(tnthP (in_tuple (domm m))) [i i_in]: k \in domm m.
    by rewrite mem_domm m_k.
  left; rewrite free_namesfsE big_tnth; apply/bigcupP.
  by rewrite {}i_in in n_in; eexists; eauto.
have /(tnthP (in_tuple (domm (invm m)))) [i i_in]: v \in domm (invm m).
  by apply/invmP; eauto.
right; rewrite free_namesfsE big_tnth; apply/bigcupP.
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
