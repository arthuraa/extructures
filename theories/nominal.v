Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.tuple MathComp.bigop MathComp.generic_quotient.

Require Import ord fset partmap fperm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive name : Type := Name of nat.

Definition nat_of_name (n : name) := let: Name n := n in n.

Canonical name_newType := Eval hnf in [newType for nat_of_name].
Definition name_eqMixin := [eqMixin of name by <:].
Canonical name_eqType := Eval hnf in EqType name name_eqMixin.
Definition name_choiceMixin := [choiceMixin of name by <:].
Canonical name_choiceType := Eval hnf in ChoiceType name name_choiceMixin.
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
  rename : {fperm name} -> T -> T;
  names : T -> {fset name};
  _ : forall s1 s2 x, rename s1 (rename s2 x) = rename (s1 * s2) x;
  _ : forall n n' x,
        n \notin names x -> n' \notin names x -> rename (fperm2 n n') x = x;
  _ : forall n n' x,
        n \in names x -> rename (fperm2 n n') x = x -> n' \in names x
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
Definition choiceType := @Choice.Pack cT xclass xT.
Definition partOrdType := @Ord.Partial.Pack cT xclass xT.
Definition ordType := @Ord.Total.Pack cT class xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Ord.Total.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion partOrdType : type >-> Ord.Partial.type.
Canonical partOrdType.
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

Definition rename (T : nominalType) :=
  Nominal.rename (Nominal.class T).

Definition names (T : nominalType) :=
  Nominal.names (Nominal.class T).

Section NominalTheory.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Section Basics.

Variable T : nominalType.

Implicit Types (s : {fperm name}) (x : T).

Lemma renameD s1 s2 x : rename s1 (rename s2 x) = rename (s1 * s2) x.
Proof. by case: T s1 s2 x=> [? [? []] ?]. Qed.

Lemma namesTeq n n' x :
  n \in names x -> rename (fperm2 n n') x = x -> n' \in names x.
Proof. by case: T n n' x=> [? [? []] ?]. Qed.

Lemma namesNNE n n' x :
  n \notin names x -> n' \notin names x ->
  rename (fperm2 n n') x = x.
Proof. by case: T n n' x=> [? [? []] ?]. Qed.

Lemma mem_names n x (X : {fset name}) :
  (forall n', n' \notin X -> rename (fperm2 n n') x != x) ->
  n \in names x.
Proof.
move/(_ (fresh (names x :|: X)))=> h; move: (freshP (names x :|: X)).
rewrite in_fsetU negb_or=> /andP [P /h {h}].
by apply: contraNT=> Pn; apply/eqP; rewrite namesNNE.
Qed.

Lemma rename1 x : rename 1 x = x.
Proof. by rewrite -(fperm2xx (fresh (names x))) namesNNE // freshP. Qed.

Lemma renameK s : cancel (@rename T s) (@rename T s^-1).
Proof. by move=> x; rewrite renameD fperm_mulVs rename1. Qed.

Lemma renameKV s : cancel (@rename T s^-1) (rename s).
Proof. by move=> x; rewrite renameD fperm_mulsV rename1. Qed.

Lemma rename_inj s : injective (@rename T s).
Proof. exact: (can_inj (renameK s)). Qed.

Lemma namesP n x :
  reflect (forall n', rename (fperm2 n n') x = x -> n' \in names x)
          (n \in names x).
Proof.
apply/(iffP idP); first by move=> n_in n'; apply namesTeq.
by apply; rewrite fperm2xx rename1.
Qed.

Lemma names_disjointE s x : fdisjoint (supp s) (names x) -> rename s x = x.
Proof.
elim/fperm2_rect: s=> [|n n' s Pn Pn' IH]; first by rewrite rename1.
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
by rewrite -renameD dis namesNNE.
Qed.

Lemma eq_in_rename s1 s2 x :
  {in names x, s1 =1 s2} ->
  rename s1 x = rename s2 x.
Proof.
move=> e; apply: (canRL (renameKV s2)); rewrite renameD.
apply/names_disjointE/fdisjointP=> n; rewrite mem_supp fpermM /=.
by rewrite (can2_eq (fpermKV s2) (fpermK _)); apply/contra=> /e ->.
Qed.

Lemma names_rename s x : names (rename s x) = s @: names x.
Proof.
apply/(canRL (imfsetK (fpermKV s))); apply/eq_fset=> n.
rewrite (mem_imfset_can _ _ (fpermKV s) (fpermK s)).
apply/(sameP idP)/(iffP idP)=> Pn.
  apply/(@mem_names _ _ (names x :|: supp s))=> n'.
  rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
  rewrite renameD -n'_fix -fperm2J fperm_mulsKV -renameD.
  rewrite (inj_eq (@rename_inj s)); apply: contra n'_fresh=> /eqP.
  by apply/namesTeq.
apply/(@mem_names _ _ (names (rename s x) :|: supp s))=> n'.
rewrite in_fsetU negb_or=> /andP [n'_fresh /suppPn n'_fix].
rewrite -(inj_eq (@rename_inj s)) renameD -(fperm_mulsKV s (_ * _)).
rewrite fperm2J n'_fix -renameD; apply: contra n'_fresh=> /eqP.
by apply/namesTeq.
Qed.

End Basics.

Section Equivariance.

Variables T S : nominalType.

Definition equivariant (f : T -> S) :=
  forall s x, rename s (f x) = f (rename s x).

Lemma equivariant_names f :
  equivariant f ->
  forall x, fsubset (names (f x)) (names x).
Proof.
move=> equi x; apply/fsubsetP=> n Pn.
apply: (@mem_names _ _ _ (names (f x))) => n'; apply: contra=> /eqP ex.
by rewrite -ex -equi names_rename -{1}(@fperm2L _ n n') mem_imfset.
Qed.

Definition finsupp (ns : {fset name}) (f : T -> S) :=
  forall (s : {fperm name}),
    fdisjoint (supp s) ns ->
    forall x, rename s (f (rename s^-1 x)) = f x.

Lemma finsuppS ns ns' f :
  finsupp ns f ->
  fsubset ns ns' ->
  finsupp ns' f.
Proof.
move=> supp_f sub s dis; apply: supp_f; move: dis.
by rewrite 2!(fdisjointC (supp s)); apply/fdisjoint_trans.
Qed.

Lemma names_finsupp ns f x :
  finsupp ns f ->
  fsubset (names (f x)) (ns :|: names x).
Proof.
move=> fs_f; apply/fsubsetP=> n; rewrite in_fsetU=> n_in_fx.
have [|n_nin_ns] //= := boolP (n \in ns).
apply: (@mem_names _ _ _ (ns :|: names (f x)))=> n'.
rewrite in_fsetU=> /norP [n'_nin_ns n'_nin_fx].
set s := fperm2 n n'.
have: rename s (f x) != f x.
  apply: contra n'_nin_fx=> /eqP <-; rewrite names_rename.
  by rewrite (mem_imfset_can _ _ (fpermK _) (fpermKV _)) fperm2V fperm2R.
apply: contra=> /eqP {2}<-.
have dis: fdisjoint (supp s) ns.
  rewrite (fdisjoint_trans (fsubset_supp_fperm2 _ _)) //.
  by apply/fdisjointP=> n'' /fset2P [->|->] {n''} //.
by rewrite -{1}(renameK s x) (fs_f _ dis).
Qed.

End Equivariance.

Section Composition.

Variables (T S R : nominalType).

Lemma finsupp_comp ns ns' (f : T -> S) (g : S -> T) :
  finsupp ns f -> finsupp ns' g -> finsupp (ns :|: ns') (g \o f).
Proof.
move=> fs_f fs_g s dis x /=.
have {dis} /andP [dis1 dis2]:
  fdisjoint (supp s) ns && fdisjoint (supp s) ns'.
  by move: dis; rewrite /fdisjoint fsetIUr fsetU_eq0.
by rewrite -[f _](renameK s) (fs_f _ dis1) (fs_g _ dis2).
Qed.

End Composition.

End NominalTheory.

Prenex Implicits renameD rename1 renameK renameKV rename_inj.

Section NameNominal.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (s : {fperm name}) (n : name).

Definition name_rename s n := s n.

Definition name_names n := fset1 n.

Lemma name_renameD s1 s2 x :
  name_rename s1 (name_rename s2 x) = name_rename (s1 * s2) x.
Proof. by rewrite /name_rename /= fpermM. Qed.

Lemma name_namesNNE n n' n'' :
  n \notin name_names n'' -> n' \notin name_names n'' ->
  name_rename (fperm2 n n') n'' = n''.
Proof.
by rewrite /name_names /name_rename !in_fset1 !(eq_sym _ n''); apply: fperm2D.
Qed.

Lemma name_namesTeq n n' n'' :
  n \in name_names n'' -> name_rename (fperm2 n n') n'' = n'' ->
  n' \in name_names n''.
Proof.
rewrite /name_rename /name_names=> /fset1P <-{n''}; rewrite in_fset1.
by rewrite fperm2L=> ->.
Qed.

Definition name_nominalMixin :=
  NominalMixin name_renameD name_namesNNE name_namesTeq.
Canonical name_nominalType := Eval hnf in NominalType name name_nominalMixin.

Lemma renamenE s n : rename s n = s n. Proof. by []. Qed.

Lemma namesnP n' n : reflect (n' = n) (n' \in names n).
Proof. rewrite in_fset1; exact/eqP. Qed.

End NameNominal.

Section TrivialNominalType.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : ordType).

Implicit Types (s : {fperm name}) (x : T).

Definition trivial_rename s x := x.

Definition trivial_names x := fset0 : {fset name}.

Lemma trivial_renameD s1 s2 x :
  trivial_rename s1 (trivial_rename s2 x) = trivial_rename (s1 * s2) x.
Proof. by []. Qed.

Lemma trivial_namesNNE n n' x :
  n \notin trivial_names x -> n' \notin trivial_names x ->
  trivial_rename (fperm2 n n') x = x.
Proof. by []. Qed.

Lemma trivial_namesTeq n n' x :
  n \in trivial_names x ->
  trivial_rename (fperm2 n n') x = x ->
  n' \in trivial_names x.
Proof. by []. Qed.

End TrivialNominalType.

Notation TrivialNominalMixin T :=
  (NominalMixin (@trivial_renameD [ordType of T])
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

Variables T' S' : nominalType.
Implicit Type (p : T' * S').

Definition prod_rename s p := (rename s p.1, rename s p.2).

Definition prod_names p := names p.1 :|: names p.2.

Lemma prod_renameD s1 s2 p :
  prod_rename s1 (prod_rename s2 p) = prod_rename (s1 * s2) p.
Proof.
by case: p => [x y]; rewrite /prod_rename /= !renameD.
Qed.

Lemma prod_namesNNE n n' p :
  n \notin prod_names p -> n' \notin prod_names p ->
  prod_rename (fperm2 n n') p = p.
Proof.
by case: p=> x y /=; rewrite /prod_rename/prod_names /= 2!in_fsetU 2!negb_or=>
  /andP [??] /andP [??]; rewrite 2?namesNNE.
Qed.

Lemma prod_namesTeq n n' p :
  n \in prod_names p ->
  prod_rename (fperm2 n n') p = p ->
  n' \in prod_names p.
Proof.
by case: p=> [x y]; rewrite /prod_names !in_fsetU /prod_rename /=
  => /orP /= [h_in|h_in] [??]; apply/orP; [left|right];
eauto using namesTeq.
Qed.

Definition prod_nominalMixin :=
  NominalMixin prod_renameD prod_namesNNE prod_namesTeq.
Canonical prod_nominalType :=
  Eval hnf in NominalType (T' * S') prod_nominalMixin.

Lemma renamepE s p : rename s p = (rename s p.1, rename s p.2).
Proof. by []. Qed.

End ProdNominalType.

Section SeqNominalType.

Variable T' : nominalType.
Implicit Type (xs : seq T').

Definition seq_rename s xs := map (rename s) xs.

Definition seq_names xs := \bigcup_(x <- xs) names x.

Lemma seq_renameD s1 s2 xs :
  seq_rename s1 (seq_rename s2 xs) = seq_rename (s1 * s2) xs.
Proof. by rewrite /seq_rename -map_comp (eq_map (@renameD T' s1 s2)). Qed.

Lemma seq_namesNNE n n' xs :
  n \notin seq_names xs -> n' \notin seq_names xs ->
  seq_rename (fperm2 n n') xs = xs.
Proof.
move=> h1 h2.
have h: forall n x, n \notin seq_names xs -> x \in xs -> n \notin names x.
  move=> {n n' h1 h2} n x Pn /seq_tnthP [i ->]; apply: contra Pn.
  by rewrite /seq_names big_tnth; move: n; apply/fsubsetP/bigcup_sup.
rewrite /seq_rename -[in RHS](map_id xs); apply/eq_in_map=> x Px.
by apply namesNNE; eauto.
Qed.

Lemma seq_namesTeq n n' xs :
  n \in seq_names xs ->
  seq_rename (fperm2 n n') xs = xs ->
  n' \in seq_names xs.
Proof.
rewrite /seq_names big_tnth => /bigcup_finP [i _ Pin e].
suff e': rename (fperm2 n n') (tnth (in_tuple xs) i) = tnth (in_tuple xs) i.
  by move: {e e'} n' (namesTeq Pin e'); apply/fsubsetP/bigcup_sup.
rewrite (tnth_nth (tnth (in_tuple xs) i)) /=.
by move: {Pin} i (tnth _ _)=> [i Pi] /= x; rewrite -{2}e {e} (nth_map x).
Qed.

Definition seq_nominalMixin :=
  NominalMixin seq_renameD seq_namesNNE seq_namesTeq.
Canonical seq_nominalType := Eval hnf in NominalType (seq T') seq_nominalMixin.

Lemma renamesE s xs : rename s xs = [seq rename s x | x <- xs].
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

Definition sum_rename s x :=
  match x with
  | inl x => inl (rename s x)
  | inr x => inr (rename s x)
  end.

Definition sum_names x :=
  match x with
  | inl x => names x
  | inr x => names x
  end.

Lemma sum_renameD s1 s2 x :
  sum_rename s1 (sum_rename s2 x) = sum_rename (s1 * s2) x.
Proof. by case: x=> [x|x] //=; rewrite renameD. Qed.

Lemma sum_namesNNE n n' x :
  n \notin sum_names x -> n' \notin sum_names x ->
  sum_rename (fperm2 n n') x = x.
Proof. by case: x=> [x|x] //= => /namesNNE h /h ->. Qed.

Lemma sum_namesTeq n n' x :
  n \in sum_names x ->
  sum_rename (fperm2 n n') x = x ->
  n' \in sum_names x.
Proof. by case: x=> [x|x] /namesTeq Pin [/Pin ?]. Qed.

Definition sum_nominalMixin :=
  NominalMixin sum_renameD sum_namesNNE sum_namesTeq.
Canonical sum_nominalType := Eval hnf in NominalType (T + S) sum_nominalMixin.

End SumNominalType.

Section OptionNominalType.

Implicit Type x : option S.

Definition option_rename s x := omap (rename s) x.

Definition option_names x :=
  match x with
  | Some x => names x
  | None => fset0
  end.

Lemma option_renameD s1 s2 x :
  option_rename s1 (option_rename s2 x) = option_rename (s1 * s2) x.
Proof. by case: x=> [x|] //=; rewrite renameD. Qed.

Lemma option_namesNNE n n' x :
  n \notin option_names x -> n' \notin option_names x ->
  option_rename (fperm2 n n') x = x.
Proof. by case: x=> [x|] //= => /namesNNE h /h ->. Qed.

Lemma option_namesTeq n n' x :
  n \in option_names x ->
  option_rename (fperm2 n n') x = x ->
  n' \in option_names x.
Proof. by case: x=> [x /namesTeq P [/P e]|]. Qed.

Definition option_nominalMixin :=
  NominalMixin option_renameD option_namesNNE option_namesTeq.
Canonical option_nominalType :=
  Eval hnf in NominalType (option S) option_nominalMixin.

Lemma renameoE s x : rename s x = omap (rename s) x.
Proof. by []. Qed.

End OptionNominalType.

Section SetNominalType.

Variable T' : nominalType.

Implicit Type X : {fset T'}.

Definition fset_rename s X := rename s @: X.

Definition fset_names X :=
  \bigcup_(x <- X) names x.

Lemma fset_renameD s1 s2 X :
  fset_rename s1 (fset_rename s2 X) = fset_rename (s1 * s2) X.
Proof.
by rewrite /fset_rename -imfset_comp; apply/eq_imfset/renameD.
Qed.

Lemma fset_namesNNE n n' X :
  n \notin fset_names X -> n' \notin fset_names X ->
  fset_rename (fperm2 n n') X = X.
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
  fset_rename (fperm2 n n') X = X ->
  n' \in fset_names X.
Proof.
rewrite /fset_names /fset_rename big_tnth => /bigcup_finP [i _ Pi] e.
have {i Pi} [x x_in Pn] : exists2 x, x \in X & n \in names x.
  by eexists; eauto; apply: mem_tnth.
move: x_in Pn; rewrite -{1}e => /imfsetP [y Py ->]; rewrite names_rename.
rewrite (mem_imfset_can _ _ (fpermK _) (fpermKV _)) fperm2V fperm2L.
by case/seq_tnthP: Py=> {y} [y ->]; move: {e} n'; apply/fsubsetP/bigcup_sup.
Qed.

Definition fset_nominalMixin :=
  NominalMixin fset_renameD fset_namesNNE fset_namesTeq.
Canonical fset_nominalType :=
  Eval hnf in NominalType {fset T'} fset_nominalMixin.

Lemma renamefsE s X : rename s X = rename s @: X.
Proof. by []. Qed.

Lemma namesfsE X : names X = \bigcup_(x <- X) names x.
Proof. by []. Qed.

Lemma namesfsP n X : reflect (exists2 x, x \in X & n \in names x)
                             (n \in names X).
Proof.
rewrite namesfsE big_tnth; apply/(iffP (bigcup_finP _ _ _)).
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

Lemma namesfsU X Y : names (X :|: Y) = names X :|: names Y.
Proof. by rewrite namesfsE bigcup_fsetU. Qed.

Lemma namesfs_subset X Y :
  fsubset X Y ->
  fsubset (names X) (names Y).
Proof. by move=> /eqP <-; rewrite namesfsU /fsubset fsetUA fsetUid. Qed.

End SetNominalType.

Section PartMapNominalType.

Implicit Type (m : {partmap T -> S}).

Definition partmap_rename s m :=
  mkpartmapfp (fun x => rename s (m (rename s^-1 x)))
              (rename s @: domm m).

Definition partmap_names m :=
  names (domm m) :|: names (codomm m).

Lemma partmap_renameD s1 s2 m :
  partmap_rename s1 (partmap_rename s2 m) = partmap_rename (s1 * s2) m.
Proof.
apply/eq_partmap=> x; rewrite /partmap_rename.
set m1 := mkpartmapfp _ (rename s2 @: domm m).
have domm_m1: domm m1 = rename s2 @: domm m.
  apply/eq_fset=> y; apply/(sameP idP)/(iffP idP).
    case/imfsetP=> [{y} y Py ->]; apply/dommP.
    case/dommP: (Py)=> [v m_y].
    exists (rename s2 v); rewrite /m1 mkpartmapfpE (mem_imfset (rename s2) Py).
    by rewrite renameK m_y.
  by move/dommP=> [v]; rewrite mkpartmapfpE; case: ifP.
rewrite domm_m1 -imfset_comp (eq_imfset (renameD _ _)).
congr getm; apply/eq_mkpartmapfp=> y; rewrite mkpartmapfpE.
rewrite (mem_imfset_can _ _ (renameK s2) (renameKV s2)) renameD.
rewrite -fperm_inv_mul mem_domm; case e: (m (rename _ y)) => [z|] //=.
by rewrite renameD.
Qed.

Lemma partmap_namesNNE n n' m :
  n \notin partmap_names m -> n' \notin partmap_names m ->
  partmap_rename (fperm2 n n') m = m.
Proof.
rewrite /partmap_names 2!in_fsetU 2!negb_or
  => /andP[/namesfsPn hn1 /namesfsPn hn2]
     /andP[/namesfsPn hn1' /namesfsPn hn2'].
apply/eq_partmap=> x; rewrite mkpartmapfpE.
rewrite (mem_imfset_can _ _ (renameK _) (renameKV _)) fperm2V mem_domm.
case e: (m x)=> [y|].
  have x_def: x \in domm m by rewrite mem_domm e.
  rewrite namesNNE; eauto; rewrite e /= renameoE /=.
  have y_def: y \in domm (invm m) by apply/codommP; eauto.
  by rewrite namesNNE; eauto.
case e': (m _)=> [y|] //=.
have x_def: rename (fperm2 n n') x \in domm m by rewrite mem_domm e'.
rewrite -(renameK (fperm2 n n') x) fperm2V namesNNE in e; eauto.
by rewrite e in e'.
Qed.

Let partmap_names_dom s m :
  domm (partmap_rename s m) = rename s @: domm m.
Proof.
apply/eq_fset=> x; rewrite (mem_imfset_can _ _ (renameK _) (renameKV _)).
apply/(sameP (dommP _ _))/(iffP (dommP _ _)).
  move=> [y Py]; exists (rename s y); rewrite mkpartmapfpE.
  by rewrite (mem_imfset_can _ _ (renameK _) (renameKV _)) mem_domm Py /=.
case=> [y]; rewrite mkpartmapfpE (mem_imfset_can _ _ (renameK _) (renameKV _)).
rewrite mem_domm renameoE; case e: (m (rename s^-1 x))=> [y'|] //=.
by move=> [e']; exists (rename s^-1 y); rewrite -e' renameK.
Qed.

Let partmap_names_codom s m :
  codomm (partmap_rename s m) = rename s @: codomm m.
Proof.
apply/eq_fset=> y; rewrite (mem_imfset_can _ _ (renameK _) (renameKV _)).
apply/(sameP (codommP _ _))/(iffP (codommP _ _)).
  move=> [x Px]; exists (rename s x); rewrite mkpartmapfpE.
  rewrite (mem_imfset_inj _ _ (@rename_inj _ _)) mem_domm Px /= renameK Px.
  by rewrite renameoE /= renameKV.
case=> [x]; rewrite mkpartmapfpE (mem_imfset_can _ _ (renameK _) (renameKV _)).
rewrite mem_domm renameoE; case e: (m (rename s^-1 x))=> [x'|] //=.
by move=> [e']; exists (rename s^-1 x); rewrite -e' renameK.
Qed.

Lemma partmap_namesTeq n n' m :
  n \in partmap_names m ->
  partmap_rename (fperm2 n n') m = m ->
  n' \in partmap_names m.
Proof.
move=> Pn e.
rewrite -{}e (_ : partmap_names _ = rename (fperm2 n n') (partmap_names m)).
  rewrite -{1}(fperm2L n n') -renamenE renamefsE.
  by rewrite (mem_imfset_inj _ _ (@rename_inj _ _)).
rewrite /partmap_names renamefsE imfsetU partmap_names_dom names_rename.
by rewrite partmap_names_codom names_rename.
Qed.

Definition partmap_nominalMixin :=
  NominalMixin partmap_renameD partmap_namesNNE partmap_namesTeq.
Canonical partmap_nominalType :=
  Eval hnf in NominalType {partmap T -> S} partmap_nominalMixin.

Lemma namesmE m : names m = names (domm m) :|: names (codomm m).
Proof. by []. Qed.

Lemma renamemE s m k : rename s m k = rename s (m (rename s^-1 k)).
Proof.
rewrite {1}/rename /=/partmap_rename mkpartmapfpE.
rewrite (mem_imfset_can _ _ (renameK s) (renameKV s)) mem_domm.
by case: (m (rename _ _)).
Qed.

Lemma renamem_set s m k v :
  rename s (setm m k v) = setm (rename s m) (rename s k) (rename s v).
Proof.
apply/eq_partmap=> k'; rewrite !renamemE !setmE.
rewrite -{1}(renameK s k) (can_eq (renameKV s)).
have [_{k'}|] //= := altP (k' =P _).
by rewrite renamemE.
Qed.

Lemma renamem_rem s m k :
  rename s (remm m k) = remm (rename s m) (rename s k).
Proof.
apply/eq_partmap=> k'; rewrite !renamemE !remmE.
rewrite -{1}(renameK s k) (can_eq (renameKV s)).
have [_{k'}|] //= := altP (k' =P _).
by rewrite renamemE.
Qed.

Lemma renamem_filter s p m :
  rename s (filterm p m) =
  filterm (fun k v => p (rename s^-1 k) (rename s^-1 v)) (rename s m).
Proof.
apply/eq_partmap=> k; rewrite renamemE 2!filtermE renamemE.
case: (m _)=> [v|] //=.
by rewrite renameK; have [|] := boolP (p _ _).
Qed.

Lemma renamem_union s m1 m2 :
  rename s (unionm m1 m2) = unionm (rename s m1) (rename s m2).
Proof.
apply/eq_partmap=> k; rewrite renamemE 2!unionmE 2!renamemE.
by rewrite [in LHS]fun_if; case: (m1 _).
Qed.

Lemma renamem_mkpartmap s kvs :
  rename s (mkpartmap kvs) =
  mkpartmap (rename s kvs) :> {partmap T -> S}.
Proof.
by elim: kvs=> [|[k v] kvs IH] //=; rewrite renamem_set IH.
Qed.

Lemma renamem_mkpartmapf s f ks :
  rename s (mkpartmapf f ks) =
  mkpartmapf (fun k => rename s (f (rename s^-1 k))) (rename s ks).
Proof.
apply/eq_partmap=> k; rewrite renamemE 2!mkpartmapfE.
rewrite [in LHS]fun_if (_ : (rename s^-1 k \in ks) = (k \in rename s ks)) //.
rewrite -[in RHS](renameKV s k) mem_map //.
exact: @rename_inj.
Qed.

Lemma renamem_dom m s :
  rename s (domm m) = domm (rename s m).
Proof.
apply/esym/eq_fset=> k; apply/(sameP idP)/(iffP idP).
  rewrite renamefsE=> /imfsetP [{k} k Pk ->].
  move/dommP: Pk=> [v Pv]; apply/dommP; exists (rename s v).
  by rewrite renamemE renameK Pv.
move=> /dommP [v]; rewrite renamemE renamefsE=> Pv.
apply/imfsetP; exists (rename s^-1 k); last by rewrite renameKV.
apply/dommP; exists (rename s^-1 v).
by move: Pv; case: (m _)=> // v' [<-]; rewrite renameK.
Qed.

CoInductive partmap_names_spec n m : Prop :=
| PMFreeNamesKey k v of m k = Some v & n \in names k
| PMFreeNamesVal k v of m k = Some v & n \in names v.

Lemma namesmP n m :
  reflect (partmap_names_spec n m) (n \in names m).
Proof.
rewrite /names/=/partmap_names; apply/(iffP idP).
  case/fsetUP; rewrite !namesfsE big_tnth=> /bigcup_finP [i _].
    move: (mem_tnth i (in_tuple (domm m)))=> /dommP [v Pv].
    by apply: PMFreeNamesKey.
  move: (mem_tnth i (in_tuple (domm (invm m))))=> /codommP [x m_x].
  by apply: PMFreeNamesVal.
case=> [k v m_k n_in|k v m_k n_in]; apply/fsetUP.
  have /(tnthP (in_tuple (domm m))) [i i_in]: k \in domm m.
    by rewrite mem_domm m_k.
  left; rewrite namesfsE big_tnth; apply/bigcupP.
  by rewrite {}i_in in n_in; eexists; eauto.
have /(tnthP (in_tuple (domm (invm m)))) [i i_in]: v \in domm (invm m).
  by apply/codommP; eauto.
right; rewrite namesfsE big_tnth; apply/bigcupP.
by rewrite {}i_in in n_in; eexists; eauto.
Qed.

(* FIXME: Use equivariant_names for these results *)
Lemma namesm_set m k v :
  fsubset (names (setm m k v)) (names m :|: names k :|: names v).
Proof.
apply/fsubsetP=> n; case/namesmP=> [k' v'|k' v']; rewrite setmE;
have [Pk'|Pk'] := altP eqP; try subst k'.
- by move=> _; rewrite !in_fsetU=> ->; rewrite orbT.
- move=> get_k' Pn; rewrite 2!in_fsetU (_ : n \in names m) //.
  by apply/namesmP; eapply PMFreeNamesKey; eauto.
- by move=> [<-]; rewrite 2!in_fsetU=> ->; rewrite orbT.
move=> get_k' Pn; rewrite 2!in_fsetU (_ : n \in names m) //.
by apply/namesmP; eapply PMFreeNamesVal; eauto.
Qed.

Lemma namesm_union m1 m2 :
  fsubset (names (unionm m1 m2)) (names m1 :|: names m2).
Proof.
apply/fsubsetP=> n; case/namesmP=> [k v|k v]; rewrite unionmE;
case get_k: (m1 k)=> [v'|] //=.
- move=> _ Pn; apply/fsetUP; left; apply/namesmP.
  by eapply PMFreeNamesKey; eauto.
- move=> get_k' Pn; apply/fsetUP; right; apply/namesmP.
  by eapply PMFreeNamesKey; eauto.
- move=> [<-] Pn; apply/fsetUP; left; apply/namesmP.
  by eapply PMFreeNamesVal; eauto.
move=> get_k' Pn; apply/fsetUP; right; apply/namesmP.
by eapply PMFreeNamesVal; eauto.
Qed.

Lemma namesm_unionl m1 m2 : fsubset (names m1) (names (unionm m1 m2)).
Proof.
apply/fsubsetP=> n; case/namesmP=> [k v|k v] get_k Pn;
apply/namesmP; have get_k' : unionm m1 m2 k = Some v by rewrite unionmE get_k.
  by eapply PMFreeNamesKey; eauto.
by eapply PMFreeNamesVal; eauto.
Qed.

Lemma namesm_union_disjoint m1 m2 :
  fdisjoint (domm m1) (domm m2) ->
  names (unionm m1 m2) = names m1 :|: names m2.
Proof.
move=> /fdisjointP dis; apply/eqP; rewrite eqEfsubset namesm_union /=.
apply/fsubsetP=> n /fsetUP []; case/namesmP=> [k v|k v] get_k Pn.
- apply/namesmP; eapply PMFreeNamesKey; eauto.
  by rewrite unionmE get_k.
- have {get_k} get_k: unionm m1 m2 k = Some v by rewrite unionmE get_k.
  by apply/namesmP; eapply PMFreeNamesVal; eauto.
- case get_k': (m1 k) => [v'|] //=.
    have: k \in domm m1 by rewrite mem_domm get_k'.
    by move=> /dis; rewrite mem_domm get_k.
  have {get_k} get_k: unionm m1 m2 k = Some v by rewrite unionmE get_k'.
  by apply/namesmP; eapply PMFreeNamesKey; eauto.
case get_k': (m1 k) => [v'|] //=.
  have: k \in domm m1 by rewrite mem_domm get_k'.
  by move=> /dis; rewrite mem_domm get_k.
have {get_k} get_k: unionm m1 m2 k = Some v by rewrite unionmE get_k'.
by apply/namesmP; eapply PMFreeNamesVal; eauto.
Qed.

Lemma namesm_filter p m :
  fsubset (names (filterm p m)) (names m).
Proof.
apply/fsubsetP=> n; case/namesmP=> [k v|k v];
rewrite filtermE; case get_k: (m k)=> [v'|] //=;
case: p=> //= - [?] Pn; subst v'; apply/namesmP.
  by eapply PMFreeNamesKey; eauto.
by eapply PMFreeNamesVal; eauto.
Qed.

End PartMapNominalType.

End Instances.

Section TransferNominalType.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : ordType) (S : nominalType) (f : T -> S) (g : S -> T).

Hypothesis fK : cancel f g.
Hypothesis gK : cancel g f.

Definition bij_rename s x := g (rename s (f x)).

Definition bij_names x := names (f x).

Lemma bij_renameD s1 s2 x :
  bij_rename s1 (bij_rename s2 x) = bij_rename (s1 * s2) x.
Proof. by rewrite /bij_rename /= gK renameD. Qed.

Lemma bij_namesNNE n n' x :
  n \notin bij_names x -> n' \notin bij_names x ->
  bij_rename (fperm2 n n') x = x.
Proof.
by rewrite /bij_names /bij_rename=> ? ?; rewrite namesNNE //.
Qed.

Lemma bij_namesTeq n n' x :
  n \in bij_names x -> bij_rename (fperm2 n n') x = x ->
  n' \in bij_names x.
Proof.
rewrite /bij_names /bij_rename=> Pn h; apply: namesTeq=> //.
by apply: (canRL gK).
Qed.

Definition BijNominalMixin :=
  NominalMixin bij_renameD bij_namesNNE bij_namesTeq.

End TransferNominalType.

Module Binding.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Section Def.

Variable T : nominalType.
Implicit Types (x y : {fset name} * T).

Definition bound_eq x y :=
  [&& x.1 :&: names x.2 == y.1 :&: names y.2 &
      has (fun s => [&& fdisjoint (supp s) (x.1 :&: names x.2) &
                         rename s x.2 == y.2])
          (enum_fperm (names x.2 :|: names y.2))].

Lemma bound_eqP x y :
  reflect (x.1 :&: names x.2 = y.1 :&: names y.2 /\
           exists2 s, fdisjoint (supp s) (x.1 :&: names x.2) &
                       rename s x.2 = y.2)
          (bound_eq x y).
Proof.
apply/(iffP idP).
  case/andP=> [/eqP eq_supp /hasP [s s_in /andP [dis /eqP e]]].
  by split=> //; eauto.
case=> [eq_supp [s dis e]]; rewrite /bound_eq {1}eq_supp eqxx /=.
apply/hasP.
have inj: {in names x.2 &, injective s} by move=> ????; apply: fperm_inj.
exists (fperm_gen inj).
  by rewrite -enum_fpermE -e names_rename supp_fperm_gen.
apply/andP; split.
  move: dis; rewrite 2![fdisjoint _ (x.1 :&: _)]fdisjointC.
  move=> /fdisjointP dis; apply/fdisjointP=> n n_in.
  move: (dis _ n_in); rewrite 2!mem_suppN=> /eqP {2}<-; apply/eqP.
  by apply/fperm_genE; case/fsetIP: n_in.
by rewrite -e; apply/eqP/eq_in_rename=> n n_in; apply/fperm_genE.
Qed.

Lemma bound_eq_refl : reflexive bound_eq.
Proof.
move=> x; apply/bound_eqP; split=> //.
exists 1; first by rewrite supp1 /fdisjoint fset0I.
by rewrite rename1.
Qed.

Lemma bound_eq_sym : symmetric bound_eq.
Proof.
apply/symmetric_from_pre=> x y /bound_eqP [e [s dis re]].
apply/bound_eqP; rewrite -e; split=> //.
exists s^-1; first by rewrite supp_inv.
by rewrite -re renameK.
Qed.

Lemma bound_eq_trans : transitive bound_eq.
Proof.
move=> z x y /bound_eqP [e1 [s1 dis1 re1]] /bound_eqP [e2 [s2 dis2 re2]].
apply/bound_eqP; rewrite {1}e1; split=> //.
exists (s2 * s1); last by rewrite -renameD re1.
apply/fdisjointP=> n /(fsubsetP _ _ (supp_mul _ _)) /fsetUP [n_in|n_in].
  by move/fdisjointP: dis2; rewrite -e1; apply.
by move/fdisjointP: dis1; apply.
Qed.

Canonical bound_eq_equivRel :=
  Eval hnf in EquivRel bound_eq bound_eq_refl bound_eq_sym bound_eq_trans.

End Def.

Local Open Scope quotient_scope.

Notation "{ 'bound' T }" := {eq_quot @bound_eq [nominalType of T]}
  (at level 0, format "{ 'bound'  T }") : type_scope.

(* FIXME: For some reason, subtype structure inference is not working here... *)
Module BoundOrd.

Section Def.

Variable T : nominalType.

Implicit Type (bx : {bound T}).

Local Open Scope ord_scope.

Definition leq bx1 bx2 :=
  repr bx1 <= repr bx2.

Lemma leq_refl : reflexive leq.
Proof. by move=> bx; rewrite /leq Ord.leqxx. Qed.

Lemma leq_sym : antisymmetric leq.
Proof.
move=> bx1 bx2; rewrite /leq=> /Ord.anti_leq.
exact: (can_inj (@reprK _ [quotType of {bound T}])).
Qed.

Lemma leq_trans : transitive leq.
Proof.
move=> bx1 bx2 bx3; rewrite /leq=> h1 h2.
exact: (Ord.leq_trans h1 h2).
Qed.

Lemma leq_total : total leq.
Proof.
by move=> bx1 bx2; rewrite /leq Ord.leq_total.
Qed.

Definition partOrdMixin := PartOrdMixin leq_refl leq_trans leq_sym.
Canonical partOrdType := Eval hnf in PartOrdType {bound T} partOrdMixin.
Definition ordMixin := OrdMixin leq_total.
Canonical ordType := Eval hnf in OrdType {bound T} ordMixin.

End Def.

End BoundOrd.

Canonical BoundOrd.partOrdType.
Canonical BoundOrd.ordType.

Section Basic.

Variable (T : nominalType).

Definition mask (A : {fset name}) (x : T) : {bound T} :=
  locked (\pi_{bound T} (A, x)).

Lemma maskE A x : mask A x = mask (A :&: names x) x.
Proof.
rewrite /mask -2!lock; apply/eqmodP/bound_eqP=> /=.
rewrite -fsetIA fsetIid; split=> //.
by exists 1; rewrite ?rename1 // supp1 /fdisjoint fset0I.
Qed.

Lemma boundP (P : {bound T} -> Type) :
  (forall A x, fsubset A (names x) -> P (mask A x)) ->
  forall x, P x.
Proof.
move=> IH; elim/quotP=> [[A x] /= _].
by move: (IH _ x (fsubsetIr A (names x))); rewrite -maskE /mask -lock.
Qed.

Lemma maskP A x x' :
  fsubset A (names x) ->
  (mask A x = mask A x'
   <-> exists2 s, fdisjoint (supp s) A & rename s x = x').
Proof.
move=> sub.
have {sub} sub: A :&: names x = A.
  by apply/eqP; rewrite eqEfsubset fsubsetIl fsubsetI fsubsetxx.
rewrite /mask -2!lock; split.
  by rewrite -{3}sub; move/eqmodP/bound_eqP=> //= [_] //.
move=> [s dis <-]; apply/eqmodP/bound_eqP; split=> /=.
  rewrite names_rename; apply/eq_fset=> n; apply/fsetIP/fsetIP.
    case=> [in_A in_names]; split=> //.
    suff ->: n = s n.
      rewrite mem_imfset_inj //; apply/fperm_inj.
    by apply/esym/suppPn; move: (n) in_A; apply/fdisjointP; rewrite fdisjointC.
  case=> [in_A in_names]; split=> //.
  suff e: n = s n.
    by rewrite e mem_imfset_inj // in in_names; apply/fperm_inj.
  by apply/esym/suppPn; move: (n) in_A; apply/fdisjointP; rewrite fdisjointC.
exists s=> //.
by move: dis; rewrite /fdisjoint fsetIA=> /eqP ->; rewrite fset0I.
Qed.

Section Elim.

Variable S : Type.
Variable f : {fset name} -> T -> S.

Definition lift_bound (x : {bound T}) :=
  f ((repr x).1 :&: names (repr x).2) (repr x).2.

Lemma lift_boundE :
  (forall A x s, fsubset A (names x) -> fdisjoint (supp s) A ->
                 f A x = f A (rename s x)) ->
  forall A x, fsubset A (names x) -> lift_bound (mask A x) = f A x.
Proof.
move=> e A x sub; rewrite /lift_bound /mask -lock.
case: piP=> [[A' x'] /eqmodP/bound_eqP /= [eA [s dis ex]]].
rewrite -{}eA //; have eA: A :&: names x = A.
  by apply/eqP; rewrite eqEfsubset fsubsetIl fsubsetI fsubsetxx.
by rewrite eA -{}ex -e // -eA.
Qed.

End Elim.

End Basic.

Section Structures.

Variable T : nominalType.
Implicit Types (s : {fperm name}) (x : T) (bx : {bound T}).

Definition bound_rename s :=
  locked (lift_bound (fun A x => mask (rename s A) (rename s x))).

Let bound_rename_morph s A x :
  bound_rename s (mask A x) = mask (rename s A) (rename s x).
Proof.
rewrite maskE [RHS]maskE names_rename -imfsetI; last first.
  by move=> ?? _ _; apply: rename_inj.
move: (A :&: _) (fsubsetIr A (names x))=> {A} A.
rewrite /bound_rename -lock; apply: lift_boundE=> {A x} A x s' sub dis.
apply/maskP; first by rewrite names_rename renamefsE imfsetS.
exists (s * s' * s^-1).
  rewrite suppJ /fdisjoint renamefsE -imfsetI.
    by move: dis; rewrite /fdisjoint=> /eqP ->; rewrite imfset0.
  by move=> ?? _ _; apply/fperm_inj.
by rewrite -renameD renameK renameD.
Qed.

Definition bound_names :=
  locked (lift_bound (fun A x => A)).

Let bound_names_morph A x :
  fsubset A (names x) -> bound_names (mask A x) = A.
Proof. by move=> sub; rewrite /bound_names -lock lift_boundE //. Qed.

Lemma bound_renameD s1 s2 bx :
  bound_rename s1 (bound_rename s2 bx) =
  bound_rename (s1 * s2) bx.
Proof.
elim/boundP: bx=> [A x sub].
rewrite bound_rename_morph //= bound_rename_morph //= ?renameD.
by rewrite bound_rename_morph.
Qed.

Lemma bound_namesTeq n n' bx :
  n \in bound_names bx ->
  bound_rename (fperm2 n n') bx = bx ->
  n' \in bound_names bx.
Proof.
elim/boundP: bx=> [/= A x sub]; rewrite bound_names_morph // => n_in.
set s := fperm2 n n'.
rewrite bound_rename_morph // renamefsE=> e_m.
suff ->: A = rename s @: A.
  by rewrite -{1}(fperm2L n n') mem_imfset.
have sub': fsubset (rename s @: A) (names (rename s x)).
  by rewrite names_rename imfsetS.
by rewrite -[LHS](bound_names_morph sub) -e_m bound_names_morph.
Qed.

Lemma bound_namesNNE n n' bx :
  n \notin bound_names bx ->
  n' \notin bound_names bx ->
  bound_rename (fperm2 n n') bx = bx.
Proof.
elim/boundP: bx=> [/= A x sub]; rewrite bound_names_morph // => n_nin n'_nin.
rewrite bound_rename_morph // namesNNE; first last.
- apply: contra n'_nin.
  by rewrite namesfsE=> /bigcupP [?? _ /namesnP ->].
- apply: contra n_nin.
  by rewrite namesfsE=> /bigcupP [?? _ /namesnP ->].
apply/esym/maskP=> //; exists (fperm2 n n'); eauto.
rewrite /fdisjoint -fsubset0.
rewrite (fsubset_trans (fsetSI _ (fsubset_supp_fperm2 _ _))) //.
apply/fsubsetP=> n'' /fsetIP [/fset2P [->|->] in_A];
by move: n_nin n'_nin; rewrite in_A.
Qed.

Definition bound_nominalMixin :=
  NominalMixin bound_renameD bound_namesNNE bound_namesTeq.
Canonical bound_nominalType :=
  Eval hnf in NominalType {bound T} bound_nominalMixin.

Lemma renamebE s A x :
  rename s (mask A x) = mask (rename s A) (rename s x).
Proof. exact: bound_rename_morph. Qed.

Lemma namesbE A x :
  fsubset A (names x) ->
  names (mask A x) = A.
Proof. exact: bound_names_morph. Qed.

Definition hide (n : name) :=
  locked (lift_bound (fun A x => mask (A :\ n) x)).

Lemma hideE n A x : hide n (mask A x) = mask (A :\ n) x.
Proof.
rewrite maskE [RHS]maskE (_ : (_ :\ _) :&: _ = (A :&: names x) :\ n).
  move: (A :&: names x) (fsubsetIr A (names x))=> {A} A sub.
  rewrite /hide -lock lift_boundE // {A x sub}.
  move=> A x s sub dis; apply/maskP=> //.
    rewrite fsubD1set (fsubset_trans sub) //.
    by rewrite fsetU1E fsubsetUr.
  exists s=> //; rewrite fdisjointC; apply/fdisjointP=> n'.
  rewrite in_fsetD1=> /andP [_]; rewrite fdisjointC in dis.
  by move/fdisjointP: dis; apply.
by apply/eq_fset=> n'; rewrite !(in_fsetI, in_fsetD1) andbA.
Qed.

Lemma names_hide n bx : names (hide n bx) = names bx :\ n.
Proof.
elim/boundP: bx=> [A x sub]; rewrite hideE [in RHS]namesbE //.
by rewrite namesbE // (fsubset_trans _ sub) // fsubD1set fsetU1E fsubsetUr.
Qed.

Lemma rename_hide s n bx :
  rename s (hide n bx) = hide (s n) (rename s bx).
Proof.
elim/boundP: bx=> [A x sub]; rewrite hideE 2!renamebE hideE.
congr mask; apply/eq_fset=> n'; rewrite in_fsetD1 renamefsE.
apply/imfsetP/andP.
  case=> [n'']; rewrite in_fsetD1=> /andP [ne in_A ->].
  rewrite inj_eq ?ne ?renamefsE ?mem_imfset_inj //;
  move=> ??; exact : rename_inj.
rewrite renamefsE=> - [ne /imfsetP [n'' in_A ?]]; subst n'.
exists n''; rewrite // in_fsetD1 in_A andbT.
by apply: contra ne=> /eqP ->.
Qed.

Definition new (ns : {fset name}) (f : name -> {bound T}) :=
  locked (hide (fresh ns) (f (fresh ns))).

Lemma newP ns f g :
  (forall n, n \notin ns -> f n = g n) ->
  new ns f = new ns g.
Proof. by move=> efg; rewrite /new -2!lock efg // freshP. Qed.

Lemma newE ns f n :
  n \notin ns -> finsupp ns f -> new ns f = hide n (f n).
Proof.
move=> n_nin_ns fs_f; rewrite /new -lock.
move: (fresh _) (freshP ns)=> n' n'_nin_ns.
pose s := fperm2 n' n.
have dis: fdisjoint (supp s) ns.
  rewrite (fdisjoint_trans (fsubset_supp_fperm2 _ _)) //.
  by apply/fdisjointP=> n'' /fset2P [->|->] {n''} //.
rewrite -(fs_f _ dis) fperm2V renamenE fperm2L.
rewrite -{1}(fperm2R n' n : s n = n') -rename_hide.
rewrite ?names_disjointE // names_hide.
suff sub': fsubset (names (f n) :\ n) ns.
  by rewrite fdisjointC (fdisjoint_trans sub') // fdisjointC.
by rewrite fsubD1set fsetU1E fsetUC (names_finsupp n fs_f).
Qed.

Lemma newS ns ns' f :
  finsupp ns f -> fsubset ns ns' -> new ns f = new ns' f.
Proof.
move=> fs_f sub; move: (fresh _) (freshP ns')=> n n_nin_ns'.
have n_nin_ns: n \notin ns.
  by apply: contra n_nin_ns'; move/fsubsetP: sub; apply.
rewrite (newE n_nin_ns') 1?(newE n_nin_ns) //.
exact: finsuppS fs_f sub.
Qed.

End Structures.

End Binding.
