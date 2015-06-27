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

Section Fresh.

Local Open Scope fset_scope.

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

Fixpoint freshk k ns :=
  if k is S k' then
    let n := fresh ns in
    n |: freshk k' (n |: ns)
  else fset0.

Lemma freshkP k ns : fdisjoint (freshk k ns) ns.
Proof.
elim: k ns => [|k IH] ns /=; first exact: fdisjoint0.
apply/fdisjointP=> n /fsetU1P [->|]; first exact: freshP.
move: n; apply/fdisjointP; rewrite fdisjointC.
apply/(fdisjoint_trans (fsubsetUr (fset1 (fresh ns)) ns)); rewrite -fsetU1E.
by rewrite fdisjointC.
Qed.

Lemma size_freshk k ns : size (freshk k ns) = k.
Proof.
elim: k ns=> [//|k IH] ns.
rewrite (lock val) /= -lock size_fsetU1 IH -add1n; congr addn.
move: (fresh _) (freshP ns)=> n Pn.
move: (freshkP k (n |: ns)); rewrite fdisjointC=> /fdisjointP/(_ n).
by rewrite in_fsetU1 eqxx /= => /(_ erefl) ->.
Qed.

End Fresh.

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
    forall x, rename s (f x) = f (rename s x).

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
by rewrite (fs_f _ dis).
Qed.

Lemma const_finsupp y : finsupp (names y) (fun _ => y).
Proof. by move=> s dis x /=; rewrite names_disjointE. Qed.

Lemma equivariant_finsupp f : equivariant f <-> finsupp fset0 f.
Proof.
split=> [equi_f|fs_f].
  by move=> s _ x; rewrite equi_f.
by move=> s x; rewrite fs_f.
Qed.

End Equivariance.

Section Composition.

Variables (T S R : nominalType).

Lemma finsupp_comp ns ns' (g : S -> R) (f : T -> S) :
  finsupp ns g -> finsupp ns' f -> finsupp (ns :|: ns') (g \o f).
Proof.
move=> fs_f fs_g s dis x /=.
have {dis} /andP [dis1 dis2]:
  fdisjoint (supp s) ns && fdisjoint (supp s) ns'.
  by move: dis; rewrite /fdisjoint fsetIUr fsetU_eq0.
by rewrite (fs_f _ dis1) (fs_g _ dis2).
Qed.

Lemma equivariant_comp (g : S -> R) (f : T -> S) :
  equivariant g -> equivariant f -> equivariant (g \o f).
Proof.
move=> /equivariant_finsupp fs_g /equivariant_finsupp fs_f.
apply/equivariant_finsupp; rewrite -(fsetU0 fset0).
exact: finsupp_comp.
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

Lemma namesnE n : names n = fset1 n.
Proof. by []. Qed.

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

Lemma namesm_set m k v :
  fsubset (names (setm m k v)) (names m :|: names k :|: names v).
Proof.
exact: equivariant_names (fun s p => renamem_set s p.1.1 p.1.2 p.2)
                         ((m, k), v).
Qed.

Lemma namesm_union m1 m2 :
  fsubset (names (unionm m1 m2)) (names m1 :|: names m2).
Proof.
exact: equivariant_names (fun s p => renamem_union s p.1 p.2) (m1, m2).
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

Module Export Binding.

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

(* FIXME: This notation does not work when MathComp.generic_quotient is
   not imported *)
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
  forall bx, P bx.
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

Definition avoid D A :=
  locked (
    let ns_old := A :&: D in
    let ns_new := freshk (size ns_old) (A :|: D) in
    let ss := enum_fperm (ns_old :|: ns_new) in
    let s_ok (s : {fperm name}) := s @: ns_old == ns_new in
    odflt 1 (fpick s_ok ss)
  ).

Lemma avoidP D A : fdisjoint (avoid D A @: A) D.
Proof.
rewrite /avoid -lock.
move: (size_freshk (size (A :&: D)) (A :|: D)).
move: (freshkP (size (A :&: D)) (A :|: D)).
move: (freshk _ _)=> N dis Psize.
case: fpickP=> [s /eqP Ps|] //=.
  rewrite -enum_fpermE -{2}(fsetID A D) imfsetU Ps=> sub.
  rewrite fdisjointC; apply/fdisjointP=> n n_in_D.
  move: (dis); rewrite in_fsetU negb_or fdisjointC.
  move/fdisjointP/(_ n); rewrite in_fsetU n_in_D orbT=> /(_ erefl) nN //=.
  rewrite nN /= (_ : s @: (A :\: D) = A :\: D) ?in_fsetD ?n_in_D //.
  rewrite -[RHS]imfset_id; apply/eq_in_imfset=> {n n_in_D nN} n.
  rewrite in_fsetD=> /andP [nD nA]; apply/suppPn.
  move/fsubsetP/(_ n)/contra: sub; apply.
  rewrite in_fsetU in_fsetI nA (negbTE nD) /=.
  move: dis; rewrite fdisjointC=> /fdisjointP/(_ n).
  by rewrite in_fsetU nA=> /(_ erefl).
move: Psize => /esym Psize P.
have [s sub im_s] := find_fperm Psize.
by rewrite enum_fpermE in sub; move: (P s sub); rewrite im_s eqxx.
Qed.

Lemma supp_avoid D A : fdisjoint (supp (avoid D A)) (A :\: D).
Proof.
rewrite /avoid -lock.
move: (size_freshk (size (A :&: D)) (A :|: D)).
move: (freshkP (size (A :&: D)) (A :|: D)).
move: (freshk _ _)=> N dis Psize.
case: fpickP=> [s /eqP Ps|] //=.
  rewrite -enum_fpermE=> /fsubsetP sub.
  apply/fdisjointP=> n; apply: contraTN; rewrite in_fsetD=> /andP [nD nA].
  move/(_ n)/contra: sub; apply.
  rewrite in_fsetU negb_or in_fsetI (negbTE nD) andbF /=.
  move: dis; rewrite fdisjointC=> /fdisjointP/(_ n); apply.
  by rewrite in_fsetU nA.
move: Psize => /esym Psize P.
have [s sub im_s] := find_fperm Psize.
by rewrite enum_fpermE in sub; move: (P s sub); rewrite im_s eqxx.
Qed.

Lemma mask_avoid D A x :
  fsubset A (names x) ->
  mask A x = mask A (rename (avoid (D :\: A) (names x)) x).
Proof.
move=> sub; apply/(maskP _ sub); eexists; last by eauto.
move/fdisjointP: (supp_avoid (D :\: A) (names x))=> dis.
apply/fdisjointP=> /= n /dis; rewrite in_fsetD=> /nandP.
rewrite negbK in_fsetD=> - [/andP [] //|].
by apply: contra; apply/fsubsetP.
Qed.

Lemma fresh_boundP D (P : {bound T} -> Type) :
  (forall A x, fsubset A (names x) -> fsubset (D :&: names x) A ->
               P (mask A x)) ->
  forall bx, P bx.
Proof.
move=> IH; elim/boundP=> [/= A x sub].
rewrite (mask_avoid D sub); apply: IH; rewrite names_rename.
  apply/fsubsetP=> n n_in_A; move/(fsubsetP _ _ sub _): (n_in_A)=> n_in_x.
  move: (supp_avoid (D :\: A) (names x)); rewrite fdisjointC.
  move/fdisjointP/(_ n); rewrite 2!in_fsetD negb_and negbK n_in_A /=.
  by move/(_ n_in_x)/suppPn=> <-; apply/mem_imfset.
rewrite -{1}(fsetID D A) fsetIUl [in X in _ :|: X]fsetIC.
move/eqP: (avoidP (D :\: A) (names x))=> ->; rewrite fsetU0.
by rewrite (fsetIC _ A) -fsetIA fsubsetIl.
Qed.

Section Elim.

Variable S : Type.
Variable f : {fset name} -> T -> S.

Definition elim_bound (x : {bound T}) :=
  f ((repr x).1 :&: names (repr x).2) (repr x).2.

Lemma elim_boundE A x :
  fsubset A (names x) ->
  (forall s, fdisjoint (supp s) A -> f A x = f A (rename s x)) ->
  elim_bound (mask A x) = f A x.
Proof.
move=> sub e; rewrite /elim_bound /mask -lock.
case: piP=> [[A' x'] /eqmodP/bound_eqP /= [eA [s dis ex]]].
rewrite -{}eA //; have eA: A :&: names x = A.
  by apply/eqP; rewrite eqEfsubset fsubsetIl fsubsetI fsubsetxx.
by rewrite eA -{}ex -e // -eA.
Qed.

End Elim.

End Basic.

Section Functor.

Section FinSupp.

Variables T S : nominalType.
Variables (D : {fset name}) (f : T -> S).

Definition lift_bound_fs :=
  elim_bound
    (fun A x => mask (D :|: A) (f (rename (avoid (D :\: A) (names x)) x))).

Lemma lift_bound_fsE :
  finsupp D f ->
  forall A x, fsubset (D :&: names x) A ->
              lift_bound_fs (mask A x) =
              mask (D :|: A) (f x).
Proof.
move=> /= fs_f A x sub; rewrite [in LHS]maskE.
rewrite [RHS](_ : _ = mask (D :|: A :&: names x) (f x)); last first.
  rewrite [LHS]maskE [RHS]maskE; congr mask.
  rewrite !fsetIUl; rewrite -fsetIA (fsetIC (names x)) fsetIA.
  apply/eqP; rewrite eqEfsubset fsubUset fsubsetUl /=; apply/andP; split.
    apply/fsubsetP=> /= n inA; rewrite in_fsetU [in X in _ || X]in_fsetI.
    rewrite inA /=; case/fsetIP: inA=> [inA inNfx].
    case/fsubsetP/(_ _ inNfx)/fsetUP: (names_finsupp x fs_f)=> [inD|inNx].
      by rewrite in_fsetI inD inNfx.
    by rewrite inNx orbT.
  rewrite fsubUset fsubsetUl /=; apply/fsubsetU/orP; right.
  exact/fsubsetIl.
have {sub} sub2: fsubset (D :&: names x) (A :&: names x).
  by rewrite fsubsetI sub fsubsetIr.
move: (_ :&: _) (fsubsetIr A (names x)) sub2=> {A} A sub1 sub2.
rewrite /lift_bound_fs elim_boundE //.
  rewrite names_disjointE // {2}(_ : names x = names x :\: (D :\: A)).
    exact: supp_avoid.
  apply/eq_fset=> /= n; apply/(sameP idP)/(iffP idP).
    by rewrite in_fsetD => /andP [].
  move=> n_in_names; rewrite in_fsetD n_in_names andbT in_fsetD.
  rewrite negb_and negbK orbC -implybE; apply/implyP=> n_in_D.
  by move/fsubsetP: sub2; apply; apply/fsetIP; split.
move=> s dis.
set s1 := avoid _ _; set s2 := avoid _ _.
rewrite [LHS]maskE [RHS]maskE.
pose s' := s2 * s * s1^-1.
have inj: {in names (rename s1 x) &, injective s'}.
  by move=> ?? _ _; apply: fperm_inj.
pose s'' := fperm_gen inj.
have disA : fdisjoint (supp s'') A.
  rewrite fdisjointC; apply/fdisjointP=> /= n inA.
  have es1n: s1 n = n.
    apply/suppPn; move: (supp_avoid _ _ : fdisjoint (supp s1) _).
    rewrite fdisjointC; move/fdisjointP; apply.
    by rewrite 2!in_fsetD inA; move: inA; apply/fsubsetP.
  apply/suppPn; rewrite fperm_genE; last first.
    rewrite names_rename -es1n.
    by apply/mem_imfset; move: inA; apply/fsubsetP.
  move/suppPn: es1n; rewrite -supp_inv=> /suppPn es1n.
  rewrite /s' fpermM /= fpermM /= es1n.
  have esn: s n = n.
    by apply/suppPn; move: dis; rewrite fdisjointC; move/fdisjointP; apply.
  rewrite esn.
  apply/suppPn; move: (supp_avoid _ _ : fdisjoint (supp s2) _).
  rewrite fdisjointC; move/fdisjointP; apply.
  rewrite names_rename 2!in_fsetD inA /= -esn.
  by apply/mem_imfset; move: inA; apply/fsubsetP.
have disD : fdisjoint (supp s'') D.
  rewrite fdisjointC; apply/fdisjointP=> /= n inN.
  have [|ninA] := boolP (n \in A).
    by apply/fdisjointP; rewrite fdisjointC.
  move/fsubsetP/(_ n)/contra: (supp_fperm_gen _ : fsubset (supp s'') _).
  apply; rewrite in_fsetU negb_or {1}names_rename.
  move: (avoidP _ _ : fdisjoint (s1 @: _) _); rewrite fdisjointC.
  move=> /fdisjointP/(_ n); rewrite in_fsetD ninA inN=> /(_ erefl) nin_im.
  rewrite nin_im /= -names_rename renameD /s' fperm_mulsKV.
  rewrite -renameD names_rename; move: (avoidP _ _ : fdisjoint (s2 @: _) _).
  by rewrite fdisjointC; move/fdisjointP; apply; rewrite in_fsetD ninA inN.
have disDA: fdisjoint (supp s'') (D :|: A).
  apply/fdisjointP=> /= n inS; rewrite in_fsetU negb_or.
  move/fdisjointP/(_ _ inS) in disA; move/fdisjointP/(_ _ inS) in disD.
  by rewrite disA disD.
set A1 := _ :&: _; set A2 := _ :&: _.
rewrite -(_ : A1 = A2).
  apply/maskP; first exact: fsubsetIr.
  exists s''=> //.
    apply/fdisjointP=> /= n inS; rewrite in_fsetI negb_and.
    by move/fdisjointP/(_ _ inS): disDA=> ->.
  rewrite fs_f // (eq_in_rename (fperm_genE inj)) 2!renameD.
  by rewrite /s' fperm_mulsKV.
apply/eq_fset=> /= n; rewrite 2!in_fsetI.
have [inDA|//] /= := boolP (n \in D :|: A).
rewrite renameD -(fperm_mulsKV s1 (s2 * s)) -renameD.
rewrite -(eq_in_rename (fperm_genE inj)) -[in RHS]fs_f //.
rewrite [in RHS]names_rename -[in RHS](_ : s'' n = n).
  rewrite mem_imfset_inj //; exact: fperm_inj.
by apply/suppPn; move: inDA; apply/fdisjointP; rewrite fdisjointC.
Qed.

End FinSupp.

Section Properties.

Variables T S R : nominalType.

Lemma lift_bound_fs_id D (bx : {bound T}) :
  lift_bound_fs D id bx = bx.
Proof.
elim/(@fresh_boundP T D): bx=> [A x sub1 sub2].
rewrite lift_bound_fsE=> //.
rewrite maskE fsetIUl; congr mask.
apply/eqP; rewrite eqEfsubset fsubUset sub2 fsubsetIl /=.
by apply/fsubsetU/orP; right; rewrite fsubsetI fsubsetxx.
Qed.

Lemma lift_bound_fs_comp Dg Df (g : S -> R) (f : T -> S) bx :
  finsupp Dg g -> finsupp Df f ->
  lift_bound_fs (Dg :|: Df) (g \o f) bx =
  lift_bound_fs Dg g (lift_bound_fs Df f bx).
Proof.
elim/(@fresh_boundP T (Dg :|: Df)): bx=> [A x sub1 sub2] fs_g fs_f.
move: (sub2); rewrite fsetIUl fsubUset=> /andP [subg subf].
rewrite lift_bound_fsE //=; last by apply: finsupp_comp.
rewrite (lift_bound_fsE fs_f) // [in RHS]maskE.
set Af := (Df :|: A) :&: names (f x).
rewrite lift_bound_fsE ?fsubsetIr //.
  rewrite [LHS]maskE [RHS]maskE; congr mask.
  apply/eq_fset=> /= n; rewrite 2!in_fsetI.
  have [inN|_] := boolP (n \in names _); last by rewrite !andbF.
  rewrite 2!andbT.
  move/fsubsetP/(_ n inN): (names_finsupp (f x) fs_g).
  rewrite in_fsetU -[in LHS]fsetUA [LHS]in_fsetU [RHS]in_fsetU.
  have [//|/= ninDg inNf] := boolP (n \in Dg).
  by rewrite /Af in_fsetI inNf andbT.
apply/fsubsetP=> /= n /fsetIP [inDg inNf].
move/fsubsetP/(_ n inNf): (names_finsupp x fs_f).
rewrite in_fsetU; have [/=|/= ninDf] := boolP (n \in Df).
  by rewrite in_fsetI inNf andbT in_fsetU=> ->.
rewrite in_fsetI inNf andbT=> inNx.
apply/fsetUP; right.
by move/fsubsetP: subg; apply; apply/fsetIP; split.
Qed.

End Properties.

Section Def.

Variable T S : nominalType.
Variable f : T -> S.

Definition lift_bound := lift_bound_fs fset0 f.

Lemma lift_boundE :
  equivariant f ->
  forall A x, lift_bound (mask A x) = mask A (f x).
Proof.
move=> /equivariant_finsupp fs_f A x.
rewrite /lift_bound lift_bound_fsE //=.
by rewrite fset0I fsub0set.
Qed.

End Def.

End Functor.

Section Structures.

Variable T : nominalType.
Implicit Types (s : {fperm name}) (x : T) (bx : {bound T}).

Definition bound_rename s :=
  locked (elim_bound (fun A x => mask (rename s A) (rename s x))).

Let bound_rename_morph s A x :
  bound_rename s (mask A x) = mask (rename s A) (rename s x).
Proof.
rewrite maskE [RHS]maskE names_rename -imfsetI; last first.
  by move=> ?? _ _; apply: rename_inj.
move: (A :&: _) (fsubsetIr A (names x))=> {A} A.
rewrite /bound_rename -lock=> sub'; rewrite elim_boundE // => s' dis.
apply/maskP; first by rewrite names_rename renamefsE imfsetS.
exists (s * s' * s^-1).
  rewrite suppJ /fdisjoint renamefsE -imfsetI.
    by move: dis; rewrite /fdisjoint=> /eqP ->; rewrite imfset0.
  by move=> ?? _ _; apply/fperm_inj.
by rewrite -renameD renameK renameD.
Qed.

Definition bound_names :=
  locked (elim_bound (fun A x => A)).

Let bound_names_morph A x :
  fsubset A (names x) -> bound_names (mask A x) = A.
Proof. by move=> sub; rewrite /bound_names -lock elim_boundE //. Qed.

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

Definition join_bound (bbx : {bound {bound T}}) : {bound T} :=
  elim_bound (fun A => elim_bound (fun _ x => mask A x)) bbx.

Lemma join_boundE A A' x :
  fsubset A A' -> join_bound (mask A (mask A' x)) = mask A x.
Proof.
move=> sub; rewrite (maskE A') maskE.
rewrite namesbE ?fsubsetIr //.
rewrite -{1}(fsetIid (names x)) 2!fsetIA fsetIC fsetIA (fsetIA (names x)).
rewrite (fsetIC (names x)) -fsetIA [RHS]maskE.
move: {sub} (fsetSI (names x) sub).
move: (A :&: _) (A' :&: _) (fsubsetIr A (names x)) (fsubsetIr A' (names x)).
move=> {A A'} A A' subA subA' subAA'.
rewrite (_ : A :&: A' = A); last first.
  by apply/eqP; rewrite eqEfsubset fsubsetI fsubsetIl fsubsetxx.
rewrite /join_bound elim_boundE // ?namesbE //.
  rewrite elim_boundE // => s dis; apply/maskP=> //.
  by exists s; rewrite // fdisjointC (fdisjoint_trans subAA') // fdisjointC.
move=> s dis; rewrite renamebE elim_boundE //; last first.
  move=> {s dis} s dis; apply/maskP=> //.
  by exists s; rewrite // fdisjointC (fdisjoint_trans subAA') // fdisjointC.
rewrite elim_boundE //.
- by apply/maskP; eauto.
- by rewrite renamefsE names_rename; apply: imfsetS.
move=> s' dis'; apply/maskP=> //.
  rewrite -(imfset_id A) -(eq_in_imfset (_ : {in A, s =1 id})).
    by rewrite names_rename; apply: imfsetS.
  by move=> /= n inA; apply/suppPn; apply: contraTN inA; apply/fdisjointP.
exists s'; rewrite // fdisjointC; apply/fdisjointP=> /= n inA.
move/fdisjointP/(_ n)/contraTN: dis'; apply.
rewrite renamefsE -(_ : s n = n).
  by apply: mem_imfset; move: inA; apply/fsubsetP.
by apply/suppPn; move: inA; apply: contraTN; apply/fdisjointP.
Qed.

Definition hide (n : name) :=
  locked (elim_bound (fun A x => mask (A :\ n) x)).

Lemma hideE n A x : hide n (mask A x) = mask (A :\ n) x.
Proof.
rewrite maskE [RHS]maskE (_ : (_ :\ _) :&: _ = (A :&: names x) :\ n).
  move: (A :&: names x) (fsubsetIr A (names x))=> {A} A sub.
  rewrite /hide -lock elim_boundE //.
  move=> s dis; apply/maskP=> //.
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

End Structures.

Section FinSuppFacts.

Variables T S R : nominalType.
Implicit Types (D A : {fset name}) (x : T) (bx : {bound T}).
Implicit Types (f : T -> S) (g : T -> S -> R).

Lemma finsupp_lift_bound_fs D f :
  finsupp D f ->
  finsupp D (lift_bound_fs D f).
Proof.
move=> fs_f s dis /=; elim/(@fresh_boundP T D)=> [A x sub fr].
have dis': fdisjoint (supp s) (names D).
  rewrite fdisjointC; apply/fdisjointP=> /= n /namesfsP [n' inD /namesnP ?].
  by subst n'; apply: contraTN inD; apply/fdisjointP.
rewrite lift_bound_fsE // 2!renamebE fs_f // lift_bound_fsE //.
  congr mask; rewrite renamefsE imfsetU; congr fsetU.
  by rewrite -renamefsE names_disjointE.
rewrite -(_ : rename s D = D) ; last by rewrite names_disjointE.
rewrite renamefsE names_rename -imfsetI ?imfsetS //.
by move=> ?? _ _; apply: rename_inj.
Qed.

Lemma curry_equivariant g x :
  equivariant (fun p => g p.1 p.2) ->
  finsupp (names x) (g x).
Proof.
move=> equi_f s dis x'; move: (equi_f s (x, x')) => /= ->.
by congr g; rewrite names_disjointE.
Qed.

End FinSuppFacts.

Section Merging.

(* Tensorial strengthening of the {bound -} monad *)

Variables T S R : nominalType.

Implicit Types (A B : {fset name}) (x : T) (z : S).
Implicit Types (bx : {bound T}) (bz : {bound S}).

Definition merge (x : T) (bz : {bound S}) : {bound T * S} :=
  lift_bound_fs (names x) (pair x) bz.

Lemma mergeE x B z :
  fsubset (names x :&: names z) B ->
  merge x (mask B z) = mask (names x :|: B) (x, z).
Proof.
move=> lim; rewrite /merge lift_bound_fsE //.
exact: curry_equivariant.
Qed.

Lemma rename_merge s x bz :
  rename s (merge x bz) = merge (rename s x) (rename s bz).
Proof.
elim/(@fresh_boundP S (names x)): bz=> [B z sub lim].
rewrite mergeE // 2!renamebE mergeE.
  by rewrite renamefsE imfsetU names_rename.
rewrite 2!names_rename -imfsetI; first exact: imfsetS.
by move=> ?? _ _; apply/fperm_inj.
Qed.

End Merging.

Section Functor2.

Variables T S R : nominalType.
Variable f : T -> S -> R.

Implicit Types (A B : {fset name}) (x : T) (z : S).
Implicit Types (bx : {bound T}) (bz : {bound S}).

Definition lift_bound2 bx bz :=
  (lift_bound (fun p => f p.2 p.1) \o
   @join_bound _ \o
   lift_bound (fun p => merge p.2 p.1) \o
   (fun p => merge p.1 p.2)) (bx, bz).

Hypothesis equi_f : equivariant (fun p => f p.1 p.2).

Lemma lift_bound2E A x B z :
  fsubset (names x :&: B) A ->
  fsubset (A :&: names z) B ->
  fsubset (names x :&: names z) (A :&: B) ->
  lift_bound2 (mask A x) (mask B z) = mask (A :|: B) (f x z).
Proof.
move=> subx subz lim.
rewrite [RHS](_ : _ = mask (A :&: names x :|: B :&: names z) (f x z)).
  have {lim} lim: fsubset (names x :&: names z)
                          ((A :&: names x) :&: (B :&: names z)).
    apply/fsubsetP=> /= n inNxz.
    case/fsubsetP/(_ _ inNxz)/fsetIP: lim=> [inA inB].
    by rewrite !in_fsetI inA inB /= -in_fsetI.
  rewrite (maskE A) (maskE B).
  move: {subx subz} (A :&: _) (fsubsetIr A (names x))
        (B :&: _) (fsubsetIr B (names z)) lim => {A B} /= A sub B sub' lim.
  rewrite /lift_bound2 /= mergeE //; last first.
    rewrite namesbE //.
    apply/(fsubset_trans _ (fsubsetIr A B))/(fsubset_trans _ lim).
    exact: fsetSI.
  rewrite namesbE // lift_boundE /=; first last.
    move=> s [??] /=; exact: rename_merge.
  rewrite mergeE //; last first.
    by rewrite fsetIC (fsubset_trans lim) // fsubsetIl.
  rewrite (fsetUC _ A) join_boundE ?fsetUS // lift_boundE //.
  by move=> s [z' x'] /=; rewrite (equi_f s (x', z')).
rewrite [LHS]maskE [RHS]maskE; congr mask.
apply/eqP; rewrite eqEfsubset; apply/andP; split; last first.
  by rewrite fsetSI // fsetUSS // fsubsetIl.
apply/fsubsetP=> /= n /fsetIP [inAB inNfxz].
rewrite in_fsetI inNfxz andbT.
move: (equivariant_names equi_f (x, z))=> /= /fsubsetP/(_ _ inNfxz) inNxz.
rewrite in_fsetU !in_fsetI; case/fsetUP: inAB=> [inA|inB].
  rewrite inA /=; case/fsetUP: inNxz=> /= [inNx|inNz].
    by rewrite inNx.
  rewrite inNz andbT; apply/orP; right.
  by move/fsubsetP: subz; apply; apply/fsetIP; split.
rewrite inB /=; case/fsetUP: inNxz=> /= [inNx|inNz].
  rewrite inNx andbT; apply/orP; left.
  by move/fsubsetP: subx; apply; apply/fsetIP; split.
by rewrite inNz orbT.
Qed.

Lemma lift_bound2E_weak A x B z :
  fsubset A (names x) ->
  fsubset B (names z) ->
  fsubset (names x :&: names z) (A :&: B) ->
  lift_bound2 (mask A x) (mask B z) = mask (A :|: B) (f x z).
Proof.
move=> subA subB lim; rewrite lift_bound2E //.
  apply/(fsubset_trans (fsetIS _ subB))/(fsubset_trans lim).
  exact: fsubsetIl.
apply/(fsubset_trans (fsetSI _ subA))/(fsubset_trans lim).
exact: fsubsetIr.
Qed.

(* TODO: Eliminator for pairs of bound things? *)

Lemma rename_lift_bound2 s bx bz :
  rename s (lift_bound2 bx bz) = lift_bound2 (rename s bx) (rename s bz).
Proof.
elim/(@fresh_boundP T (names bz)): bx=> [A x subA disA].
elim/(@fresh_boundP S (names x)): bz disA=> [B z subB].
rewrite namesbE // => lim1 lim2.
have {lim1 lim2} lim: fsubset (names x :&: names z) (A :&: B).
  rewrite fsubsetI lim1 andbT (fsubset_trans _ lim2) //.
  by rewrite fsubsetI fsubsetIl andbT.
rewrite lift_bound2E_weak // !renamebE lift_bound2E_weak //; first last.
- rewrite !names_rename !renamefsE -imfsetI; last first.
    by move=> ?? _ _; apply: fperm_inj.
  rewrite -imfsetI; last by move=> ?? _ _; apply: fperm_inj.
  exact: imfsetS.
- by rewrite names_rename renamefsE imfsetS.
- by rewrite names_rename renamefsE imfsetS.
rewrite renamefsE imfsetU; congr mask.
exact: equi_f s (x, z).
Qed.

Lemma finsupp_lift_bound2l bx :
  finsupp (names bx) (lift_bound2 bx).
Proof.
by apply: curry_equivariant=> {bx} s [bx bz] /=; rewrite rename_lift_bound2.
Qed.

Lemma finsupp_lift_bound2r bz :
  finsupp (names bz) (lift_bound2^~ bz).
Proof.
apply: (@curry_equivariant _ _ _ (fun bz=> lift_bound2^~ bz) bz).
by move=> {bz} s [bz bx] /=; rewrite rename_lift_bound2.
Qed.

End Functor2.

Section Flip.

Variables T S R : nominalType.

Lemma flip_lift_bound2 (op : T -> S -> R) bx bz :
  equivariant (fun p => op p.1 p.2) ->
  lift_bound2 (fun z x => op x z) bz bx =
  lift_bound2 op bx bz.
Proof.
move=> equi_op.
elim/(@fresh_boundP T (names bz)): bx=> [A x subA disA].
elim/(@fresh_boundP S (names x)): bz disA=> [B z subB].
rewrite namesbE // => lim1 lim2.
have {lim1 lim2} lim: fsubset (names x :&: names z) (A :&: B).
  rewrite fsubsetI lim1 andbT (fsubset_trans _ lim2) //.
  by rewrite fsubsetI fsubsetIl andbT.
rewrite [in RHS]lift_bound2E_weak // lift_bound2E_weak //; first last.
- by rewrite fsetIC (fsetIC B).
- by move=> s [z' x'] /=; rewrite (equi_op s (x', z')).
by rewrite fsetUC.
Qed.

End Flip.

Section Monoid.

Section BasicFacts.

Variables (T : nominalType) (op : T -> T -> T) (idx : T).

Hypothesis equi_op : equivariant (fun p => op p.1 p.2).

Lemma bound_left_id :
  left_id idx op -> left_id (mask fset0 idx) (lift_bound2 op).
Proof.
move=> op1x bx.
move: {1 3}(mask fset0 idx) (erefl (mask fset0 idx)).
elim/(@fresh_boundP T (names bx))=> [fset0' idx' sub0 lim] e.
have ?: fset0' = fset0.
  by move: (congr1 (@names _) e); rewrite namesbE // namesbE ?fsub0set.
subst fset0'; move/(maskP _ sub0): e=> [s dis eidx].
elim/(@fresh_boundP T (names idx')): bx lim=> [A x subA lim'].
rewrite namesbE // => lim''; rewrite lift_bound2E_weak //.
  rewrite fset0U -(renameK s (op _ _)) (equi_op s (idx', x)) /=.
  by rewrite eidx op1x renameK.
rewrite fset0I; apply/(fsubset_trans _ lim'').
by rewrite fsubsetI lim' fsubsetIl.
Qed.

Lemma bound_associative :
  associative op -> associative (lift_bound2 op).
Proof.
move=> opA bx1 bx2 bx3.
elim/(@fresh_boundP T (names bx2 :|: names bx3)): bx1.
move=> A1 x1 subA1.
elim/(@fresh_boundP T (names x1 :|: names bx3)): bx2.
move=> A2 x2 subA2; rewrite namesbE; last by [].
elim/(@fresh_boundP T (names x1 :|: names x2)): bx3.
move=> A3 x3 subA3; rewrite namesbE; last by [].
rewrite !fsetIUl !fsubUset.
case/andP=> [dis13 dis23] /andP [dis12 dis32] /andP [dis21 dis31].
have names_op: forall x x', fsubset (names (op x x')) (names x :|: names x').
  move=> x x'; exact: (equivariant_names equi_op (x, x')).
rewrite lift_bound2E_weak; trivial; last first.
  rewrite fsubsetI dis23 andbT (fsubset_trans _ dis32) //.
  rewrite fsubsetI dis23 /=; apply/fsubsetIl.
rewrite [in RHS]lift_bound2E_weak; trivial; last first.
  rewrite fsubsetI dis12 andbT (fsubset_trans _ dis21) //.
  rewrite fsubsetI dis12 /=; apply/fsubsetIl.
rewrite lift_bound2E; trivial; first last.
- apply/(fsubset_trans (fsetIS _ (names_op x2 x3))).
  rewrite 2!fsetIUr; apply/fsetUSS.
    rewrite fsubsetI dis12 andbT (fsubset_trans _ dis21) //.
    by rewrite (fsetIC A2) fsubsetI fsubsetIl.
  rewrite fsubsetI dis13 andbT (fsubset_trans _ dis31) //.
  by rewrite fsubsetI dis13 fsubsetIl.
- apply/(fsubset_trans (fsetIS _ (names_op x2 x3))).
  rewrite fsetIUr; apply/fsetUSS.
  apply/(fsubset_trans _ dis12); rewrite fsubsetI fsubsetIr andbT.
  by apply/(fsubset_trans _ subA1)/fsubsetIl.
- apply/(fsubset_trans _ dis13).
  rewrite fsubsetI fsubsetIr andbT (fsubset_trans _ subA1) //.
  by apply/fsubsetIl.
- by rewrite fsetIUr fsubUset fsetIC dis21 /= fsetIC.
rewrite lift_bound2E; trivial; first last.
- apply/(fsubset_trans (fsetSI _ (names_op x1 x2))).
  rewrite 2!fsetIUl; apply/fsetUSS.
    rewrite fsubsetI dis13 andbT (fsubset_trans _ dis31) //.
    by rewrite (fsetIC A3) fsubsetI fsubsetIl.
  rewrite fsubsetI dis23 andbT (fsubset_trans _ dis32) //.
  by rewrite fsubsetI dis23 fsubsetIl.
- rewrite fsetIUl fsubUset; apply/andP; split.
    by apply/(fsubset_trans _ dis13)/fsetSI.
  by apply/(fsubset_trans _ dis23)/fsetSI.
- apply/(fsubset_trans (fsetSI _ (names_op x1 x2))).
  by rewrite fsetIUl; apply/fsetUSS; rewrite fsetIC.
by rewrite fsetUA opA.
Qed.

End BasicFacts.

Section RightId.

Variables (T : nominalType) (op : T -> T -> T) (idx : T).

Hypothesis equi_op : equivariant (fun p => op p.1 p.2).

Lemma bound_right_id :
  right_id idx op -> right_id (mask fset0 idx) (lift_bound2 op).
Proof.
move=> opx1 bx; rewrite -(flip_lift_bound2 _ _ equi_op).
rewrite bound_left_id // => s [bx1 bx2] /=.
by rewrite (equi_op s (bx2, bx1)).
Qed.

End RightId.

End Monoid.

Section New.

Section Basic.

Variable T : nominalType.

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
rewrite -{1 2}(fperm2R n' n : s n = n') -(fs_f _ dis) -rename_hide.
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

Lemma new_const bx : new (names bx) (fun _ => bx) = bx.
Proof.
rewrite (newE (freshP (names bx)) (@const_finsupp _ _ bx)).
elim/boundP: bx=> [A x sub]; rewrite hideE; congr mask.
apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
apply/fsubsetP=> n n_in_A; rewrite in_fsetD1 n_in_A andbT.
rewrite namesbE //; apply: contraTN n_in_A=> /eqP ->.
exact: freshP.
Qed.

End Basic.

Section Composition.

Variables T S : nominalType.

Lemma new_comp B A (g : T -> S) (f : name -> {bound T}) :
  finsupp B g -> finsupp A f ->
  lift_bound_fs B g (new A f) =
  new (A :|: B) (lift_bound_fs B g \o f).
Proof.
move=> fs_g fs_f.
move: (fresh _) (freshP (A :|: B))=> n ninAB.
rewrite (newE ninAB) /=; last first.
  rewrite fsetUC; apply/finsupp_comp=> //.
  exact/finsupp_lift_bound_fs.
have ninA: n \notin A.
  by apply: contra ninAB; apply/fsubsetP/fsubsetUl.
have ninB: n \notin B.
  by apply: contra ninAB; apply/fsubsetP/fsubsetUr.
rewrite (newE ninA) //.
elim/(@fresh_boundP T B): (f n) (names_finsupp n fs_f)=> [/= A' x sub dis].
rewrite namesbE // => sub'; rewrite hideE lift_bound_fsE //.
  rewrite lift_bound_fsE // hideE; congr mask.
  rewrite fsetD1U; congr fsetU.
  apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr andbT.
  apply/fsubsetP=> /= n' inB; rewrite in_fsetD1 inB andbT.
  by apply: contraTN inB=> /eqP ->.
apply/fsubsetP=> /= n' inI; rewrite in_fsetD1.
rewrite (fsubsetP _ _ dis _ inI) andbT.
by apply: contraTN inI=> /eqP ->; rewrite in_fsetI negb_and ninB.
Qed.

End Composition.

Section Left.

Variables T S R : nominalType.

Lemma new_comp2l (op : T -> S -> R) A (f : name -> {bound T}) bz :
  equivariant (fun p => op p.1 p.2) ->
  finsupp A f ->
  lift_bound2 op (new A f) bz =
  new (A :|: names bz) (fun n => lift_bound2 op (f n) bz).
Proof.
move=> equi_op fs_f.
move: (fresh _) (freshP (A :|: names bz))=> n ninAN.
rewrite (newE ninAN) /=; last first.
  rewrite fsetUC.
  exact: (finsupp_comp (@finsupp_lift_bound2r _ _ _ _ equi_op bz) fs_f).
have ninA: n \notin A.
  by apply: contra ninAN; apply/fsubsetP/fsubsetUl.
have ninB: n \notin (names bz).
  by apply: contra ninAN; apply/fsubsetP/fsubsetUr.
rewrite (newE ninA) //.
elim/(@fresh_boundP T (names bz)): (f n) (names_finsupp n fs_f).
move=> /= A' x subA' dis.
rewrite namesbE // namesnE fsetUC -fsetU1E=> sub'; rewrite hideE.
elim/(@fresh_boundP S (names x)): bz ninAN ninB dis=> [/= B z subB sub].
rewrite namesbE // => ninAB ninB lim.
have dis: fsubset (names x :&: names z) A'.
  by rewrite (fsubset_trans _ lim) // fsubsetI sub fsubsetIl.
rewrite lift_bound2E_weak //.
- rewrite lift_bound2E_weak // ?hideE.
    rewrite fsetD1U (_ : B :\ n = B) //.
    apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
    apply/fsubsetP=> /= n' inB; rewrite in_fsetD1 inB andbT.
    by apply: contraTN inB=> /eqP ->.
  by rewrite fsubsetI sub dis.
- by rewrite fsubD1set (fsubset_trans subA') // fsetU1E fsubsetUr.
rewrite fsubsetI sub andbT.
apply/fsubsetP=> /= n' inI; rewrite in_fsetD1.
rewrite (fsubsetP _ _ dis _ inI) andbT.
apply: contra ninAB=> /eqP <-; move: inI; apply/fsubsetP.
by apply/(fsubset_trans sub)/fsubsetUr.
Qed.

End Left.

Section Right.

Variables T S R : nominalType.

Lemma new_comp2r (op : T -> S -> R) B (f : name -> {bound S}) bx :
  equivariant (fun p => op p.1 p.2) ->
  finsupp B f ->
  lift_bound2 op bx (new B f) =
  new (names bx :|: B) (fun n => lift_bound2 op bx (f n)).
Proof.
move=> equi_op fs_f.
rewrite -(flip_lift_bound2 _ _ equi_op).
rewrite new_comp2l //; last first.
  by move=> s [z x] /=; rewrite (equi_op s (x, z)).
by rewrite fsetUC; apply/newP=> n ninNB; rewrite flip_lift_bound2.
Qed.

End Right.

End New.

End Binding.
