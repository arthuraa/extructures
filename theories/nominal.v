Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

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

End Equivariance.

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
rewrite /seq_names big_tnth => /bigcupP [i _ Pin e].
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
rewrite /fset_names /fset_rename big_tnth => /bigcupP [i _ Pi] e.
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
  case/fsetUP; rewrite !namesfsE big_tnth=> /bigcupP [i _].
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
