From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype tuple bigop
  generic_quotient.

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
Definition name_ordMixin := [ordMixin of name by <:].
Canonical name_ordType := Eval hnf in OrdType name name_ordMixin.

Section Fresh.

Local Open Scope fset_scope.

Lemma fresh_key : unit. Proof. exact: tt. Qed.
Definition fresh_def (ns : {fset name}) : name :=
  Name (foldr maxn 0 [seq nat_of_name n | n <- ns]).+1.
Definition fresh := locked_with fresh_key fresh_def.

Lemma freshP ns : fresh ns \notin ns.
Proof.
suff ub: forall n, n \in ns -> nat_of_name n < nat_of_name (fresh ns).
  by apply/negP=> /ub; rewrite ltnn.
move=> [n] /=; rewrite /fresh unlock=> /=; rewrite ltnS inE /=.
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
apply/(fdisjoint_trans (fsubsetUr (fset1 (fresh ns)) ns)).
by rewrite fdisjointC.
Qed.

Lemma size_freshk k ns : size (freshk k ns) = k.
Proof.
elim: k ns=> [//|k IH] ns.
rewrite (lock val) /= -lock sizesU1 IH -add1n; congr addn.
move: (fresh _) (freshP ns)=> n Pn.
move: (freshkP k (n |: ns)); rewrite fdisjointC=> /fdisjointP/(_ n).
by rewrite in_fsetU1 eqxx /= => /(_ erefl) ->.
Qed.

End Fresh.

Module Type AvoidSig.
Local Open Scope fset_scope.
Parameter avoid : {fset name} -> {fset name} -> {fperm name}.
Axiom avoidP : forall D A, fdisjoint (avoid D A @: A) D.
Axiom supp_avoid : forall D A, fdisjoint (supp (avoid D A)) (A :\: D).
End AvoidSig.

Module Export AvoidDef : AvoidSig.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Definition avoid D A :=
  let ns_old := A :&: D in
  let ns_new := freshk (size ns_old) (A :|: D) in
  let ss := enum_fperm (ns_old :|: ns_new) in
  let s_ok (s : {fperm name}) := s @: ns_old == ns_new in
  odflt 1 (fpick s_ok ss).

Lemma avoidP D A : fdisjoint (avoid D A @: A) D.
Proof.
rewrite /avoid.
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
rewrite /avoid.
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

End AvoidDef.

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
Definition ordType := @Ord.Total.Pack cT xclass xT.

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

Lemma renameJ s x : fdisjoint (supp s) (names x) -> rename s x = x.
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

Lemma names0P x : reflect (forall s, rename s x = x) (names x == fset0).
Proof.
apply/(iffP eqP).
  by move=> eq0 s; rewrite renameJ // eq0 fdisjointC fdisjoint0.
move=> reE; apply/eqP; rewrite eqEfsubset fsub0set andbT.
apply/fsubsetP=> n inN; move: (reE (fperm2 n (fresh (names x)))).
by move/(namesTeq inN); apply/contraTT; rewrite freshP.
Qed.

Lemma eq_in_rename s1 s2 x :
  {in names x, s1 =1 s2} ->
  rename s1 x = rename s2 x.
Proof.
move=> e; apply: (canRL (renameKV s2)); rewrite renameD.
apply/renameJ/fdisjointP=> n; rewrite mem_supp fpermM /=.
by rewrite (can2_eq (fpermKV s2) (fpermK _)); apply/contra=> /e ->.
Qed.

(* FIXME: The variant [names_eqvar] below is more useful, but it requires
   declaring finite sets as a nominal set, and that requires this lemma. *)

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

Lemma renameP s x : rename s x = rename (fperm s (names x)) x.
Proof.
apply/eq_in_rename=> n n_in; symmetry; apply/fpermE=> // n1 n2 _ _.
exact: fperm_inj.
Qed.

End Basics.

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

End NominalTheory.

Ltac finsupp := typeclasses eauto with typeclass_instances.

Class finsupp_perm (D : {fset name}) (s : {fperm name}) :=
  finsupp_permP : fdisjoint (supp s) D.

Class fsubset_class (A B : {fset name}) :=
  fsubset_classP : fsubset A B.

Class nominalRel (T : Type) :=
  nomR : {fperm name} -> T -> T -> Prop.

Existing Class nomR.

Notation "{ 'finsupp' D x }" :=
  (forall s : {fperm name}, finsupp_perm D s -> nomR s x x)
  (at level 0, D at next level, format "{ 'finsupp'  D  x }") : type_scope.

Notation "{ 'eqvar' x }" :=
  (forall s : {fperm name}, nomR s x x)
  (at level 0, format "{ 'eqvar'  x }") : type_scope.

Section FiniteSupport.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (s : {fperm name}) (D : {fset name}).

Global Instance fset0_fsubset_class D : fsubset_class fset0 D.
Proof. exact: fsub0set. Qed.

Global Instance id_fsubset_class D : fsubset_class D D.
Proof. exact: fsubsetxx. Qed.

Global Instance fsetUl_fsubset_class D D1 D2 :
  fsubset_class D D1 ->
  fsubset_class D (D1 :|: D2).
Proof. by move=> fs; apply: (fsubset_trans fs); exact: fsubsetUl. Qed.

Global Instance fsetUr_fsubset_class D D1 D2 :
  fsubset_class D D2 ->
  fsubset_class D (D1 :|: D2).
Proof. by move=> fs; apply: (fsubset_trans fs); exact: fsubsetUr. Qed.

Global Instance fsubset_finsupp_perm D D' s :
  finsupp_perm D' s ->
  fsubset_class D D' ->
  finsupp_perm D s | 2.
Proof.
move=> fs sub; rewrite /finsupp_perm fdisjointC; apply: fdisjoint_trans.
  exact: sub.
by rewrite fdisjointC.
Qed.

Global Instance fset0_finsupp_perm s : finsupp_perm fset0 s.
Proof. by rewrite /finsupp_perm fdisjointC fdisjoint0. Qed.

Global Instance nominalType_nominalRel (T : nominalType) : nominalRel T :=
  fun s x y => rename s x = y.

Global Instance Prop_nominalRel : nominalRel Prop :=
  fun _ P Q => P <-> Q.

Global Instance arrow_nominalRel T S (eT : nominalRel T) (eS : nominalRel S) :
  nominalRel (T -> S) :=
  fun s f g => forall x y, nomR s x y -> nomR s (f x) (g y).

Global Instance nomR_nominal (T : nominalType) s (x : T) :
  nomR s x (rename s x).
Proof. by []. Qed.

Global Instance nomR_nominalJ (T : nominalType) s (x : T) :
  finsupp_perm (names x) s ->
  nomR s x x | 2.
Proof. by move=> fs_s; rewrite -{2}(renameJ fs_s). Qed.

Global Instance nomR_app T S
  {eT : nominalRel T} {eS : nominalRel S} s (f g : T -> S) x y :
  nomR s f g -> nomR s x y -> nomR s (f x) (g y) | 1.
Proof. by apply. Qed.

Definition Prop_finsupp (P : Prop) : {finsupp fset0 P}.
Proof. by []. Qed.

Lemma nom_finsuppP (T : nominalType) A (x : T) :
  {finsupp A x} <-> fsubset (names x) A.
Proof.
split.
  move: (fresh _) (freshP (names x :|: A)) => n'.
  rewrite in_fsetU => /norP [nin_x' nin_A'].
  move=> fs; apply/fsubsetP=> n /namesP/(_ n') in_n.
  have [//|nin_A] := boolP (n \in A).
  rewrite in_n // in nin_x'; eapply fs; apply: fdisjoint_trans.
    exact: fsubset_supp_fperm2.
  rewrite fdisjointUl fdisjointC fdisjoints1 nin_A fdisjointUl fdisjoint0.
  by rewrite fdisjointC fdisjoints1 nin_A'.
move=> sub s dis; apply: renameJ.
rewrite fdisjointC; apply: fdisjoint_trans; eauto.
by rewrite fdisjointC.
Qed.

Lemma nom_eqvarP (T : nominalType) (x : T) : {eqvar x} -> names x = fset0.
Proof. move=> eq_x; apply/eqP; rewrite -fsubset0; apply/nom_finsuppP. Qed.

End FiniteSupport.

Hint Extern 2 (nomR ?s (fun _ => _) (fun _ => _)) =>
  move=> ??? : typeclass_instances.

Module TrivialNominal.

Section ClassDef.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Record mixin_of (T : nominalType) := Mixin {
  _ : forall s (x : T), rename s x = x
}.

Section Mixins.

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

Definition DefNominalMixin :=
  NominalMixin trivial_renameD trivial_namesNNE trivial_namesTeq.

Definition DefMixin :=
  @Mixin (NominalType T DefNominalMixin) (fun _ _ => erefl).

End Mixins.

Record class_of T :=
  Class {base : Nominal.class_of T; mixin : mixin_of (Nominal.Pack base T)}.
Local Coercion base : class_of >-> Nominal.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Nominal.Pack T b0 T)) :=
  fun bT b & phant_id (Nominal.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Total.Pack cT xclass xT.
Definition nominalType := @Nominal.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Nominal.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.Total.type.
Canonical ordType.
Coercion nominalType : type >-> Nominal.type.
Canonical nominalType.
Notation trivialNominalType := type.
Notation trivialNominalMixin := mixin_of.
Notation TrivialNominalMixin := Mixin.
Notation TrivialNominalType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'nominalType' 'for' T 'by' // ]" :=
  (NominalType T (DefNominalMixin [ordType of T]))
  (at level 0, format "[ 'nominalType'  'for'  T  'by'  // ]")
  : form_scope.
Notation "[ 'trivialNominalType' 'for' T ]" :=
  (TrivialNominalType T (@TrivialNominalMixin [nominalType of T]
                                              (fun _ _ => erefl)))
  (at level 0, format "[ 'trivialNominalType'  'for'  T ]")
  : form_scope.
Notation "[ 'trivialNominalType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'trivialNominalType'  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'trivialNominalType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'trivialNominalType'  'of'  T ]") : form_scope.
End Exports.

End TrivialNominal.
Export TrivialNominal.Exports.

Canonical unit_nominalType := Eval hnf in [nominalType for unit by //].
Canonical unit_trivialNominalType := Eval hnf in [trivialNominalType for unit].

Canonical bool_nominalType := Eval hnf in [nominalType for bool by //].
Canonical bool_trivialNominalType := Eval hnf in [trivialNominalType for bool].

Canonical nat_nominalType := Eval hnf in [nominalType for nat by //].
Canonical nat_trivialNominalType := Eval hnf in [trivialNominalType for nat].

Global Instance funcomp_eqvar (T S R : nominalType) : {eqvar @funcomp T S R}.
Proof. by move=> s [] _ <- /= f1 f2 f12 g1 g2 g12 x1 x2 x12 /=; finsupp. Qed.

Section TrivialNominalTheory.

Variable T : trivialNominalType.
Implicit Type (x : T).

Lemma renameT : forall s x, rename s x = x.
Proof. by case: (T)=> [? [[? ? []]]]. Qed.

Lemma namesT : forall x, names x = fset0.
Proof. move=> x; apply/eqP/names0P=> s; exact: renameT. Qed.

End TrivialNominalTheory.

Global Instance eq_op_eqvar (T : nominalType) : {eqvar (@eq_op T)}.
Proof.
move=> s x _ <- y _ <-; rewrite inj_eq //; apply: rename_inj.
Qed.

Global Instance nomR_if T {eT : nominalRel T} s
  (b1 b2 : bool) (x1 x2 y1 y2 : T) :
  nomR s b1 b2 -> nomR s x1 x2 -> nomR s y1 y2 ->
  nomR s (if b1 then x1 else y1) (if b2 then x2 else y2).
Proof. by move=> <-; case: b1. Qed.

Global Instance finsupp_permT (T : trivialNominalType) (x : T) s :
  finsupp_perm (names x) s.
Proof. by rewrite namesT; finsupp. Qed.

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

Lemma namespE p : names p = names p.1 :|: names p.2.
Proof. by []. Qed.

Global Instance pair_eqvar : {eqvar (@pair T' S')}.
Proof. by move=> s x ? <- y ? <-. Qed.

Global Instance fst_eqvar : {eqvar (@fst T' S')}.
Proof. by move=> s [??] ? <-. Qed.

Global Instance snd_eqvar : {eqvar (@snd T' S')}.
Proof. by move=> s [??] ? <-. Qed.

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
  rewrite /seq_names big_tnth; move: n; apply/fsubsetP.
  apply/bigcup_sup=> //; exact: mem_index_enum.
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
  move: {e e'} n' (namesTeq Pin e'); apply/fsubsetP.
  apply/bigcup_sup=> //; exact: mem_index_enum.
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

Lemma namessE xs :
  names xs = foldr fsetU fset0 [seq names x | x <- xs].
Proof.
rewrite {1}/names /= /seq_names; elim: xs=> [|x xs IH].
  by rewrite big_nil.
by rewrite big_cons IH.
Qed.

Global Instance nth_eqvar : {eqvar (@nth T')}.
Proof.
move=> s d _ <- xs _ <- n _ <-.
rewrite !renamesE; have [in_xs|nin] := boolP (n < size xs).
  by rewrite (nth_map d).
by rewrite -leqNgt in nin; rewrite 2?nth_default // size_map.
Qed.

Global Instance nil_eqvar : {eqvar (@nil T')}.
Proof. by []. Qed.

Global Instance cons_eqvar : {eqvar (@cons T')}.
Proof. by move=> s x _ <- xs _ <-. Qed.

Global Instance size_eqvar : {eqvar (@size T')}.
Proof. by move=> s xs _ <-; rewrite renamesE size_map. Qed.

Lemma namess1 x xs : names (x :: xs) = names x :|: names xs.
Proof. by rewrite 2!namessE. Qed.

Lemma names_nseq k x : names (nseq k x) = if 0 < k then names x else fset0.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> n.
  by case/namessP=> [x' /nseqP [-> ->]].
case: ifP=> gt_0; last by rewrite in_fset0.
move=> n_x; apply/namessP; exists x=> //.
by apply/nseqP; split.
Qed.

End SeqNominalType.

Global Instance map_eqvar (T' S' : nominalType) : {eqvar (@map T' S')}.
Proof.
by move=> s f g fg xs _ <-; elim: xs => [|x xs IH] /=; finsupp.
Qed.

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

Variable S' : nominalType.
Implicit Type x : option S'.

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
  Eval hnf in NominalType (option S') option_nominalMixin.

Lemma renameoE s x : rename s x = omap (rename s) x.
Proof. by []. Qed.

Global Instance Some_eqvar : {eqvar (@Some S')}.
Proof. by move=> s ?? <-. Qed.

Global Instance None_eqvar : {eqvar (@None S')}.
Proof. by []. Qed.

Global Instance isSome_eqvar : {eqvar (@isSome S')}.
Proof. by move=> s [?|] _ <-. Qed.

End OptionNominalType.

Global Instance obind_eqvar (T S : nominalType) : {eqvar (@obind T S)}.
Proof. by move=> s f g fg [x|] _ <- //=; apply: fg. Qed.

Global Instance oapp_eqvar (T S : nominalType) : {eqvar (@oapp T S)}.
Proof. by move=> s f g fg ??? [x|] _ <- //=; finsupp. Qed.

Global Instance omap_eqvar (T S : nominalType) : {eqvar (@omap T S)}.
Proof. by move=> s f g fg [x|] /= y <- //=; finsupp. Qed.

Section OptionTrivial.

Variable T' : trivialNominalType.

Let trivial_rename : forall s (x : option T'), rename s x = x.
Proof. by move=> s [x|]; rewrite renameoE //= renameT. Qed.

Canonical option_trivialNominalType :=
  TrivialNominalType (option T') (TrivialNominalMixin trivial_rename).

End OptionTrivial.

Global Instance pmap_eqvar (T' S' : nominalType) : {eqvar (@pmap T' S')}.
Proof.
by move=> s f g fg xs _ <-; elim: xs => [|x xs IH] //=; finsupp.
Qed.

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
apply: eq_in_imfset=> x x_in; apply: renameJ.
apply/fdisjointP=> n'' /(fsubsetP _ _ (fsubset_supp_fperm2 n n')).
have sub: fsubset (names x) (fset_names X).
  case/seq_tnthP: x_in=> [/= i ->]; rewrite /fset_names big_tnth.
  by apply/(@bigcup_sup _ _ _ _ _ (fun x => names _)).
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
case/seq_tnthP: Py=> {y} [y ->]; move: {e} n'; apply/fsubsetP.
by apply/(@bigcup_sup _ _ _ _ _ (fun x => names _)).
Qed.

Definition fset_nominalMixin :=
  NominalMixin fset_renameD fset_namesNNE fset_namesTeq.
Canonical fset_nominalType :=
  Eval hnf in NominalType (FSet.fset_type T') fset_nominalMixin.
Canonical fset_of_nominalType :=
  Eval hnf in [nominalType of {fset T'}].

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

Global Instance fset0_eqvar : {eqvar (@fset0 T')}.
Proof. move=> s; exact: imfset0. Qed.

Lemma namesfs0 : names fset0 = fset0.
Proof. by rewrite namesfsE big_nil. Qed.

Global Instance fset1_eqvar : {eqvar (@fset1 T')}.
Proof. move=> s x _ <-; exact: imfset1. Qed.

Global Instance fsetU_eqvar : {eqvar (@fsetU T')}.
Proof. move=> s X _ <- Y _ <-; exact: imfsetU. Qed.

Global Instance fsetI_eqvar : {eqvar (@fsetI T')}.
Proof. move=> s X _ <- Y _ <-; apply: imfsetI=> ????; exact: rename_inj. Qed.

Global Instance fsetD_eqvar : {eqvar (@fsetD T')}.
Proof.
move=> s X _ <- Y _ <-; apply/eq_fset=> x.
by rewrite !(mem_imfset_can _ _ (renameK s) (renameKV s), in_fsetD).
Qed.

Global Instance fdisjoint_eqvar : {eqvar (@fdisjoint T')}.
Proof.
by move=> ???????; rewrite /fdisjoint; finsupp.
Qed.

Global Instance fsubset_eqvar : {eqvar (@fsubset T')}.
Proof.
move=> s X _ <- Y _ <-.
apply/idP/idP; first exact: imfsetS.
rewrite -{2}(renameK s X) -{2}(renameK s Y); exact: imfsetS.
Qed.

Lemma names_fset (xs : seq T') : names (fset xs) = names xs.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP.
  move=> n /namesfsP [x]; rewrite in_fset => x_xs n_x.
  by apply/namessP; eauto.
move=> n /namessP [x x_xs n_x].
by apply/namesfsP; exists x; rewrite ?in_fset.
Qed.

End SetNominalType.

Lemma namesfsnE (A : {fset name}) : names A = A.
Proof.
apply/eq_fset=> n; apply/namesfsP=> /=; have [inA|ninA] := boolP (n \in A).
  by exists n=> //; apply/namesnP.
by case=> [n' inA /namesnP nn']; move: ninA; rewrite nn' inA.
Qed.

Global Instance names_eqvar : {eqvar (@names T)}.
Proof. by move=> s x _ <-; rewrite names_rename. Qed.

Global Instance nomRJ (f : T -> S) (s : {fperm name}) :
  nomR s f (rename s \o f \o rename s^-1).
Proof. by move=> x _ <- /=; rewrite renameK. Qed.

Global Instance finsuppJ A (f1 f2 : T -> S) (s : {fperm name}) :
  {finsupp A f1} ->
  nomR s f1 f2 ->
  {finsupp (rename s A) f2}.
Proof.
move=> fs_f1 f1f2 s' dis x _ <- /=; rewrite /nomR /= /nominalType_nominalRel.
have dis' : finsupp_perm A (s^-1 * s' * s).
  rewrite -{2}(fperm_invK s) /finsupp_perm suppJ.
  apply/eqP; rewrite -(imfsetK (fpermK s) A) -imfsetI; last first.
    by move=> ?? _ _; apply: fperm_inj.
  by move/eqP: dis=> ->; rewrite imfset0.
rewrite -{1}[x](renameKV s) -(f1f2 (rename s^-1 x) _ erefl).
rewrite -[LHS](renameKV s) 2![rename _ (rename _ (f1 _))]renameD.
rewrite fperm_mulA fs_f1 f1f2 !renameD !fperm_mulA fperm_mulsK.
by rewrite fperm_mulsV fperm_mul1s.
Qed.

Section SetTrivialNominalType.

Variable T' : trivialNominalType.

Let trivial_rename s (xs : {fset T'}) : rename s xs = xs.
Proof.
by rewrite -[RHS]imfset_id renamefsE; apply/eq_imfset=> x; rewrite renameT.
Qed.

Canonical fset_trivialNominalType :=
  Eval hnf in TrivialNominalType (FSet.fset_type T')
                                 (TrivialNominalMixin trivial_rename).

End SetTrivialNominalType.

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
  Eval hnf in NominalType (PartMap.partmap_type T S) partmap_nominalMixin.
Canonical partmap_of_nominalType :=
  Eval hnf in [nominalType of {partmap T -> S}].

Lemma namesmE m : names m = names (domm m) :|: names (codomm m).
Proof. by []. Qed.

Lemma renamemE s m k : rename s m k = rename s (m (rename s^-1 k)).
Proof.
rewrite {1}/rename /= /partmap_rename mkpartmapfpE.
rewrite (mem_imfset_can _ _ (renameK s) (renameKV s)) mem_domm.
by case: (m (rename _ _)).
Qed.

Global Instance getm_eqvar : {eqvar (@getm T S)}.
Proof. by move=> s m _ <- k _ <-; rewrite renamemE renameK. Qed.

Lemma getm_nomR s m1 m2 : nomR s (getm m1) (getm m2) -> nomR s m1 m2.
Proof.
move=> m1m2; apply/eq_partmap=> k.
rewrite -[k](renameKV s); move: (rename s^-1 k) => {k} k.
move/(_ k (rename s k) erefl): m1m2 => <-.
by symmetry; apply: getm_eqvar.
Qed.

Global Instance setm_eqvar : {eqvar (@setm T S)}.
Proof.
move=> ? ??? ??? ???.
by eapply getm_nomR=> ???; rewrite !setmE; finsupp.
Qed.

Global Instance remm_eqvar : {eqvar (@remm T S)}.
Proof.
move=> ? ??? ???.
by eapply getm_nomR=> ???; rewrite !remmE; finsupp.
Qed.

Global Instance filterm_eqvar : {eqvar (@filterm T S)}.
Proof.
move=> ? ??? ???.
by eapply getm_nomR=> ???; rewrite !filtermE; finsupp.
Qed.

Global Instance unionm_eqvar : {eqvar (@unionm T S)}.
Proof.
move=> ? ??? ???.
by eapply getm_nomR=> ???; rewrite !unionmE; finsupp.
Qed.

Lemma namesm_empty : names emptym = fset0.
Proof.
by rewrite namesmE domm0 codomm0 !namesfsE !big_nil fsetUid.
Qed.

Global Instance emptym_eqvar : {eqvar (@emptym T S)}.
Proof. by apply/names0P/eqP/namesm_empty. Qed.

Global Instance mkpartmap_eqvar : {eqvar (@mkpartmap T S)}.
Proof.
by move=> s kvs _ <-; elim: kvs=> [|[k v] kvs IH] /=; finsupp.
Qed.

Global Instance mkpartmapf_eqvar : {eqvar (@mkpartmapf T S)}.
Proof.
by move=> s f g fg ks1 ks2 ks12; rewrite /mkpartmapf; finsupp.
Qed.

Global Instance mkpartmapfp_eqvar : {eqvar (@mkpartmapfp T S)}.
Proof.
by move=> ? ??? ???; rewrite /mkpartmapfp; finsupp.
Qed.

Global Instance domm_eqvar : {eqvar (@domm T S)}.
Proof.
move=> s m _ <-.
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
    by apply: PMFreeNamesKey Pv.
  move: (mem_tnth i (in_tuple (domm (invm m))))=> /codommP [x m_x].
  by apply: PMFreeNamesVal m_x.
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
move=> /fdisjointP dis; apply/eqP; rewrite eqEfsubset.
apply/andP; split; first by eapply nom_finsuppP; finsupp.
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

Lemma namesm_mkpartmapf f ks :
  names (mkpartmapf f ks) = names ks :|: names [seq f k | k <- ks].
Proof.
apply/eq_fset=> n; apply/namesmP/fsetUP.
  case=> [k v|k v]; rewrite mkpartmapfE; case: ifP=> // in_ks [].
    by move=> _ {v} in_k; left; apply/namessP; eauto.
  move=> <- {v} in_fk; right; apply/namessP; exists (f k)=> //.
  by apply/mapP; eauto.
case=> [] /namessP => [[k in_ks in_k]|[v /mapP [k in_ks -> {v} in_fk]]].
  apply: (@PMFreeNamesKey n _ k (f k))=> //.
  by rewrite mkpartmapfE in_ks.
apply: (@PMFreeNamesVal n _ k (f k))=> //.
by rewrite mkpartmapfE in_ks.
Qed.

End PartMapNominalType.

End Instances.

Section MorePartMap.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types T S R : nominalType.

Global Instance partmap_of_seq_eqvar T : {eqvar (@partmap_of_seq T)}.
Proof.
by move=> ????; eapply getm_nomR=> ???; rewrite !partmap_of_seqE; finsupp.
Qed.

Global Instance uncurrym_eqvar T S R : {eqvar (@uncurrym T S R)}.
Proof.
by move=> s ???; eapply getm_nomR=> ???; rewrite !uncurrymE; finsupp.
Qed.

Global Instance currym_eqvar T S R : {eqvar (@currym T S R)}.
Proof.
move=> s m _ <-.
apply/eq_partmap=> x.
move: (erefl (x \in domm (currym (rename s m)))).
rewrite {1}domm_curry -domm_eqvar.
rewrite (_ : (x \in @fst _ _ @: rename s (domm m)) =
             (rename s^-1 x \in @fst _ _ @: (domm m))).
  rewrite -domm_curry !mem_domm renamemE.
  case get_x: (currym m _)=> [n|];
  case get_x': (currym _ _)=> [n'|] //= _.
  congr Some; apply/eq_partmap=> y; rewrite renamemE.
  move: (currymE (rename s m) x y).
  rewrite get_x' /= renamemE pair_eqvar /= => <-.
  by rewrite currymE /= get_x /=.
rewrite -(mem_imfset_can _ _ (renameK s) (renameKV s)).
by rewrite !renamefsE -2!imfset_comp //.
Qed.

End MorePartMap.

Module SubNominal.

Section ClassDef.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable T : nominalType.
Variable P : pred T.

Structure type := Pack {
  sort : subType P;
  _ : {eqvar P}
}.

Local Coercion sort : type >-> subType.

Implicit Type (s : {fperm name}).

Variable (sT : type).

Let subeqvar s x : P x = P (rename s x).
Proof. by case: sT => ? e; rewrite -[RHS]e. Qed.

Implicit Type (x : sT).

Definition subType_rename s x : sT :=
  Sub (rename s (val x))
      (eq_ind (P (val x)) is_true (valP x) _ (subeqvar s _)).

Definition subType_names x := names (val x).

Lemma subType_renameD s1 s2 x :
  subType_rename s1 (subType_rename s2 x) =
  subType_rename (s1 * s2) x.
Proof. by apply: val_inj; rewrite /subType_rename /= !SubK renameD. Qed.

Lemma subType_namesNNE n n' x :
  n \notin subType_names x -> n' \notin subType_names x ->
  subType_rename (fperm2 n n') x = x.
Proof.
move=> n_nin n'_nin; apply: val_inj; rewrite /subType_rename /= !SubK.
by apply: namesNNE.
Qed.

Lemma subType_namesTeq n n' x :
  n \in subType_names x -> subType_rename (fperm2 n n') x = x ->
  n' \in subType_names x.
Proof.
move=> n_in /(f_equal val); rewrite /subType_rename /= !SubK.
by apply: namesTeq.
Qed.

Definition nominalMixin :=
  NominalMixin subType_renameD subType_namesNNE subType_namesTeq.
Definition nominalType := NominalType sT nominalMixin.

Definition pack (sT : subType P) m & phant sT := Pack sT m.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> subType.
Coercion nominalType : type >-> Nominal.type.
Canonical nominalType.
Notation subNominalType := type.
Notation SubNominalType T m := (@pack _ _ _ m (Phant T)).
Notation "[ 'nominalMixin' 'of' T 'by' <: ]" :=
    (nominalMixin _ : Nominal.mixin_of T)
  (at level 0, format "[ 'nominalMixin'  'of'  T  'by'  <: ]") : form_scope.
End Exports.

End SubNominal.
Export SubNominal.Exports.

Section SubNominalTheory.

Variables (T : nominalType) (P : pred T) (sT : subNominalType P).

Implicit Types (s : {fperm name}) (x : sT).

Global Instance val_eqvar : {eqvar (@val _ _ sT)}.
Proof. move=> s x _ <-; symmetry; exact: SubK. Qed.

Lemma nomR_val s x1 x2 : nomR s (val x1) (val x2) -> nomR s x1 x2.
Proof. by move=> x1x2; apply: val_inj; rewrite -x1x2 val_eqvar. Qed.

Global Instance nomR_Sub s (y1 y2 : T) (p1 : P y1) (p2 : P y2) :
  nomR s y1 y2 -> nomR s (Sub y1 p1 : sT) (Sub y2 p2).
Proof. by move=> y1y2; eapply nomR_val; rewrite !SubK. Qed.

Lemma subnamesE x : names x = names (val x).
Proof. by []. Qed.

End SubNominalTheory.

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
rewrite /bij_names /bij_rename=> Pn h; apply: namesTeq; eauto.
by apply: (canRL gK).
Qed.

Definition BijNominalMixin :=
  NominalMixin bij_renameD bij_namesNNE bij_namesTeq.

End TransferNominalType.

Module BoundEq.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Section Def.

Variable T : nominalType.
Variable l : T -> {fset name}.
Hypothesis eq_l : {eqvar l}.

Implicit Types (x y : T).

Definition eq x y :=
  has (fun s => [&& fdisjoint (supp s) (names x :\: l x) &
                 rename s x == y])
      (enum_fperm (names x :|: names y)).

Lemma eqP x y :
  reflect (exists2 s, fdisjoint (supp s) (names x :\: l x) &
                      rename s x = y)
          (eq x y).
Proof.
apply/(iffP idP); first by case/hasP=> s s_in /andP [dis /eqP e]; eauto.
case=> s dis e; rewrite /eq /=; apply/hasP.
have inj: {in names x &, injective s} by move=> ????; apply: fperm_inj.
exists (fperm s (names x)).
  by rewrite -enum_fpermE -e names_rename supp_fperm.
apply/andP; split.
  move: dis; rewrite 2![fdisjoint _ (_ :\: _)]fdisjointC.
  move=> /fdisjointP dis; apply/fdisjointP=> n n_in.
  move: (dis _ n_in); rewrite 2!mem_suppN=> /eqP {2}<-; apply/eqP.
  by apply/fpermE=> //; case/fsetDP: n_in.
by rewrite -e; apply/eqP/eq_in_rename=> n n_in; apply/fpermE=> //.
Qed.

Lemma eq_refl : reflexive eq.
Proof.
move=> x; apply/eqP; exists 1; first by rewrite supp1 /fdisjoint fset0I.
by rewrite rename1.
Qed.

Lemma eq_sym : symmetric eq.
Proof.
apply/symmetric_from_pre=> x y /eqP [s dis re].
apply/eqP; exists s^-1; last by rewrite -re renameK.
by rewrite supp_inv -{}re -eq_l -names_eqvar -fsetD_eqvar renameJ 1?namesfsnE.
Qed.

Lemma eq_trans : transitive eq.
Proof.
move=> z x y /eqP [s1 dis1 re1] /eqP [s2 dis2 re2].
apply/eqP.
exists (s2 * s1); last by rewrite -renameD re1.
move: {re2} dis2; rewrite -{}re1 -eq_l -names_eqvar -fsetD_eqvar.
rewrite renameJ 1?namesfsnE // => dis2.
by apply: (fdisjoint_trans (supp_mul _ _)); rewrite fdisjointUl dis2.
Qed.

Definition equivRel := Eval hnf in EquivRel eq eq_refl eq_sym eq_trans.

End Def.

End BoundEq.

Canonical BoundEq.equivRel.

Section Bound.

Local Open Scope quotient_scope.
Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable T : nominalType.
Variable l : T -> {fset name}.
Hypothesis eq_l : {eqvar l}.

CoInductive bound_type := Bound of {eq_quot BoundEq.equivRel eq_l}.

Definition quot_of_bound b := let: Bound b := b in b.

Canonical bound_newType := [newType for quot_of_bound].
Definition bound_eqMixin := [eqMixin of bound_type by <:].
Canonical bound_eqType := Eval hnf in EqType bound_type bound_eqMixin.
Definition bound_choiceMixin := [choiceMixin of bound_type by <:].
Canonical bound_choiceType :=
  Eval hnf in ChoiceType bound_type bound_choiceMixin.
Definition bound_ordMixin := [ordMixin of bound_type by <:].
Canonical bound_ordType := Eval hnf in OrdType bound_type bound_ordMixin.

Implicit Types (D : {fset name}) (x y : T).
Implicit Types (xx : bound_type).

Lemma bind_key : unit. Proof. exact: tt. Qed.
Definition bind := locked_with bind_key (fun x => Bound (\pi x)).

Lemma unbind_key : unit. Proof. exact: tt. Qed.
Local Notation unbind_def :=
  (fun D xx =>
     let x := repr (val xx) in
     rename (avoid (D :\: (names x :\: l x)) (names x)) x).
Definition unbind := locked_with unbind_key unbind_def.

Lemma unbindK D : cancel (unbind D) bind.
Proof.
case=> xx; rewrite [bind]unlock [unbind]unlock /unbind_def /=; congr Bound.
symmetry; rewrite -[LHS]reprK /=; apply/eqmodP/BoundEq.eqP.
eexists; last by eauto.
move: (repr xx)=> {xx} x.
move: (supp_avoid (D :\: (names x :\: l x)) (names x)).
rewrite ![fdisjoint (supp _) _]fdisjointC; apply: fdisjoint_trans.
apply/fsubsetP=> n /fsetDP [n_in n_nin].
by rewrite !(in_fsetD, negb_and, negb_or, negbK) /= n_in n_nin.
Qed.

Lemma unbindP D xx : fdisjoint D (l (unbind D xx)).
Proof.
case: xx=> xx; rewrite [unbind]unlock /=.
move: (repr xx) => {xx} x.
set s := avoid (D :\: (names x :\: l x)) (names x); set x' := rename _ _.
rewrite -(fsetID D (names x :\: l x)) fdisjointUl; apply/andP; split.
  apply: (fdisjoint_trans (fsubsetIr _ _)).
  suff ->: names x :\: l x = names x' :\: l x'.
    rewrite fdisjointC; apply/fdisjointP=> n n_in.
    by rewrite in_fsetD negb_and negbK n_in.
  symmetry.
  rewrite /x' -eq_l -names_eqvar -[LHS]fsetD_eqvar renameJ // namesfsnE.
  move: (supp_avoid (D :\: (names x :\: l x)) (names x)).
  rewrite ![fdisjoint (supp _) _]fdisjointC; apply: fdisjoint_trans.
  apply/fsubsetP=> n /fsetDP [n_in n_nin].
  by rewrite !(in_fsetD, negb_and, negb_or, negbK) /= n_in n_nin.
rewrite fdisjointC /x' -[l x']namesfsnE.
apply: (@fdisjoint_trans _ _ (names x')).
  by move: x'=> x'; eapply nom_finsuppP; finsupp.
rewrite /x' names_rename /s; exact: avoidP.
Qed.

Lemma bind_eqP x y : (exists2 s, fdisjoint (supp s) (names x :\: l x) &
                                 rename s x = y) <->
                     bind x = bind y.
Proof.
rewrite [bind]unlock /=; split.
  by move=> /BoundEq.eqP e; congr Bound; apply/eqmodP.
by move=> [] /eqmodP/BoundEq.eqP.
Qed.

CoInductive ubind_spec D x : T -> Prop :=
| UBindSpec s of fdisjoint (supp s) (names x :\: l x)
  & fdisjoint (supp s) D : ubind_spec D x (rename s x).

Lemma ubindP D x : fdisjoint D (l x) -> ubind_spec D x (unbind D (bind x)).
Proof.
case/esym/bind_eqP: (unbindK D (bind x)) (unbindP D (bind x))=> s dis <- disx.
pose s' := fperm s (l x).
have dis': fdisjoint (supp s') (names x :\: l x).
  apply: (fdisjoint_trans (supp_fperm s (l x))).
  rewrite fdisjointC; apply/fdisjointP=> n /fsetDP [] n_in n_nin.
  rewrite in_fsetU negb_or n_nin /=.
  have e : s n = n.
    apply/suppPn; move: dis; rewrite fdisjointC; move/fdisjointP; apply.
    by apply/fsetDP; split.
  rewrite -e mem_imfset_inj //; exact: fperm_inj.
have e: rename s x = rename s' x.
  apply/eq_in_rename=> n n_in; symmetry; rewrite /s'.
  have [n_in'|n_nin] := boolP (n \in l x).
    rewrite fpermE // => ????; exact: fperm_inj.
  by transitivity n; last symmetry; apply/suppPn; [move: dis'|move: dis];
  rewrite fdisjointC; move/fdisjointP; apply; apply/fsetDP; split.
move=> dis''; rewrite e; apply: UBindSpec=> //.
apply: (fdisjoint_trans (supp_fperm _ _)).
by rewrite fdisjointUl fdisjointC dis'' /= -renamefsE eq_l fdisjointC.
Qed.

Lemma ubindP0 x : ubind_spec fset0 x (unbind fset0 (bind x)).
Proof. exact: ubindP (fdisjoint0 _). Qed.

Definition bound_rename s xx := bind (rename s (unbind fset0 xx)).

Let bound_rename_morph s x : bound_rename s (bind x) = bind (rename s x).
Proof.
rewrite /bound_rename; case: ubindP0=> s' dis _; apply/esym/bind_eqP.
exists (s * s' * s^-1); last by rewrite -renameD renameK renameD.
by rewrite suppJ -renamefsE -eq_l -names_eqvar -fsetD_eqvar -fdisjoint_eqvar.
Qed.

Definition bound_names xx :=
  let x := unbind fset0 xx in
  names x :\: l x.

Let bound_names_morph x : bound_names (bind x) = names x :\: l x.
Proof.
rewrite /bound_names; case: ubindP0=> s' dis _.
by rewrite -eq_l -names_eqvar -fsetD_eqvar renameJ // namesfsnE.
Qed.

Lemma bound_renameD s1 s2 xx :
  bound_rename s1 (bound_rename s2 xx) =
  bound_rename (s1 * s2) xx.
Proof.
rewrite -[xx](unbindK fset0).
rewrite bound_rename_morph //= bound_rename_morph //= ?renameD.
by rewrite bound_rename_morph.
Qed.

Lemma bound_namesTeq n n' xx :
  n \in bound_names xx ->
  bound_rename (fperm2 n n') xx = xx ->
  n' \in bound_names xx.
Proof.
rewrite -[xx](unbindK fset0) bound_names_morph; set s := fperm2 n n'.
move/(mem_imfset s).
rewrite -[s @: _]renamefsE fsetD_eqvar renamefsE -names_rename.
move: {xx} (unbind _ _)=> x; rewrite bound_rename_morph {1}/s fperm2L eq_l.
by move=> n'_in e; rewrite -bound_names_morph -e bound_names_morph.
Qed.

Lemma bound_namesNNE n n' xx :
  n \notin bound_names xx ->
  n' \notin bound_names xx ->
  bound_rename (fperm2 n n') xx = xx.
Proof.
rewrite -[xx](unbindK fset0) bound_names_morph; move: (unbind _ _)=> {xx} x.
rewrite bound_rename_morph=> n_nin n'_nin; apply/esym/bind_eqP; eexists=> //.
apply: (fdisjoint_trans (fsubset_supp_fperm2 n n')).
rewrite fdisjointC !fdisjointUr !fdisjoints1 n'_nin n_nin fdisjointC.
exact: fdisjoint0.
Qed.

Definition bound_nominalMixin :=
  NominalMixin bound_renameD bound_namesNNE bound_namesTeq.
Canonical bound_nominalType :=
  Eval hnf in NominalType bound_type bound_nominalMixin.

Global Instance bind_eqvar : {eqvar bind}.
Proof. move=> ? ? _ <-; exact: bound_rename_morph. Qed.

Lemma namesbE x : names (bind x) = names x :\: l x.
Proof. exact: bound_names_morph. Qed.

Section Elim.

Variable S : nominalType.

Definition elimb D (f : T -> S) xx :=
  f (unbind D xx).

Lemma elimbE D f x :
  {finsupp D f} ->
  fdisjoint D (l x) ->
  fdisjoint (names (f x)) (l x) ->
  elimb D f (bind x) = f x.
Proof.
move=> fs_f dis dis'; rewrite /elimb.
case: (ubindP dis) => /= s dis'' dis'''.
rewrite -(fs_f s dis''') renameJ // fdisjointC.
suffices ?: fsubset (names (f x)) (D :|: names x :\: l x).
  apply: fdisjoint_trans; first by eauto.
  by rewrite fdisjointUl fdisjointC dis''' fdisjointC.
rewrite -(fsetDidPl _ _ dis') -(fsetDidPl _ _ dis) -fsetDUl fsetSD //.
by eapply nom_finsuppP; finsupp.
Qed.

End Elim.

End Bound.

Notation "{ 'bound' l }" := (@bound_type _ l _)
  (at level 0, format "{ 'bound'  l }") : type_scope.

Arguments ubindP {_ _ _ _ _} _.
Arguments bind {_ _ _} _.

Section Bound2.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T S : nominalType).
Variables (lT : T -> {fset name}) (lS : S -> {fset name}).
Hypothesis (eq_T : {eqvar lT}) (eq_S : {eqvar lS}).

Implicit Types (x : T) (y : S) (xx : {bound lT}) (yy : {bound lS}).

Definition unbind2 D xx yy :=
  let x := unbind (D :|: names yy) xx in
  let y := unbind (D :|: names x) yy in
  (x, y).

CoInductive ubind2_spec D x y : T * S -> Prop :=
| UBind2Spec s of fdisjoint (supp s) (names x :\: lT x)
  & fdisjoint (supp s) (names y :\: lS y)
  & fdisjoint (supp s) D
  : ubind2_spec D x y (rename s x, rename s y).

Lemma ubind2P D x y :
  fdisjoint D (lT x :|: lS y) ->
  fdisjoint (lT x) (names y) ->
  fdisjoint (lS y) (names x) ->
  ubind2_spec D x y (unbind2 D (bind x) (bind y)).
Proof.
rewrite fdisjointUr /unbind2=> /andP [dis_x dis_y] disxy disyx.
set xx := bind x; set yy := bind y.
have dis: fdisjoint (D :|: names yy) (lT x).
  rewrite /yy fdisjointUl dis_x /=.
  move: disxy; rewrite fdisjointC; apply: fdisjoint_trans.
  by eapply nom_finsuppP; finsupp.
case: (ubindP dis)=> s1 dis_s1; rewrite fdisjointUr.
case/andP => dis_s1D dis_s1_yy.
rewrite -(renameJ dis_s1_yy) /yy bind_eqvar.
have dis': fdisjoint (D :|: names (rename s1 x)) (lS (rename s1 y)).
  rewrite -(@renameJ _ s1 D) ?namesfsnE // -names_eqvar -fsetU_eqvar -eq_S.
  by rewrite -fdisjoint_eqvar fdisjointUl dis_y fdisjointC.
case: (ubindP dis') => /= s2 dis_s2; rewrite fdisjointUr.
case/andP=> dis_s2D dis_s2_x.
rewrite -(renameJ dis_s2_x) !renameD.
apply: UBind2Spec.
- apply: (fdisjoint_trans (supp_mul _ _)).
  rewrite fdisjointUl dis_s1 andbT; rewrite -[_ :\: _]namesfsnE in dis_s1.
  rewrite -(renameJ dis_s1) fsetD_eqvar names_eqvar eq_T.
  rewrite fdisjointC; move: dis_s2_x; rewrite fdisjointC.
  by apply: fdisjoint_trans; rewrite fsubDset fsubsetUr.
- apply: (fdisjoint_trans (supp_mul s2 s1)); rewrite fdisjointUl.
  rewrite /yy namesbE in dis_s1_yy; rewrite dis_s1_yy.
  rewrite -eq_S -names_eqvar -fsetD_eqvar renameJ ?namesfsnE // in dis_s2.
  by rewrite dis_s2.
by apply: (fdisjoint_trans (supp_mul s2 s1)); rewrite fdisjointUl dis_s2D.
Qed.

Lemma ubind2P0 x y :
  fdisjoint (lT x) (names y) ->
  fdisjoint (lS y) (names x) ->
  ubind2_spec fset0 x y (unbind2 fset0 (bind x) (bind y)).
Proof. exact: ubind2P (fdisjoint0 _). Qed.

End Bound2.

Section TrivialNominalType.

Variable T : trivialNominalType.
Variable l : T -> {fset name}.
Hypothesis eq_l : {eqvar l}.

Let bound_renameT s (xx : {bound l}) : rename s xx = xx.
Proof.
rewrite -(unbindK fset0 xx) bind_eqvar renameJ // namesT.
by rewrite fdisjointC fdisjoint0.
Qed.

Canonical bound_trivialNominalType :=
  Eval hnf in TrivialNominalType (bound_type eq_l)
                                 (TrivialNominalMixin bound_renameT).

End TrivialNominalType.

Module Restriction.

Section ClassDef.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Record law (T : nominalType) (hide : {fset name} -> T -> T) := Law {
  _ : {eqvar hide};
  _ : forall A x, hide A x = hide (A :&: names x) x;
  _ : forall A1 A2 x, hide A1 (hide A2 x) = hide (A1 :|: A2) x;
  _ : forall x, hide fset0 x = x;
  _ : forall A x, fdisjoint A (names (hide A x))
}.

Record mixin_of (T : nominalType) := Mixin {
  hide : {fset name} -> T -> T;
  _ : law hide
}.

Record class_of T :=
  Class {base : Nominal.class_of T; mixin : mixin_of (Nominal.Pack base T)}.
Local Coercion base : class_of >-> Nominal.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Nominal.Pack T b0 T)) :=
  fun bT b & phant_id (Nominal.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition ordType := @Ord.Total.Pack cT xclass xT.
Definition nominalType := @Nominal.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Nominal.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion ordType : type >-> Ord.Total.type.
Canonical ordType.
Coercion nominalType : type >-> Nominal.type.
Canonical nominalType.
Notation restrType := type.
Notation restrMixin := mixin_of.
Notation RestrMixin := Mixin.
Notation RestrType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'restrType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'restrType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'restrType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'restrType'  'of'  T ]") : form_scope.
End Exports.

End Restriction.
Export Restriction.Exports.

Section RestrictionTheory.

Variable T : restrType.

Local Open Scope fset_scope.

Implicit Types (A : {fset name}) (x : T).

Definition hide A x : T :=
  Restriction.hide (Restriction.class T) A x.

Global Instance hide_eqvar : {eqvar hide}.
Proof. by rewrite /hide; case: T=> [? [? [? []]] ?]. Qed.

Lemma hideI A x : hide A x = hide (A :&: names x) x.
Proof. by rewrite /hide; move: A x; case: T=> [? [? [? []]] ?]. Qed.

Lemma hideU A1 A2 x : hide A1 (hide A2 x) = hide (A1 :|: A2) x.
Proof. by rewrite /hide; move: A1 A2 x; case: T=> [? [? [? []]] ?]. Qed.

Lemma hide0 x : hide fset0 x = x.
Proof. by rewrite /hide; move: x; case: T=> [? [? [? []]] ?]. Qed.

Lemma hideP A x : fdisjoint A (names (hide A x)).
Proof. by rewrite /hide; move: A x; case: T => [? [? [? []]] ?]. Qed.

End RestrictionTheory.

Section OptionRestriction.

Variable T : restrType.

Definition option_hide A := @omap T _ (hide A).

Lemma option_hide_law : Restriction.law option_hide.
Proof.
rewrite /option_hide; constructor=> /=.
- finsupp.
- by move=> A [x|] //=; rewrite hideI.
- by move=> A1 A2 [x|] //=; rewrite hideU.
- by move=> [x|] //=; rewrite hide0.
- move=> A [x|] //=; rewrite ?hideP 1?fdisjointC //; exact: fdisjoint0.
Qed.

Definition option_restrMixin := RestrMixin option_hide_law.
Canonical option_restrType :=
  Eval hnf in RestrType (option T) option_restrMixin.

End OptionRestriction.

Module Type FreeRestrictionSig.

Implicit Types (A : {fset name}) (T S : nominalType).

Local Open Scope fset_scope.

Parameter restr_of : forall T, phant T -> restrType.

Notation "{ 'restr' T }" := (@restr_of _ (Phant T))
  (at level 0, format "{ 'restr'  T }") : type_scope.

Parameter Restr0 : forall T, T -> {restr T}.

Parameter Restr0_eqvar : forall T, {eqvar (@Restr0 T)}.

Parameter namesrE : forall T (x : T), names (Restr0 x) = names x.

Parameter names_hider :
  forall T A (xx : {restr T}), names (hide A xx) = names xx :\: A.

Parameter restr_eqP :
  forall T A1 (x1 : T) A2 (x2 : T),
  (exists2 s, fdisjoint (supp s) (names x1 :\: A1) &
              (rename s (A1 :&: names x1), rename s x1) =
              (A2 :&: names x2, x2))
  <-> hide A1 (Restr0 x1) = hide A2 (Restr0 x2).

CoInductive restr_spec T A : {restr T} -> Prop :=
| RestrSpec A' x of fdisjoint A A' & fsubset A' (names x)
  : restr_spec A (hide A' (Restr0 x)).

Parameter restrP : forall T A (xx : {restr T}), restr_spec A xx.

Parameter elimr :
  forall (T S : nominalType),
    {fset name} -> ({fset name} -> T -> S) -> {restr T} -> S.

Parameter elimrE :
  forall (T S : nominalType) A (f : {fset name} -> T -> S) A' x,
    {finsupp A f} ->
    fdisjoint A A' ->
    fdisjoint (names (f A' x)) A' ->
    fsubset A' (names x) ->
    elimr A f (hide A' (Restr0 x)) = f A' x.

End FreeRestrictionSig.

Module Export FreeRestriction : FreeRestrictionSig.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Section Def.

Variable T : nominalType.

Implicit Types (A : {fset name}) (x : T).

Record prerestr := PreRestr_ {
  prval :> {fset name} * T;
  _ : fsubset prval.1 (names prval.2)
}.

Lemma prerestr_eqvar :
  {eqvar (fun p : {fset name} * T => fsubset p.1 (names p.2))}.
Proof. by move=> /= s p1 p2 p1p2; finsupp. Qed.

Canonical prerestr_subType := Eval hnf in [subType for prval].
Definition prerestr_eqMixin := [eqMixin of prerestr by <:].
Canonical prerestr_eqType := Eval hnf in EqType prerestr prerestr_eqMixin.
Definition prerestr_choiceMixin := [choiceMixin of prerestr by <:].
Canonical prerestr_choiceType :=
  Eval hnf in ChoiceType prerestr prerestr_choiceMixin.
Definition prerestr_ordMixin := [ordMixin of prerestr by <:].
Canonical prerestr_ordType := Eval hnf in OrdType prerestr prerestr_ordMixin.
Canonical prerestr_subNominalType :=
  Eval hnf in SubNominalType prerestr prerestr_eqvar.
Definition prerestr_nominalMixin := [nominalMixin of prerestr by <:].
Canonical prerestr_nominalType :=
  Eval hnf in NominalType prerestr prerestr_nominalMixin.

Definition PreRestr A x :=
  nosimpl (@PreRestr_ (A :&: names x, x) (fsubsetIr _ _)).

Global Instance PreRestr_eqvar : {eqvar PreRestr}.
Proof. by move=> s A _ <- x _ <-; eapply nomR_Sub; finsupp. Qed.

Definition prerestr_op (p : prerestr) := (val p).1.

Global Instance prerestr_op_eqvar : {eqvar prerestr_op}.
Proof. by move=> s p1 p2 p1p2; rewrite /prerestr_op; finsupp. Qed.

Definition restr_type := {bound prerestr_op}.

Canonical restr_eqType := [eqType of restr_type].
Canonical restr_choiceType := [choiceType of restr_type].
Canonical restr_ordType := [ordType of restr_type].
Canonical restr_nominalType := [nominalType of restr_type].

Implicit Types (s : {fperm name}) (xx : restr_type).

Definition restr A x : restr_type :=
  bind (PreRestr A x).

Lemma restrI A x : restr A x = restr (A :&: names x) x.
Proof.
rewrite /restr; congr bind; apply: val_inj=> /=.
by rewrite -fsetIA fsetIid.
Qed.

Lemma restr_eqP_int A1 x1 A2 x2 :
  (exists2 s, fdisjoint (supp s) (names x1 :\: A1) &
              (rename s (A1 :&: names x1), rename s x1) =
              (A2 :&: names x2, x2))
  <-> restr A1 x1 = restr A2 x2.
Proof.
rewrite /restr -bind_eqP /= /prerestr_op /=; split.
  case=> s dis [e1 e2]; exists s.
    rewrite subnamesE /= fsetDUl /= namesfsnE fsetDv fset0U.
    by rewrite fsetDIr fsetDv fsetU0.
  by apply/val_inj=> /=; rewrite pair_eqvar /= e1 e2.
rewrite !subnamesE /= namespE /= fsetDUl /= namesfsnE fsetDv fset0U.
rewrite fsetDIr fsetDv fsetU0=> - [s dis /(congr1 val) /= <-].
by exists s.
Qed.

CoInductive urestr_spec D A x : {fset name} * T -> Prop :=
| URestrSpec s of fdisjoint D (rename s A)
  & fdisjoint (supp s) (names x :\: A)
  & fdisjoint (supp s) D
  : urestr_spec D A x (rename s A, rename s x).

Lemma urestrP D A x :
  fdisjoint D A ->
  fsubset A (names x) ->
  urestr_spec D A x (val (unbind D (restr A x))).
Proof.
move=> dis /fsetIidPl e; move: (unbindP D (restr A x)); rewrite /restr /=.
case: ubindP; first by rewrite /= /prerestr_op /= e.
move=> //= s; rewrite subnamesE /prerestr_op pair_eqvar /= e.
rewrite {1}/names /= fsetDUl /= namesfsnE fsetDv fset0U.
move=> dis_s sub disD; exact: URestrSpec.
Qed.

Lemma urestrP0 A x :
  fsubset A (names x) ->
  urestr_spec fset0 A x (val (unbind fset0 (restr A x))).
Proof. exact: urestrP (fdisjoint0 _). Qed.

CoInductive restr_spec_int D : restr_type -> Prop :=
| RestrSpecInt A x of fdisjoint D A & fsubset A (names x)
  : restr_spec_int D (restr A x).

Lemma restrP_int D xx : restr_spec_int D xx.
Proof.
rewrite -[xx](unbindK D).
case: (unbind _ _) (unbindP D xx) => {xx} - [A x] /= sub dis.
rewrite (_ : bind _ = restr A x); first exact: RestrSpecInt.
rewrite /restr; congr bind; apply: val_inj=> /=; congr pair.
by apply/esym/fsetIidPl.
Qed.

Lemma namesrE_int A x : names (restr A x) = names x :\: A.
Proof.
rewrite -[RHS]fset0U -(fsetDv (names x)) -fsetDIr fsetIC restrI.
move: (A :&: names x) (fsubsetIr A (names x))=> {A} A subA.
rewrite /restr namesbE /= /prerestr_op /= subnamesE fsetDUl /=.
by rewrite namesfsnE fsetDv fset0U fsetIC fsetDIr fsetDv fset0U.
Qed.

Instance restr_eqvar : {eqvar restr}.
Proof. by move=> s A _ <- x _ <-; rewrite /restr; finsupp. Qed.

Definition restr_hide A xx :=
  let: (A', x) := val (unbind fset0 xx) in
  restr (A :|: A') x.

Lemma restr_hideE A A' x : restr_hide A (restr A' x) = restr (A :|: A') x.
Proof.
rewrite /restr_hide (restrI A') (restrI (_ :|: _)) fsetIUl.
move: (A' :&: names x) (fsubsetIr A' (names x)) => {A'} A' subA'.
case: (urestrP0 subA')=> s _ dis sub.
rewrite -{1}(renameKV s A) -fsetU_eqvar -restr_eqvar renameJ; last first.
  rewrite namesrE_int fsetUC fdisjointC; rewrite fdisjointC in dis.
  by apply: fdisjoint_trans dis; rewrite -fsetDDl fsubDset fsubsetUr.
rewrite [LHS]restrI fsetIUl (fsetIidPl _ _ subA') -(fsetID (names x) A').
rewrite ![_ :|: _ :\: _]fsetUC !fsetIUr -!fsetUA !fsetIA.
rewrite !(fsetUidPr _ _ (fsubsetIr _ A')) -[_ :&: _](renameK s) fsetI_eqvar.
rewrite renameKV [rename s _]renameJ ?namesfsnE // renameJ //.
rewrite supp_inv fdisjointC namesfsnE; rewrite fdisjointC in dis.
apply: fdisjoint_trans dis; exact: fsubsetIr.
Qed.

Lemma restr_hide_law : Restriction.law restr_hide.
Proof.
constructor.
- move=> s A _ <- xx _ <-; case/(restrP_int fset0): xx=> A' x _ sub.
  by rewrite !(restr_eqvar, restr_hideE); finsupp.
- move=> A; case/(restrP_int fset0)=> A' x _ sub; rewrite !restr_hideE.
  rewrite namesrE_int [LHS]restrI fsetIUl (fsetIidPl _ _ sub); congr restr.
  rewrite -{1}(fsetID (names x) A') [in A :&: _]fsetUC fsetIUr -fsetUA.
  by rewrite fsetIA (fsetUidPr _ _ (fsubsetIr _ _)).
- move=> A1 A2; case/(restrP_int fset0)=> A'' x _ _.
  by rewrite !restr_hideE fsetUA.
- by case/(restrP_int fset0)=> A x _ sub; rewrite restr_hideE fset0U.
move=> A; case/(restrP_int fset0)=> A' x _ sub.
rewrite restr_hideE namesrE_int fdisjointC; apply/fsetDidPl.
by rewrite fsetDDl -fsetUA [A' :|: _]fsetUC fsetUA fsetUid.
Qed.

Definition restr_restrMixin := RestrMixin restr_hide_law.
Definition restr_of of phant T := RestrType restr_type restr_restrMixin.
Notation "{ 'restr' T }" := (restr_of (Phant T))
  (at level 0, format "{ 'restr'  T }") : type_scope.

Definition Restr0 x : {restr T} := restr fset0 x.

Lemma Restr0_eqvar : {eqvar Restr0}.
Proof. by rewrite /Restr0; finsupp. Qed.

Lemma namesrE x : names (Restr0 x) = names x.
Proof. by rewrite /Restr0 namesrE_int fsetD0. Qed.

Lemma names_hider A (xx : {restr T}) : names (hide A xx) = names xx :\: A.
Proof.
case/(restrP_int fset0): xx=> A' x _ sub.
by rewrite /hide /= restr_hideE !namesrE_int fsetDDl fsetUC.
Qed.

Lemma restr_eqP :
  forall A1 x1 A2 x2,
  (exists2 s, fdisjoint (supp s) (names x1 :\: A1) &
              (rename s (A1 :&: names x1), rename s x1) =
              (A2 :&: names x2, x2))
  <-> hide A1 (Restr0 x1) = hide A2 (Restr0 x2).
Proof.
by move=> ????; rewrite restr_eqP_int /Restr0 /hide /= !restr_hideE !fsetU0.
Qed.

CoInductive restr_spec A : {restr T} -> Prop :=
| RestrSpec A' x of fdisjoint A A' & fsubset A' (names x)
  : restr_spec A (hide A' (Restr0 x)).

Lemma restrP A (xx : {restr T}) : restr_spec A xx.
Proof.
case/(restrP_int A): xx=> A' x dis sub.
rewrite -[A']fsetU0 -restr_hideE; exact: RestrSpec.
Qed.

Definition elimr (S : nominalType) A (f : {fset name} -> T -> S)
  (xx : {restr T}) :=
  elimb A (fun p => f (val p).1 (val p).2) xx.

Lemma elimrE (S : nominalType) A (f : {fset name} -> T -> S) A' x :
  {finsupp A f} ->
  fdisjoint A A' ->
  fdisjoint (names (f A' x)) A' ->
  fsubset A' (names x) ->
  elimr A f (hide A' (Restr0 x)) = f A' x.
Proof.
move=> fs_f dis1 dis2 sub.
rewrite /elimr /restr /Restr0 /hide /= restr_hideE fsetU0.
by rewrite elimbE /prerestr_op /= ?(fsetIidPl _ _ sub).
Qed.

End Def.

End FreeRestriction.

Notation "{ 'restr' T }" := (restr_of (Phant T))
  (at level 0, format "{ 'restr'  T }") : type_scope.

Section TrivialFreeRestriction.

Variable (T : trivialNominalType).

Implicit Types (s : {fperm name}) (A : {fset name}) (x : T) (xx : {restr T}).

Lemma restr_renameT s xx : rename s xx = xx.
Proof.
case/(restrP fset0): xx => A x _.
rewrite namesT fsubset0 => /eqP ->.
by rewrite hide0 Restr0_eqvar renameT.
Qed.

Definition restr_trivialNominalMixin :=
  TrivialNominalMixin restr_renameT.
Canonical restr_trivialNominalType :=
  Eval hnf in TrivialNominalType {restr T} restr_trivialNominalMixin.

(* FIXME: This should be generalizable to any trivial nominal type with a
   restriction structure *)
Lemma hideT A (xx : {restr T}) : hide A xx = xx.
Proof. by rewrite hideI namesT fsetI0 hide0. Qed.

End TrivialFreeRestriction.

Section BindR.

Local Open Scope fset_scope.

Variables (T : nominalType) (S : restrType).

Implicit Types (A : {fset name}) (x : T) (xx : {restr T}) (f : T -> S).

Definition bindr A (f : T -> S) (xx : {restr T}) :=
  elimr A (fun A' x => hide A' (f x)) xx.

(* FIXME: The hypothesis on f should not be needed *)
Lemma bindr_Restr0 A f x :
  {finsupp A f} ->
  bindr A f (Restr0 x) = f x.
Proof.
move=> fs_f.
by rewrite /bindr -[Restr0 x]hide0 elimrE ?hide0 ?fsub0set
           1?fdisjointC ?fdisjoint0.
Qed.

Lemma bindrE A f A' x :
  {finsupp A f} ->
  fdisjoint A A' ->
  bindr A f (hide A' (Restr0 x)) = hide A' (f x).
Proof.
move=> fs_f dis; rewrite /bindr.
have dis': fdisjoint A (A' :&: names x).
  rewrite fdisjointC; move: dis; rewrite fdisjointC.
  by apply: fdisjoint_trans; rewrite fsubsetIl.
have sub : fsubset (names (f x)) (A :|: names x).
  by eapply nom_finsuppP; finsupp.
rewrite hideI [RHS]hideI namesrE elimrE // 1?fdisjointC ?hideP ?fsubsetIr //.
rewrite [LHS]hideI -fsetIA (fsetIC (names x)) fsetIA.
congr hide; apply: fsetIidPl; apply: fsubset_trans (fsubsetIr A' _).
apply: (fsubset_trans (fsetIS A' sub)).
rewrite -[_ :&: names x]fset0U -(fdisjoint_fsetI0 dis) (fsetIC A).
by rewrite -fsetIUr fsetIS // fsubsetxx.
Qed.

Lemma hide_bindr A f A' xx :
  {finsupp A f} ->
  fdisjoint A A' ->
  hide A' (bindr A f xx) = bindr A f (hide A' xx).
Proof.
move=> fs_f disA; case/(restrP A): xx=> [A'' x disA'' sub].
by rewrite hideU !bindrE // 1?fdisjointUr ?disA // hideU.
Qed.

Lemma bindr_irrel A1 A2 f xx :
  {finsupp A1 f} ->
  {finsupp A2 f} ->
  bindr A1 f xx = bindr A2 f xx.
Proof.
case/(restrP (A1 :|: A2)): xx=> A x.
rewrite fdisjointUl=> /andP [dis1 dis2] sub fs1 fs2.
by rewrite !bindrE //.
Qed.

(* FIXME: This is not exactly a lemma about equivariance. *)

Global Instance bindr_eqvar A f : {finsupp A f} -> {finsupp A (bindr A f)}.
Proof.
move=> fs_f s dis xx _ <-; case: xx /(restrP A)=> [A' x dis' sub].
rewrite hide_eqvar Restr0_eqvar !bindrE //; first by finsupp.
by rewrite -[A](@renameJ _ s) ?namesfsnE // -1?fdisjoint_eqvar.
Qed.

End BindR.

Lemma names_hide (T : restrType) A (x : T) :
  fsubset (names (hide A x)) (names x :\: A)%fset.
Proof.
rewrite -[names x]namesrE -names_hider.
rewrite (_ : hide A x = bindr fset0 id (hide A (Restr0 x))).
  by eapply nom_finsuppP; move: (hide _ _) => xx; finsupp.
by rewrite bindrE // fdisjoint0.
Qed.

Section Iso.

Variable T : nominalType.

Definition orestr (xx : {restr option T}) : option {restr T} :=
  bindr fset0 (omap (@Restr0 T)) xx.

Lemma orestr_hide A xx : orestr (hide A xx) = hide A (orestr xx).
Proof. by rewrite /orestr hide_bindr ?fdisjoint0. Qed.

Lemma orestrE A x : orestr (hide A (Restr0 x)) = hide A (omap (@Restr0 T) x).
Proof. by rewrite /orestr bindrE ?fdisjoint0. Qed.

Lemma rename_orestr : {eqvar orestr}.
Proof. move=> s x _ <-; rewrite /orestr; finsupp. Qed.

End Iso.

Section Mapr.

Variables T S : nominalType.
Variables (A : {fset name}) (f : T -> S).
Implicit Types (x : T) (xx : {restr T}).

Definition mapr := bindr A (fun x => Restr0 (f x)).

Lemma maprE :
  {finsupp A f} ->
  forall A' x, fdisjoint A A' ->
              mapr (hide A' (Restr0 x)) = hide A' (Restr0 (f x)).
Proof. by move=> fs_f A' x dis; rewrite /mapr bindrE ?hiderE ?fsetU0. Qed.

End Mapr.

Section MaprProperties.

Variables T S R : nominalType.

Lemma mapr_id D (xx : {restr T}) : mapr D id xx = xx.
Proof. by case: xx / (restrP D)=> [A x dis sub]; rewrite maprE. Qed.

Lemma mapr_comp D (g : S -> R) (f : T -> S) xx :
  {finsupp D g} -> {finsupp D f} ->
  mapr D (g \o f) xx = mapr D g (mapr D f xx).
Proof.
by move=> fs_g fs_f; case: xx / (restrP D)=> [A x dis sub]; rewrite !maprE.
Qed.

Lemma hide_mapr D A (f : T -> S) xx :
  {finsupp D f} ->
  fdisjoint D A ->
  hide A (mapr D f xx) = mapr D f (hide A xx).
Proof. by move=> fs_f dis; rewrite /mapr hide_bindr. Qed.

Lemma mapr_irrel D1 D2 (f : T -> S) xx :
  {finsupp D1 f} ->
  {finsupp D2 f} ->
  mapr D1 f xx = mapr D2 f xx.
Proof.
move=> fs1 fs2; rewrite /mapr; eapply bindr_irrel=> [{fs2}|{fs1}]; finsupp.
Qed.

(* FIXME: This is not exactly about equivariance. *)
Global Instance mapr_eqvar D (f : T -> S) :
  {finsupp D f} -> {finsupp D (mapr D f)}.
Proof. move=> fs_f; rewrite /mapr; finsupp. Qed.

End MaprProperties.

Section New.

Local Open Scope fset_scope.

Variable T : restrType.

Implicit Types (A : {fset name}) (f : name -> T) (n : name).

Definition new D f := hide (fset1 (fresh D)) (f (fresh D)).

Lemma newE D f n :
  {finsupp D f} -> n \notin D -> new D f = hide (fset1 n) (f n).
Proof.
move=> n_nin_D fs_f; rewrite /new.
move: (fresh _) (freshP D)=> n' n'_nin_D.
pose s := fperm2 n' n.
have dis: finsupp_perm D s.
  rewrite /finsupp_perm (fdisjoint_trans (fsubset_supp_fperm2 _ _)) //.
  by apply/fdisjointP=> n'' /fset2P [->|->] {n''} //.
rewrite -{1 2}(fperm2R n' n : rename s n = n') -hide_eqvar namesnE.
rewrite ?renameJ // fdisjointC.
apply: fdisjoint_trans.
  apply: names_hide.
suff sub': fsubset (names (f n) :\ n) D.
  apply: fdisjoint_trans; first exact: sub'.
  rewrite fdisjointC; exact: dis.
by rewrite fsubD1set fsetUC -namesnE; eapply nom_finsuppP; finsupp.
Qed.

Lemma new_irrel D1 D2 f :
  {finsupp D1 f} -> {finsupp D2 f} -> new D1 f = new D2 f.
Proof.
move: (fresh _) (freshP (D1 :|: D2)) => n.
rewrite in_fsetU => /norP [nin1 nin2] fs1 fs2.
by rewrite (newE fs1 nin1) (newE fs2 nin2).
Qed.

Lemma new_const xx : new (names xx) (fun _ => xx) = xx.
Proof.
rewrite (newE _ (freshP (names xx))).
rewrite hideI -[RHS]hide0; congr hide.
by apply: fdisjoint_fsetI0; rewrite fdisjointC fdisjoints1 freshP.
Qed.

Lemma new_eqvar s A1 A2 f1 f2 :
  nomR s A1 A2 ->
  {finsupp A1 f1} ->
  nomR s f1 f2 ->
  nomR s (new A1 f1) (new A2 f2).
Proof.
move=> <- {A2} fs_f1 f1f2; move: (fresh _) (freshP A1) => n nin1.
have nin2: rename s n \notin rename s A1.
  rewrite renamefsE renamenE mem_imfset_inj //.
  exact: fperm_inj.
by rewrite (newE _ nin1) (newE _ nin2); finsupp.
Qed.

End New.

Section Trivial.

Variable T : trivialNominalType.

Definition expose (xx : {restr T}) : T :=
  elimr fset0 (fun _ x => x) xx.

Lemma exposeE A x : expose (hide A (Restr0 x)) = x.
Proof.
rewrite /expose hideI namesrE namesT fsetI0 elimrE 1?fdisjointC ?fdisjoint0 //.
exact: fsub0set.
Qed.

Lemma rename_expose : {eqvar expose}.
Proof.
move=> s x _ <-; case: x / (restrP fset0) => /= [A x _ _].
by rewrite !exposeE hide_eqvar Restr0_eqvar exposeE.
Qed.

End Trivial.

Section OExpose.

Variable T : nominalType.

Definition oexpose (xx : {restr T}) : option T :=
  elimr fset0 (fun A x => if A == fset0 then Some x else None) xx.

Lemma oexposeE A x :
  oexpose (hide A (Restr0 x)) =
  if fdisjoint A (names x) then Some x else None.
Proof.
rewrite hideI namesrE /oexpose /fdisjoint; move: (fsubsetIr A (names x))=> sub.
rewrite elimrE ?fdisjoint0 //.
case: (fsetI _ _ =P fset0) => /= [->|]; last by rewrite fdisjoint0.
by rewrite fdisjointC fdisjoint0.
Qed.

Global Instance oexpose_eqvar : {eqvar oexpose}.
Proof.
move=> s xx _ <-; case: xx / (restrP fset0) => [A x _].
by rewrite hide_eqvar Restr0_eqvar !oexposeE; finsupp.
Qed.

End OExpose.
