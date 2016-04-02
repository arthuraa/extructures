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

Lemma names0P x : reflect (forall s, rename s x = x) (names x == fset0).
Proof.
apply/(iffP eqP).
  by move=> eq0 s; rewrite names_disjointE // eq0 fdisjointC fdisjoint0.
move=> reE; apply/eqP; rewrite eqEfsubset fsub0set andbT.
apply/fsubsetP=> n inN; move: (reE (fperm2 n (fresh (names x)))).
by move/(namesTeq inN); apply/contraTT; rewrite freshP.
Qed.

Lemma eq_in_rename s1 s2 x :
  {in names x, s1 =1 s2} ->
  rename s1 x = rename s2 x.
Proof.
move=> e; apply: (canRL (renameKV s2)); rewrite renameD.
apply/names_disjointE/fdisjointP=> n; rewrite mem_supp fpermM /=.
by rewrite (can2_eq (fpermKV s2) (fpermK _)); apply/contra=> /e ->.
Qed.

(* FIXME: It would be better to state the right-hand side with rename
   instead *)

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

Section Equivariance.

Variables T S : nominalType.

Implicit Types (s : {fperm name}) (x : T) (f : T -> S).

Definition equivariant f :=
  forall s x, rename s (f x) = f (rename s x).

(* FIXME: rename this *)

Lemma names_disjoint' ns f x :
  (forall s, fdisjoint (supp s) ns ->
             rename s (f x) = f (rename s x)) ->
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

Lemma equivariant_names f :
  equivariant f ->
  forall x, fsubset (names (f x)) (names x).
Proof.
move=> equi x; rewrite -[names x]fset0U; apply: names_disjoint'=> s _.
by rewrite equi.
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
move=> fs_f; apply names_disjoint'=> s dis; exact: fs_f.
Qed.

Lemma const_finsupp y : finsupp (names y) (fun _ => y).
Proof. by move=> s dis x /=; rewrite names_disjointE. Qed.

Lemma equivariant_finsupp f : equivariant f <-> finsupp fset0 f.
Proof.
split=> [equi_f|fs_f].
  by move=> s _ x; rewrite equi_f.
by move=> s x; rewrite fs_f.
Qed.

Lemma finsuppJ A f (s : {fperm name}) :
  finsupp A f ->
  finsupp (s @: A) (rename s \o f \o rename s^-1).
Proof.
move=> fs_f s' dis x /=; apply/(canRL (renameKV s)).
rewrite -{2}(renameKV s x); move: (rename s^-1 x)=> {x} x.
rewrite !renameD; apply: fs_f; rewrite -{2}(fperm_invK s) suppJ.
apply/eqP; rewrite -(imfsetK (fpermK s) A) -imfsetI; last first.
  by move=> ?? _ _; apply: fperm_inj.
by move/eqP: dis=> ->; rewrite imfset0.
Qed.

Structure eqvar_type := Eqvar {
  eqvar_fun :> T -> S;
  _ : equivariant eqvar_fun
}.

Definition eqvar_of of phant (T -> S) := eqvar_type.
Identity Coercion type_of_eqvar_of : eqvar_of >-> eqvar_type.

Lemma eqvarE (f : eqvar_type) : equivariant f.
Proof. by case: f. Qed.

End Equivariance.

Section Composition.

Variables (T S R : nominalType).

Lemma finsupp_comp ns ns' (g : S -> R) (f : T -> S) :
  finsupp ns g -> finsupp ns' f -> finsupp (ns :|: ns') (g \o f).
Proof.
move=> fs_f fs_g s; rewrite fdisjointUr=> /andP [dis1 dis2] x.
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

Notation "{ 'eqvar' T }" := (@eqvar_of _ _ (Phant T))
  (at level 0, format "{ 'eqvar'  T }") : type_scope.

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

Section TrivialNominalTheory.

Variable T : trivialNominalType.
Implicit Type (x : T).

Lemma renameT : forall s x, rename s x = x.
Proof. by case: (T)=> [? [[? ? []]]]. Qed.

Lemma namesT : forall x, names x = fset0.
Proof. move=> x; apply/eqP/names0P=> s; exact: renameT. Qed.

End TrivialNominalTheory.

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

Lemma renamepE s p : rename s p = (rename s p.1, rename s p.2).
Proof. by []. Qed.

Lemma rename_fst s p : rename s (fst p) = fst (rename s p).
Proof. by []. Qed.

Lemma rename_snd s p : rename s (snd p) = snd (rename s p).
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

Lemma renames_nth s d xs n :
  rename s (nth d xs n) = nth (rename s d) (rename s xs) n.
Proof.
rewrite !renamesE; have [in_xs|nin] := boolP (n < size xs).
  by rewrite (nth_map d).
by rewrite -leqNgt in nin; rewrite 2?nth_default // size_map.
Qed.

Lemma namessE xs :
  names xs = foldr fsetU fset0 [seq names x | x <- xs].
Proof.
rewrite {1}/names /= /seq_names; elim: xs=> [|x xs IH].
  by rewrite big_nil.
by rewrite big_cons IH.
Qed.

Lemma namess0 : names [::] = fset0.
Proof. by rewrite namessE. Qed.

Lemma namess1 x xs : names (x :: xs) = names x :|: names xs.
Proof. by rewrite 2!namessE. Qed.

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

End OptionNominalType.

Lemma rename_omap T' S' f : @equivariant T' S' f -> equivariant (omap f).
Proof.
by move=> equi_f s [x|] //=; rewrite renameoE /= equi_f.
Qed.

Section OptionTrivial.

Variable T' : trivialNominalType.

Let trivial_rename : forall s (x : option T'), rename s x = x.
Proof. by move=> s [x|]; rewrite renameoE //= renameT. Qed.

Canonical option_trivialNominalType :=
  TrivialNominalType (option T') (TrivialNominalMixin trivial_rename).

End OptionTrivial.

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

Lemma renamefs0 s : rename s (@fset0 T') = fset0.
Proof. exact: imfset0. Qed.

Lemma renamefs1 s x : rename s (fset1 x) = fset1 (rename s x).
Proof. exact: imfset1. Qed.

Lemma renamefsU s X Y : rename s (X :|: Y) = rename s X :|: rename s Y.
Proof. exact: imfsetU. Qed.

Lemma renamefsU1 s x X : rename s (x |: X) = rename s x |: rename s X.
Proof. by rewrite fsetU1E renamefsU renamefs1. Qed.

Lemma renamefsI s X Y : rename s (X :&: Y) = rename s X :&: rename s Y.
Proof. apply: imfsetI=> ????; exact: rename_inj. Qed.

Lemma renamefsD s X Y : rename s (X :\: Y) = rename s X :\: rename s Y.
Proof.
apply/eq_fset=> x.
by rewrite !(mem_imfset_can _ _ (renameK s) (renameKV s), in_fsetD).
Qed.

Lemma renamefs_disjoint s X Y :
  fdisjoint X Y = fdisjoint (rename s X) (rename s Y).
Proof.
rewrite /fdisjoint -renamefsI -{2}[fset0](renameKV s) [rename _ fset0]imfset0.
(* FIXME: This annotation should not be needed... *)
rewrite inj_eq //=; exact: (@rename_inj fset_nominalType).
Qed.

Lemma renamefs_subset s X Y :
  fsubset X Y = fsubset (rename s X) (rename s Y).
Proof.
apply/idP/idP; first exact: imfsetS.
rewrite -{2}(renameK s X) -{2}(renameK s Y); exact: imfsetS.
Qed.

End SetNominalType.

Lemma namesfsnE (A : {fset name}) : names A = A.
Proof.
apply/eq_fset=> n; apply/namesfsP=> /=; have [inA|ninA] := boolP (n \in A).
  by exists n=> //; apply/namesnP.
by case=> [n' inA /namesnP nn']; move: ninA; rewrite nn' inA.
Qed.

Section SetTrivialNominalType.

Variable T' : trivialNominalType.

Let trivial_rename s (xs : {fset T'}) : rename s xs = xs.
Proof.
by rewrite -[RHS]imfset_id renamefsE; apply/eq_imfset=> x; rewrite renameT.
Qed.

Canonical fset_trivialNominalType :=
  Eval hnf in TrivialNominalType {fset T'}
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

Lemma namesm_empty : names emptym = fset0.
Proof.
by rewrite namesmE domm0 codomm0 !namesfsE !big_nil fsetUid.
Qed.

Lemma renamem_empty s : rename s emptym = emptym.
Proof.
by move: s; apply/names0P/eqP/namesm_empty.
Qed.

Lemma renamem_mkpartmap s kvs :
  rename s (mkpartmap kvs) =
  mkpartmap (rename s kvs) :> {partmap T -> S}.
Proof.
elim: kvs=> [|[k v] kvs IH] /=; first by rewrite renamem_empty.
by rewrite renamem_set IH.
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

Lemma renamem_mkpartmapfp s f ks :
  rename s (mkpartmapfp f ks) =
  mkpartmapfp (fun k => rename s (f (rename s^-1 k))) (rename s ks).
Proof.
apply/eq_partmap=> k; rewrite renamemE 2!mkpartmapfpE.
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

Lemma renamem_partmap_of_seq (T : nominalType) s (xs : seq T) :
  rename s (partmap_of_seq xs) = partmap_of_seq (rename s xs).
Proof.
apply/eq_partmap=> n; rewrite renamemE !partmap_of_seqE renameT.
by rewrite renames_nth renameoE /= renamesE -!map_comp /funcomp.
Qed.

Lemma renamem_uncurry (T S R : nominalType) s m :
  rename s (@uncurrym T S R m) = uncurrym (rename s m).
Proof.
apply/eq_partmap=> - [x y]; rewrite renamemE.
case get_xy: (uncurrym _ (x, y))=> [v|] //=.
  move/uncurrymP: get_xy=> [m' get_x get_y].
  have ->: uncurrym m (rename s^-1 (x, y)) = Some (rename s^-1 v).
    apply/uncurrymP=> /=; exists (rename s^-1 m').
      by move: get_x; rewrite renamemE=> /(canRL (renameK s)).
    by rewrite renamemE renameK get_y.
  by rewrite renameoE /= renameKV.
case get_xy': (uncurrym _ _)=> [v|] //=.
move/uncurrymP: get_xy'=> [m' /= get_x get_y]; move: get_xy.
suff ->: uncurrym (rename s m) (x, y) = Some (rename s v) by [].
apply/uncurrymP=> /=; exists (rename s m').
  by move: get_x; rewrite renamemE=> ->.
by rewrite renamemE get_y.
Qed.

Lemma renamem_curry (T S R : nominalType) s m :
  rename s (@currym T S R m) = currym (rename s m).
Proof.
apply/eq_partmap=> x.
move: (erefl (x \in domm (currym (rename s m)))).
rewrite {1}domm_curry -renamem_dom.
rewrite (_ : (x \in @fst _ _ @: rename s (domm m)) =
             (rename s^-1 x \in @fst _ _ @: (domm m))).
  rewrite -domm_curry !mem_domm renamemE.
  case get_x: (currym m _)=> [n|];
  case get_x': (currym _ _)=> [n'|] //= _.
  congr Some; apply/eq_partmap=> y; rewrite renamemE.
  move: (currymE (rename s m) x y).
  rewrite get_x' /= renamemE renamepE /= => <-.
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
  _ : forall s x, P x = P (rename s x)
}.

Local Coercion sort : type >-> subType.

Implicit Type (s : {fperm name}).

Variable (sT : type).

Let subeqvar s x : P x = P (rename s x).
Proof. by case: sT. Qed.

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

Lemma subrenameE s x : val (rename s x) = rename s (val x).
Proof. exact: SubK. Qed.

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
rewrite /bij_names /bij_rename=> Pn h; apply: namesTeq=> //.
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
Variable l : {eqvar T -> {fset name}}.

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
by rewrite supp_inv -{}re -eqvarE names_rename -renamefsE -renamefsD
  names_disjointE 1?namesfsnE //.
Qed.

Lemma eq_trans : transitive eq.
Proof.
move=> z x y /eqP [s1 dis1 re1] /eqP [s2 dis2 re2].
apply/eqP.
exists (s2 * s1); last by rewrite -renameD re1.
move: {re2} dis2; rewrite -{}re1 -eqvarE names_rename -renamefsE -renamefsD.
rewrite names_disjointE 1?namesfsnE // => dis2.
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
Variable l : {eqvar T -> {fset name}}.

CoInductive bound_type := Bound of {eq_quot BoundEq.equivRel l}.
Definition bound_of (l' : T -> {fset name}) of phant_id (eqvar_fun l) l' :=
  bound_type.
Identity Coercion type_of_bound_of : bound_of >-> bound_type.

Definition quot_of_bound b := let: Bound b := b in b.

Canonical newType := [newType for quot_of_bound].
Definition eqMixin := [eqMixin of bound_type by <:].
Canonical eqType := Eval hnf in EqType bound_type eqMixin.
Definition choiceMixin := [choiceMixin of bound_type by <:].
Canonical choiceType := Eval hnf in ChoiceType bound_type choiceMixin.
Definition ordMixin := [ordMixin of bound_type by <:].
Canonical ordType := Eval hnf in OrdType bound_type ordMixin.

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
  rewrite /x' names_rename -eqvarE -renamefsE -renamefsD names_disjointE //.
  rewrite namesfsnE.
  move: (supp_avoid (D :\: (names x :\: l x)) (names x)).
  rewrite ![fdisjoint (supp _) _]fdisjointC; apply: fdisjoint_trans.
  apply/fsubsetP=> n /fsetDP [n_in n_nin].
  by rewrite !(in_fsetD, negb_and, negb_or, negbK) /= n_in n_nin.
rewrite fdisjointC /x' -[l x']namesfsnE.
apply: (fdisjoint_trans (equivariant_names (eqvarE l) _)).
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

CoInductive bind_spec D x : T -> Prop :=
| BindSpec s of fdisjoint (supp s) (names x :\: l x)
  & fdisjoint (supp s) D : bind_spec D x (rename s x).

Lemma fbindP D x : fdisjoint D (l x) -> bind_spec D x (unbind D (bind x)).
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
move=> dis''; rewrite e; apply: BindSpec=> //.
apply: (fdisjoint_trans (supp_fperm _ _)).
by rewrite fdisjointUl fdisjointC dis'' /= -renamefsE eqvarE fdisjointC.
Qed.

Lemma bindP x : bind_spec fset0 x (unbind fset0 (bind x)).
Proof. exact: fbindP (fdisjoint0 _). Qed.

Definition bound_rename s xx := bind (rename s (unbind fset0 xx)).

Let bound_rename_morph s x : bound_rename s (bind x) = bind (rename s x).
Proof.
rewrite /bound_rename; case: bindP=> s' dis _; apply/esym/bind_eqP.
exists (s * s' * s^-1); last by rewrite -renameD renameK renameD.
by rewrite suppJ names_rename -eqvarE -!renamefsE -renamefsD
   -renamefs_disjoint.
Qed.

Definition bound_names xx :=
  let x := unbind fset0 xx in
  names x :\: l x.

Let bound_names_morph x : bound_names (bind x) = names x :\: l x.
Proof.
rewrite /bound_names; case: bindP=> s' dis _.
rewrite names_rename -eqvarE -!renamefsE -renamefsD names_disjointE //.
by rewrite namesfsnE.
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
move/(mem_imfset s); rewrite -renamefsE renamefsD renamefsE -names_rename.
move: {xx} (unbind _ _)=> x; rewrite bound_rename_morph {1}/s fperm2L eqvarE.
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
by rewrite /fset2 fsetU1E fdisjointC fdisjointUr !fdisjoints1 n'_nin.
Qed.

Definition bound_nominalMixin :=
  NominalMixin bound_renameD bound_namesNNE bound_namesTeq.
Canonical bound_nominalType :=
  Eval hnf in NominalType bound_type bound_nominalMixin.

Lemma renamebE s x : rename s (bind x) = bind (rename s x).
Proof. exact: bound_rename_morph. Qed.

Lemma namesbE x : names (bind x) = names x :\: l x.
Proof. exact: bound_names_morph. Qed.

End Bound.

Notation "{ 'bound' l }" := (@bound_of _ _ l id)
  (at level 0, format "{ 'bound'  l }") : type_scope.

Arguments bind {_ _} _.

Section Bound2.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T S : nominalType).
Variables (lT : {eqvar T -> {fset name}}) (lS : {eqvar S -> {fset name}}).

Implicit Types (x : T) (y : S) (xx : {bound lT}) (yy : {bound lS}).

Definition unbind2 D xx yy :=
  let x := unbind (D :|: names yy) xx in
  let y := unbind (D :|: names x) yy in
  (x, y).

CoInductive bind2_spec D x y : T * S -> Prop :=
| Bind2Spec s of fdisjoint (supp s) (names x :\: lT x)
  & fdisjoint (supp s) (names y :\: lS y)
  & fdisjoint (supp s) D
  : bind2_spec D x y (rename s x, rename s y).

Lemma fbind2P D x y :
  fdisjoint D (lT x :|: lS y) ->
  fdisjoint (lT x) (names y) ->
  fdisjoint (lS y) (names x) ->
  bind2_spec D x y (unbind2 D (bind x) (bind y)).
Proof.
rewrite fdisjointUr /unbind2=> /andP [dis_x dis_y] disxy disyx.
set xx := bind x; set yy := bind y.
have dis: fdisjoint (D :|: names yy) (lT x).
  rewrite /yy fdisjointUl dis_x /=.
  move: disxy; rewrite fdisjointC; apply: fdisjoint_trans.
  by apply: equivariant_names; apply: renamebE.
case: (fbindP dis)=> s1 dis_s1; rewrite fdisjointUr.
case/andP => dis_s1D dis_s1_yy.
rewrite -(names_disjointE dis_s1_yy) /yy renamebE.
have dis': fdisjoint (D :|: names (rename s1 x)) (lS (rename s1 y)).
  rewrite fdisjointUl names_rename -renamefsE -eqvarE -renamefs_disjoint.
  rewrite andbC fdisjointC disyx /=.
  by rewrite -(@names_disjointE _ s1 D) -?renamefs_disjoint // namesfsnE.
case: (fbindP dis') => /= s2 dis_s2; rewrite fdisjointUr.
case/andP=> dis_s2D dis_s2_x.
rewrite -(names_disjointE dis_s2_x) !renameD.
apply: Bind2Spec.
- apply: (fdisjoint_trans (supp_mul _ _)).
  rewrite fdisjointUl dis_s1 andbT; rewrite -[_ :\: _]namesfsnE in dis_s1.
  rewrite -(names_disjointE dis_s1) renamefsD eqvarE renamefsE.
  rewrite -names_rename fdisjointC; move: dis_s2_x; rewrite fdisjointC.
  by apply: fdisjoint_trans; rewrite fsubDset fsubsetUr.
- apply: (fdisjoint_trans (supp_mul s2 s1)); rewrite fdisjointUl.
  rewrite /yy namesbE in dis_s1_yy; rewrite dis_s1_yy.
  rewrite names_rename -eqvarE -renamefsE -renamefsD in dis_s2.
  rewrite names_disjointE ?namesfsnE // in dis_s2.
  by rewrite dis_s2.
by apply: (fdisjoint_trans (supp_mul s2 s1)); rewrite fdisjointUl dis_s2D.
Qed.

Lemma bind2 x y :
  fdisjoint (lT x) (names y) ->
  fdisjoint (lS y) (names x) ->
  bind2_spec fset0 x y (unbind2 fset0 (bind x) (bind y)).
Proof. exact: fbind2P (fdisjoint0 _). Qed.

End Bound2.

Section TrivialNominalType.

Variable T : trivialNominalType.
Variable l : {eqvar T -> {fset name}}.

Let bound_renameT s (xx : {bound l}) : rename s xx = xx.
Proof.
rewrite -(unbindK fset0 xx) renamebE names_disjointE // namesT.
by rewrite fdisjointC fdisjoint0.
Qed.

Canonical bound_trivialNominalType :=
  Eval hnf in TrivialNominalType (bound_type l)
                                 (TrivialNominalMixin bound_renameT).

End TrivialNominalType.

Section Restriction.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Section Def.

Variable T : nominalType.

Record prerestr := PreRestr {
  prval :> {fset name} * T;
  _ : fsubset prval.1 (names prval.2)
}.

Lemma prerestr_eqvar s (p : {fset name} * T) :
  fsubset p.1 (names p.2) = fsubset (rename s p).1 (names (rename s p).2).
Proof. by rewrite renamepE /= names_rename -renamefsE -renamefs_subset. Qed.

Canonical prerestr_subType := [subType for prval].
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

Definition prerestr_op (p : prerestr) := (val p).1.

Lemma prerestr_op_eqvarP : equivariant prerestr_op.
Proof. by move=> s p; rewrite /prerestr_op subrenameE renamepE /=. Qed.
Canonical prerestr_op_eqvar := Eqvar prerestr_op_eqvarP.

Definition restr_type := {bound prerestr_op}.
Definition restr_of of phant T := restr_type.
Identity Coercion type_of_restr_of : restr_of >-> restr_type.

Canonical restr_eqType := [eqType of restr_type].
Canonical restr_choiceType := [choiceType of restr_type].
Canonical restr_ordType := [ordType of restr_type].
Canonical restr_nominalType := [nominalType of restr_type].

End Def.

Notation "{ 'restr' T }" := (@restr_of _ (Phant T))
  (at level 0, format "{ 'restr'  T }") : type_scope.

Section TrivialNominalType.

Variable (T : trivialNominalType).

Implicit Types (s : {fperm name}) (x : prerestr T) (xx : {restr T}).

Lemma prerestr_renameT s x : rename s x = x.
Proof.
case: x => - [A x] /= sub; apply: val_inj; rewrite subrenameE /=.
rewrite renamepE /= renameT; move: sub; rewrite namesT fsubset0=> /eqP ->.
by rewrite renamefsE imfset0.
Qed.

Definition prerestr_trivialNominalMixin :=
  TrivialNominalMixin prerestr_renameT.
Canonical prerestr_trivialNominalType :=
  Eval hnf in TrivialNominalType (prerestr T) prerestr_trivialNominalMixin.
Canonical restr_trivialNominalType := [trivialNominalType of restr_type T].

End TrivialNominalType.

(* FIXME: mask is already defined in seq.v *)

Lemma mask_key : unit. Proof. exact: tt. Qed.
Definition mask : forall T : nominalType, {fset name} -> T -> {restr T} :=
  locked_with mask_key
              (fun T A x => bind (Sub (A :&: names x, x) (fsubsetIr _ _))).

Section Basic.

Variable (T : nominalType).

Implicit Types (s : {fperm name}) (A D : {fset name}) (x : T) (xx : {restr T}).

Lemma maskI A x : mask A x = mask (A :&: names x) x.
Proof.
rewrite [mask]unlock; congr bind; apply: val_inj=> /=.
by rewrite -fsetIA fsetIid.
Qed.

CoInductive mask_spec D A x : {fset name} * T -> Prop :=
| MaskSpec s of fdisjoint D (rename s A)
  & fdisjoint (supp s) (names x :\: A)
  & fdisjoint (supp s) D
  : mask_spec D A x (rename s A, rename s x).

Lemma fmaskP D A x :
  fdisjoint D A ->
  fsubset A (names x) ->
  mask_spec D A x (val (unbind D (mask A x))).
Proof.
move=> dis /fsetIidPl e; move: (unbindP D (mask A x)); rewrite [mask]unlock /=.
case: fbindP; first by rewrite /= /prerestr_op /= e.
move=> //= s; rewrite subnamesE /prerestr_op renamepE /= e.
rewrite {1}/names /= fsetDUl /= namesfsnE fsetDv fset0U.
move=> dis_s sub disD; exact: MaskSpec.
Qed.

Lemma maskP A x :
  fsubset A (names x) ->
  mask_spec fset0 A x (val (unbind fset0 (mask A x))).
Proof. exact: fmaskP (fdisjoint0 _). Qed.

CoInductive restr_spec D : {restr T} -> Prop :=
| RestrSpec A x of fdisjoint D A & fsubset A (names x)
  : restr_spec D (mask A x).

Lemma restrP D xx : restr_spec D xx.
Proof.
rewrite -[xx](unbindK D).
case: (unbind _ _) (unbindP D xx) => {xx} - [A x] /= sub dis.
rewrite (_ : bind _ = mask A x); first exact: RestrSpec.
rewrite [mask]unlock; congr bind; apply: val_inj=> /=; congr pair.
by apply/esym/fsetIidPl.
Qed.

Lemma namesrE A x : names (mask A x) = names x :\: A.
Proof.
rewrite -[RHS]fset0U -(fsetDv (names x)) -fsetDIr fsetIC maskI.
move: (A :&: names x) (fsubsetIr A (names x))=> {A} A subA.
rewrite [mask]unlock namesbE /= /prerestr_op /= subnamesE fsetDUl /=.
by rewrite namesfsnE fsetDv fset0U fsetIC fsetDIr fsetDv fset0U.
Qed.

Lemma renamerE s A x : rename s (mask A x) = mask (rename s A) (rename s x).
Proof.
rewrite [mask]unlock renamebE; congr bind; apply: val_inj=> /=.
by rewrite renamepE /= renamefsI names_rename.
Qed.

End Basic.

Section Hide.

Variable (T : nominalType).

Implicit Types (s : {fperm name}) (A D : {fset name}) (x : T) (xx : {restr T}).

Definition hiden A xx :=
  let: (A', x) := val (unbind fset0 xx) in
  mask (A :|: A') x.

Lemma hidenE A A' x : hiden A (mask A' x) = mask (A :|: A') x.
Proof.
rewrite /hiden (maskI A') (maskI (_ :|: _)) fsetIUl.
move: (A' :&: names x) (fsubsetIr A' (names x)) => {A'} A' subA'.
case: (maskP subA')=> s _ dis sub.
rewrite -{1}(renameKV s A) -renamefsU -renamerE names_disjointE; last first.
  rewrite namesrE fsetUC fdisjointC; rewrite fdisjointC in dis.
  by apply: fdisjoint_trans dis; rewrite -fsetDDl fsubDset fsubsetUr.
rewrite [LHS]maskI fsetIUl (fsetIidPl _ _ subA') -(fsetID (names x) A').
rewrite ![_ :|: _ :\: _]fsetUC !fsetIUr -!fsetUA !fsetIA.
rewrite !(fsetUidPr _ _ (fsubsetIr _ A')) -[_ :&: _](renameK s) renamefsI.
rewrite renameKV [rename s _]names_disjointE ?namesfsnE // names_disjointE //.
rewrite supp_inv fdisjointC namesfsnE; rewrite fdisjointC in dis.
apply: fdisjoint_trans dis; exact: fsubsetIr.
Qed.

Lemma hidenI A xx : hiden A xx = hiden (A :&: names xx) xx.
Proof.
case/(restrP fset0): xx=> A' x _ sub; rewrite !hidenE.
rewrite namesrE [LHS]maskI fsetIUl (fsetIidPl _ _ sub); congr mask.
rewrite -{1}(fsetID (names x) A') [in A :&: _]fsetUC fsetIUr -fsetUA.
by rewrite fsetIA (fsetUidPr _ _ (fsubsetIr _ _)).
Qed.

Lemma hiden0 xx : hiden fset0 xx = xx.
Proof.
by case/(restrP fset0): xx=> A x _ sub; rewrite hidenE fset0U.
Qed.

Lemma rename_hiden s A xx :
  rename s (hiden A xx) = hiden (rename s A) (rename s xx).
Proof.
case/(restrP fset0): xx=> A' x _ sub.
by rewrite !(renamerE, hidenE) renamefsU.
Qed.

Lemma names_hiden A xx : names (hiden A xx) = names xx :\: A.
Proof.
case/(restrP fset0): xx=> A' x _ sub.
by rewrite hidenE !namesrE fsetDDl fsetUC.
Qed.

(* FIXME: This should probably just be a notation *)

Definition hide (n : name) := hiden (fset1 n).

Lemma hideE n A x : hide n (mask A x) = mask (n |: A) x.
Proof. by rewrite /hide hidenE fsetU1E. Qed.

Lemma names_hide n xx : names (hide n xx) = names xx :\ n.
Proof. by rewrite /hide names_hiden fsetD1E. Qed.

Lemma rename_hide s n xx :
  rename s (hide n xx) = hide (s n) (rename s xx).
Proof. by rewrite /hide rename_hiden renamefsE imfset1. Qed.

Lemma hide0 n xx : names xx = fset0 -> hide n xx = xx.
Proof. by rewrite /hide hidenI -{4}[xx]hiden0=> ->; rewrite fsetI0. Qed.

End Hide.

Lemma hidenT (T : trivialNominalType) A xx : @hiden T A xx = xx.
Proof. by rewrite hidenI namesT fsetI0 hiden0. Qed.

Lemma hideT (T : trivialNominalType) n xx : @hide T n xx = xx.
Proof. by rewrite hide0 // namesT. Qed.

Section Join.

Variable (T : nominalType).

Implicit Types (s : {fperm name}) (A D : {fset name}) (x : T) (xx : {restr T}).

Definition join_restr (bxx : {restr {restr T}}) : {restr T} :=
  let: (A, xx) := val (unbind fset0 bxx) in
  hiden A xx.

Lemma join_restrE A A' x :
  join_restr (mask A (mask A' x)) = mask (A :|: A') x.
Proof.
rewrite -hidenE; move: (mask A' _)=> {A' x} xx; rewrite /join_restr.
rewrite maskI hidenI; move: (_ :&: _) (fsubsetIr A (names xx))=> {A} A subA.
case: maskP => // s _ dis sub.
by rewrite -rename_hiden names_disjointE // names_hiden.
Qed.

End Join.

Section Iso.

Variable T : nominalType.

Definition orestr (xx : {restr option T}) : option {restr T} :=
  let: (A, x) := val (unbind fset0 xx) in
  omap (mask A) x.

Lemma orestrE A x : orestr (mask A x) = omap (mask A) x.
Proof.
transitivity (omap (mask (A :&: names x)) x); last first.
  by case: x=> //= x; rewrite [in RHS]maskI.
rewrite [in LHS]maskI.
move: (_ :&: _) (fsubsetIr A (names x))=> {A} A subA.
rewrite /orestr; case: maskP=> // s _ dis sub.
case: x subA dis sub => //= x subA dis sub.
by rewrite -renamerE names_disjointE // namesrE.
Qed.

Lemma rename_orestr : equivariant orestr.
Proof.
move=> s x; case/(restrP fset0): x=> /= A x _ _.
rewrite orestrE renamerE orestrE //=.
by case: x=> //= x; rewrite renameoE /= renamerE.
Qed.

Lemma orestr_hiden A xx :
  orestr (hiden A xx) = omap (hiden A) (orestr xx).
Proof.
case/(restrP fset0): xx=> A' x _ _.
rewrite hidenE !orestrE; case: x => [x|] //=.
by rewrite hidenE.
Qed.

End Iso.

Section Functor.

Section FinSupp.

Variables T S : nominalType.
Variables (D : {fset name}) (f : T -> S).
Implicit Types (x : T) (xx : {restr T}).

Lemma mapr_fs_key : unit. Proof. exact: tt. Qed.
Definition mapr_fs_def xx :=
  let: (A, x) := val (unbind D xx) in
  mask A (f x).
Definition mapr_fs := locked_with mapr_fs_key mapr_fs_def.

Lemma mapr_fsE :
  finsupp D f ->
  forall A x, fdisjoint D A ->
              mapr_fs (mask A x) = mask A (f x).
Proof.
move=> f_fs A x dis; rewrite [mapr_fs]unlock /mapr_fs_def.
have dis': fdisjoint D (A :&: names x).
  rewrite fdisjointC; move: dis; rewrite fdisjointC.
  by apply: fdisjoint_trans; rewrite fsubsetIl.
rewrite maskI; case: (fmaskP _ (fsubsetIr _ _))=> //= s disD dis_s dis_sD.
rewrite -f_fs -1?renamerE ?names_disjointE //.
  rewrite [LHS]maskI [RHS]maskI -fsetIA (fsetIC (names x)) fsetIA.
  congr mask; apply: fsetIidPl; apply: fsubset_trans (fsubsetIr A _).
  move/(fsetIS A): (names_finsupp x f_fs)=> sub; apply: (fsubset_trans sub).
  rewrite -[_ :&: names x]fset0U -(fdisjoint_fsetI0 dis) (fsetIC D).
  by rewrite -fsetIUr fsetIS // fsubsetxx.
rewrite namesrE /fdisjoint -fsubset0 fsetIDA fsubDset fsetU0.
move/(fsetIS (supp s)): (names_finsupp x f_fs); rewrite fsetIUr.
move: dis_sD; rewrite /fdisjoint=> /eqP ->; rewrite fset0U => sub'.
apply: (fsubset_trans sub'); rewrite fsubsetI fsubsetIr andbT.
rewrite -(fsetID (names x) (A :&: names x)) fsetIUr (fdisjoint_fsetI0 dis_s).
by rewrite fsetU0 (fsetIC A) !fsetIA fsubsetIr.
Qed.

End FinSupp.

Section Properties.

Variables T S R : nominalType.

Lemma mapr_fs_id D (xx : {restr T}) :
  mapr_fs D id xx = xx.
Proof.
case: xx / (restrP D)=> [A x dis sub].
by rewrite mapr_fsE=> //.
Qed.

Lemma mapr_fs_comp Dg Df (g : S -> R) (f : T -> S) xx :
  finsupp Dg g -> finsupp Df f ->
  mapr_fs (Dg :|: Df) (g \o f) xx =
  mapr_fs Dg g (mapr_fs Df f xx).
Proof.
case: xx / (restrP (Dg :|: Df))=> [A x dis sub] fs_g fs_f.
move: (dis); rewrite fdisjointUl=> /andP [disg disf].
rewrite !mapr_fsE //.
by apply: finsupp_comp.
Qed.

End Properties.

Section Def.

Variable T S : nominalType.
Variable f : T -> S.

Definition mapr := mapr_fs fset0 f.

Lemma maprE :
  equivariant f ->
  forall A x, mapr (mask A x) = mask A (f x).
Proof.
move=> /equivariant_finsupp fs_f A x.
by rewrite /mapr mapr_fsE //= fdisjoint0.
Qed.

Lemma rename_mapr : equivariant f -> equivariant mapr.
Proof.
move=> equi_f s /= xx; case: xx / (restrP fset0) => [A x sub _].
by rewrite maprE // !renamerE maprE // equi_f.
Qed.

End Def.

End Functor.

Section FinSuppFacts.

Variables T S R : nominalType.
Implicit Types (D A : {fset name}) (x : T) (xx : {restr T}).
Implicit Types (f : T -> S) (g : T -> S -> R).

Lemma finsupp_mapr_fs D f :
  finsupp D f ->
  finsupp D (mapr_fs D f).
Proof.
move=> fs_f s dis /= xx; case: xx / (restrP D)=> [A x sub fr].
have dis': fdisjoint (supp s) (names D).
  rewrite fdisjointC; apply/fdisjointP=> /= n /namesfsP [n' inD /namesnP ?].
  by subst n'; apply: contraTN inD; apply/fdisjointP.
rewrite mapr_fsE // 2!renamerE fs_f // mapr_fsE //.
by rewrite -(names_disjointE dis') -renamefs_disjoint.
Qed.

Lemma curry_equivariant g x :
  equivariant (fun p => g p.1 p.2) ->
  finsupp (names x) (g x).
Proof.
move=> equi_f s dis x'; move: (equi_f s (x, x')) => /= ->.
by congr g; rewrite names_disjointE.
Qed.

End FinSuppFacts.

Section Functor2.

Lemma mapr2_key : unit. Proof. exact: tt. Qed.
Definition mapr2_def (T S R : nominalType) (f : T -> S -> R)
                     (xx : {restr T}) (yy : {restr S}) :=
  let: (px, py) := unbind2 fset0 xx yy in
  let: (A, x) := val px in
  let: (B, y) := val py in
  mask (A :|: B) (f x y).
Definition mapr2 := locked_with mapr2_key mapr2_def.

Variables T S R : nominalType.
Variable f : T -> S -> R.

Implicit Types (A B : {fset name}) (x : T) (y : S).
Implicit Types (xx : {restr T}) (yy : {restr S}).

Hypothesis equi_f : equivariant (fun p => f p.1 p.2).

Definition mutfresh A x B y :=
  [&& fdisjoint A (names y) & fdisjoint B (names x)].

Lemma rename_mutfresh s A x B y :
  mutfresh (rename s A) (rename s x) (rename s B) (rename s y) =
  mutfresh A x B y.
Proof.
by rewrite /mutfresh !names_rename -!renamefs_disjoint.
Qed.

Lemma mapr2E A x B y :
  mutfresh A x B y ->
  mapr2 f (mask A x) (mask B y) = mask (A :|: B) (f x y).
Proof.
case/andP=> disA disB.
have sub: fsubset (names (f x y)) (names x :|: names y).
  exact: (equivariant_names equi_f (x, y)).
rewrite [RHS]maskI -(fsetIidPr _ _ sub) fsetIA -maskI fsetIUl !fsetIUr.
rewrite (fdisjoint_fsetI0 disA) (fdisjoint_fsetI0 disB) fsetU0 fset0U.
have {disA} disA: fdisjoint (A :&: names x) (names y).
  exact: (fdisjoint_trans (fsubsetIl _ _)).
have {disB} disB: fdisjoint (B :&: names y) (names x).
  exact: (fdisjoint_trans (fsubsetIl _ _)).
rewrite (maskI A) (maskI B) [mapr2]unlock /mapr2_def {1 2}[mask]unlock.
case: (@fbind2P _ _ _ _ fset0); rewrite ?subnamesE /= /prerestr_op /=.
- exact: fdisjoint0.
- rewrite -!fsetIA !fsetIid {2}/names /= /prod_names /= namesfsnE.
  by rewrite (fsetUidPr _ _ (fsubsetIr _ _)).
- rewrite -!fsetIA !fsetIid {2}/names /= /prod_names /= namesfsnE.
  by rewrite (fsetUidPr _ _ (fsubsetIr _ _)).
rewrite -!fsetIA !fsetIid=> s dis1 dis2 _.
rewrite -!renamefsU -(equi_f s (x, y)) -renamerE /=.
rewrite names_disjointE // namesrE.
move: (A :&: names x) (B :&: names y) disA disB dis1 dis2
      (fsubsetIr A (names x)) (fsubsetIr B (names y))
      => /= {A B} A B disA disB dis1 dis2 subA subB.
move/(fsetSD (A :|: B)) in sub; rewrite fdisjointC.
apply: (fdisjoint_trans sub); rewrite fsetDUl fdisjointUl.
rewrite fdisjointC in dis1; rewrite fdisjointC in dis2.
apply/andP; split.
  apply: fdisjoint_trans dis1; rewrite fsetDUl /= namesfsnE fsetDv.
  rewrite fset0U.
  apply: fsetDS; exact: fsubsetUl.
apply: fdisjoint_trans dis2; rewrite fsetDUl /= namesfsnE fsetDv.
rewrite fset0U.
apply: fsetDS; exact: fsubsetUr.
Qed.

CoInductive frestr2_spec D : {restr T} -> {restr S} -> Prop :=
| FRestr2Spec A x B y of mutfresh A x B y
                      &  fdisjoint D (A :|: B)
                      &  fsubset A (names x)
                      &  fsubset B (names y)
                      :  frestr2_spec D (mask A x) (mask B y).

Lemma frestr2P D xx yy : frestr2_spec D xx yy.
Proof.
case: xx / (restrP (D :|: names yy))=> [A x disA subA].
move: disA; rewrite fdisjointUl=> /andP [fA disA].
case: yy / (restrP (D :|: names x)) disA => [B y disB subB].
move: disB; rewrite fdisjointUl=> /andP [fB disB].
rewrite namesrE // => disA; constructor=> //.
  rewrite /mutfresh andbC fdisjointC disB /= fdisjointC.
  rewrite -(fsetID (names y) B) fdisjointUl andbC disA /=.
  rewrite fdisjointC; apply: (fdisjoint_trans subA).
  rewrite fdisjointC; apply: (fdisjoint_trans (fsubsetIr _ _)).
  by rewrite fdisjointC.
by rewrite fdisjointUr fA.
Qed.

CoInductive restr2_spec : {restr T} -> {restr S} -> Prop :=
| Restr2Spec A x B z of mutfresh A x B z
                     &  fsubset A (names x)
                     &  fsubset B (names z)
                     :  restr2_spec (mask A x) (mask B z).

Lemma restr2P xx yy : restr2_spec xx yy.
Proof.
by case: xx yy / (frestr2P fset0)=> ???????; constructor.
Qed.

Lemma rename_mapr2 s xx yy :
  rename s (mapr2 f xx yy) = mapr2 f (rename s xx) (rename s yy).
Proof.
case: xx yy / restr2P=> [A x B y mf]; rewrite mapr2E //.
rewrite 3!renamerE mapr2E; last by rewrite rename_mutfresh.
by rewrite !renamefsE imfsetU (equi_f s (x, y)).
Qed.

Lemma finsupp_mapr2l xx :
  finsupp (names xx) (mapr2 f xx).
Proof.
by apply: curry_equivariant=> {xx} s [xx yy] /=; rewrite rename_mapr2.
Qed.

Lemma finsupp_mapr2r yy :
  finsupp (names yy) (mapr2 f^~ yy).
Proof.
apply: (@curry_equivariant _ _ _ (fun yy=> mapr2 f^~ yy) yy).
by move=> {yy} s [yy xx] /=; rewrite rename_mapr2.
Qed.

End Functor2.

Section Independence.

Implicit Types T S R : nominalType.

Lemma mutfresh_sym T S A (x : T) B (y : S) :
  mutfresh A x B y = mutfresh B y A x.
Proof. by rewrite /mutfresh andbC. Qed.

Lemma mutfreshS T T' S S' A x x' B y y' :
  @mutfresh T S A x B y ->
  fsubset (names x') (names x) ->
  fsubset (names y') (names y) ->
  @mutfresh T' S' A x' B y'.
Proof.
move=> /andP [disA disB] sx sy.
rewrite /mutfresh; apply/andP; split.
  by rewrite fdisjointC; apply: (fdisjoint_trans sy); rewrite fdisjointC.
by rewrite fdisjointC; apply: (fdisjoint_trans sx); rewrite fdisjointC.
Qed.

Lemma mutfreshEl T S R (f : T -> R) A x B (y : S) :
  equivariant f ->
  mutfresh A x B y -> mutfresh A (f x) B y.
Proof.
move=> equi_f /andP [disA disB]; apply/andP; split=> //.
rewrite fdisjointC.
by apply: (fdisjoint_trans (equivariant_names equi_f x)); rewrite fdisjointC.
Qed.

Lemma mutfreshEr T S R (g : S -> R) A (x : T) B z :
  equivariant g ->
  mutfresh A x B z -> mutfresh A x B (g z).
Proof. by rewrite !(mutfresh_sym A); apply/mutfreshEl. Qed.

Lemma mutfreshE2l T1 T2 S R (f : T1 -> T2 -> R) A1 x1 A2 x2 B (y : S) :
  equivariant (fun p => f p.1 p.2) ->
  mutfresh A1 x1 B y -> mutfresh A2 x2 B y ->
  mutfresh (A1 :|: A2) (f x1 x2) B y.
Proof.
move=> equi_f /andP [disA1 disB1] /andP [disA2 disB2].
apply/andP; split=> //.
- by rewrite fdisjointUl disA1 disA2.
rewrite fdisjointC.
apply/(fdisjoint_trans (equivariant_names equi_f (x1, x2))).
by rewrite fdisjointC fdisjointUr disB1.
Qed.

Lemma mutfreshE2r T S1 S2 R (g : S1 -> S2 -> R) A (x : T) B1 z1 B2 z2 :
  equivariant (fun p => g p.1 p.2) ->
  mutfresh A x B1 z1 -> mutfresh A x B2 z2 ->
  mutfresh A x (B1 :|: B2) (g z1 z2).
Proof. by rewrite !(mutfresh_sym A); apply/mutfreshE2l. Qed.

End Independence.

Section Hiding.

Lemma hiden_mapr T S A f xx :
  equivariant f -> hiden A (@mapr T S f xx) = mapr f (hiden A xx).
Proof.
move=> equi_f; case: xx / (restrP fset0)=> [/= A' x _ sub].
by rewrite maprE // !hidenE maprE.
Qed.

Lemma hiden_mapr2l T S R A f xx yy :
  equivariant (fun p => f p.1 p.2) ->
  fdisjoint A (names yy) ->
  hiden A (@mapr2 T S R f xx yy) = mapr2 f (hiden A xx) yy.
Proof.
move=> equi ninN.
case: xx yy / (frestr2P A) ninN => [/= A' x B y mf].
rewrite fdisjointUr namesrE // => /andP [disA1 disA2] sub1 sub2 dis'.
rewrite mapr2E // !hidenE mapr2E // ?fsetUA //.
case/andP: mf=> [subA subB]; apply/andP; split=> //.
rewrite fdisjointUl subA andbT fdisjointC -(fsetID (names y) B) fdisjointUl.
by rewrite (fsetIidPr _ _ sub2) fdisjointC disA2 /= fdisjointC.
Qed.

Lemma hiden_mapr2r T S R A f xx yy :
  equivariant (fun p => f p.1 p.2) ->
  fdisjoint A (names xx) ->
  hiden A (@mapr2 T S R f xx yy) = mapr2 f xx (hiden A yy).
Proof.
move=> equi ninN.
case: xx yy / (frestr2P A) ninN => [/= A' x B y mf].
rewrite fdisjointUr namesrE // => /andP [disA1 disA2] sub1 sub2 dis'.
rewrite mapr2E // !hidenE mapr2E //.
  by rewrite fsetUA (fsetUC A) -fsetUA.
case/andP: mf=> [subA subB]; apply/andP; split=> //.
rewrite fdisjointUl subB andbT fdisjointC -(fsetID (names x) A') fdisjointUl.
by rewrite (fsetIidPr _ _ sub1) fdisjointC disA1 /= fdisjointC.
Qed.

Lemma hide_mapr T S n f xx :
  equivariant f -> hide n (@mapr T S f xx) = mapr f (hide n xx).
Proof. exact: hiden_mapr. Qed.

Lemma hide_mapr2l T S R n f xx yy :
  equivariant (fun p => f p.1 p.2) ->
  n \notin names yy ->
  hide n (@mapr2 T S R f xx yy) = mapr2 f (hide n xx) yy.
Proof.
move=> e pn; apply: (hiden_mapr2l _ e).
by rewrite fdisjointC fdisjoints1.
Qed.

Lemma hide_mapr2r T S R n f xx yy :
  equivariant (fun p => f p.1 p.2) ->
  n \notin names xx ->
  hide n (@mapr2 T S R f xx yy) = mapr2 f xx (hide n yy).
Proof.
move=> e pn; apply: (hiden_mapr2r _ e).
by rewrite fdisjointC fdisjoints1.
Qed.

End Hiding.

Section Flip.

Variables T S R : nominalType.

Lemma flip_mapr2 (op : T -> S -> R) xx yy :
  equivariant (fun p => op p.1 p.2) ->
  mapr2 (fun z x => op x z) yy xx =
  mapr2 op xx yy.
Proof.
move=> equi_op.
case: xx yy / restr2P=> [A x B z mf].
rewrite mapr2E // -1?mutfresh_sym // 1?mapr2E // 1?fsetUC //.
by move=> s [z' x'] /=; rewrite (equi_op s (x', z')).
Qed.

End Flip.

Section Monoid.

Section BasicFacts.

Variables (T : nominalType) (op : T -> T -> T) (idx : T).

Hypothesis equi_op : equivariant (fun p => op p.1 p.2).

Lemma restr_left_id :
  left_id idx op -> left_id (mask fset0 idx) (mapr2 op).
Proof.
move=> op1x xx; case: xx / (restrP (names idx))=> A x dis sub.
by rewrite mapr2E // ?fset0U ?op1x // /mutfresh fdisjoint0 /= fdisjointC.
Qed.

Lemma restr_associative : associative op -> associative (mapr2 op).
Proof.
move=> opA xx1 xx2 xx3.
case: xx1 xx2 / (frestr2P (names xx3))
      => [A1 x1 A2 x2 mf12 dis sub1 sub2].
case: xx3 / (restrP (names x1 :|: names x2)) dis => /= [A3 x3].
rewrite fdisjointC fdisjointUr=> /andP [mf mf'] sub3.
rewrite fdisjointC namesrE fdisjointUl=> /andP [mf5 mf6].
have mf13: mutfresh A1 x1 A3 x3.
  rewrite /mutfresh mf andbT -(fsetID (names x3) A3) fdisjointUr mf5 andbT.
  apply: (fdisjoint_trans sub1); rewrite fdisjointC.
  by apply: (fdisjoint_trans (fsubsetIr _ _)).
have mf23: mutfresh A2 x2 A3 x3.
  rewrite /mutfresh mf' andbT -(fsetID (names x3) A3) fdisjointUr mf6 andbT.
  apply:  (fdisjoint_trans sub2); rewrite fdisjointC.
  by apply: (fdisjoint_trans (fsubsetIr _ _)).
rewrite ?mapr2E // ?opA ?fsetUA //; by [apply/mutfreshE2l|apply/mutfreshE2r].
Qed.

End BasicFacts.

Section RightId.

Variables (T : nominalType) (op : T -> T -> T) (idx : T).

Hypothesis equi_op : equivariant (fun p => op p.1 p.2).

Lemma restr_right_id :
  right_id idx op -> right_id (mask fset0 idx) (mapr2 op).
Proof.
move=> opx1 xx; rewrite -(flip_mapr2 _ _ equi_op).
rewrite restr_left_id // => s [xx1 xx2] /=.
by rewrite (equi_op s (xx2, xx1)).
Qed.

End RightId.

End Monoid.

Section New.

Section Basic.

Variable T : nominalType.

Definition new (ns : {fset name}) (f : name -> {restr T}) :=
  hide (fresh ns) (f (fresh ns)).

Lemma newP ns f g :
  (forall n, n \notin ns -> f n = g n) ->
  new ns f = new ns g.
Proof. by move=> efg; rewrite /new efg // freshP. Qed.

Lemma newE ns f n :
  n \notin ns -> finsupp ns f -> new ns f = hide n (f n).
Proof.
move=> n_nin_ns fs_f; rewrite /new.
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

Lemma new_const xx : new (names xx) (fun _ => xx) = xx.
Proof.
rewrite (newE (freshP (names xx)) (@const_finsupp _ _ xx)) /hide.
rewrite hidenI -[RHS]hiden0; congr hiden.
by apply: fdisjoint_fsetI0; rewrite fdisjointC fdisjoints1 freshP.
Qed.

Lemma rename_new s A (f : name -> {restr T}) :
  finsupp A f ->
  rename s (new A f) = new (s @: A) (rename s \o f \o rename s^-1).
Proof.
move: (fresh _) (freshP (supp s :|: A :|: s @: A))=> n nin fs_f.
have /and3P [/suppPn ninS ninA ninSA]:
  [&& n \notin supp s, n \notin A & n \notin s @: A].
  by move: nin; rewrite !in_fsetU !negb_or -andbA.
rewrite (newE ninA) // rename_hide (newE ninSA); last exact: finsuppJ.
by rewrite ninS /= renamenE -{4}ninS fpermK.
Qed.

Lemma newC D f :
  finsupp D (fun p => f p.1 p.2) ->
  new D (fun n => new (n |: D) (fun n' => f n n')) =
  new D (fun n' => new (n' |: D) (fun n => f n n')).
Proof.
move=> fs_f; rewrite /new.
move: (fresh _) (freshP D)=> n pn.
move: (fresh _) (freshP (n |: D))=> n'.
rewrite in_fsetU1 negb_or=> /andP [nn' pn'].
have dis: fdisjoint (supp (fperm2 n n')) D.
  apply/(fdisjoint_trans (fsubset_supp_fperm2 _ _)).
  by apply/fdisjointP=> /= n'' /fset2P [->|->].
move/(_ _ dis (n, n')): (fs_f); rewrite /= !renamenE fperm2L fperm2R => <-.
have: fsubset (names (f n n')) (D :|: (fset1 n :|: fset1 n')).
  exact: (names_finsupp (n, n') fs_f).
move: (f n n') {fs_f}=> xx; case: xx / (restrP D)=> [A x sub dis'].
rewrite namesrE // renamerE !hideE => sub'.
rewrite 2!fsetU1E fsetUA [fset1 n :|: _]fsetUC -fsetUA -2!fsetU1E.
rewrite -{3}(fperm2L n n') -{5}(fperm2R n n') -2!renamenE.
rewrite -!renamefsU1 -!renamerE names_disjointE //.
rewrite namesrE; move/fsubsetP: (fsubset_supp_fperm2 n n')=> sub''.
apply/fdisjointP=> n'' /sub''; rewrite in_fset2 !in_fsetD !in_fsetU1.
by rewrite !negb_or !negb_and !negbK=> /orP [->|->] //; rewrite orbT.
Qed.

End Basic.

Section Composition.

Variables T S : nominalType.

Lemma new_comp B A (g : T -> S) (f : name -> {restr T}) :
  finsupp B g -> finsupp A f ->
  mapr_fs B g (new A f) =
  new (A :|: B) (mapr_fs B g \o f).
Proof.
move=> fs_g fs_f.
move: (fresh _) (freshP (A :|: B))=> n ninAB.
rewrite (newE ninAB) /=; last first.
  rewrite fsetUC; apply/finsupp_comp=> //.
  exact/finsupp_mapr_fs.
have ninA: n \notin A.
  by apply: contra ninAB; apply/fsubsetP/fsubsetUl.
have ninB: n \notin B.
  by apply: contra ninAB; apply/fsubsetP/fsubsetUr.
rewrite (newE ninA) //.
case: (restrP B (f n)) (names_finsupp n fs_f)=> [/= A' x sub dis].
rewrite namesrE // => sub'; rewrite hideE mapr_fsE //.
  by rewrite mapr_fsE // hideE; congr mask.
by rewrite fsetU1E fdisjointUr fdisjoints1 ninB.
Qed.

End Composition.

Section Left.

Variables T S R : nominalType.

Lemma new_comp2l (op : T -> S -> R) A (f : name -> {restr T}) yy :
  equivariant (fun p => op p.1 p.2) ->
  finsupp A f ->
  mapr2 op (new A f) yy =
  new (A :|: names yy) (fun n => mapr2 op (f n) yy).
Proof.
move=> equi_op fs_f.
move: (fresh _) (freshP (A :|: names yy))=> n ninAN.
rewrite (newE ninAN) /=; last first.
  rewrite fsetUC.
  exact: (finsupp_comp (@finsupp_mapr2r _ _ _ _ equi_op yy) fs_f).
have ninA: n \notin A.
  by apply: contra ninAN; apply/fsubsetP/fsubsetUl.
have ninB: n \notin (names yy).
  by apply: contra ninAN; apply/fsubsetP/fsubsetUr.
rewrite (newE ninA) //.
case: yy / (frestr2P (fset1 n) (f n)) (names_finsupp n fs_f) ninAN ninB
      => /= [A' x B y mf].
rewrite fdisjointUr !(fdisjointC (fset1 n)) !fdisjoints1=> /andP [dis1 dis2].
move=> subA' subB; rewrite !namesrE // namesnE fsetUC -fsetU1E.
move=> sub' ninAB ninB; rewrite hideE mapr2E //.
  by rewrite mapr2E // hideE fsetU1E -fsetUA -fsetU1E.
case/andP: mf=> [mfA mfB]; rewrite /mutfresh mfB andbT.
rewrite fsetU1E fdisjointUl mfA andbT fdisjointC fdisjoints1.
by apply: contra ninB; rewrite in_fsetD dis2.
Qed.

End Left.

Section Right.

Variables T S R : nominalType.

Lemma new_comp2r (op : T -> S -> R) B (f : name -> {restr S}) xx :
  equivariant (fun p => op p.1 p.2) ->
  finsupp B f ->
  mapr2 op xx (new B f) =
  new (names xx :|: B) (fun n => mapr2 op xx (f n)).
Proof.
move=> equi_op fs_f.
rewrite -(flip_mapr2 _ _ equi_op).
rewrite new_comp2l //; last first.
  by move=> s [z x] /=; rewrite (equi_op s (x, z)).
by rewrite fsetUC; apply/newP=> n ninNB; rewrite flip_mapr2.
Qed.

End Right.

End New.

Section Trivial.

Variable T : trivialNominalType.

Definition expose (xx : {restr T}) : T :=
  let: (_, x) := val (unbind fset0 xx) in x.

Lemma exposeE A x : expose (mask A x) = x.
Proof.
rewrite /expose maskI namesT fsetI0; case: maskP.
  exact: fsub0set.
by move=> s _; rewrite renameT.
Qed.

Lemma rename_expose : equivariant expose.
Proof.
move=> s x; case: x / (restrP fset0) => /= [A x sub].
by rewrite exposeE renamerE exposeE.
Qed.

End Trivial.

Section OExpose.

Variable T : nominalType.

Definition oexpose (xx : {restr T}) : option T :=
  let: (A, x) := val (unbind fset0 xx) in
  if A == fset0 then Some x else None.

Lemma oexposeE A x :
  oexpose (mask A x) = (if A :&: names x == fset0 then Some x else None).
Proof.
rewrite maskI /oexpose; move: (fsubsetIr A (names x))=> sub.
case: maskP=> // s _ dis _.
rewrite -{1}(renamefs0 _ s) inj_eq; last exact: @rename_inj.
case: (A :&: names x =P fset0) dis=> // ->.
by rewrite fsetD0 => dis; rewrite names_disjointE.
Qed.

Lemma oexpose_rename : equivariant oexpose.
Proof.
move=> s xx; case: xx / (restrP fset0) => [A x _].
rewrite renamerE !oexposeE renamefsE -[rename s @: A]/(s @: A).
rewrite names_rename -renamefsI -{2}(renamefs0 _ s) inj_eq.
  by have [e|] //= := A :&: names x =P fset0.
(* FIXME: Why these annotations????? *)
by move=> ??; apply: (@rename_inj [nominalType of {fset name}] s).
Qed.

End OExpose.

End Restriction.
