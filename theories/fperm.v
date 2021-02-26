From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path bigop.

Require Import ord fset fmap ffun.

(******************************************************************************)
(*   This file defines a type {fperm T} of finite permutations of an ordType  *)
(* T.  By "finite", we mean that that there are only finitely many x such     *)
(* that s x != x.  Permutations are a subtype of finite functions (cf. ffun)  *)
(* and thus support extensional equality (cf. eq_fperm).                      *)
(*                                                                            *)
(*         fperm_one, 1 == Identity permutation.                              *)
(*               supp s == The support of s (the set of elements that are not *)
(*                         fixed by s).                                       *)
(*            fperm f X == Builds a permutation out of a function f.  If f is *)
(*                         bijective on X and x \in X, then fperm f X x = f x *)
(*    fperm_inv s, s^-1 == Inverse of a permutation.                          *)
(*              s1 * s2 == Permutation composition.                           *)
(*           fperm2 x y == Transposition of x and y (i.e. the permutation     *)
(*                         that swaps these elements)                         *)
(*          fperm2_rect == Induction on the number of transpositions          *)
(*         enum_fperm X == The set of all permutations with support in X      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FPerm.

Section Def.

Variables (T : ordType).

Local Open Scope ord_scope.
Local Open Scope fset_scope.

Definition axiom (f : ffun (@id T)) := f @: supp f == supp f.

Record fperm_type := FPerm {
  fpval : ffun id;
  _ : axiom fpval
}.

Definition fperm_of & phant T := fperm_type.

End Def.

Module Exports.

Identity Coercion fperm_of_fperm : fperm_of >-> fperm_type.
Coercion fpval : fperm_type >-> ffun.
Notation "{ 'fperm' T }" := (@fperm_of _ (Phant T))
  (at level 0, format "{ 'fperm'  T }") : type_scope.

Section WithOrdType.

Variable T : ordType.
Canonical fperm_subType := [subType for @fpval T].
Definition fperm_eqMixin :=
   [eqMixin of fperm_type T by <:].
Canonical fperm_eqType :=
  Eval hnf in EqType (fperm_type T) fperm_eqMixin.
Definition fperm_choiceMixin :=
  [choiceMixin of fperm_type T by <:].
Canonical fperm_choiceType :=
  Eval hnf in ChoiceType (fperm_type T) fperm_choiceMixin.
Definition fperm_ordMixin :=
  [ordMixin of fperm_type T by <:].
Canonical fperm_ordType :=
  Eval hnf in OrdType (fperm_type T) fperm_ordMixin.

Canonical fperm_of_subType := Eval hnf in [subType of {fperm T}].
Canonical fperm_of_eqType := Eval hnf in [eqType of {fperm T}].
Canonical fperm_of_choiceType := Eval hnf in [choiceType of {fperm T}].
Canonical fperm_of_ordType := Eval hnf in [ordType of {fperm T}].

End WithOrdType.

End Exports.

End FPerm.

Export FPerm.Exports.

Declare Scope fperm_scope.
Delimit Scope fperm_scope with fperm.

Section Operations.

Variable T : ordType.

Implicit Types (s : {fperm T}) (x : T) (X Y : {fset T}).

Local Open Scope fset_scope.

Lemma eq_fperm s1 s2 : s1 =1 s2 <-> s1 = s2.
Proof.
split; last congruence; by move=> /eq_ffun /val_inj.
Qed.

Lemma imfset_supp s : s @: supp s = supp s.
Proof. exact/eqP/(valP s). Qed.

Lemma imfset_suppS s X : fsubset (supp s) X -> s @: X = X.
Proof.
move=> subX; rewrite -(fsetID X (supp s)) imfsetU.
rewrite (fsetIidPr subX) imfset_supp; congr fsetU.
under eq_in_imfset => x /fsetDP [] _ /suppPn -> do [].
by rewrite imfset_id.
Qed.

Lemma fperm_inj s : injective s.
Proof.
move=> x y.
have inj : {in x |: (y |: supp s) &, injective s}.
  apply/imfset_injP; rewrite imfset_suppS //.
  by rewrite fsubsetU // fsubsetU ?fsubsetxx orbT.
by apply: inj; rewrite ?in_fsetU1 ?eqxx // ?orbT.
Qed.

Lemma fperm_supp s x : (s x \in supp s) = (x \in supp s).
Proof.
rewrite -{1}imfset_supp; apply/(sameP idP)/(iffP idP).
  by apply: mem_imfset.
by case/imfsetP=> x' hx' /fperm_inj ->.
Qed.

Lemma fperm_one_subproof : FPerm.axiom (@emptyf T _ _).
Proof. by rewrite /FPerm.axiom supp0 imfset0. Qed.

Definition fperm_one : {fperm T} :=
  @FPerm.FPerm T emptyf fperm_one_subproof.
Notation "1" := fperm_one.

Lemma fperm1 x : 1 x = x.
Proof. by []. Qed.


Lemma mem_suppN s x : (x \notin supp s) = (s x == x).
Proof. by rewrite mem_supp negbK. Qed.


Lemma imfset_supp_sub s X : fsubset (supp s) X -> s @: X = X.
Proof.
move=> h_sub; apply/eq_fset=> x; have h_im_sub := imfsetS s h_sub.
have [in_supp|nin_supp] := boolP (x \in supp s).
  rewrite (fsubsetP h_sub _ in_supp); move/fsubsetP: h_im_sub; apply.
  by rewrite imfset_supp.
move: nin_supp; rewrite mem_supp negbK =>/eqP ex.
apply/(sameP idP)/(iffP idP); first by rewrite -{2}ex; apply: mem_imfset.
case/imfsetP=> [y Py ey]; rewrite {2}ey in ex.
by move/fperm_inj in ex; rewrite ex.
Qed.

Lemma supp1 : supp 1 = fset0.
Proof.
apply/eqP; rewrite -fsubset0; apply/fsubsetP=> x.
by rewrite mem_supp fperm1 eqxx.
Qed.

Lemma supp_eq0 s : (supp s == fset0) = (s == 1).
Proof.
apply/(sameP idP)/(iffP idP)=> [/eqP->|]; first by rewrite supp1.
move=> /eqP e; apply/eqP/eq_fperm=> x; rewrite fperm1; apply/suppPn.
by rewrite e in_fset0.
Qed.

Section Build.

Implicit Types (f : T -> T).

Lemma fperm_def_aux f X : f @: X = X -> FPerm.axiom (mkffun f X).
Proof.
move=> fP; apply/eqP/eq_fset => x; apply/(sameP idP)/(iffP idP).
- rewrite {1}supp_mkffun in_fset mem_filter; case/andP => fx_x x_X.
  move: x x_X fx_x; rewrite -{1}fP => _ /imfsetP [] x x_X -> ffx_fx.
  apply/imfsetP; exists x.
    by rewrite mem_supp mkffunE x_X; apply: contraNN ffx_fx => /eqP {1}->.
  by rewrite mkffunE x_X.
- case/imfsetP => {}x x_X ->.
  move: x_X; rewrite !mem_supp !mkffunE.
  case: ifP => [x_X fx_x|]; last by rewrite eqxx.
  have fx_X : f x \in X by rewrite -fP mem_imfset.
  have inj : {in X &, injective f} by apply/imfset_injP; rewrite fP.
  by rewrite fx_X; apply: contraNN fx_x => /eqP /inj ->.
Qed.

Definition fperm_def f X x :=
  let Y1 := f @: X :\: X in
  let Y2 := X :\: f @: X in
  if x \in Y1 then nth x Y2 (index x Y1) else f x.

Definition fperm f X :=
  odflt 1 (insub (mkffun (fperm_def f X) (X :|: f @: X))).

Lemma fpermE f X : {in X &, injective f} -> {in X, fperm f X =1 f}.
Proof.
move=> /imfset_injP inj x x_X; rewrite /fperm insubT /=; last first.
  by move=> _; rewrite mkffunE in_fsetU /fperm_def /= in_fsetD x_X.
apply/fperm_def_aux; rewrite /fperm_def {x x_X}.
set Y1 := f @: X :\: X; set Y2 := X :\: f @: X.
set g := fun x => if _ then _ else _.
pose h x := if x \in Y2 then nth x Y1 (index x Y2)
            else odflt x (fpick (fun y => f y == x) Y1).
set D := X :|: f @: X.
have sY12 : size Y1 = size Y2.
  apply: (@addnI (size (f @: X :&: X))).
  rewrite -sizesD fsetIC -sizesD; exact/eqP.
have nY1_X x : x \in D -> x \notin Y1 -> x \in X.
  case/fsetUP=> //; by rewrite in_fsetD => ->; rewrite andbT negbK.
have nth_Y2 x : x \in D -> x \in Y1 -> nth x Y2 (index x Y1) \in Y2.
  move=> ??; by rewrite mem_nth // -sY12 index_mem.
have /imfset_injP/eqP g_inj: {in D &, injective g}.
  move=> x y x_D y_D.
  rewrite /g; case: ifPn => x_Y1; case: ifPn => y_Y1.
  - rewrite (set_nth_default y) -?sY12 ?index_mem // => exy.
    have {}exy : index x Y1 = index y Y1.
      by apply/uniqP; eauto; rewrite ?uniq_fset // -?sY12 inE ?index_mem.
    by rewrite -[x](nth_index x x_Y1) exy nth_index.
  - move=> exy; move: (nth_Y2 _ x_D x_Y1).
    by rewrite in_fsetD exy mem_imfset // nY1_X.
  - move=> exy; move: (nth_Y2 _ y_D y_Y1).
    by rewrite in_fsetD -exy mem_imfset // nY1_X.
  - by apply: (imfset_injP _ _ inj); rewrite nY1_X.
apply/eqP; rewrite eqEfsize g_inj leqnn andbT.
apply/fsubsetP => _ /imfsetP [] {}x {}x_X ->.
rewrite /g; case: ifPn => x_Y1; last first.
  by apply/fsetUP; right; rewrite mem_imfset // nY1_X.
by case/fsetDP: (nth_Y2 _ x_X x_Y1) => ? ?; apply/fsetUP; left.
Qed.

Lemma supp_fperm f X : fsubset (supp (fperm f X)) (X :|: f @: X).
Proof.
rewrite /fperm; case: insubP => /= [g _ ->|_]; first exact: supp_mkffun_sub.
by rewrite supp0 fsub0set.
Qed.

Lemma fpermEst f X x : f @: X = X -> fperm f X x = if x \in X then f x else x.
Proof.
move=> st; case: ifPn=> /= [|x_nin].
  by apply/fpermE/imfset_injP/eqP; rewrite st.
apply/suppPn; apply: contra x_nin; apply/fsubsetP.
rewrite -{2}[X]fsetUid -{3}st; exact: supp_fperm.
Qed.

End Build.

Section Renaming.

(* FIXME: find a better name for this *)
Lemma find_fperm (X Y : {fset T}) :
  size X = size Y ->
  exists2 s : {fperm T}, fsubset (supp s) (X :|: Y) & s @: X = Y.
Proof.
move=> size_X.
suff [f f_inj im_f]: exists2 f, {in X &, injective f} & f @: X = Y.
  rewrite -im_f.
  exists (fperm f X); first by rewrite supp_fperm.
  by apply: eq_in_imfset; apply: fpermE.
elim/fset_ind: X Y size_X => [|x X x_nin_X IH] Y.
  rewrite /=; move/esym/eqP; rewrite sizes_eq0=> /eqP ->.
  exists id; first by move=> x; rewrite in_fset0.
  by rewrite imfset0.
rewrite sizesU1 x_nin_X add1n.
elim/fset_ind: Y => [|y Y y_nin_Y _]; first by rewrite sizes0.
rewrite sizesU1 y_nin_Y /= add1n=> - [/IH [f Pf PXY]].
exists (fun x' => if x' == x then y else f x').
  move=> x1 x2 /=; rewrite !in_fsetU1.
  have [-> _|ne1] /= := altP (x1 =P x).
    have [-> _|ne2] //= := altP (x2 =P x).
    move=> x2_in_X ey; move: y_nin_Y; rewrite {}ey -PXY.
    by rewrite mem_imfset.
  move=> x1_in_X.
  have [-> _|ne2] /= := altP (x2 =P x).
    by move=> ey; move: y_nin_Y; rewrite -{}ey -PXY mem_imfset.
  by move: x1_in_X; apply: Pf.
rewrite imfsetU1 eqxx -{}PXY; congr fsetU.
apply/eq_in_imfset=> x' x'_in_X.
by move: x'_in_X x_nin_X; have [->|//] := altP eqP=> ->.
Qed.

End Renaming.

Section Inverse.

Variable s : {fperm T}.

Local Notation inv_def := (fun x => odflt x (fpick (pred1 x \o s) (supp s))).

Lemma fperm_inv_subproof : inv_def @: supp s = supp s.
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  move=> x_in_supp; apply/imfsetP; exists (s x).
    by rewrite -imfset_supp (mem_imfset _ x_in_supp).
  case: fpickP=> [y' /= /eqP/esym e _|/(_ _ x_in_supp) /=].
    exact: fperm_inj e.
  by rewrite eqxx.
by case/imfsetP=> [y Py -> {x}]; case: fpickP.
Qed.

Definition fperm_inv := locked (fperm inv_def (supp s)).

Lemma fpermK : cancel s fperm_inv.
Proof.
move=> x; rewrite /fperm_inv -lock fpermEst; last exact: fperm_inv_subproof.
rewrite fperm_supp; case: ifPn=> [x_in_supp|]; last exact/suppPn.
case: fpickP => [y /= /eqP/esym /fperm_inj-> //|/(_ _ x_in_supp) /=].
by rewrite eqxx.
Qed.

Lemma fpermKV : cancel fperm_inv s.
Proof.
move=> x; rewrite /fperm_inv -lock fpermEst; last exact: fperm_inv_subproof.
case: ifPn=> [x_in_supp|].
  case: fpickP=> [x' /= /eqP/esym -> //|/=].
  rewrite -imfset_supp in x_in_supp; case/imfsetP: x_in_supp=> [x' Px' ->].
  by move/(_ _ Px'); rewrite eqxx.
by rewrite mem_supp negbK => /eqP.
Qed.

Lemma supp_inv : supp fperm_inv = supp s.
Proof.
apply/eq_fset=> x; apply/(sameP idP)/(iffP idP).
  by rewrite !mem_supp; apply: contra => /eqP {1}<-; rewrite fpermKV eqxx.
by rewrite !mem_supp; apply: contra=> /eqP {1}<-; rewrite fpermK eqxx.
Qed.

Lemma fperm_suppV x : (fperm_inv x \in supp s) = (x \in supp s).
Proof. by rewrite -{1}supp_inv fperm_supp supp_inv. Qed.

End Inverse.

Lemma fperm_mul_subproof s1 s2 :
  (s1 \o s2) @: (supp s1 :|: supp s2) = supp s1 :|: supp s2.
Proof.
by rewrite imfset_comp !imfset_supp_sub // ?fsubsetUr // fsubsetUl.
Qed.

Definition fperm_mul s1 s2 := locked (fperm (s1 \o s2) (supp s1 :|: supp s2)).

Infix "*" := fperm_mul.
Notation "x ^-1" := (fperm_inv x).

Lemma fpermM s1 s2 : s1 * s2 =1 s1 \o s2.
Proof.
move=> x; rewrite /fperm_mul -lock fpermEst; last exact: fperm_mul_subproof.
have [|nin_supp] //= := boolP (x \in _).
rewrite in_fsetU negb_or !mem_supp !negbK in nin_supp.
by case/andP: nin_supp=> [/eqP h1 /eqP ->]; rewrite h1.
Qed.

Lemma supp_mul s1 s2 : fsubset (supp (s1 * s2)) (supp s1 :|: supp s2).
Proof.
apply/fsubsetP=> x; rewrite in_fsetU !mem_supp fpermM /=.
have [-> -> //|] := altP (s2 x =P x).
by rewrite orbT.
Qed.

Lemma suppJ s1 s2 : supp (s1 * s2 * s1^-1) = s1 @: supp s2.
Proof.
apply/eq_fset=> x; apply/esym/imfsetP; rewrite mem_supp fpermM /= fpermM /=.
rewrite (can2_eq (fpermK s1) (fpermKV s1)).
have [e|ne] /= := altP eqP.
  case=> [y Py e']; move: e Py.
  by rewrite e' fpermK mem_supp=> ->; rewrite eqxx.
exists (s1^-1 x); last by rewrite fpermKV.
by rewrite mem_supp.
Qed.

Lemma fperm_mulC s1 s2 :
  fdisjoint (supp s1) (supp s2) ->
  s1 * s2 = s2 * s1.
Proof.
move=> dis; apply/eq_fperm=> x; rewrite !fpermM /=.
have [ins1|nins1] := boolP (x \in supp s1).
  move: (ins1); rewrite -fperm_supp=> ins1'.
  move/fdisjointP in dis.
  move/suppPn: (dis _ ins1)=> ->.
  by move/suppPn: (dis _ ins1')=> ->.
have [ins2|nins2] := boolP (x \in supp s2).
  move: (ins2); rewrite -fperm_supp=> ins2'.
  move: dis; rewrite fdisjointC=> /fdisjointP dis.
  move/suppPn: (dis _ ins2)=> ->.
  by move/suppPn: (dis _ ins2')=> ->.
move: nins1 nins2=> /suppPn nins1 /suppPn nins2.
by rewrite nins1 nins2.
Qed.

Lemma fperm_mul1s : left_id 1 fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM. Qed.

Lemma fperm_muls1 : right_id 1 fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM. Qed.

Lemma fperm_mulsV : right_inverse 1 fperm_inv fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM /= fpermKV. Qed.

Lemma fperm_mulVs : left_inverse 1 fperm_inv fperm_mul.
Proof. by move=> s; apply/eq_fperm=> x; rewrite fpermM /= fpermK. Qed.

Lemma fperm_mulA : associative fperm_mul.
Proof. by move=> s1 s2 s3; apply/eq_fperm=> x; rewrite !fpermM /= !fpermM. Qed.

Lemma fperm_inv_mul : {morph fperm_inv : s1 s2 / s1 * s2 >-> s2 * s1}.
Proof.
move=> s1 s2 /=.
rewrite -[s2^-1 * _]fperm_mul1s -(fperm_mulVs (s1 * s2)) -2!fperm_mulA.
by rewrite (fperm_mulA s2) fperm_mulsV fperm_mul1s fperm_mulsV fperm_muls1.
Qed.

Lemma fperm_mulsK : right_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -fperm_mulA fperm_mulsV fperm_muls1. Qed.

Lemma fperm_mulKs : left_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite fperm_mulA fperm_mulVs fperm_mul1s. Qed.

Lemma fperm_mulsI : right_injective fperm_mul.
Proof. by move=> s1 s2 s3 e; rewrite -(fperm_mulKs s1 s2) e fperm_mulKs. Qed.

Lemma fperm_mulIs : left_injective fperm_mul.
Proof. by move=> s1 s2 s3 e; rewrite -(fperm_mulsK s1 s2) e fperm_mulsK. Qed.

Lemma fperm_invK : involutive fperm_inv.
Proof.
by move=> s; apply (@fperm_mulsI s^-1); rewrite fperm_mulsV fperm_mulVs.
Qed.

Lemma fperm_mulsKV : rev_right_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -{2}(fperm_invK s1) fperm_mulsK. Qed.

Lemma fperm_mulKVs : rev_left_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -{1}(fperm_invK s1) fperm_mulKs. Qed.

Notation fperm2_def x y := [fun z => z with x |-> y, y |-> x].

Lemma fperm2_subproof x y :
   fperm2_def x y @: [fset x; y] = [fset x; y].
Proof.
apply/eq_fset=> z; apply/(sameP idP)/(iffP idP).
  case/fset2P=> [->|->] /=; apply/imfsetP;
  [exists y; try apply fset22|exists x; try apply fset21].
    by rewrite /= eqxx; have [->|] //= := altP eqP.
  by rewrite /= eqxx.
case/imfsetP=> [w /fset2P [->|->] ->] /=; rewrite eqxx ?fset22 //.
case: ifP=> ?; by [apply fset21|apply fset22].
Qed.

Definition fperm2 x y := fperm (fperm2_def x y) [fset x; y].

Lemma fperm2E x y : fperm2 x y =1 [fun z => z with x |-> y, y |-> x].
Proof.
move=> z; rewrite fpermEst; last exact: fperm2_subproof.
rewrite /= in_fset2.
have [->|] := altP eqP => //= ?.
by have [?|] := altP eqP => //= ?.
Qed.

CoInductive fperm2_spec x y z : T -> Type :=
| FPerm2First  of z = x : fperm2_spec x y z y
| FPerm2Second of z = y : fperm2_spec x y z x
| FPerm2None   of z <> x & z <> y : fperm2_spec x y z z.

Lemma fperm2P x y z : fperm2_spec x y z (fperm2 x y z).
Proof. by rewrite fperm2E /=; do 2?[case: eqP=> //]; constructor; auto. Qed.

Lemma fperm2L x y : fperm2 x y x = y.
Proof. by rewrite fperm2E /= eqxx. Qed.

Lemma fperm2R x y : fperm2 x y y = x.
Proof. by rewrite fperm2E /= eqxx; case: eqP=> [->|]. Qed.

Lemma fperm2D x y z : z != x -> z != y -> fperm2 x y z = z.
Proof. by rewrite fperm2E /= => /negbTE-> /negbTE->. Qed.

Lemma fperm2C x y : fperm2 x y = fperm2 y x.
Proof. apply/eq_fperm=> z; do 2?[case: fperm2P=> //]; congruence. Qed.

Lemma fperm2V x y : (fperm2 x y)^-1 = fperm2 x y.
Proof.
rewrite -[in LHS](fperm_muls1 _^-1).
apply/(canLR (fperm_mulKs (fperm2 x y)))/eq_fperm=> z.
rewrite fperm1 fpermM /= !fperm2E /=; have [->{z}|] := altP (z =P x).
  by rewrite eqxx; case: ifP=> // /eqP ->.
have [->{z}|] := altP (z =P y); first by rewrite eqxx.
by move=> /negbTE -> /negbTE ->.
Qed.

Lemma fperm2xx x : fperm2 x x = 1.
Proof.
apply/eq_fperm=> y; rewrite fperm2E fperm1 /=.
by have [->|] := altP (y =P x).
Qed.

Lemma supp_fperm2 x y :
  supp (fperm2 x y) = if x == y then fset0 else [fset x; y].
Proof.
have [<-{y}|ne] := altP eqP; first by rewrite fperm2xx supp1.
apply/eq_fset=> z; rewrite mem_supp /= in_fset2.
case: fperm2P => [->|->|]; [rewrite eq_sym| |]; rewrite ?ne ?eqxx ?orbT //.
by move=> /eqP/negbTE-> /eqP/negbTE->.
Qed.

Lemma fsubset_supp_fperm2 x y : fsubset (supp (fperm2 x y)) [fset x; y].
Proof.
by rewrite supp_fperm2 fun_if if_arg fsub0set fsubsetxx; case: (_ == _).
Qed.

Lemma fperm2_rect (P : {fperm T} -> Type) :
  P 1 ->
  (forall x y s, x \notin supp s -> y \in supp (fperm2 x y * s) ->
                 P s -> P (fperm2 x y * s)) ->
  forall s, P s.
Proof.
move=> P1 PM s; move: {2}(size _) (leqnn (size (supp s)))=> n.
elim: n s=> [|n IH] s; first by rewrite leqn0 sizes_eq0 supp_eq0=> /eqP ->.
case e: (supp s) / fsetP=>[|x X Px].
  by move/eqP: e; rewrite supp_eq0=> /eqP ->.
rewrite sizesU1 Px ltnS -(fperm_mulKs (fperm2 x (s x)) s) fperm2V=> es.
apply: PM; first by apply/suppPn; rewrite fpermM /= fperm2R.
  by rewrite -{1}fperm2V fperm_mulKs fperm_supp e in_fsetU1 eqxx.
apply: IH; rewrite (leq_trans _ es) // {es}; apply/fsubset_leq_size/fsubsetP.
move=> y; rewrite mem_supp fpermM /=; case: fperm2P.
- move=> ex ny; have: y \in supp s.
    by have [//|/suppPn ey] := boolP (y \in _); rewrite -ex !ey eqxx in ny.
  by rewrite e; case/fsetU1P=> [ey|//]; rewrite -ey ex ey eqxx in ny.
- by move/fperm_inj=> ->; rewrite eqxx.
move=> _ /eqP; rewrite (inj_eq (@fperm_inj _))=> e2.
by rewrite -mem_supp e in_fsetU1 (negbTE e2).
Qed.

Definition enum_fperm X : {fset {fperm T}} :=
  fset (pmap (obind insub \o insub) (enum_fmap X X)).

Lemma enum_fpermE X s : fsubset (supp s) X = (s \in enum_fperm X).
Proof.
rewrite /enum_fperm in_fset mem_pmap; apply/idP/mapP.
  move=> supp_s; exists (val (val s)); last by rewrite /= !valK /= valK.
  apply/enum_fmapP; split; first by move/fsubsetP: supp_s.
  move=> x /codommP [x' Px']; move/fsubsetP: supp_s; apply.
  have <- : s x' = x by rewrite /appf Px'.
  by rewrite fperm_supp /supp mem_domm Px'.
move=> [s' Ps' Pss']; case/enum_fmapP: Ps' => /fsubsetP.
move: Pss' => /=; case: insubP => //= ? _ <-.
by case: insubP => //= ? _ <- [] <-.
Qed.

End Operations.

Arguments fperm_one {_}.
Prenex Implicits fperm_inv fperm_mul fperm2.

Delimit Scope fperm_scope with fperm.

Notation "1" := fperm_one : fperm_scope.
Infix "*" := fperm_mul : fperm_scope.
Notation "x ^-1" := (fperm_inv x) : fperm_scope.

Section Trans.

Local Open Scope fperm_scope.

Lemma inj_fperm2 (T T' : ordType) (f : T -> T') x y z :
  injective f -> f (fperm2 x y z) = fperm2 (f x) (f y) (f z).
Proof.
move=> f_inj; case: (fperm2P x)=> [->|->| ]; rewrite ?fperm2L ?fperm2R //.
by move=>/eqP hx /eqP hy; apply/esym/fperm2D; rewrite (inj_eq f_inj).
Qed.

Lemma fperm2J (T : ordType) s (x y : T) :
  s * fperm2 x y * s^-1 = fperm2 (s x) (s y).
Proof.
apply/eq_fperm=> z; rewrite fpermM /= fpermM /= inj_fperm2 ?fpermKV //.
exact: fperm_inj.
Qed.

End Trans.
