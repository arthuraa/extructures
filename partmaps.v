Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PartMap.

Section Def.

Variables (T : countType) (S : Type).

Fixpoint axiom (s : seq T) : bool :=
  if s is k :: s then
    all [pred k' | pickle k < pickle k'] s && axiom s
  else true.

Fixpoint loc_axiom' k (s : seq T) : bool :=
  if s is k' :: s then (pickle k < pickle k') && loc_axiom' k' s
  else true.

Definition loc_axiom s :=
  if s is k :: s then loc_axiom' k s
  else true.

Lemma axiomE : axiom =1 loc_axiom.
Proof.
case=> // k s /=; elim: s k=> //= k' s <- k.
have [k_k'|] //= := boolP (_ < _).
rewrite andbA; congr andb.
have [/allP /= H|] //= := boolP (all [pred k'' | pickle k' < pickle k''] s);
  last by rewrite andbF.
by rewrite andbT; apply/allP=> k'' /H /=; apply: ltn_trans.
Qed.

Record type := PMap {pmval :> seq (T * S); _ : axiom [seq p.1 | p <- pmval]}.

End Def.

Module Exports.

Notation partmap := type.
Canonical partmap_subType T S := [subType for @pmval T S].
Definition partmap_eqMixin T (S : eqType) := [eqMixin of type T S by <:].
Canonical partmap_eqType T (S : eqType) :=
  Eval hnf in EqType (type T S) (partmap_eqMixin T S).
Definition partmap_choiceMixin T (S : choiceType) :=
  [choiceMixin of type T S by <:].
Canonical partmap_choiceType T (S : choiceType) :=
  Eval hnf in ChoiceType (type T S) (partmap_choiceMixin T S).
Definition partmap_countMixin T (S : countType) :=
  [countMixin of type T S by <:].
Canonical partmap_countType T (S : countType) :=
  Eval hnf in CountType (type T S) (partmap_countMixin T S).
Canonical partmap_subCountType T (S : countType) :=
  [subCountType of type T S].

End Exports.

End PartMap.

Export PartMap.Exports.

Section Operations.

Variables (T : countType) (S : Type).

Local Coercion PartMap.pmval : partmap >-> seq.

Fixpoint get' (s : seq (T * S)) (k : T) : option S :=
  if s is p :: s then
    if k == p.1 then Some p.2
    else get' s k
  else None.

Definition get (m : partmap T S) k := get' m k.

Fixpoint set' (s : seq (T * S)) (k : T) (v : S) : seq (T * S) :=
  if s is p :: s' then
    if pickle k < pickle p.1 then (k, v) :: s
    else if k == p.1 then (k, v) :: s'
    else p :: set' s' k v
  else [:: (k, v)].

Lemma set_proof (s : seq (T * S)) k v (Ps : PartMap.axiom [seq p.1 | p <- s]) :
  PartMap.axiom [seq p.1 | p <- set' s k v].
Proof.
move: s Ps.
have E: forall s, [seq p.1 | p <- set' s k v] =i k :: [seq p.1 | p <- s].
  elim=> // p s /= IH k'; rewrite ![in X in X = _]fun_if /= !inE.
  rewrite IH inE -(inj_eq (pcan_inj (@pickleK T)) k).
  case: ltngtP=> // H; try by bool_congr.
  by rewrite (pcan_inj (@pickleK T) H) orbA orbb.
elim=> // p s /= IH /andP [lb Ps].
rewrite -(inj_eq (pcan_inj (@pickleK T)) k) ![in X in is_true X]fun_if /=.
rewrite {}IH // Ps !andbT.
rewrite !(eq_all_r (E s)) {E} /= lb andbT; case: ltngtP=> //=.
  by move=> k_p; move/allP in lb; apply/allP=> p' /lb /=; apply: ltn_trans.
by move=> /(pcan_inj (@pickleK T)) ->.
Qed.

Definition set (s : partmap T S) k v := PartMap.PMap (set_proof k v (valP s)).

Lemma pmmap_proof S' (f : S -> S') (m : partmap T S) :
  PartMap.axiom (map (fun p => p.1) (map (fun p => (p.1, f p.2)) m)).
Proof. by rewrite -!map_comp; apply: (valP m). Qed.

Definition pmmap S' (f : S -> S') m := PartMap.PMap (pmmap_proof f m).

Lemma pmfilter_proof (a : pred S) (m : partmap T S) :
  PartMap.axiom [seq p.1 | p <- m & a p.2].
Proof.
case: m=> /=; elim=> [|p s IH /= /andP [lb /IH {IH} IH]] //=.
rewrite 2!fun_if /= {}IH andbT; case: (a p.2)=> //.
elim: s lb=> //= p' s IH /andP [lb /IH {IH} IH].
by rewrite 2!fun_if /= lb IH; case: (a _).
Qed.

Definition pmfilter (a : pred S) (m : partmap T S) :=
  PartMap.PMap (pmfilter_proof a m).

Fixpoint pmrem' (s : seq (T * S)) k :=
  if s is p :: s then
    if p.1 == k then s else p :: pmrem' s k
  else [::].

Lemma pmrem_proof s k :
  PartMap.axiom [seq p.1 | p <- s] ->
  PartMap.axiom [seq p.1 | p <- pmrem' s k].
Proof.
elim: s=> [|p s IH /= /andP [lb Ps]] //=.
rewrite 2!fun_if /= {}IH // {}Ps andbT; case: (_ == _)=> //.
elim: s lb=> // p' s IH /= /andP [lb Ps].
by rewrite 2!fun_if /= {}IH // /= lb Ps; case: (_ == _).
Qed.

Definition pmrem (m : partmap T S) k :=
  PartMap.PMap (pmrem_proof k (valP m)).

End Operations.

Coercion get : partmap >-> Funclass.

Section Properties.

Variables (T : countType) (S : Type).

Lemma getE (m : partmap T S) : [pred k | m k] =i [seq p.1 | p <- val m].
Proof.
case: m => [s Ps] k; rewrite /get /= {Ps} inE.
elim: s=> [|p s IH] //=; rewrite !inE [in LHS]fun_if /= {}IH.
by case: (_ == _).
Qed.

Lemma get_set (m : partmap T S) k v k' :
  set m k v k' =
  if k' == k then Some v else get m k'.
Proof.
case: m; rewrite /get /set /=; elim=> //= p s IH /andP [lb /IH {IH} IH].
rewrite ![in LHS](fun_if, if_arg) /= {}IH.
have [->{k'}|Hne] := altP (k' =P k);
  rewrite -(inj_eq (pcan_inj (@pickleK T)) k p.1); case: ltngtP=> //.
by move=> /(pcan_inj (@pickleK T)) <-; rewrite (negbTE Hne).
Qed.

Lemma get_map S' (f : S -> S') (m : partmap T S) : pmmap f m =1 omap f \o m.
Proof.
case: m=> [s Ps] k; rewrite /pmmap /get /=; elim: s {Ps}=> [|[k' v] s IH] //=.
by rewrite {}IH ![in RHS]fun_if /=.
Qed.

Lemma get_filter (a : pred S) (m : partmap T S) :
  pmfilter a m =1 obind (fun x => if a x then Some x else None) \o m.
Proof.
case: m=> [s Ps] k; rewrite /pmfilter /get /=.
elim: s Ps=> [|p s IH /= /andP [lb /IH {IH} IH]] //=.
rewrite ![in LHS](fun_if, if_arg) /= {}IH.
have [-> {k}|k_p] //= := altP (_ =P _); case: (a _)=> //.
elim: s lb => [|p' s IH /andP /= [lb /IH {IH} IH]] //=.
by move: lb; have [->|//] := altP (_ =P _); rewrite ltnn.
Qed.

Lemma get_rem (m : partmap T S) k k' :
  pmrem m k k' =
  if k' == k then None else get m k'.
Proof.
case: m; rewrite /pmrem /get /=; elim=> [|p s IH /= /andP [lb Ps]] //=.
  by case: (_ == _).
rewrite ![in LHS](fun_if, if_arg) /= {}IH //.
move: {Ps} lb; have [-> lb|ne lb] := altP (_ =P _).
  have [-> {k' p}|ne //] := altP (_ =P _).
  elim: s lb=> [|p s IH /= /andP [lb /IH {IH} ->]] //=.
  by move: lb; have [->|//] := altP (_ =P _); rewrite ltnn.
have [-> {k'}|ne'] // := altP (k' =P k).
by rewrite eq_sym (negbTE ne).
Qed.

Lemma eq_partmap (m1 m2 : partmap T S) : m1 =1 m2 -> m1 = m2.
Proof.
have in_seq: forall s : seq (T * S), [pred k | get' s k] =i [seq p.1 | p <- s].
  elim=> [|p s IH] k; rewrite /= !inE // -IH inE.
  by case: (k == p.1).
case: m1 m2 => [s1 Ps1] [s2 Ps2]; rewrite /get /= => s1_s2.
apply: val_inj=> /=.
elim: s1 Ps1 s2 Ps2 s1_s2
      => [_|[k1 v1] s1 IH /= /andP [lb1 /IH {IH} IH]]
         [_|[k2 v2] s2 /= /andP [lb2 Ps2]] //
      => [/(_ k2)|/(_ k1)| ]; try by rewrite eqxx.
move/IH: Ps2=> {IH} IH s1_s2.
wlog: k1 k2 v1 v2 s1 s2 lb1 lb2 s1_s2 IH / pickle k1 <= pickle k2.
  move=> H.
  case: (ltngtP (pickle k1) (pickle k2)) => [/ltnW|/ltnW k2_k1|/eq_leq]; eauto.
  symmetry; apply: H; eauto.
    by move=> k /=; rewrite s1_s2.
  by move=> H'; rewrite IH //.
rewrite leq_eqVlt=> /orP [/eqP/(pcan_inj (@pickleK T)) k1_k2|k1_k2].
  rewrite -{}k1_k2 {k2} in lb2 s1_s2 *.
  move: (s1_s2 k1); rewrite eqxx=> - [->].
  rewrite {}IH // => k; move: {s1_s2} (s1_s2 k).
  have [-> {k} _|ne ?] // := altP (_ =P _).
  move: (in_seq s1 k1) (in_seq s2 k1); rewrite !inE.
  case: (get' s1 k1) (get' s2 k1) => [v1'|] [v2'|] //=.
  - by move=> _ /esym/(allP lb2) /=; rewrite ltnn.
  - by move=> /esym/(allP lb1) /=; rewrite ltnn.
  by move=> _ /esym/(allP lb2) /=; rewrite ltnn.
move/(_ k1)/esym: s1_s2 k1_k2; rewrite eqxx.
have [->|_ s1_s2] := altP (_ =P _); first by rewrite ltnn.
move/(_ s2 k1): in_seq; rewrite inE {}s1_s2 /= => /esym/(allP lb2)/ltnW /=.
by rewrite ltnNge => ->.
Qed.

End Properties.
