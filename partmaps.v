Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PartMap.

Section Def.

Variables (T : countType) (S : Type).

Fixpoint axiom (s : seq (T * S)) : bool :=
  if s is p :: s then
    all [pred p' | pickle p.1 < pickle p'.1] s && axiom s
  else true.

Fixpoint loc_axiom' k (s : seq (T * S)) : bool :=
  if s is p' :: s then (pickle k < pickle p'.1) && loc_axiom' p'.1 s
  else true.

Definition loc_axiom s :=
  if s is p :: s then loc_axiom' p.1 s
  else true.

Lemma axiomE : axiom =1 loc_axiom.
Proof.
case=> // p s /=; elim: s p=> //= p' s <- p.
have [p_p'|] //= := boolP (_ < _).
pose is_lb k := all [pred p | k < pickle p] [seq p.1 | p <- s].
have E : forall k, all [pred p | k < pickle p.1] s = is_lb k.
  by move=> lb; rewrite /is_lb all_map //.
rewrite !{}E.
suff <- : is_lb (pickle p.1) && is_lb (pickle p'.1) = is_lb (pickle p'.1)
  by bool_congr.
have [/allP /= H|] //= := boolP (is_lb (pickle p'.1)); last by rewrite andbF.
by rewrite andbT; apply/allP=> k /H /=; apply: ltn_trans.
Qed.

Record type := PMap {pmval :> seq _; _ : axiom pmval}.

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

Lemma set_proof (s : seq (T * S)) k v (Ps : PartMap.axiom s) :
  PartMap.axiom (set' s k v).
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
rewrite -!(all_map (fun p => p.1) [pred p' | _ < pickle p']) in lb *.
rewrite !(eq_all_r (E s)) {E} /= lb andbT; case: ltngtP=> //=.
  by move=> k_p; move/allP in lb; apply/allP=> p' /lb /=; apply: ltn_trans.
by move=> /(pcan_inj (@pickleK T)) ->.
Qed.

Definition set (s : partmap T S) k v := PartMap.PMap (set_proof k v (valP s)).

Lemma get_set m k v k' :
  get (set m k v) k' =
  if k' == k then Some v else get m k'.
Proof.
case: m; rewrite /get /set /=; elim=> //= p s IH /andP [lb /IH {IH} IH].
rewrite ![in LHS](fun_if, if_arg) /= {}IH.
have [->{k'}|Hne] := altP (k' =P k);
  rewrite -(inj_eq (pcan_inj (@pickleK T)) k p.1); case: ltngtP=> //.
by move=> /(pcan_inj (@pickleK T)) <-; rewrite (negbTE Hne).
Qed.

Lemma partmap_eq_ext m1 m2 : get m1 =1 get m2 -> m1 = m2.
Proof.
have in_seq: forall s, [pred k | get' s k] =i [seq p.1 | p <- s].
  elim=> [|p s IH] k; rewrite /= !inE // -IH inE.
  by case: (k == p.1).
case: m1 m2 => [s1 Ps1] [s2 Ps2]; rewrite /get /= => s1_s2.
apply: val_inj=> /=.
elim: s1 Ps1 s2 Ps2 s1_s2
      => [_|[k1 v1] s1 IH /= /andP [lb1 /IH {IH} IH]]
         [_|[k2 v2] s2 /= /andP [lb2 Ps2]] //
      => [/(_ k2)|/(_ k1)| ]; try by rewrite eqxx.
move/IH: Ps2=> {IH} IH s1_s2.
rewrite -!(all_map (fun p => p.1) [pred p' | _ < pickle p']) in lb1 lb2.
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

End Operations.
