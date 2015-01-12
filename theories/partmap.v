Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype.
Require Import ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PartMap.

Section Def.

Variables (T : ordType) (S : Type).

Local Open Scope ord_scope.

Fixpoint axiom (s : seq T) : bool :=
  if s is k :: s then
    all [pred k' | k < k'] s && axiom s
  else true.

Fixpoint loc_axiom' k (s : seq T) : bool :=
  if s is k' :: s then (k < k') && loc_axiom' k' s
  else true.

Definition loc_axiom s :=
  if s is k :: s then loc_axiom' k s
  else true.

Lemma axiomE : axiom =1 loc_axiom.
Proof.
case=> // k s /=; elim: s k=> //= k' s <- k.
have [k_k'|] //= := boolP (_ < _).
rewrite andbA; congr andb.
have [/allP /= H|] //= := boolP (all [pred k'' | k' < k''] s);
  last by rewrite andbF.
by rewrite andbT; apply/allP=> k'' /H /=; apply: Ord.lt_trans.
Qed.

Record partmap_type := PMap {pmval :> seq (T * S); _ : axiom [seq p.1 | p <- pmval]}.
Definition partmap_of of phant (T -> S) := partmap_type.
Identity Coercion type_of_partmap_of : partmap_of >-> partmap_type.

End Def.

Module Exports.

Notation "{ 'partmap' T }" := (@partmap_of _ _ (Phant T))
  (at level 0, format "{ 'partmap'  T }") : type_scope.
Canonical partmap_subType T S := [subType for @pmval T S].
Definition partmap_eqMixin T (S : eqType) :=
  [eqMixin of partmap_type T S by <:].
Canonical partmap_eqType T (S : eqType) :=
  Eval hnf in EqType (partmap_type T S) (partmap_eqMixin T S).

(*

Still need to rethink the interface hierarchy to allow this...

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
*)

End Exports.

End PartMap.

Export PartMap.Exports.

Section Operations.

Variables (T : ordType) (S : Type).

Local Coercion PartMap.pmval : PartMap.partmap_type >-> seq.
Local Open Scope ord_scope.

Fixpoint getm' (s : seq (T * S)) (k : T) : option S :=
  if s is p :: s then
    if k == p.1 then Some p.2
    else getm' s k
  else None.

Definition getm (m : PartMap.partmap_type T S) k := getm' m k.

Fixpoint setm' (s : seq (T * S)) (k : T) (v : S) : seq (T * S) :=
  if s is p :: s' then
    if k < p.1 then (k, v) :: s
    else if k == p.1 then (k, v) :: s'
    else p :: setm' s' k v
  else [:: (k, v)].

Lemma setm_proof (s : seq (T * S)) k v (Ps : PartMap.axiom [seq p.1 | p <- s]) :
  PartMap.axiom [seq p.1 | p <- setm' s k v].
Proof.
move: s Ps.
have E: forall s, [seq p.1 | p <- setm' s k v] =i k :: [seq p.1 | p <- s].
  elim=> // p s /= IH k'; rewrite ![in X in X = _]fun_if /= !inE.
  rewrite IH inE.
  case: (Ord.ltgtP k p.1) => // H; try by bool_congr.
  by rewrite H orbA orbb.
elim=> // p s /= IH /andP [lb Ps].
rewrite ![in X in is_true X]fun_if /= {}IH // Ps !andbT.
rewrite !(eq_all_r (E s)) {E} /= lb andbT; case: Ord.ltgtP=> //=.
  by move=> k_p; move/allP in lb; apply/allP=> p' /lb /=; apply: Ord.lt_trans.
by move=> ->.
Qed.

Definition setm (m : {partmap T -> S}) k v :=
  PartMap.PMap (setm_proof k v (valP m)).

Definition updm (m : {partmap T -> S}) k v :=
  if getm m k then Some (setm m k v) else None.

Definition unionm (m1 m2 : {partmap T -> S}) :=
  foldr (fun p m => setm m p.1 p.2) m2 m1.

Lemma mapm_proof S' (f : S -> S') (m : {partmap T -> S}) :
  PartMap.axiom (map (fun p => p.1) (map (fun p => (p.1, f p.2)) m)).
Proof. by rewrite -!map_comp; apply: (valP m). Qed.

Definition mapm S' (f : S -> S') m := PartMap.PMap (mapm_proof f m).

Lemma filterm_proof (a : pred S) (m : {partmap T -> S}) :
  PartMap.axiom [seq p.1 | p <- m & a p.2].
Proof.
case: m=> /=; elim=> [|p s IH /= /andP [lb /IH {IH} IH]] //=.
rewrite 2!fun_if /= {}IH andbT; case: (a p.2)=> //.
elim: s lb=> //= p' s IH /andP [lb /IH {IH} IH].
by rewrite 2!fun_if /= lb IH; case: (a _).
Qed.

Definition filterm (a : pred S) (m : {partmap T -> S}) :=
  PartMap.PMap (filterm_proof a m).

Fixpoint remm' (s : seq (T * S)) k :=
  if s is p :: s then
    if p.1 == k then s else p :: remm' s k
  else [::].

Lemma remm_proof s k :
  PartMap.axiom [seq p.1 | p <- s] ->
  PartMap.axiom [seq p.1 | p <- remm' s k].
Proof.
elim: s=> [|p s IH /= /andP [lb Ps]] //=.
rewrite 2!fun_if /= {}IH // {}Ps andbT; case: (_ == _)=> //.
elim: s lb=> // p' s IH /= /andP [lb Ps].
by rewrite 2!fun_if /= {}IH // /= lb Ps; case: (_ == _).
Qed.

Definition remm (m : {partmap T -> S}) k :=
  PartMap.PMap (remm_proof k (valP m)).

Definition emptym : {partmap T -> S} :=
  @PartMap.PMap T S [::] erefl.

Definition mkpartmap (kvs : seq (T * S)) : {partmap T -> S} :=
  foldr (fun kv m => setm m kv.1 kv.2) emptym kvs.

Definition mem_partmap (m : {partmap T -> S}) :=
  [pred k : T | getm m k].

Canonical mem_partmap_predType := mkPredType mem_partmap.

End Operations.

Coercion getm : PartMap.partmap_type >-> Funclass.

Arguments emptym {_ _}.
Arguments unionm {_ _} _ _.

Notation "[ 'partmap' kv1 ; .. ; kvn ]" :=
  (mkpartmap (cons kv1 .. (cons kvn nil) ..))
  (at level 0, format "[ 'partmap'  '[' kv1 ; '/' .. ; '/' kvn ']' ]")
  : form_scope.

Section Properties.

Variables (T : ordType) (S : Type).
Local Open Scope ord_scope.

Lemma getmE (m : {partmap T -> S}) : [pred k | m k] =i [seq p.1 | p <- val m].
Proof.
case: m => [s Ps] k; rewrite /getm /= {Ps} inE.
elim: s=> [|p s IH] //=; rewrite !inE [in LHS]fun_if /= {}IH.
by case: (_ == _).
Qed.

Lemma getm_set (m : {partmap T -> S}) k v k' :
  setm m k v k' =
  if k' == k then Some v else getm m k'.
Proof.
case: m; rewrite /getm /setm /=; elim=> //= p s IH /andP [lb /IH {IH} IH].
rewrite ![in LHS](fun_if, if_arg) /= {}IH.
have [->{k'}|Hne] := altP (k' =P k); case: (Ord.ltgtP k) => //.
by move=> <-; rewrite (negbTE Hne).
Qed.

Lemma mem_unionm (m1 m2 : {partmap T -> S}) k :
  k \in unionm m1 m2 = (k \in m1) || (k \in m2).
Proof.
rewrite /unionm /=; case: m1=> [m1 Pm1] /=.
rewrite [in X in X || _]/in_mem /= [in X in X || _]/getm /= {Pm1}.
elim: m1 => [|p m1 IH] //=; rewrite {1}/in_mem /= getm_set.
by case: (_ == _).
Qed.

Lemma getm_union (m1 m2 : {partmap T -> S}) k :
  unionm m1 m2 k = if m1 k then m1 k else m2 k.
Proof.
case: m1 => [m1 Pm1]; rewrite /unionm {2 3}/getm /= {Pm1}.
elim: m1 => [|p m1 IH] //=.
by rewrite getm_set {}IH; case: (_ == _).
Qed.

Lemma emptymP : @emptym T S =1 [fun : T => None].
Proof. by []. Qed.

Lemma getm_map S' (f : S -> S') (m : {partmap T -> S}) :
  mapm f m =1 omap f \o m.
Proof.
case: m=> [s Ps] k; rewrite /mapm /getm /=.
by elim: s {Ps}=> [|[k' v] s IH] //=; rewrite {}IH ![in RHS]fun_if /=.
Qed.

Lemma getm_filter (a : pred S) (m : {partmap T -> S}) :
  filterm a m =1 obind (fun x => if a x then Some x else None) \o m.
Proof.
case: m=> [s Ps] k; rewrite /filterm /getm /=.
elim: s Ps=> [|p s IH /= /andP [lb /IH {IH} IH]] //=.
rewrite ![in LHS](fun_if, if_arg) /= {}IH.
have [-> {k}|k_p] //= := altP (_ =P _); case: (a _)=> //.
elim: s lb => [|p' s IH /andP /= [lb /IH {IH} IH]] //=.
by move: lb; have [->|//] := altP (_ =P _); rewrite Ord.ltxx.
Qed.

Lemma getm_rem (m : {partmap T -> S}) k k' :
  remm m k k' =
  if k' == k then None else getm m k'.
Proof.
case: m; rewrite /remm /getm /=; elim=> [|p s IH /= /andP [lb Ps]] //=.
  by case: (_ == _).
rewrite ![in LHS](fun_if, if_arg) /= {}IH //.
move: {Ps} lb; have [-> lb|ne lb] := altP (_ =P _).
  have [-> {k' p}|ne //] := altP (_ =P _).
  elim: s lb=> [|p s IH /= /andP [lb /IH {IH} ->]] //=.
  by move: lb; have [->|//] := altP (_ =P _); rewrite Ord.ltxx.
have [-> {k'}|ne'] // := altP (k' =P k).
by rewrite eq_sym (negbTE ne).
Qed.

Lemma mem_mkpartmap (kvs : seq (T * S)) :
  mkpartmap kvs =i [seq kv.1 | kv <- kvs].
Proof.
move=> k; elim: kvs => [|kv kvs IH] //=; rewrite !inE getm_set -{}IH.
by case: (_ == _).
Qed.

Lemma getm_mkpartmap (kvs : seq (T * S)) : mkpartmap kvs =1 getm' kvs.
Proof.
by move=> k; elim: kvs=> [|p kvs IH] //=; rewrite getm_set IH.
Qed.

Lemma eq_partmap (m1 m2 : {partmap T -> S}) : m1 =1 m2 -> m1 = m2.
Proof.
have in_seq: forall s : seq (T * S), [pred k | getm' s k] =i [seq p.1 | p <- s].
  elim=> [|p s IH] k; rewrite /= !inE // -IH inE.
  by case: (k == p.1).
case: m1 m2 => [s1 Ps1] [s2 Ps2]; rewrite /getm /= => s1_s2.
apply: val_inj=> /=.
elim: s1 Ps1 s2 Ps2 s1_s2
      => [_|[k1 v1] s1 IH /= /andP [lb1 /IH {IH} IH]]
         [_|[k2 v2] s2 /= /andP [lb2 Ps2]] //
      => [/(_ k2)|/(_ k1)| ]; try by rewrite eqxx.
move/IH: Ps2=> {IH} IH s1_s2.
wlog: k1 k2 v1 v2 s1 s2 lb1 lb2 s1_s2 IH / k1 <= k2.
  move=> H.
  have [|/Ord.ltW k2_k1] := boolP (k1 <= k2); first by eauto.
  symmetry; apply: H; eauto.
    by move=> k /=; rewrite s1_s2.
  by move=> H'; rewrite IH //.
rewrite Ord.leq_eqVlt=> /orP [/eqP k1_k2|k1_k2].
  rewrite -{}k1_k2 {k2} in lb2 s1_s2 *.
  move: (s1_s2 k1); rewrite eqxx=> - [->].
  rewrite {}IH // => k; move: {s1_s2} (s1_s2 k).
  have [-> {k} _|ne ?] // := altP (_ =P _).
  move: (in_seq s1 k1) (in_seq s2 k1); rewrite !inE.
  case: (getm' s1 k1) (getm' s2 k1) => [v1'|] [v2'|] //=.
  - by move=> _ /esym/(allP lb2) /=; rewrite Ord.ltxx.
  - by move=> /esym/(allP lb1) /=; rewrite Ord.ltxx.
  by move=> _ /esym/(allP lb2) /=; rewrite Ord.ltxx.
move/(_ k1)/esym: s1_s2 k1_k2; rewrite eqxx.
have [->|_ s1_s2] := altP (_ =P _); first by rewrite Ord.ltxx.
move/(_ s2 k1): in_seq; rewrite inE {}s1_s2 /= => /esym/(allP lb2)/Ord.ltW /=.
by move=> ->.
Qed.

Lemma union0m : left_id (@emptym T S) unionm.
Proof. by []. Qed.

Lemma unionm0 : right_id (@emptym T S) unionm.
Proof.
move=> m; apply: eq_partmap=> k; rewrite getm_union emptymP /=.
by case: (m k).
Qed.

Lemma unionmA : associative (@unionm T S).
Proof.
move=> m1 m2 m3; apply: eq_partmap=> k; rewrite !getm_union.
by case: (m1 k).
Qed.

Lemma unionmI : idempotent (@unionm T S).
Proof.
move=> m; apply: eq_partmap=> k; rewrite !getm_union.
by case: (m k).
Qed.

End Properties.

(* Find a good name for this *)
Lemma getm_mkpartmap' (T : ordType) (S : eqType) (kvs : seq (T * S)) k v
  : mkpartmap kvs k = Some v -> (k, v) \in kvs.
Proof.
elim: kvs => [|[k' v'] kvs IH] //=; rewrite getm_set.
have [-> [->]|_ H] := altP (_ =P _); first by rewrite inE eqxx.
by rewrite inE IH // orbT.
Qed.
