Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.path.

Require Import ord fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PartMap.

Section Def.

Variables (T : ordType) (S : Type).

Local Open Scope ord_scope.

Record partmap_type := PMap {
  pmval : seq (T * S);
  _ : sorted (@Ord.lt T) (unzip1 pmval)
}.
Definition partmap_of of phant (T -> S) := partmap_type.
Identity Coercion type_of_partmap_of : partmap_of >-> partmap_type.

End Def.

Module Exports.

Notation "{ 'partmap' T }" := (@partmap_of _ _ (Phant T))
  (at level 0, format "{ 'partmap'  T }") : type_scope.
Coercion pmval : partmap_type >-> seq.
Canonical partmap_subType T S := [subType for @pmval T S].
Definition partmap_eqMixin T (S : eqType) :=
  [eqMixin of partmap_type T S by <:].
Canonical partmap_eqType T (S : eqType) :=
  Eval hnf in EqType (partmap_type T S) (partmap_eqMixin T S).
Definition partmap_partOrdMixin T (S : partOrdType) :=
  [partOrdMixin of partmap_type T S by <:].
Canonical partmap_partOrdType T (S : ordType) :=
  Eval hnf in PartOrdType (partmap_type T S) (partmap_partOrdMixin T S).
Definition partmap_ordMixin T (S : ordType) :=
  [ordMixin of partmap_type T S by <:].
Canonical partmap_ordType T (S : ordType) :=
  Eval hnf in OrdType (partmap_type T S) (partmap_ordMixin T S).

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

(* Redefine the partmap constructor with a different signature, in
order to keep types consistent. *)
Definition partmap (T : ordType) S s Ps : {partmap T -> S} :=
  @PartMap.PMap T S s Ps.

Section Operations.

Variables (T : ordType) (S : Type).

Implicit Type m : {partmap T -> S}.
Implicit Type k : T.

Local Open Scope ord_scope.

Fixpoint getm_def s k : option S :=
  if s is p :: s then
    if k == p.1 then Some p.2
    else getm_def s k
  else None.

Definition getm (m : PartMap.partmap_type T S) k := getm_def m k.

Fixpoint setm_def s k v : seq (T * S) :=
  if s is p :: s' then
    if k < p.1 then (k, v) :: s
    else if k == p.1 then (k, v) :: s'
    else p :: setm_def s' k v
  else [:: (k, v)].

Lemma setm_subproof m k v : sorted (@Ord.lt T) (unzip1 (setm_def m k v)).
Proof.
have E: forall s, [seq p.1 | p <- setm_def s k v] =i k :: unzip1 s.
  elim=> // p s /= IH k'; rewrite ![in X in X = _]fun_if /= !inE.
  rewrite IH inE.
  case: (Ord.ltgtP k p.1) => // H; try by bool_congr.
  by rewrite H orbA orbb.
case: m; elim=> // p s /= IH Ps.
move: (order_path_min (@Ord.lt_trans T) Ps) => lb.
rewrite ![in X in is_true X]fun_if /= path_min_sorted; last exact: (allP lb).
rewrite (path_sorted Ps); case: Ord.ltgtP=> [k_p//|k_p|-> //] /=.
rewrite path_min_sorted ?(IH (path_sorted Ps)) //=; apply/allP.
by rewrite !(eq_all_r (E s)) {E} /= lb andbT.
Qed.

Definition setm (m : {partmap T -> S}) k v :=
  partmap (setm_subproof m k v).

Definition repm (m : {partmap T -> S}) k f : option {partmap T -> S} :=
  omap (setm m k \o f) (getm m k).

Definition updm (m : {partmap T -> S}) k v :=
  if getm m k then Some (setm m k v) else None.

Definition unionm (m1 m2 : {partmap T -> S}) :=
  foldr (fun p m => setm m p.1 p.2) m2 m1.

Lemma mapm_subproof S' (f : S -> S') m :
  sorted (@Ord.lt T) (unzip1 (map (fun p => (p.1, f p.2)) m)).
Proof. by rewrite /unzip1 -!map_comp; apply: (valP m). Qed.

Definition mapm S' (f : S -> S') m := partmap (mapm_subproof f m).

Lemma filterm_subproof (a : T -> S -> bool) m :
  sorted (@Ord.lt T) (unzip1 [seq p | p <- m & a p.1 p.2]).
Proof.
rewrite (subseq_sorted _ _ (valP m)) //; first exact: Ord.lt_trans.
rewrite /=; elim: {m} (PartMap.pmval m) => // p s IH.
rewrite (lock subseq) /=; case: (a _); rewrite /= -lock.
  by rewrite /= eqxx.
by rewrite (subseq_trans IH) // subseq_cons.
Qed.

Definition filterm (a : T -> S -> bool) (m : {partmap T -> S}) :=
  partmap (filterm_subproof a m).

Fixpoint remm_def (s : seq (T * S)) k :=
  if s is p :: s then
    if p.1 == k then s else p :: remm_def s k
  else [::].

Lemma remm_subproof m k : sorted (@Ord.lt T) (unzip1 (remm_def m k)).
Proof.
apply/(subseq_sorted _ _ (valP m)); first exact: Ord.lt_trans.
rewrite /=; elim: {m} (PartMap.pmval m) => // p s IH.
rewrite (lock subseq) /=; case: (_ == _); rewrite /= -lock.
  by rewrite subseq_cons.
by rewrite /= eqxx.
Qed.

Definition remm m k :=
  partmap (remm_subproof m k).

Definition emptym : {partmap T -> S} :=
  @partmap T S [::] erefl.

Definition mkpartmap (kvs : seq (T * S)) : {partmap T -> S} :=
  foldr (fun kv m => setm m kv.1 kv.2) emptym kvs.

Definition mkpartmapf (f : T -> S) (ks : seq T) : {partmap T -> S} :=
  mkpartmap [seq (k, f k) | k <- ks].

Definition mkpartmapfp (f : T -> option S) (ks : seq T) : {partmap T -> S} :=
  mkpartmap (pmap (fun k => omap (pair k) (f k)) ks).

Definition domm m := mkfset (unzip1 m).

End Operations.

Coercion getm : PartMap.partmap_type >-> Funclass.

Arguments emptym {_ _}.
Arguments unionm {_ _} _ _.

Notation "[ 'partmap' kv1 ; .. ; kvn ]" :=
  (mkpartmap (cons kv1 .. (cons kvn nil) ..))
  (at level 0, format "[ 'partmap'  '[' kv1 ; '/' .. ; '/' kvn ']' ]")
  : form_scope.

Section PredPartMap.

Variables (T : ordType) (S : eqType).

Definition mem_partmap (m : {partmap T -> S}) :=
  [pred p : T * S | p \in val m].

Canonical mem_partmap_predType := mkPredType mem_partmap.

End PredPartMap.

Section Properties.

Variables (T : ordType) (S : Type).
Local Open Scope ord_scope.
Local Open Scope fset_scope.

Implicit Type m : {partmap T -> S}.

Lemma mem_domm m k : k \in domm m = m k.
Proof.
rewrite inE /domm /= in_mkfset.
case: m => [s Ps] /=; rewrite /getm /=.
by elim: s {Ps} => [|p s IH] //=; rewrite inE IH; case: (k == p.1).
Qed.

Lemma dommP m k : reflect (exists v, m k = Some v) (k \in domm m).
Proof.
by rewrite mem_domm; case: (m k) => /=; constructor; eauto; case.
Qed.

Lemma setmE m k v k' :
  setm m k v k' =
  if k' == k then Some v else getm m k'.
Proof.
case: m; rewrite /getm /setm /=; elim=> //= p s IH Ps.
rewrite ![in LHS](fun_if, if_arg) /= {}IH; last exact: path_sorted Ps.
have [->{k'}|Hne] := altP (k' =P k); case: (Ord.ltgtP k) => //.
by move=> <-; rewrite (negbTE Hne).
Qed.

Lemma repmE m m' k f :
  repm m k f = Some m' ->
  forall k', m' k' = if k' == k then omap f (m k) else getm m k'.
Proof.
by rewrite /repm; case: (m k) => [v [<-]|] //= k'; rewrite setmE.
Qed.

Lemma updm_set m m' k v :
  updm m k v = Some m' -> m' = setm m k v.
Proof. by rewrite /updm; case: (getm m _) => [m''|] //= [<-]. Qed.

Lemma unionmE m1 m2 k : unionm m1 m2 k = if m1 k then m1 k else m2 k.
Proof.
case: m1 => [m1 Pm1]; rewrite /unionm {2 3}/getm /= {Pm1}.
elim: m1 => [|p m1 IH] //=.
by rewrite setmE {}IH; case: (_ == _).
Qed.

Lemma domm_union m1 m2 : domm (unionm m1 m2) = domm m1 :|: domm m2.
Proof.
by apply/eq_fset=> k; rewrite in_fsetU !mem_domm unionmE; case: (m1 k).
Qed.

Lemma domm_set m k v : domm (setm m k v) = k |: domm m.
Proof.
apply/eq_fset=> k'; apply/(sameP (dommP _ _))/(iffP idP);
rewrite setmE in_fsetU1.
  case/orP=> [->|]; first by eauto.
  by move=> /dommP [v' ->]; case: eq_op; eauto.
by have [-> //|] := altP eqP => _ /= [v']; rewrite mem_domm => ->.
Qed.

Lemma emptymP : @emptym T S =1 [fun : T => None].
Proof. by []. Qed.

Lemma mapmE S' (f : S -> S') m : mapm f m =1 omap f \o m.
Proof.
case: m=> [s Ps] k; rewrite /mapm /getm /=.
by elim: s {Ps}=> [|[k' v] s IH] //=; rewrite {}IH ![in RHS]fun_if /=.
Qed.

Lemma filtermE a m k :
  filterm a m k = obind (fun x => if a k x then Some x else None) (m k).
Proof.
case: m=> [s Ps]; rewrite /filterm /getm /=.
elim: s Ps=> [|p s IH /= Ps] //=.
rewrite ![in LHS](fun_if, if_arg) /= {}IH; last exact: path_sorted Ps.
have [-> {k}|k_p] //= := altP (_ =P _); case: (a _)=> //.
elim: s {Ps} (order_path_min (@Ord.lt_trans _) Ps)
      => [|p' s IH /andP /= [lb /IH {IH} IH]] //=.
by move: lb; have [->|//] := altP (_ =P _); rewrite Ord.ltxx.
Qed.

Lemma remmE m k k' :
  remm m k k' =
  if k' == k then None else getm m k'.
Proof.
case: m; rewrite /remm /getm /=; elim=> [|p s IH /= Ps] //=.
  by case: (_ == _).
rewrite ![in LHS](fun_if, if_arg) /= {}IH //; last exact: path_sorted Ps.
move: {Ps} (order_path_min (@Ord.lt_trans _) Ps).
have [-> lb|ne lb] := altP (_ =P _).
  have [-> {k' p}|ne //] := altP (_ =P _).
  elim: s lb=> [|p s IH /= /andP [lb /IH {IH} ->]] //=.
  by move: lb; have [->|//] := altP (_ =P _); rewrite Ord.ltxx.
have [-> {k'}|ne'] // := altP (k' =P k).
by rewrite eq_sym (negbTE ne).
Qed.

Lemma domm_mkpartmap (kvs : seq (T * S)) : domm (mkpartmap kvs) =i unzip1 kvs.
Proof.
move=> k; rewrite mem_domm.
elim: kvs => [|kv kvs IH] //=; rewrite !inE setmE -{}IH.
by case: (_ == _).
Qed.

Lemma mkpartmapE (kvs : seq (T * S)) : mkpartmap kvs =1 getm_def kvs.
Proof.
by move=> k; elim: kvs=> [|p kvs IH] //=; rewrite setmE IH.
Qed.

Lemma mkpartmapfE (f : T -> S) (ks : seq T) k :
  mkpartmapf f ks k = if k \in ks then Some (f k) else None.
Proof.
rewrite /mkpartmapf; elim: ks => [|k' ks IH] //=.
by rewrite setmE inE {}IH; have [<-|?] := altP (k =P k').
Qed.

Lemma mkpartmapfpE (f : T -> option S) (ks : seq T) k :
  mkpartmapfp f ks k = if k \in ks then f k else None.
Proof.
rewrite /mkpartmapfp; elim: ks => [|k' ks IH] //=.
case e: (f k') => [v|] //=.
  by rewrite setmE inE {}IH; have [->|? //] := altP (k =P k'); rewrite e.
rewrite inE {}IH; have [->|?] //= := altP (k =P k'); rewrite e.
by case: ifP.
Qed.

Lemma domm_mkpartmapfp (f : T -> option S) (ks : seq T) :
  domm (mkpartmapfp f ks) = mkfset [seq k <- ks | f k].
Proof.
apply/eq_fset=> k; rewrite mem_domm mkpartmapfpE in_mkfset mem_filter andbC.
by case: (k \in ks).
Qed.

Lemma eq_partmap m1 m2 : m1 =1 m2 <-> m1 = m2.
Proof.
split; last congruence.
have in_seq: forall s : seq (T * S), [pred k | getm_def s k] =i [seq p.1 | p <- s].
  elim=> [|p s IH] k; rewrite /= !inE // -IH inE.
  by case: (k == p.1).
case: m1 m2 => [s1 Ps1] [s2 Ps2]; rewrite /getm /= => s1_s2.
apply: val_inj=> /=.
elim: s1 Ps1 s2 Ps2 s1_s2
      => [_|[k1 v1] s1 IH /= Ps1] [_|[k2 v2] s2 /= Ps2] //
      => [/(_ k2)|/(_ k1)| ]; try by rewrite eqxx.
have lb1 := order_path_min (@Ord.lt_trans _) Ps1.
have lb2 := order_path_min (@Ord.lt_trans _) Ps2.
move: {Ps1 Ps2} (path_sorted Ps2) (path_sorted Ps1) => Ps1 Ps2.
move: IH => /(_ Ps2 _ Ps1) {Ps1 Ps2} IH s1_s2.
wlog: k1 k2 v1 v2 s1 s2 lb1 lb2 s1_s2 IH / k1 <= k2.
  move=> H.
  have [|k2_k1] := orP (Ord.leq_total k1 k2); first by eauto.
  symmetry; apply: H; eauto.
    by move=> k /=; rewrite s1_s2.
  by move=> H'; rewrite IH //.
rewrite Ord.leq_eqVlt=> /orP [/eqP k1_k2|k1_k2].
  rewrite -{}k1_k2 {k2} in lb2 s1_s2 *.
  move: (s1_s2 k1); rewrite eqxx=> - [->].
  rewrite {}IH // => k; move: {s1_s2} (s1_s2 k).
  have [-> {k} _|ne ?] // := altP (_ =P _).
  move: (in_seq s1 k1) (in_seq s2 k1); rewrite !inE.
  case: (getm_def s1 k1) (getm_def s2 k1) => [v1'|] [v2'|] //=.
  - by move=> _ /esym/(allP lb2) /=; rewrite Ord.ltxx.
  - by move=> /esym/(allP lb1) /=; rewrite Ord.ltxx.
  by move=> _ /esym/(allP lb2) /=; rewrite Ord.ltxx.
move/(_ k1)/esym: s1_s2 k1_k2; rewrite eqxx.
have [->|_ s1_s2] := altP (_ =P _); first by rewrite Ord.ltxx.
move/(_ s2 k1): in_seq; rewrite inE {}s1_s2 /= => /esym/(allP lb2)/Ord.ltW /=.
by rewrite Ord.ltNge => ->.
Qed.

Lemma setm_union m1 m2 k v :
  setm (unionm m1 m2) k v = unionm (setm m1 k v) m2.
Proof.
apply/eq_partmap=> k'; rewrite !(setmE, unionmE).
by have [->{k'}|] := altP (k' =P k).
Qed.

Lemma filterm_union p m1 m2 :
  fdisjoint (domm m1) (domm m2) ->
  filterm p (unionm m1 m2) =
  unionm (filterm p m1) (filterm p m2).
Proof.
move=> dis; apply/eq_partmap=> k; rewrite filtermE !unionmE !filtermE.
case get_k1: (m1 k)=> [v|] //=.
have: k \in domm m1 by rewrite mem_domm get_k1.
move/fdisjointP: dis=> dis /dis; rewrite mem_domm.
by case: (m2 k)=> //= _; case: ifP.
Qed.

Lemma eq_mkpartmapf (f1 f2 : T -> S) :
  f1 =1 f2 -> mkpartmapf f1 =1 mkpartmapf f2.
Proof.
by move=> e ks; apply/eq_partmap=> k; rewrite !mkpartmapfE e.
Qed.

Lemma eq_mkpartmapfp (f1 f2 : T -> option S) :
  f1 =1 f2 -> mkpartmapfp f1 =1 mkpartmapfp f2.
Proof.
by move=> e ks; apply/eq_partmap=> k; rewrite !mkpartmapfpE e.
Qed.

Lemma eq_filterm f1 f2 m :
  (f1 =2 f2) ->
  filterm f1 m = filterm f2 m.
Proof.
move=> e; apply/eq_partmap=> k; rewrite 2!filtermE.
case: (m k) => [v|] //=.
by rewrite e.
Qed.

Lemma domm_filter p m :
  fsubset (domm (filterm p m)) (domm m).
Proof.
apply/fsubsetP=> k; rewrite !mem_domm filtermE.
by case: (m k).
Qed.

Lemma setmI m k v : m k = Some v -> setm m k v = m.
Proof.
move=> get_k; apply/eq_partmap=> k'; rewrite setmE.
by have [->{k'}|//] := altP (_ =P _); rewrite get_k.
Qed.

Lemma union0m : left_id (@emptym T S) unionm.
Proof. by []. Qed.

Lemma unionm0 : right_id (@emptym T S) unionm.
Proof.
move=> m; apply/eq_partmap=> k; rewrite unionmE emptymP /=.
by case: (m k).
Qed.

Lemma unionmA : associative (@unionm T S).
Proof.
move=> m1 m2 m3; apply/eq_partmap=> k; rewrite !unionmE.
by case: (m1 k).
Qed.

Lemma unionmI : idempotent (@unionm T S).
Proof.
move=> m; apply/eq_partmap=> k; rewrite !unionmE.
by case: (m k).
Qed.

End Properties.

Section EqType.

Variables (T : ordType) (S : eqType).
Implicit Types (m : {partmap T -> S}) (k : T) (v : S).

Lemma getmP m k v : reflect (m k = Some v) ((k, v) \in m).
Proof.
case: m => [s Ps] /=; apply/(iffP idP); rewrite /getm /= inE /=.
  elim: s Ps => [|[k' v'] s IH] //= sorted_s.
  move/(_ (path_sorted sorted_s)) in IH.
  rewrite inE => /orP [/eqP [e_k e_v]|in_s].
    by rewrite -{}e_k -{}e_v {k' v' sorted_s} eqxx.
  have [e_k {IH} |n_k] := altP (k =P k'); last by auto.
  rewrite -{}e_k {k'} in sorted_s.
  suff : Ord.lt k k by rewrite Ord.ltxx.
  move/allP: (order_path_min (@Ord.lt_trans T) sorted_s); apply.
  by apply: map_f in_s.
elim: s Ps=> [|[k' v'] s IH] //= sorted_s.
move/(_ (path_sorted sorted_s)) in IH.
have [e_k [e_v]|n_k get_k] := altP (k =P k').
  by rewrite -{}e_k {}e_v {k' v'} inE eqxx in sorted_s *.
by rewrite inE IH // orbT.
Qed.

Lemma mkpartmap_Some (kvs : seq (T * S)) k v
  : mkpartmap kvs k = Some v -> (k, v) \in kvs.
Proof.
elim: kvs => [|[k' v'] kvs IH] //=; rewrite setmE.
have [-> [->]|_ H] := altP (_ =P _); first by rewrite inE eqxx.
by rewrite inE IH // orbT.
Qed.

Definition injectivem m := uniq (unzip2 m).

Lemma injectivemP m : reflect {in domm m, injective m} (injectivem m).
Proof.
apply/(iffP idP).
  move=> inj_m k1; rewrite mem_domm; case m_k1: (m k1) => [v|] // _.
  move/getmP in m_k1; move=> k2 /esym/getmP.
  move: inj_m m_k1; rewrite /injectivem.
  have: uniq (unzip1 m).
    apply (sorted_uniq (@Ord.lt_trans T) (@Ord.ltxx T)).
    exact: (valP m).
  rewrite !inE /=; elim: (val m) => [|[k' v'] s IH] //=.
  move=>/andP [k'_nin_s /IH {IH} IH] /andP [v'_nin_s /IH {IH} IH].
  rewrite !inE -pair_eqE /=.
  have [k1k'|k1k'] /= := altP (k1 =P k').
    subst k'; have /negbTE ->: (k1, v) \notin s.
      apply: contra k'_nin_s => k'_in_s.
      by apply/mapP; exists (k1, v).
    rewrite orbF=> /eqP ?; subst v'; rewrite eqxx andbT.
    have /negbTE ->: (k2, v) \notin s.
      apply: contra v'_nin_s => v'_in_s.
      by apply/mapP; exists (k2, v).
    by rewrite orbF => /eqP ->.
  move=> k1_in_s; move: (k1_in_s)=> /IH {IH} IH.
  have [k2k'|k2k'] //= := altP (k2 =P k').
  subst k'; case/orP=> [/eqP ?|//]; subst v'.
  suff c : v \in unzip2 s by rewrite c in v'_nin_s.
  by apply/mapP; exists (k1, v).
move=> inj_m.
rewrite /injectivem map_inj_in_uniq.
  apply: (@map_uniq _ _ (@fst T S)).
  apply: (sorted_uniq (@Ord.lt_trans T) (@Ord.ltxx T)).
  exact: (valP m).
move=> [k1 v] [k2 v'] /= /getmP k1_in_m /getmP k2_in_m ?; subst v'.
move: (inj_m k1); rewrite mem_domm k1_in_m => /(_ erefl k2 (esym k2_in_m)).
congruence.
Qed.

End EqType.

Section Inverse.

Section Def.

Variables (T S : ordType).

Implicit Type (m : {partmap T -> S}).

Definition invm m := mkpartmap [seq (p.2, p.1) | p <- m].

End Def.

Section Cancel.

Variables (T S : ordType).

Implicit Type (m : {partmap T -> S}).

Lemma getm_inv m k k' : invm m k = Some k' -> m k' = Some k.
Proof.
rewrite /invm =>/mkpartmap_Some/mapP [[h h'] /getmP get_k /= [??]].
by subst h h'.
Qed.

Lemma invmP m k : reflect (exists k', m k' = Some k) (k \in domm (invm m)).
Proof.
apply/(iffP idP).
  rewrite mem_domm; case im_k: (invm m k) => [k'|] //= _.
  by rewrite -(getm_inv im_k); eauto.
move=> [k' /getmP m_k'].
rewrite /invm domm_mkpartmap; apply/mapP; exists (k, k') => //.
by apply/mapP; exists (k', k).
Qed.

Lemma invmPn m k : reflect (forall k', m k' != Some k) (k \notin domm (invm m)).
Proof.
apply/(iffP idP).
  by move=> h k'; apply: contra h=> /eqP h; apply/invmP; eauto.
move=> h; apply/negP=> /invmP [k' h'].
by move: (h k'); rewrite h' eqxx.
Qed.

Lemma invmE m k : obind m (invm m k) = if invm m k then Some k else None.
Proof.
case get_k: (invm m k) => [k'|] //=.
rewrite /invm in get_k; move/mkpartmap_Some/mapP in get_k.
by case: get_k => [[h h'] /getmP get_k [??]]; subst k k'.
Qed.

End Cancel.

Section CancelRev.

Variables (T S : ordType).

Implicit Type (m : {partmap T -> S}).

Lemma invmEV m k :
  {in domm m, injective m} ->
  obind (invm m) (m k) = if m k then Some k else None.
Proof.
move=> inj_m; case m_k: (m k) => [k'|] //=.
move: (invmE m k').
case im_k': (invm m k') => [k''|] //=.
  move=> m_k''; congr Some; apply: inj_m; last by congruence.
  by rewrite mem_domm m_k''.
have /invmPn/(_ k) : k' \notin domm (invm m) by rewrite mem_domm im_k'.
by rewrite m_k eqxx.
Qed.

End CancelRev.

Variables (T S : ordType).

Implicit Type (m : {partmap T -> S}).

Lemma invm_inj m : {in domm (invm m), injective (invm m)}.
Proof.
move=> k1 in_im k2 h; rewrite mem_domm in in_im.
have {h}: obind m (invm m k1) = obind m (invm m k2) by congruence.
rewrite invmE {}in_im.
case im_k2: (invm m k2) => [k|] //=.
by move/getm_inv in im_k2; congruence.
Qed.

Lemma invmK m : {in domm m, injective m} -> invm (invm m) = m.
Proof.
move=> inj_m; apply/eq_partmap=> k.
move: (invmEV k inj_m).
case m_k: (m k) => [k'|] //= im_k'.
  by move: (invmEV k' (@invm_inj m)); rewrite im_k' /=.
move {im_k'}.
suff : k \notin domm (invm (invm m)) by rewrite mem_domm; case: (invm (invm m) k).
apply/invmPn=> k'; apply/eqP=> im_k'.
by move: (invmE m k'); rewrite im_k' /= m_k.
Qed.

End Inverse.
