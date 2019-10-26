From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path bigop.

Require Import ord fset.

(******************************************************************************)
(*   This file defines a type {fmap T -> S} of partial functions with finite  *)
(* domain from T to S, where T is assumed to have an ordType structure.       *)
(* Throughtout this development, we refer to such functions as (finite) maps. *)
(* The type {fmap T -> S} is defined as a list of pairs (k, v) : T * S that   *)
(* is kept ordered by its keys.  This implies that the type supports          *)
(* extensional equality, as shown by the lemma eq_fmap.                       *)
(*                                                                            *)
(*       getm m k == the value of the map f associated with the key k. getm   *)
(*                   is declared as a coercion into Funclass, allowing us to  *)
(*                   simply write m k instead.                                *)
(*     setm m k v == set the value of k in m to v, replacing any previous     *)
(*                   value.                                                   *)
(*     updm m k v == a partial version of setm, that only replaces the value  *)
(*                   of k if it is already present in m, and returns None     *)
(*                   otherwise.                                               *)
(*      mapim f m == apply the function f : T -> S -> S' to all bindings in   *)
(*                   the map m : {fmap T -> S}.                               *)
(*       mapm f m == specialized version of mapim that ignores the key value. *)
(*   unionm m1 m2 == a map containing all the bindings of m1 and m2.  If a    *)
(*                   key is present in both of them, the value of m1 is used. *)
(*    filterm a m == given a predicate a : T -> S -> bool, remove from m all  *)
(*                   bindings (k, v) such that a k v is false.                *)
(*       remm m k == remove the value of k in m, if there is one.             *)
(*         domm m == the domain of m: the set of keys associated with some    *)
(*                   value in m.                                              *)
(*       codomm m == the codomain of m: the set of values associated with     *)
(*                   key in m.  This requires an ordType structure on the     *)
(*                   type of values.                                          *)
(*   injectivem m == the map m is injective on its domain (the type of        *)
(*                   values must be an eqType).                               *)
(*         invm m == the inverse of m.  If multiple keys of m are mapped to   *)
(*                   the same value, only one of the bindings is used.        *)
(*  fmap_of_seq s == convert s : seq T into a map {fmap nat -> T} that        *)
(*                   indexes into s.                                          *)
(*       currym m == convert from {fmap T * S -> R} to                        *)
(*                   {fmap T -> {fmap S -> R}}.                               *)
(*     uncurrym m == the left inverse of the previous function.               *)
(* enum_fmap s s' == sequence of all maps whose domain and codomain are       *)
(*                   contained in the sequences s and s'.                     *)
(*                                                                            *)
(*   The behavior of many of these functions is described by lemmas such as   *)
(* setmE, unionmE, etc.  For example, setmE says that setm m k v k' is equal  *)
(* to if k' == k then Some v else m k'.  Maps coerce to predicates:           *)
(* (k, v) \in m means that m k = Some v (cf. getmP).                          *)
(*                                                                            *)
(*   We provide the following map constructors:                               *)
(*                                                                            *)
(*         emptym == the empty map.                                           *)
(*     mkfmap kvs == construct a map from kvs : seq (T * S).  If multiple     *)
(*                   bindings are present in kvs for a given key k : T, the   *)
(*                   first one is used.                                       *)
(*   mkfmapf f ks == construct a map that associates to each element k of     *)
(*                   the sequence ks the value f k, mapping all other keys to *)
(*                   None.                                                    *)
(*  mkfmapfp f ks == same as above but for a partial function                 *)
(*                   f : T -> option S.                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FMap.

Section Def.

Variables (T : ordType) (S : Type).

Local Open Scope ord_scope.

Record fmap_type := FMap {
  fmval : seq (T * S);
  _ : sorted (@Ord.lt T) (unzip1 fmval)
}.

Definition fmap_of & phant (T -> S) := fmap_type.

End Def.

Module Exports.

Identity Coercion fmap_of_fmap : fmap_of >-> fmap_type.
Notation "{ 'fmap' T }" := (@fmap_of _ _ (Phant T))
  (at level 0, format "{ 'fmap'  T }") : type_scope.

Section WithOrdType.

Variable T : ordType.

Coercion fmval : fmap_type >-> seq.
Canonical fmap_subType S := [subType for @fmval T S].
Definition fmap_eqMixin (S : eqType) :=
  [eqMixin of fmap_type T S by <:].
Canonical fmap_eqType (S : eqType) :=
  Eval hnf in EqType (fmap_type T S) (fmap_eqMixin S).
Definition fmap_choiceMixin (S : choiceType) :=
  [choiceMixin of fmap_type T S by <:].
Canonical fmap_choiceType (S : choiceType) :=
  Eval hnf in ChoiceType (fmap_type T S) (fmap_choiceMixin S).
Definition fmap_ordMixin (S : ordType) :=
  [ordMixin of fmap_type T S by <:].
Canonical fmap_ordType (S : ordType) :=
  Eval hnf in OrdType (fmap_type T S) (fmap_ordMixin S).

Canonical fmap_of_subType (S : Type) :=
  Eval hnf in [subType of {fmap T -> S}].
Canonical fmap_of_eqType (S : eqType) :=
  Eval hnf in [eqType of {fmap T -> S}].
Canonical fmap_of_choiceType (S : choiceType) :=
  Eval hnf in [choiceType of {fmap T -> S}].
Canonical fmap_of_ordType (S : ordType) :=
  Eval hnf in [ordType of {fmap T -> S}].

(*

Still need to rethink the interface hierarchy to allow this...

Definition fmap_countMixin T (S : countType) :=
  [countMixin of type T S by <:].
Canonical fmap_countType T (S : countType) :=
  Eval hnf in CountType (type T S) (fmap_countMixin T S).
Canonical fmap_subCountType T (S : countType) :=
  [subCountType of type T S].
*)

End WithOrdType.

End Exports.

End FMap.

Export FMap.Exports.

(* Redefine the fmap constructor with a different signature, in
order to keep types consistent. *)
Definition fmap (T : ordType) S s Ps : {fmap T -> S} :=
  @FMap.FMap T S s Ps.

Section Operations.

Variables (T : ordType) (S : Type).

Implicit Type m : {fmap T -> S}.
Implicit Type k : T.

Local Open Scope ord_scope.

Fixpoint getm_def s k : option S :=
  if s is p :: s then
    if k == p.1 then Some p.2
    else getm_def s k
  else None.

Definition getm (m : FMap.fmap_type T S) k := getm_def m k.

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

Definition setm (m : {fmap T -> S}) k v :=
  fmap (setm_subproof m k v).

Definition repm (m : {fmap T -> S}) k f : option {fmap T -> S} :=
  omap (setm m k \o f) (getm m k).

Definition updm (m : {fmap T -> S}) k v :=
  if getm m k then Some (setm m k v) else None.

Definition unionm (m1 m2 : {fmap T -> S}) :=
  foldr (fun p m => setm m p.1 p.2) m2 m1.

Lemma mapim_subproof S' (f : T -> S -> S') m :
  sorted (@Ord.lt T) (unzip1 (map (fun p => (p.1, f p.1 p.2)) m)).
Proof. by rewrite /unzip1 -!map_comp; apply: (valP m). Qed.

Definition mapim S' (f : T -> S -> S') m := fmap (mapim_subproof f m).

Definition mapm S' (f : S -> S') := mapim (fun _ x => f x).

Lemma filterm_subproof (a : T -> S -> bool) m :
  sorted (@Ord.lt T) (unzip1 [seq p | p <- m & a p.1 p.2]).
Proof.
rewrite (subseq_sorted _ _ (valP m)) //; first exact: Ord.lt_trans.
rewrite /=; elim: {m} (FMap.fmval m) => // p s IH.
rewrite (lock subseq) /=; case: (a _); rewrite /= -lock.
  by rewrite /= eqxx.
by rewrite (subseq_trans IH) // subseq_cons.
Qed.

Definition filterm (a : T -> S -> bool) (m : {fmap T -> S}) :=
  fmap (filterm_subproof a m).

Fixpoint remm_def (s : seq (T * S)) k :=
  if s is p :: s then
    if p.1 == k then s else p :: remm_def s k
  else [::].

Lemma remm_subproof m k : sorted (@Ord.lt T) (unzip1 (remm_def m k)).
Proof.
apply/(subseq_sorted _ _ (valP m)); first exact: Ord.lt_trans.
rewrite /=; elim: {m} (FMap.fmval m) => // p s IH.
rewrite (lock subseq) /=; case: (_ == _); rewrite /= -lock.
  by rewrite subseq_cons.
by rewrite /= eqxx.
Qed.

Definition remm m k :=
  fmap (remm_subproof m k).

Definition emptym : {fmap T -> S} :=
  @fmap T S [::] erefl.

Definition mkfmap (kvs : seq (T * S)) : {fmap T -> S} :=
  foldr (fun kv m => setm m kv.1 kv.2) emptym kvs.

Definition mkfmapf (f : T -> S) (ks : seq T) : {fmap T -> S} :=
  mkfmap [seq (k, f k) | k <- ks].

Definition mkfmapfp (f : T -> option S) (ks : seq T) : {fmap T -> S} :=
  mkfmap (pmap (fun k => omap (pair k) (f k)) ks).

Definition domm m := fset (unzip1 m).

End Operations.

Coercion getm : FMap.fmap_type >-> Funclass.

Arguments emptym {_ _}.
Arguments unionm {_ _} _ _.

Notation "[ 'fmap' kv1 ; .. ; kvn ]" :=
  (mkfmap (cons kv1 .. (cons kvn nil) ..))
  (at level 0, format "[ 'fmap'  '[' kv1 ; '/' .. ; '/' kvn ']' ]")
  : form_scope.

Section PredFmap.

Variables (T : ordType) (S : eqType).

Definition mem_fmap (m : {fmap T -> S}) :=
  [pred p : T * S | p \in val m].

Canonical mem_fmap_predType := PredType mem_fmap.

End PredFmap.

Section Properties.

Variables (T : ordType) (S : Type).
Local Open Scope ord_scope.
Local Open Scope fset_scope.

Implicit Type m : {fmap T -> S}.

Lemma eq_fmap m1 m2 : m1 =1 m2 <-> m1 = m2.
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

Lemma mem_domm m k : k \in domm m = m k.
Proof.
rewrite inE /domm /= in_fset.
case: m => [s Ps] /=; rewrite /getm /=.
by elim: s {Ps} => [|p s IH] //=; rewrite inE IH; case: (k == p.1).
Qed.

Lemma dommP m k : reflect (exists v, m k = Some v) (k \in domm m).
Proof.
by rewrite mem_domm; case: (m k) => /=; constructor; eauto; case.
Qed.

Lemma dommPn m k : reflect (m k = None) (k \notin domm m).
Proof.
by rewrite mem_domm; case: (m k)=> /=; constructor.
Qed.

Arguments dommP [_ _].
Arguments dommPn [_ _].

Lemma setmE m k v k' :
  setm m k v k' =
  if k' == k then Some v else getm m k'.
Proof.
case: m; rewrite /getm /setm /=; elim=> //= p s IH Ps.
rewrite ![in LHS](fun_if, if_arg) /= {}IH; last exact: path_sorted Ps.
have [->{k'}|Hne] := altP (k' =P k); case: (Ord.ltgtP k) => //.
by move=> <-; rewrite (negbTE Hne).
Qed.

Lemma setmC m k v k' v' : k != k' ->
  setm (setm m k v) k' v' = setm (setm m k' v') k v.
Proof.
move=> ne; apply/eq_fmap=> k''; rewrite !setmE.
have [->{k''}|//] := altP (k'' =P k').
by rewrite eq_sym (negbTE ne).
Qed.

Lemma setmxx m k v v' : setm (setm m k v) k v' = setm m k v'.
Proof. by apply/eq_fmap=> k'; rewrite !setmE; case: eqP. Qed.

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
apply/eq_fset=> k'; apply/(sameP dommP)/(iffP idP);
rewrite setmE in_fsetU1.
  case/orP=> [->|]; first by eauto.
  by move=> /dommP [v' ->]; case: eq_op; eauto.
by have [-> //|] := altP eqP => _ /= [v']; rewrite mem_domm => ->.
Qed.

Lemma emptymE k : @emptym T S k = None.
Proof. by []. Qed.

Lemma domm0 : domm (@emptym T S) = fset0.
Proof.
by apply/eq_fset=> k; rewrite mem_domm.
Qed.

Lemma emptymP m : reflect (m = emptym) (domm m == fset0).
Proof.
apply/(iffP eqP); last by move=> ->; rewrite domm0.
by move=> e; apply/eq_fmap => x; apply/dommPn; rewrite e.
Qed.

Lemma mapimE S' (f : T -> S -> S') m k : mapim f m k = omap (f k) (m k).
Proof.
case: m=> [s Ps]; rewrite /mapim /getm /=.
elim: s {Ps}=> [|[k' v] s IH] //=; rewrite {}IH ![in RHS]fun_if /=.
by case: (k =P k') => [<-|].
Qed.

Lemma mapmE S' (f : S -> S') m k : mapm f m k = omap f (m k).
Proof. exact: mapimE. Qed.

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

Lemma domm_rem m k : domm (remm m k) = domm m :\ k.
Proof.
by apply/eq_fset=> k'; rewrite in_fsetD1 !mem_domm remmE; case: eqP.
Qed.

Lemma domm_mkfmap (kvs : seq (T * S)) : domm (mkfmap kvs) =i unzip1 kvs.
Proof.
move=> k; rewrite mem_domm.
elim: kvs => [|kv kvs IH] //=; rewrite !inE setmE -{}IH.
by case: (_ == _).
Qed.

Lemma mkfmapE (kvs : seq (T * S)) : mkfmap kvs =1 getm_def kvs.
Proof.
by move=> k; elim: kvs=> [|p kvs IH] //=; rewrite setmE IH.
Qed.

Lemma mkfmapfE (f : T -> S) (ks : seq T) k :
  mkfmapf f ks k = if k \in ks then Some (f k) else None.
Proof.
rewrite /mkfmapf; elim: ks => [|k' ks IH] //=.
by rewrite setmE inE {}IH; have [<-|?] := altP (k =P k').
Qed.

Lemma mkfmapfpE (f : T -> option S) (ks : seq T) k :
  mkfmapfp f ks k = if k \in ks then f k else None.
Proof.
rewrite /mkfmapfp; elim: ks => [|k' ks IH] //=.
case e: (f k') => [v|] //=.
  by rewrite setmE inE {}IH; have [->|? //] := altP (k =P k'); rewrite e.
rewrite inE {}IH; have [->|?] //= := altP (k =P k'); rewrite e.
by case: ifP.
Qed.

Lemma domm_mkfmapf (f : T -> S) (ks : seq T) :
  domm (mkfmapf f ks) = fset ks.
Proof.
apply/eq_fset=> k; rewrite mem_domm mkfmapfE in_fset.
by case: (k \in ks).
Qed.

Lemma domm_mkfmapfp (f : T -> option S) (ks : seq T) :
  domm (mkfmapfp f ks) = fset [seq k <- ks | f k].
Proof.
apply/eq_fset=> k; rewrite mem_domm mkfmapfpE in_fset mem_filter andbC.
by case: (k \in ks).
Qed.

Lemma setm_union m1 m2 k v :
  setm (unionm m1 m2) k v = unionm (setm m1 k v) m2.
Proof.
apply/eq_fmap=> k'; rewrite !(setmE, unionmE).
by have [->{k'}|] := altP (k' =P k).
Qed.

Lemma filterm_union p m1 m2 :
  fdisjoint (domm m1) (domm m2) ->
  filterm p (unionm m1 m2) =
  unionm (filterm p m1) (filterm p m2).
Proof.
move=> dis; apply/eq_fmap=> k; rewrite filtermE !unionmE !filtermE.
case get_k1: (m1 k)=> [v|] //=.
have: k \in domm m1 by rewrite mem_domm get_k1.
move/fdisjointP: dis=> dis /dis; rewrite mem_domm.
by case: (m2 k)=> //= _; case: ifP.
Qed.

Lemma eq_mkfmapf (f1 f2 : T -> S) :
  f1 =1 f2 -> mkfmapf f1 =1 mkfmapf f2.
Proof.
by move=> e ks; apply/eq_fmap=> k; rewrite !mkfmapfE e.
Qed.

Lemma eq_mkfmapfp (f1 f2 : T -> option S) :
  f1 =1 f2 -> mkfmapfp f1 =1 mkfmapfp f2.
Proof.
by move=> e ks; apply/eq_fmap=> k; rewrite !mkfmapfpE e.
Qed.

Lemma eq_filterm f1 f2 m :
  (f1 =2 f2) ->
  filterm f1 m = filterm f2 m.
Proof.
move=> e; apply/eq_fmap=> k; rewrite 2!filtermE.
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
move=> get_k; apply/eq_fmap=> k'; rewrite setmE.
by have [->{k'}|//] := altP (_ =P _); rewrite get_k.
Qed.

Lemma union0m : left_id (@emptym T S) unionm.
Proof. by []. Qed.

Lemma unionm0 : right_id (@emptym T S) unionm.
Proof.
move=> m; apply/eq_fmap=> k; rewrite unionmE emptymE /=.
by case: (m k).
Qed.

Lemma unionmA : associative (@unionm T S).
Proof.
move=> m1 m2 m3; apply/eq_fmap=> k; rewrite !unionmE.
by case: (m1 k).
Qed.

Lemma unionmI : idempotent (@unionm T S).
Proof.
move=> m; apply/eq_fmap=> k; rewrite !unionmE.
by case: (m k).
Qed.

Lemma unionmC m1 m2 :
  fdisjoint (domm m1) (domm m2) ->
  unionm m1 m2 = unionm m2 m1.
Proof.
move=> dis; apply/eq_fmap=> k; rewrite !unionmE.
have {dis}: ~~ (m1 k) || ~~ (m2 k).
  by rewrite -!mem_domm -implybE; apply/implyP/fdisjointP.
by case: (m1 k) (m2 k)=> [?|] [?|] //=.
Qed.

Lemma unionmK m1 m2 : filterm (fun k _ => m1 k) (unionm m1 m2) = m1.
Proof.
apply/eq_fmap=> k; rewrite filtermE unionmE.
by case: (m1 k) (m2 k)=> //= - [].
Qed.

End Properties.

Arguments dommP {_ _} [_ _].
Arguments dommPn {_ _} [_ _].

Section Map.

Variables (T : ordType) (S S' : Type).

Implicit Types (m : {fmap T -> S}) (k : T).

Lemma domm_mapi (f : T -> S -> S') m : domm (mapim f m) = domm m.
Proof.
by apply/eq_fset=> k; rewrite !mem_domm mapimE; case: (m k).
Qed.

Lemma domm_map (f : S -> S') m : domm (mapm f m) = domm m.
Proof. exact: domm_mapi. Qed.

End Map.

Section Map2.

Implicit Types (T : ordType) (S : Type).

Local Open Scope fset_scope.

Definition mapm2 T T' S S' f g (m : {fmap T -> S}) : {fmap T' -> S'} :=
  mkfmap [seq (f p.1, g p.2) | p <- m].

Lemma mapm2E T T' S S' (f : T -> T') (g : S -> S') m x :
  injective f ->
  mapm2 f g m (f x) = omap g (m x).
Proof.
rewrite /mapm2 => f_inj; rewrite mkfmapE /getm.
case: m=> [/= m _]; elim: m=> [|[x' y] m IH] //=.
by rewrite (inj_eq f_inj) [in RHS]fun_if IH.
Qed.

Lemma domm_map2 T T' S S' (f : T -> T') (g : S -> S') m :
  domm (mapm2 f g m) = f @: domm m.
Proof.
apply/eq_fset=> x; rewrite /mapm2 domm_mkfmap /unzip1 -map_comp /comp /=.
by rewrite /domm imfset_fset in_fset -map_comp.
Qed.

Lemma mapm2_comp T T' T'' S S' S'' f f' g g' :
  injective f  ->
  injective f' ->
  mapm2 (f' \o f) (g' \o g) =1
  @mapm2 T' T'' S' T'' f' g' \o @mapm2 T T' S S' f g.
Proof.
move=> f_inj f'_inj m; apply/eq_fmap=> x /=.
have [|xnin] := boolP (x \in domm (mapm2 (f' \o f) (g' \o g) m)).
- rewrite domm_map2; case/imfsetP=> {x} x xin ->.
  rewrite mapm2E /=; last exact: inj_comp.
  by rewrite !mapm2E //; case: (m x).
- move: (xnin); rewrite (dommPn xnin).
  rewrite !domm_map2 // imfset_comp -(domm_map2 f g) -(domm_map2 f' g').
  by move/dommPn=> ->.
Qed.

End Map2.

Section EqType.

Variables (T : ordType) (S : eqType).
Implicit Types (m : {fmap T -> S}) (k : T) (v : S).

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

Lemma mkfmap_Some (kvs : seq (T * S)) k v
  : mkfmap kvs k = Some v -> (k, v) \in kvs.
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

Lemma eq_domm0 (S' : eqType) (m : {fmap T -> S'}) :
  (domm m == fset0) = (m == emptym).
Proof.
apply/(sameP idP)/(iffP idP)=> [/eqP->|/eqP Pdom]; first by rewrite domm0.
apply/eqP/eq_fmap=> k; rewrite emptymE; apply/dommPn.
by rewrite Pdom in_fset0.
Qed.

End EqType.

Section Inverse.

Section Def.

Variables (T S : ordType).

Implicit Type (m : {fmap T -> S}).

Definition invm m := mkfmap [seq (p.2, p.1) | p <- m].

Definition codomm m := domm (invm m).

End Def.

Section Cancel.

Variables (T S : ordType).

Implicit Type (m : {fmap T -> S}).

Lemma getm_inv m k k' : invm m k = Some k' -> m k' = Some k.
Proof.
rewrite /invm =>/mkfmap_Some/mapP [[h h'] /getmP get_k /= [??]].
by subst h h'.
Qed.

Lemma codommP m k : reflect (exists k', m k' = Some k) (k \in codomm m).
Proof.
rewrite /codomm; apply/(iffP idP).
  rewrite mem_domm; case im_k: (invm m k) => [k'|] //= _.
  by rewrite -(getm_inv im_k); eauto.
move=> [k' /getmP m_k'].
rewrite /invm domm_mkfmap; apply/mapP; exists (k, k') => //.
by apply/mapP; exists (k', k).
Qed.

Lemma codommPn m k : reflect (forall k', m k' != Some k) (k \notin codomm m).
Proof.
apply/(iffP idP).
  by move=> h k'; apply: contra h=> /eqP h; apply/codommP; eauto.
move=> h; apply/negP=> /codommP [k' h'].
by move: (h k'); rewrite h' eqxx.
Qed.

Arguments codommP [_ _].
Arguments codommPn [_ _].

Lemma codomm0 : codomm (@emptym T S) = fset0.
Proof. by rewrite /codomm /domm fset0E. Qed.

Lemma codomm_rem m k : fsubset (codomm (remm m k)) (codomm m).
Proof.
apply/fsubsetP=> v /codommP [k']; rewrite remmE.
by case: eqP=> // _ Pv; apply/codommP; eauto.
Qed.

Lemma invmE m k : obind m (invm m k) = if invm m k then Some k else None.
Proof.
case get_k: (invm m k) => [k'|] //=.
rewrite /invm in get_k; move/mkfmap_Some/mapP in get_k.
by case: get_k => [[h h'] /getmP get_k [??]]; subst k k'.
Qed.

End Cancel.

Section CancelRev.

Variables (T S : ordType).

Implicit Type (m : {fmap T -> S}).

Lemma invmEV m k :
  {in domm m, injective m} ->
  obind (invm m) (m k) = if m k then Some k else None.
Proof.
move=> inj_m; case m_k: (m k) => [k'|] //=.
move: (invmE m k').
case im_k': (invm m k') => [k''|] //=.
  move=> m_k''; congr Some; apply: inj_m; last by congruence.
  by rewrite mem_domm m_k''.
have /codommPn/(_ k) : k' \notin domm (invm m) by rewrite mem_domm im_k'.
by rewrite m_k eqxx.
Qed.

End CancelRev.

Variables (T S : ordType).

Implicit Type (m : {fmap T -> S}).

Lemma invm_inj m : {in codomm m, injective (invm m)}.
Proof.
move=> k1 in_im k2 h; rewrite mem_domm in in_im.
have {h}: obind m (invm m k1) = obind m (invm m k2) by congruence.
rewrite invmE {}in_im.
case im_k2: (invm m k2) => [k|] //=.
by move/getm_inv in im_k2; congruence.
Qed.

Lemma invmK m : {in domm m, injective m} -> invm (invm m) = m.
Proof.
move=> inj_m; apply/eq_fmap=> k.
move: (invmEV k inj_m).
case m_k: (m k) => [k'|] //= im_k'.
  by move: (invmEV k' (@invm_inj m)); rewrite im_k' /=.
move {im_k'}.
suff : k \notin domm (invm (invm m)) by rewrite mem_domm; case: (invm (invm m) k).
apply/codommPn=> k'; apply/eqP=> im_k'.
by move: (invmE m k'); rewrite im_k' /= m_k.
Qed.

End Inverse.

Arguments codommP {_ _} [_ _].
Arguments codommPn {_ _} [_ _].

Section OfSeq.

Variable (T : Type).

Definition fmap_of_seq (xs : seq T) : {fmap nat -> T} :=
  mkfmapfp (nth None [seq Some x | x <- xs]) (iota 0 (size xs)).

Lemma fmap_of_seqE xs n :
  fmap_of_seq xs n = nth None [seq Some x | x <- xs] n.
Proof.
rewrite /fmap_of_seq mkfmapfpE mem_iota leq0n /= add0n.
case: ltnP=> [l|g] //.
by rewrite nth_default // size_map.
Qed.

End OfSeq.

Section Currying.

Variables (T S : ordType) (R : Type).
Implicit Type (m : {fmap T * S -> R}).
Implicit Type (n : {fmap T -> {fmap S -> R}}).

Local Open Scope fset_scope.

Definition currym m :=
  mkfmapf (fun x => mkfmapfp (fun y => m (x, y))
                                   (@snd _ _ @: domm m))
             (@fst _ _ @: domm m).

Definition uncurrym n : {fmap T * S -> R} :=
  mkfmapfp (fun p : T * S => if n p.1 is Some n' then n' p.2
                             else None)
              (\bigcup_(x <- domm n)
                  if n x is Some n' then pair x @: domm n'
                  else fset0).

Lemma currymP m x y v :
  (exists2 n, currym m x = Some n & n y = Some v) <->
  m (x, y) = Some v.
Proof.
split.
  move=> [n]; rewrite /currym mkfmapfE.
  case: ifP=> [/imfsetP/= [[x' y'] /= E ?]|//]; subst x'.
  move=> [<-] {n}; rewrite mkfmapfpE.
  by case: ifP.
move=> get_xy.
exists (mkfmapfp (fun y' => m (x, y')) (@snd _ _ @: domm m)).
  rewrite /currym mkfmapfE -{1}[x]/(x, y).1 mem_imfset //.
  by rewrite mem_domm get_xy.
by rewrite mkfmapfpE -{1}[y]/(x, y).2 mem_imfset // mem_domm get_xy.
Qed.

Lemma currymE m x y :
  m (x, y) = obind (fun n : {fmap S -> R} => n y) (currym m x).
Proof.
rewrite /currym mkfmapfE.
case: imfsetP=> [[[x' y'] /=]|].
  rewrite mem_domm => get_xy ?; subst x'.
  rewrite mkfmapfpE.
  case get_xy': (m (x, y))=> [v|] //=; last by case: ifP.
  by rewrite -{1}[y]/(x, y).2 mem_imfset // mem_domm get_xy'.
case get_xy: (m (x, y))=> [v|] // h.
suff: False by [].
by apply: h; exists (x, y)=> //; rewrite mem_domm get_xy.
Qed.

Lemma domm_curry m : domm (currym m) = @fst _ _ @: (domm m).
Proof.
by apply/eq_fset=> x; rewrite /currym mem_domm mkfmapfE; case: ifP.
Qed.

Lemma uncurrymP n x y v :
  (exists2 n', n x = Some n' & n' y = Some v) <->
  uncurrym n (x, y) = Some v.
Proof.
pose f x' := if n x' is Some n'' then pair x' @: domm n'' else fset0.
split.
  move=> [n' get_x get_y].
  rewrite /uncurrym mkfmapfpE /= get_x get_y.
  have inDn' : (x, y) \in f x.
    by rewrite /f get_x mem_imfset // mem_domm get_y.
  have inD : x \in domm n by rewrite mem_domm get_x.
  by move/fsubsetP/(_ _ inDn'): (bigcup_sup f inD erefl)=> ->.
rewrite /uncurrym mkfmapfpE /=.
by case: ifP=> [inU|] //=; case: (n x) => [n'|] //= get_y; eauto.
Qed.

Lemma uncurrymE n p :
  uncurrym n p = obind (fun nn => getm nn p.2) (n p.1).
Proof.
case: p=> x y /=.
case e: (uncurrym n (x, y))=> [v|] /=.
  by case/uncurrymP: e => nn -> /= ->.
case e': (n x) => [nn|] //=.
case e'': (nn y) => [v|] //=.
have/uncurrymP : exists2 n', n x = Some n' & n' y = Some v by eauto.
by rewrite e.
Qed.

Lemma currymK : cancel currym uncurrym.
Proof.
move=> m; apply/eq_fmap=> - [x y].
case get_m: (m _)=> [v|]; first by move/currymP/uncurrymP: get_m.
case get_ucm : (uncurrym _ _)=> [v|] //.
by move/uncurrymP/currymP: get_ucm get_m => ->.
Qed.

End Currying.

Section Enumeration.

Variables (T S : ordType).
Implicit Types (m : {fmap T -> S}) (xs : seq T) (ys : seq S).

Local Open Scope fset_scope.

Definition enum_fmap xs ys :=
  foldr (fun x ms => ms ++ [seq setm m x y | m <- ms, y <- ys]) [:: emptym] xs.

Lemma enum_fmapP xs ys m :
  reflect ({subset domm m <= xs} /\ {subset codomm m <= ys})
          (m \in enum_fmap xs ys).
Proof.
elim: xs m=> [|x xs IHx] //= m.
  rewrite inE; apply/(iffP eqP)=> [->|[eq0 _]].
    by rewrite domm0 codomm0; split=> ?; rewrite in_fset0.
  apply/eqP; rewrite -eq_domm0 -fsubset0.
  by apply/fsubsetP=> x /eq0.
rewrite mem_cat.
apply/(iffP orP) => [[/IHx [subx suby] | /allpairsP h] | [subx suby]].
- by split=> // x' x'_in; rewrite inE; apply/orP; right; apply: subx.
- move: m h => m' [[m y] /= [/IHx [subx suby] h ->]] {m'}; split.
    rewrite domm_set=> x' /fsetU1P [->|/subx]; rewrite inE ?eqxx //.
    by move=> ->; rewrite orbT.
  move=> y' /codommP [x']; rewrite setmE.
  case: eqP=> [_ [<-] //| _ m_x']; apply: suby.
  by apply/codommP; eauto.
have [/dommP [y h]|x_nin] := boolP (x \in domm m).
  right; apply/allpairsP; exists (remm m x, y)=> /=; split.
  - apply/IHx; rewrite domm_rem; split.
      by move=> x' /fsetDP [/subx]; rewrite inE => /orP [/eqP -> /fset1P|].
    move=> y' /codommP [x' m_x']; apply: suby; apply/codommP.
    by exists x'; move: m_x'; rewrite remmE; case: ifP.
  - by apply: suby; apply/codommP; exists x.
  by apply/eq_fmap=> x'; rewrite setmE remmE; case: eqP => [->|].
left; apply/IHx; split=> // x' x'_in; move/(_ _ x'_in): subx (x'_in) x_nin.
by rewrite inE => /orP [/eqP -> ->|].
Qed.

End Enumeration.
