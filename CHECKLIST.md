# `fset`

| Name                         | Type     | In finmap?    | Closest analogue    |
|------------------------------|----------|---------------|---------------------|
| `fset`                       | Function | Close         | `[fset x in xs]`    |
| `pred_of_fset`               | Coercion | Yes           |                     |
| `in_fset`                    | Lemma    | Close         | `inE`, `in_fsetE`   |
| `fset0`                      | Function | Yes           |                     |
| `fset1`                      | Function | Yes           |                     |
| `fsetU`                      | Function | Yes           |                     |
| `fset_filter`                | Function | No            | `[fset x in A | P]` |
| `fsetI`                      | Function | Yes           |                     |
| `fsetD`                      | Function | Yes           |                     |
| `fsubset`                    | Function | Yes           |                     |
| `fdisjoint`                  | Function | Yes           |                     |
| ``s1 `|` s2``                | Notation | Yes           |                     |
| ``x   |` s``                 | Notation | Yes           |                     |
| ``s1 `&` s2``                | Notation | Yes           |                     |
| ``s1 `\` s2``                | Notation | Yes           |                     |
| ``s `\ x``                   | Notation | Yes           |                     |
| ``s1 `<=` s2``               | Notation | Yes           |                     |
| ``s1 `#` s2``                | Notation | No            | `[disjoint A & B]`  |
| `[fset a1; .. ; an]`         | Notation | Yes           |                     |
| `all_fset`                   | Lemma    | No            | ?                   |
| `has_fset`                   | Lemma    | No            | ?                   |
| `eq_fset`                    | Lemma    | Close         | `fsetP`             |
| `fset_eqP`                   | Lemma    | Close         | `fset_eqP`          |
| `fsvalK`                     | Lemma    | No            |                     |
| `fset0E`                     | Lemma    | No            | ?                   |
| `fset1E`                     | Lemma    | No            | ?                   |
| `in_fset0`                   | Lemma    | Yes           |                     |
| `in_fset1`                   | Lemma    | Yes           |                     |
| `fset1P`                     | Lemma    | Yes           |                     |
| `fset1_inj`                  | Lemma    | Yes           |                     |
| `in_fsetU`                   | Lemma    | Yes           |                     |
| `in_fset1U`                  | Lemma    | Yes           |                     |
| `fset_cat`                   | Lemma    | No            | ?                   |
| `all_fsetU`                  | Lemma    | No            | ?                   |
| `in_fset2`                   | Lemma    | Yes           |                     |
| `fset21`                     | Lemma    | Yes           |                     |
| `fset22`                     | Lemma    | Yes           |                     |
| `fset2P`                     | Lemma    | Yes           |                     |
| `fsetP`                      | Lemma    | No            | ?                   |
| `fset1U_rect`                | Lemma    | Yes           |                     |
| `fset1U_ind`                 | Lemma    | No            | `fset1U_rect`       |
| `fset1UP`                    | Lemma    | Yes           |                     |
| `fsetUP`                     | Lemma    | Yes           |                     |
| `fsetUC`                     | Lemma    | Yes           |                     |
| `fsetUA`                     | Lemma    | Yes           |                     |
| `fset0U`                     | Lemma    | Yes           |                     |
| `fsetU0`                     | Lemma    | Yes           |                     |
| `fsetUid`                    | Lemma    | Yes           |                     |
| `fset_eq0E`                  | Lemma    | No            | ?                   |
| `fsubsetP`                   | Lemma    | Yes           |                     |
| `fsubset_refl`               | Lemma    | Yes           |                     |
| `fsubset_trans`              | Lemma    | Yes           |                     |
| `fsubsetUl`                  | Lemma    | Yes           |                     |
| `fsubsetUr`                  | Lemma    | Yes           |                     |
| `fsub1Uset`                  | Lemma    | No (but soon) |                     |
| `fsubUset`                   | Lemma    | Yes           |                     |
| `fsetUS`                     | Lemma    | Yes           |                     |
| `fsetSU`                     | Lemma    | Yes           |                     |
| `fsetUSS`                    | Lemma    | Yes           |                     |
| `fsub1set`                   | Lemma    | Yes           |                     |
| `fset_cons`                  | Lemma    | Yes           |                     |
| `uniq_fset`                  | Lemma    | Close         | `fset_uniq`         |
| `in_fset_filter`             | Lemma    | No            | ?                   |
| `in_fsetI`                   | Lemma    | Yes           |                     |
| `fsetIP`                     | Lemma    | Yes           |                     |
| `fsetIC`                     | Lemma    | Yes           |                     |
| `fsetIA`                     | Lemma    | Yes           |                     |
| `fsetIid`                    | Lemma    | Yes           |                     |
| `fset0I`                     | Lemma    | Yes           |                     |
| `fsetI0`                     | Lemma    | Yes           |                     |
| `fsetUIl`                    | Lemma    | Yes           |                     |
| `fsetUIr`                    | Lemma    | Yes           |                     |
| `fsetIUl`                    | Lemma    | Yes           |                     |
| `fsetIUr`                    | Lemma    | Yes           |                     |
| `fsubsetIl`                  | Lemma    | Yes           |                     |
| `fsubsetIr`                  | Lemma    | Yes           |                     |
| `fsubsetI`                   | Lemma    | Yes           |                     |
| `fsubIset`                   | Lemma    | Yes           |                     |
| `fsetIS`                     | Lemma    | Yes           |                     |
| `fsetSI`                     | Lemma    | Yes           |                     |
| `fsetISS`                    | Lemma    | Yes           |                     |
| `fsetIidPl`                  | Lemma    | Yes           |                     |
| `fsetIidPr`                  | Lemma    | Yes           |                     |
| `fsetUidPl`                  | Lemma    | Yes           |                     |
| `fsetUidPr`                  | Lemma    | Yes           |                     |
| `fset1I`                     | Lemma    | No            | ?                   |
| `fdisjointC`                 | Lemma    | Close         | `fdisjoint_sym`     |
| `fdisjointP`                 | Lemma    | Yes           |                     |
| `fdisjointSl`                | Lemma    | Close         | `fdisjointWl`       |
| `fdisjointSr`                | Lemma    | Close         | `fdisjointWr`       |
| `fdisjoint0s`                | Lemma    | Close         | `fdisjoint0X`       |
| `fdisjoints0`                | Lemma    | Close         | `fdisjointX0`       |
| `fdisjoints1`                | Lemma    | Close         | `fdisjointX1`       |
| `fdisjoint1s`                | Lemma    | Close         | `fdisjoint1X`       |
| `in_fsetD`                   | Lemma    | Yes           |                     |
| `in_fsetD1`                  | Lemma    | Yes           |                     |
| `fsetDP`                     | Lemma    | Yes           |                     |
| `fsetD1P`                    | Lemma    | No            | ?                   |
| `fsubDset`                   | Lemma    | Yes           |                     |
| `fsubD1set`                  | Lemma    | No            | ?                   |
| `fsetID`                     | Lemma    | Yes           |                     |
| `fsetDUl`                    | Lemma    | Yes           |                     |
| `fsetDUr`                    | Lemma    | Yes           |                     |
| `fsetUDr`                    | Lemma    | Mismatch      | `fsetUDl`           |
| `fsetDIl`                    | Lemma    | Yes           |                     |
| `fsetIDA`                    | Lemma    | Yes           |                     |
| `fsetIDAC`                   | Lemma    | Yes           |                     |
| `fsetDIr`                    | Lemma    | Yes           |                     |
| `fsetDDl`                    | Lemma    | Yes           |                     |
| `fsetDDr`                    | Lemma    | Yes           |                     |
| `fsetSD`                     | Lemma    | Yes           |                     |
| `fsetDS`                     | Lemma    | Yes           |                     |
| `fdisjoint_fsetI0`           | Lemma    | No            | ?                   |
| `fpick`                      | Function | No            | ?                   |
| `fpickP`                     | Lemma    | No            |                     |
| `sizes0`                     | Lemma    | Close         | `cardfs0`           |
| `sizes1`                     | Lemma    | Close         | `cardfs1`           |
| `sizesU`                     | Lemma    | No            | ?                   |
| `sizes1U`                    | Lemma    | Close         | `cardfsU1`          |
| `sizesD1`                    | Lemma    | Close         | `cardfsD1`          |
| `sizesD`                     | Lemma    | Close         | `cardfsD`           |
| `size_fset`                  | Lemma    | No            | `card_fseq`         |
| `uniq_size_fset`             | Lemma    | No            | ?                   |
| `fsubset_leq_size`           | Lemma    | Close         | `fsubset_leq_card`  |
| `sizes_eq0`                  | Lemma    | Close         | `cardfs_eq0`        |
| `fset0Pn`                    | Lemma    | Yes           |                     |
| `fsubset_sizeP`              | Lemma    | Close         | `fsubset_cardP`     |
| `eqEfsubset`                 | Lemma    | Yes           |                     |
| `eqEfsize`                   | Lemma    | Close         | `eqEfcard`          |
| `fsub0set`                   | Lemma    | Yes           |                     |
| `fsubset0`                   | Lemma    | Yes           |                     |
| `fsubset1`                   | Lemma    | Yes           |                     |
| `fsetU_eq0`                  | Lemma    | Yes           |                     |
| `fdisjointUl`                | Lemma    | Close         | `fdisjointUX`       |
| `fdisjointUr`                | Lemma    | Close         | `fdisjointXU`       |
| `fset0D`                     | Lemma    | Yes           |                     |
| `fsetD0`                     | Lemma    | Yes           |                     |
| `fsetDv`                     | Lemma    | Yes           |                     |
| `fsetDidPl`                  | Lemma    | Yes           |                     |
| `val_fset_filter`            | Lemma    | No            | ?                   |
| `fset_filter_subset`         | Lemma    | No            | ?                   |
| `fdisjoint_trans`            | Lemma    | Yes           |                     |
| `\bigcup_(i <- r | P) F`     | Notation | Yes           |                     |
| `\bigcup_(i <- r) F`         | Notation | Yes           |                     |
| `\bigcup_(m <= i < n | P) F` | Notation | No            |                     |
| `\bigcup_(m <= i < n) F`     | Notation | No            |                     |
| `\bigcup_(i | P) F`          | Notation | Yes           |                     |
| `\bigcup_i F`                | Notation | No            |                     |
| `\bigcup_(i : t | P) F`      | Notation | No            |                     |
| `\bigcup_(i : t) F`          | Notation | No            |                     |
| `\bigcup_(i < n | P) F`      | Notation | No            |                     |
| `\bigcup_(i < n) F`          | Notation | No            |                     |
| `\bigcup_(i in A | P) F`     | Notation | Yes           |                     |
| `\bigcup_(i in A) F`         | Notation | Yes           |                     |
| `bigcup_sup`                 | Lemma    | Close         | `bigfcup_sup`       |
| `bigcupP`                    | Lemma    | Close         | `bigfcupP`          |
| `bigcup_fin_sup`             | Lemma    | No            | `bigfcup_sup`       |
| `bigcup_finP`                | Lemma    | No            | `bigfcupP`          |
| `imfset`                     | Function | Yes           |                     |
| `imfsetP`                    | Lemma    | Yes           |                     |
| `eq_imfset`                  | Lemma    | Close         | `eq_imfset`         |
| `eq_in_imfset`               | Lemma    | Close         | `eq_in_imfset`      |
| `mem_imfset`                 | Lemma    | Mismatch      | ?                   |
| `imfset0`                    | Lemma    | Yes           |                     |
| `imfset1`                    | Lemma    | Close         | `imfset_fset1`      |
| `imfsetU`                    | Lemma    | Yes           |                     |
| `imfset1U`                   | Lemma    | Close         | `imfsetU1`          |
| `imfsetI`                    | Lemma    | Yes           |                     |
| `imfset_fset`                | Lemma    | No            | ?                   |
| `imfset_eq0`                 | Lemma    | No            | ?                   |
| `pimfset`                    | Function | No            | ?                   |
| `` f @` X ``                 | Notation | Yes           |                     |
| `imfset_id`                  | Lemma    | Yes           |                     |
| `imfset_comp`                | Lemma    | Yes           |                     |
| `imfsetK`                    | Lemma    | No            | ?                   |
| `imfset_inj`                 | Lemma    | No            | ?                   |
| `imfsetS`                    | Lemma    | No            | ?                   |
| `mem_imfset_can`             | Lemma    | No            | ?                   |
| `mem_imfset_inj`             | Lemma    | Close         | `mem_imfset`        |
| `size_imfset`                | Lemma    | No            | ?                   |
| `imfset_injP`                | Lemma    | No            | `card_imfset`       |
| `in_pimfset`                 | Lemma    | No            | ?                   |
| `pimfsetP`                   | Lemma    | No            | ?                   |
| `powerset`                   | Function | Close         | `fpowerset`         |
| `powersetE`                  | Lemma    | Close         | `fpowersetE`        |
| `powersetS`                  | Lemma    | Close         | `fpowersetS`        |
| `powerset0`                  | Lemma    | Close         | `fpowerset0`        |
| `powerset1`                  | Lemma    | Close         | `fpowerset1`        |
| `splits`                     | Function | No            | ?                   |
| `big_fset1U`                 | Lemma    | Close         | `big_fsetU1`        |
| `big_fsetU`                  | Lemma    | No            | ?                   |
| `big_idem_fset1U`            | Lemma    | No            | ?                   |
| `big_idem_fsetU`             | Lemma    | No            | ?                   |
| `big_idem_bigcup`            | Lemma    | No            | ?                   |
| `big_idem_imfset`            | Lemma    | No            | ?                   |
| `bigcup_fset1U`              | Lemma    | Close         | `big_fsetU1`        |
| `bigcup_fsetU`               | Lemma    | No            | ?                   |
| `bigcup_bigcup`              | Lemma    | No            | ?                   |
| `bigcupS`                    | Lemma    | No            | ?                   |
| `in_bigcup`                  | Lemma    | No            | ?                   |
| `bigcup1_cond`               | Lemma    | No            | ?                   |
| `bigcup1`                    | Lemma    | No            |                     |


# `fmap`

Definition fmap_of & phant (T -> S) := fmap_type.
Notation "{ 'fmap' T }" := (@fmap_of _ _ (Phant T))
Definition fmap (T : ordType) S s Ps : {fmap T -> S} :=
Definition getm (m : FMap.fmap_type T S) k := getm_def m k.
Lemma setm_subproof m k v : sorted (@Ord.lt T) (unzip1 (setm_def m k v)).
Definition setm (m : {fmap T -> S}) k v :=
Definition repm (m : {fmap T -> S}) k f : option {fmap T -> S} :=
Definition updm (m : {fmap T -> S}) k v :=
Definition unionm (m1 m2 : {fmap T -> S}) :=
Lemma mapim_subproof S' (f : T -> S -> S') m :
Definition mapim S' (f : T -> S -> S') m := fmap (mapim_subproof f m).
Definition mapm S' (f : S -> S') := mapim (fun _ x => f x).
Lemma filterm_subproof (a : T -> S -> bool) m :
Definition filterm (a : T -> S -> bool) (m : {fmap T -> S}) :=
Lemma remm_subproof m k : sorted (@Ord.lt T) (unzip1 (remm_def m k)).
Definition remm m k :=
Definition emptym : {fmap T -> S} :=
Definition mkfmap (kvs : seq (T * S)) : {fmap T -> S} :=
Definition mkfmapf (f : T -> S) (X : {fset T}) : {fmap T -> S} :=
Definition mkfmapfp (f : T -> option S) (X : {fset T}) : {fmap T -> S} :=
Definition domm m := fset (unzip1 m).
Notation "[ 'fmap' kv1 ; .. ; kvn ]" :=
Definition mem_fmap (m : {fmap T -> S}) :=
Lemma eq_fmap m1 m2 : m1 =1 m2 <-> m1 = m2.
Lemma mem_domm m k : k \in domm m = m k.
Lemma getmP m k : getm_spec m k (m k) (k \in domm m).
Lemma dommP m k : reflect (exists v, m k = Some v) (k \in domm m).
Lemma dommPn m k : reflect (m k = None) (k \notin domm m).
Lemma eq_in_fmap m1 m2 :
Lemma setmE m k v k' :
Lemma setmC m k v k' v' : k != k' ->
Lemma setmxx m k v v' : setm (setm m k v) k v' = setm m k v'.
Lemma repmE m m' k f :
Lemma updm_set m m' k v :
Lemma unionmE m1 m2 k : unionm m1 m2 k = if m1 k then m1 k else m2 k.
Lemma domm_union m1 m2 : domm (unionm m1 m2) = domm m1 `|` domm m2.
Lemma domm_set m k v : domm (setm m k v) = k |` domm m.
Lemma emptymE k : @emptym T S k = None.
Lemma domm0 : domm (@emptym T S) = fset0.
Lemma emptymP m : reflect (m = emptym) (domm m == fset0).
Lemma mapimE S' (f : T -> S -> S') m k : mapim f m k = omap (f k) (m k).
Lemma mapmE S' (f : S -> S') m k : mapm f m k = omap f (m k).
Lemma filtermE a m k :
Lemma filterm0 (a : T -> S -> bool) : filterm a emptym = emptym.
Lemma remmE m k k' :
Lemma remmI m k : k \notin domm m -> remm m k = m.
Lemma setm_rem m k v : setm (remm m k) k v = setm m k v.
Lemma filterm_set (a : T -> S -> bool) m x y :
Lemma domm_rem m k : domm (remm m k) = domm m `\ k.
Lemma domm_mkfmap (kvs : seq (T * S)) : domm (mkfmap kvs) =i unzip1 kvs.
Lemma domm_mkfmap' (kvs : seq (T * S)) :
Lemma mkfmapE (kvs : seq (T * S)) : mkfmap kvs =1 getm_def kvs.
Lemma mkfmapfE (f : T -> S) X k :
Lemma mkfmapfpE (f : T -> option S) X k :
Lemma domm_mkfmapf (f : T -> S) X : domm (mkfmapf f X) = X.
Lemma domm_mkfmapfp (f : T -> option S) X :
Lemma setm_union m1 m2 k v :
Lemma filterm_union p m1 m2 :
Lemma eq_mkfmapf (f1 f2 : T -> S) :
Lemma eq_mkfmapfp (f1 f2 : T -> option S) :
Lemma eq_filterm f1 f2 m :
Lemma domm_filter p m : domm (filterm p m) `<=` domm m.
Lemma domm_filter_eq (p : pred T) m :
Lemma setmI m k v : m k = Some v -> setm m k v = m.
Lemma union0m : left_id (@emptym T S) unionm.
Lemma unionm0 : right_id (@emptym T S) unionm.
Lemma unionmA : associative (@unionm T S).
Lemma unionmI : idempotent_op (@unionm T S).
Lemma unionmC m1 m2 :
Lemma unionmK m1 m2 : filterm (fun k _ => m1 k) (unionm m1 m2) = m1.
Lemma fmap_rect (P : {fmap T -> S} -> Type) :
Lemma fmap_ind (P : {fmap T -> S} -> Prop) :
Lemma val_domm m : domm m = unzip1 m :> seq _.
Lemma fmvalK : cancel val (@mkfmap T S).
Lemma mkfmapK (kvs : seq (T * S)) :
Lemma getm_nth p (m : {fmap T -> S}) i :
Lemma eq_setm (T : ordType) (S : eqType) m1 m2 (x : T) (y1 y2 : S) :
Definition splitm m :=
Lemma sizeES m :
Lemma dommES m :
Definition filter_map f m :=
Lemma filter_mapE f m x : filter_map f m x = obind (f x) (m x).
Lemma domm_filter_map f m :
Lemma mapimK (g : T -> R -> S) f :
Lemma domm_mapi (f : T -> S -> S') m : domm (mapim f m) = domm m.
Lemma domm_map (f : S -> S') m : domm (mapm f m) = domm m.
Lemma mapim_map (f : S -> S') m : mapim (fun=> f) m = mapm f m.
Lemma eq_mapm f g : f =1 g -> @mapm T S S' f =1 mapm g.
Lemma mapm_comp S'' (g : S' -> S'') (f : S -> S') m :
Lemma mapm_mkfmapf (f : S -> S') (g : T -> S) (X : {fset T}) :
Definition mapm2 T T' S S' f g (m : {fmap T -> S}) : {fmap T' -> S'} :=
Lemma mapm2E T T' S S' (f : T -> T') (g : S -> S') m x :
Lemma domm_map2 T T' S S' (f : T -> T') (g : S -> S') m :
Lemma mapm2_comp T T' T'' S S' S'' f f' g g' :
Lemma in_fmapP m k v : reflect (m k = Some v) ((k, v) \in m).
Lemma mkfmap_Some (kvs : seq (T * S)) k v
Definition injectivem m := uniq (unzip2 m).
Lemma injectivemP m : reflect {in domm m, injective m} (injectivem m).
Lemma eq_domm0 (S' : eqType) (m : {fmap T -> S'}) :
Definition invm m := mkfmap [seq (p.2, p.1) | p <- m].
Definition codomm m := domm (invm m).
Lemma getm_inv m k k' : invm m k = Some k' -> m k' = Some k.
Lemma codommP m k : reflect (exists k', m k' = Some k) (k \in codomm m).
Lemma codommPn m k : reflect (forall k', m k' != Some k) (k \notin codomm m).
Lemma codomm0 : codomm (@emptym T S) = fset0.
Lemma codomm_rem m k : codomm (remm m k) `<=` codomm m.
Lemma invmE m k : obind m (invm m k) = if invm m k then Some k else None.
Lemma invmEV m k :
Lemma invm_inj m : {in codomm m, injective (invm m)}.
Lemma invmK m : {in domm m, injective m} -> invm (invm m) = m.
Definition fmap_of_seq (xs : seq T) : {fmap nat -> T} :=
Lemma fmap_of_seqE xs n :
Definition currym m :=
Definition uncurrym n : {fmap T * S -> R} :=
Lemma currymP m x y v :
Lemma currymE m x y :
Lemma domm_curry m : domm (currym m) = @fst _ _ @` (domm m).
Lemma uncurrymP n x y v :
Lemma uncurrymE n p :
Lemma currymK : cancel currym uncurrym.
Definition enum_fmap xs ys :=
Lemma enum_fmapP xs ys m :

# `ffun`

Definition appf f x :=
Lemma eq_ffun f g : f =1 g <-> f = g.
Definition finsupp f := domm (val f).
Lemma mem_finsupp f x : (x \in finsupp f) = (f x != def x).
Lemma mem_finsuppN f x : (x \notin finsupp f) = (f x == def x).
Lemma finsuppPn f x : reflect (f x = def x) (x \notin finsupp f).
Lemma emptyf_subproof : wf (@emptym T S).
Definition emptyf := FFun emptym emptyf_subproof.
Lemma emptyfE x : emptyf x = def x.
Lemma finsupp0 : finsupp emptyf = fset0.
Definition upd_def f x y :=
Lemma upd_subproof f x y : wf (upd_def f x y).
Definition upd f x y := FFun (upd_def f x y) (upd_subproof f x y).
Lemma updE f x1 y x2 :
Definition mkffun (fb : T -> S) (xs : seq T) :=
Lemma mkffunE fb xs x :
Lemma finsupp_mkffun fb xs :
Lemma finsupp_mkffun_sub fb (X : {fset T}) : finsupp (mkffun fb X) `<=` X.
Definition updfm f (xs : {fmap T -> S}) : ffun :=
Lemma updfmE f xs x :
Definition mkffunm (m : {fmap T -> S}) : ffun :=
Lemma mkffunmE m x : mkffunm m x = odflt (def x) (m x).
Lemma val_mkffun (f : T -> S) (X : {fset T}) :
Definition mapf (g : S -> R) (f : ffun def) : ffun (g \o def) :=
Lemma mapfE (g : S -> R) (f : ffun def) x :
Lemma val_mapf (g : S -> R) :
Notation supp := finsupp (only parsing).
Notation mem_supp := mem_finsupp (only parsing).
Notation mem_suppN := mem_finsuppN (only parsing).
Notation suppPn := finsuppPn (only parsing).
Notation supp0 := finsupp0 (only parsing).
Notation supp_mkffun := finsupp_mkffun (only parsing).
Notation supp_mkffun_sub := finsupp_mkffun_sub (only parsing).
