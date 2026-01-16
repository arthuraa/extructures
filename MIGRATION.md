# Migration guide from Extructures to Finmap

Extructures is being phased out in favor of [Finmap library available in
Mathematical Components][finmap].  To smooth the transition between the two
libraries, this document summarizes the main differences between them.  Near the
end of the file, you will find a comprehensive list of all the public symbols
and notations in Extructures and a mapping to their closest analogue in Finmap.

## Things that do not exist in Finmap

### `ordType`

Most container types in Extructures require types to be instances of the
`ordType` interface.  In Finmap, instead, they are required to be instances of
`choiceType`.

### Results that rely on `fset : seq T -> {fset T}`

In Extructures, `fset` is one of the main functions for building new sets.  In
Finmap, we instead use the more general `imfset`, which computes the image of a
finite predicate under any function.  (There is a `set_fset` function with this
type, but it's not meant to be used directly.) As a result, several lemmas
stated for `fset` do not have direct analogues in Finmap.

- `all_fset, has_fset`.  If `A : {fset T}`, consider writing `[forall x : A, P
  (val x)]` instead of `all P x`.
  
- `fset_eqP`.  The closest result in Finmap, also called `fset_eqP`, has a
  different statement.

- `fsvalK`, `fset0E`, `fset1E`, `fset_cat`, `all_fsetU`, `fset_eq0E`.

### Results that rely on `val X` being sorted

Extructures uses sorted lists to represent functions and sets. Because of this,
we can expose lemmas such as `val_fset_filter` that explain how the
representation is affected by certain operations.  In Finmap, everything is up
to a choice of representative, so these lemmas cannot be used.

Affected lemmas: `val_fset_filter`.

## Compatibility layer to add to Finmap

- A notation `fset xs` to turn a list into a set.

- An equivalent of the current `fsetP`.

- Change the canonicalization function so that singletons are preserved.

- `fsub1Uset`.

## Equivalence table

The following table maps definitions in Extructures to their counterparts in
Finmap.  We consider four possibilities (cf. the "In finmap?" column):

- **Yes** The definition already exists in Finmap with the same name.

- **Close** The definition does not exist in Finmap, but it has a very close
  analogue.

- **No** The definition does not exist in Finmap. It might be emulated in some
  cases by composing several other definitions or lemmas.  (A "?" indicates that
  there is probably a canonical way of doing so, but we haven't found one yet.)

- **No+Boot** Same thing, but we should also consider adding it to
  `mathcomp-boot`.

- **Mismatch** The name or notation exists in Finmap, but it means something
  else.
  
(NB: below, we're listing coercions into Funclass and predType instances as
notations, even though they are not notations in the Rocq sense.)

### `fset`

| Extructures Name              | What?    | In finmap? | Closest analogue     |
|-------------------------------|----------|------------|----------------------|
| `{fset T}`                    | Type     | Yes        |                      |
| `fset`                        | Function | Close      | `[fset x in xs]`     |
| `pred_of_fset`                | Function | Close      | `[in A]`             |
| `x \in A`                     | Notation | Yes        |                      |
| `in_fset`                     | Lemma    | Close      | `inE`, `in_fsetE`    |
| `fset0`                       | Function | Yes        |                      |
| `fset1`                       | Function | Yes        |                      |
| `fsetU`                       | Function | Yes        |                      |
| `fset_filter`                 | Function | No         | `[fset x in A |\ P]` |
| `fsetI`                       | Function | Yes        |                      |
| `fsetD`                       | Function | Yes        |                      |
| `fsubset`                     | Function | Yes        |                      |
| `fdisjoint`                   | Function | Yes        |                      |
| ``s1 `\|` s2``                | Notation | Yes        |                      |
| ``x   \|` s``                 | Notation | Yes        |                      |
| ``s1 `&` s2``                 | Notation | Yes        |                      |
| ``s1 `\` s2``                 | Notation | Yes        |                      |
| ``s `\ x``                    | Notation | Yes        |                      |
| ``s1 `<=` s2``                | Notation | Yes        |                      |
| ``s1 `#` s2``                 | Notation | No         | `[disjoint A & B]`   |
| `[fset a1; .. ; an]`          | Notation | Yes        |                      |
| `all_fset`                    | Lemma    | No         | ?                    |
| `has_fset`                    | Lemma    | No         | ?                    |
| `eq_fset`                     | Lemma    | Close      | `fsetP`              |
| `fset_eqP`                    | Lemma    | Close      | `fset_eqP`           |
| `fsvalK`                      | Lemma    | No         |                      |
| `fset0E`                      | Lemma    | No         | ?                    |
| `fset1E`                      | Lemma    | No         | ?                    |
| `in_fset0`                    | Lemma    | Yes        |                      |
| `in_fset1`                    | Lemma    | Yes        |                      |
| `fset1P`                      | Lemma    | Yes        |                      |
| `fset1_inj`                   | Lemma    | Yes        |                      |
| `in_fsetU`                    | Lemma    | Yes        |                      |
| `in_fset1U`                   | Lemma    | Yes        |                      |
| `fset_cat`                    | Lemma    | Close      | `fset_cat`           |
| `all_fsetU`                   | Lemma    | No         | ?                    |
| `in_fset2`                    | Lemma    | Yes        |                      |
| `fset21`                      | Lemma    | Yes        |                      |
| `fset22`                      | Lemma    | Yes        |                      |
| `fset2P`                      | Lemma    | Yes        |                      |
| `fsetP`                       | Lemma    | No+Boot    | `fset_0Vmem`         |
| `fset1U_rect`                 | Lemma    | Yes        |                      |
| `fset1U_ind`                  | Lemma    | No         | `fset1U_rect`        |
| `fset1UP`                     | Lemma    | Yes        |                      |
| `fsetUP`                      | Lemma    | Yes        |                      |
| `fsetUC`                      | Lemma    | Yes        |                      |
| `fsetUA`                      | Lemma    | Yes        |                      |
| `fset0U`                      | Lemma    | Yes        |                      |
| `fsetU0`                      | Lemma    | Yes        |                      |
| `fsetUid`                     | Lemma    | Yes        |                      |
| `fset_eq0E`                   | Lemma    | No         | ?                    |
| `fsubsetP`                    | Lemma    | Yes        |                      |
| `fsubset_refl`                | Lemma    | Yes        |                      |
| `fsubset_trans`               | Lemma    | Yes        |                      |
| `fsubsetUl`                   | Lemma    | Yes        |                      |
| `fsubsetUr`                   | Lemma    | Yes        |                      |
| `fsub1Uset`                   | Lemma    | No         |                      |
| `fsubUset`                    | Lemma    | Yes        |                      |
| `fsetUS`                      | Lemma    | Yes        |                      |
| `fsetSU`                      | Lemma    | Yes        |                      |
| `fsetUSS`                     | Lemma    | Yes        |                      |
| `fsub1set`                    | Lemma    | Yes        |                      |
| `fset_cons`                   | Lemma    | Yes        |                      |
| `uniq_fset`                   | Lemma    | Close      | `fset_uniq`          |
| `in_fset_filter`              | Lemma    | Close      | `inE`, `in_fsetE`    |
| `in_fsetI`                    | Lemma    | Yes        |                      |
| `fsetIP`                      | Lemma    | Yes        |                      |
| `fsetIC`                      | Lemma    | Yes        |                      |
| `fsetIA`                      | Lemma    | Yes        |                      |
| `fsetIid`                     | Lemma    | Yes        |                      |
| `fset0I`                      | Lemma    | Yes        |                      |
| `fsetI0`                      | Lemma    | Yes        |                      |
| `fsetUIl`                     | Lemma    | Yes        |                      |
| `fsetUIr`                     | Lemma    | Yes        |                      |
| `fsetIUl`                     | Lemma    | Yes        |                      |
| `fsetIUr`                     | Lemma    | Yes        |                      |
| `fsubsetIl`                   | Lemma    | Yes        |                      |
| `fsubsetIr`                   | Lemma    | Yes        |                      |
| `fsubsetI`                    | Lemma    | Yes        |                      |
| `fsubIset`                    | Lemma    | Yes        |                      |
| `fsetIS`                      | Lemma    | Yes        |                      |
| `fsetSI`                      | Lemma    | Yes        |                      |
| `fsetISS`                     | Lemma    | Yes        |                      |
| `fsetIidPl`                   | Lemma    | Yes        |                      |
| `fsetIidPr`                   | Lemma    | Yes        |                      |
| `fsetUidPl`                   | Lemma    | Yes        |                      |
| `fsetUidPr`                   | Lemma    | Yes        |                      |
| `fset1I`                      | Lemma    | No+Boot    | ?                    |
| `fdisjoint_sym`               | Lemma    | Yes        |                      |
| `fdisjointP`                  | Lemma    | Yes        |                      |
| `fdisjointSl`                 | Lemma    | Close      | `fdisjointWl`        |
| `fdisjointSr`                 | Lemma    | Close      | `fdisjointWr`        |
| `fdisjoint0s`                 | Lemma    | Close      | `fdisjoint0X`        |
| `fdisjoints0`                 | Lemma    | Close      | `fdisjointX0`        |
| `fdisjoints1`                 | Lemma    | Close      | `fdisjointX1`        |
| `fdisjoint1s`                 | Lemma    | Close      | `fdisjoint1X`        |
| `in_fsetD`                    | Lemma    | Yes        |                      |
| `in_fsetD1`                   | Lemma    | Yes        |                      |
| `fsetDP`                      | Lemma    | Yes        |                      |
| `fsetD1P`                     | Lemma    | No         | ?                    |
| `fsubDset`                    | Lemma    | Yes        |                      |
| `fsubD1set`                   | Lemma    | No         | ?                    |
| `fsetID`                      | Lemma    | Yes        |                      |
| `fsetDUl`                     | Lemma    | Yes        |                      |
| `fsetDUr`                     | Lemma    | Yes        |                      |
| `fsetUDr`                     | Lemma    | Mismatch   | `fsetUDl`            |
| `fsetDIl`                     | Lemma    | Yes        |                      |
| `fsetIDA`                     | Lemma    | Yes        |                      |
| `fsetIDAC`                    | Lemma    | Yes        |                      |
| `fsetDIr`                     | Lemma    | Yes        |                      |
| `fsetDDl`                     | Lemma    | Yes        |                      |
| `fsetDDr`                     | Lemma    | Yes        |                      |
| `fsetSD`                      | Lemma    | Yes        |                      |
| `fsetDS`                      | Lemma    | Yes        |                      |
| `fdisjoint_fsetI0`            | Lemma    | No         | ?                    |
| `fpick`                       | Function | No         | ?                    |
| `fpickP`                      | Lemma    | No         |                      |
| `sizes0`                      | Lemma    | Close      | `cardfs0`            |
| `sizes1`                      | Lemma    | Close      | `cardfs1`            |
| `sizesU`                      | Lemma    | No         | ?                    |
| `sizes1U`                     | Lemma    | Close      | `cardfsU1`           |
| `sizesD1`                     | Lemma    | Close      | `cardfsD1`           |
| `sizesD`                      | Lemma    | Close      | `cardfsD`            |
| `size_fset`                   | Lemma    | No         | `card_fseq`          |
| `uniq_size_fset`              | Lemma    | No         | ?                    |
| `fsubset_leq_size`            | Lemma    | Close      | `fsubset_leq_card`   |
| `sizes_eq0`                   | Lemma    | Close      | `cardfs_eq0`         |
| `fset0Pn`                     | Lemma    | Yes        |                      |
| `fsubset_sizeP`               | Lemma    | Close      | `fsubset_cardP`      |
| `eqEfsubset`                  | Lemma    | Yes        |                      |
| `eqEfsize`                    | Lemma    | Close      | `eqEfcard`           |
| `fsub0set`                    | Lemma    | Yes        |                      |
| `fsubset0`                    | Lemma    | Yes        |                      |
| `fsubset1`                    | Lemma    | Yes        |                      |
| `fsetU_eq0`                   | Lemma    | Yes        |                      |
| `fdisjointUl`                 | Lemma    | Close      | `fdisjointUX`        |
| `fdisjointUr`                 | Lemma    | Close      | `fdisjointXU`        |
| `fset0D`                      | Lemma    | Yes        |                      |
| `fsetD0`                      | Lemma    | Yes        |                      |
| `fsetDv`                      | Lemma    | Yes        |                      |
| `fsetDidPl`                   | Lemma    | Yes        |                      |
| `val_fset_filter`             | Lemma    | No         | ?                    |
| `fset_filter_subset`          | Lemma    | No         | ?                    |
| `fdisjoint_trans`             | Lemma    | Yes        |                      |
| `\bigcup_(i <- r \| P) F`     | Notation | Yes        |                      |
| `\bigcup_(i <- r) F`          | Notation | Yes        |                      |
| `\bigcup_(m <= i < n \| P) F` | Notation | No         |                      |
| `\bigcup_(m <= i < n) F`      | Notation | No         |                      |
| `\bigcup_(i \| P) F`          | Notation | Yes        |                      |
| `\bigcup_i F`                 | Notation | No         |                      |
| `\bigcup_(i : t \| P) F`      | Notation | No         |                      |
| `\bigcup_(i : t) F`           | Notation | No         |                      |
| `\bigcup_(i < n \| P) F`      | Notation | No         |                      |
| `\bigcup_(i < n) F`           | Notation | No         |                      |
| `\bigcup_(i in A \| P) F`     | Notation | Yes        |                      |
| `\bigcup_(i in A) F`          | Notation | Yes        |                      |
| `bigcup_sup`                  | Lemma    | Close      | `bigfcup_sup`        |
| `bigcupP`                     | Lemma    | Close      | `bigfcupP`           |
| `bigcup_fin_sup`              | Lemma    | No         | `bigfcup_sup`        |
| `bigcup_finP`                 | Lemma    | No         | `bigfcupP`           |
| `imfset`                      | Function | Yes        |                      |
| `imfsetP`                     | Lemma    | Yes        |                      |
| `eq_imfset`                   | Lemma    | Close      | `eq_imfset`          |
| `eq_in_imfset`                | Lemma    | Close      | `eq_in_imfset`       |
| `mem_imfset`                  | Lemma    | Mismatch   | ?                    |
| `imfset0`                     | Lemma    | Yes        |                      |
| `imfset1`                     | Lemma    | Close      | `imfset_fset1`       |
| `imfsetU`                     | Lemma    | Yes        |                      |
| `imfset1U`                    | Lemma    | Close      | `imfsetU1`           |
| `imfsetI`                     | Lemma    | Yes        |                      |
| `imfset_fset`                 | Lemma    | No         | ?                    |
| `imfset_eq0`                  | Lemma    | No         | ?                    |
| `pimfset`                     | Function | No         | ?                    |
| `` f @` X ``                  | Notation | Yes        |                      |
| `imfset_id`                   | Lemma    | Yes        |                      |
| `imfset_comp`                 | Lemma    | Yes        |                      |
| `imfsetK`                     | Lemma    | No         | ?                    |
| `imfset_inj`                  | Lemma    | No         | ?                    |
| `imfsetS`                     | Lemma    | No         | ?                    |
| `mem_imfset_can`              | Lemma    | No         | ?                    |
| `mem_imfset_inj`              | Lemma    | Close      | `mem_imfset`         |
| `size_imfset`                 | Lemma    | No         | ?                    |
| `imfset_injP`                 | Lemma    | No         | `card_imfset`        |
| `in_pimfset`                  | Lemma    | No         | ?                    |
| `pimfsetP`                    | Lemma    | No         | ?                    |
| `fpowerset`                   | Function | Yes        |                      |
| `fpowersetE`                  | Lemma    | Yes        |                      |
| `fpowersetS`                  | Lemma    | Yes        |                      |
| `fpowerset0`                  | Lemma    | Yes        |                      |
| `fpowerset1`                  | Lemma    | Yes        |                      |
| `splits`                      | Function | No         | ?                    |
| `big_fset1U`                  | Lemma    | Close      | `big_fsetU1`         |
| `big_fsetU`                   | Lemma    | No         | ?                    |
| `big_idem_fset1U`             | Lemma    | No         | ?                    |
| `big_idem_fsetU`              | Lemma    | No         | ?                    |
| `big_idem_bigcup`             | Lemma    | No         | ?                    |
| `big_idem_imfset`             | Lemma    | No         | ?                    |
| `bigcup_fset1U`               | Lemma    | Close      | `big_fsetU1`         |
| `bigcup_fsetU`                | Lemma    | No         | ?                    |
| `bigcup_bigcup`               | Lemma    | No         | ?                    |
| `bigcupS`                     | Lemma    | No         | ?                    |
| `in_bigcup`                   | Lemma    | No         | ?                    |
| `bigcup1_cond`                | Lemma    | No         | ?                    |
| `bigcup1`                     | Lemma    | No         |                      |

#### Notes

- `fsetP`: We should rename this to `fset_0VmemP` and create analog lemmas in
  Finmap and MathComp boot.

### `fmap`

| Extructures Name   | What?    | In finmap? | Closest analogue                 |
|--------------------|----------|------------|----------------------------------|
| `{fmap T -> S}`    | Type     | Yes        |                                  |
| `fmap`             | Function | No         | ?                                |
| `getm`             | Function | Close      | `fnd`, `m.[? x]`                 |
| `m x`              | Notation | Mismatch   | `m.[? x]`                        |
| `setm`             | Function | Close      | `setf`, `m.[x <- v]`             |
| `repm`             | Function | No         | ?                                |
| `updm`             | Function | No         | ?                                |
| `unionm`           | Function | Close      | `catf`, `m1 + m2`                |
| `mapim`            | Function | Close      | `[fmap x : domf m => F x (m x)]` |
| `mapm`             | Function | Close      | `[fmap x : domf m => F (m x)]`   |
| `filterm`          | Function | Close      | `filterf`                        |
| `remm`             | Function | Close      | `restrictf`, `m.[~ x]`           |
| `emptym`           | Function | Close      | `fmap0`, `[fmap]`                |
| `mkfmap`           | Function | No         | ?                                |
| `mkfmapf`          | Function | Close      | `[fmap x : X => f x]`            |
| `mkfmapfp`         | Function | No         | ?                                |
| `domm`             | Function | Close      | `domf`                           |
| `[fmap kv1 ; .. ]` | Notation | No         | ?                                |
| `mem_fmap`         | Function | No         | `m.[? x] == Some v`              |
| `(x,v) \in m`      | Notation | No         | `m.[? x] == Some v`              |
| `eq_fmap`          | Lemma    | Close      | `fmapP`                          |
| `mem_domm`         | Lemma    | No         | `case: fndP`                     |
| `getmP`            | Lemma    | Close      | `fndP`                           |
| `dommP`            | Lemma    | No         | `fndP`                           |
| `dommPn`           | Lemma    | No         | `fndP`                           |
| `eq_in_fmap`       | Lemma    | Close      | `getfP`                          |
| `setmE`            | Lemma    | Close      | `fnd_set`                        |
| `setmC`            | Lemma    | Close      | `setfC`                          |
| `setmxx`           | Lemma    | Close      | `setfC`                          |
| `repmE`            | Lemma    | No         | ?                                |
| `updm_set`         | Lemma    | No         | ?                                |
| `unionmE`          | Lemma    | Close      | `fnd_cat`                        |
| `domm_union`       | Lemma    | Close      | `domf_cat`                       |
| `domm_set`         | Lemma    | Close      | `dom_setf`                       |
| `emptymE`          | Lemma    | Close      | `fnd_fmap0`                      |
| `domm0`            | Lemma    | Close      | `domf0`                          |
| `emptymP`          | Lemma    | No         | ?                                |
| `mapimE`           | Lemma    | Close      | `rewrite /= ffunE`               |
| `mapmE`            | Lemma    | Close      | `rewrite /= ffunE`               |
| `filtermE`         | Lemma    | Close      | `fnd_filterf`                    |
| `filterm0`         | Lemma    | No         | ?                                |
| `remmE`            | Lemma    | Close      | `fnd_rem1`                       |
| `remmI`            | Lemma    | Close      | `remf1_id`                       |
| `setm_rem`         | Lemma    | Close      | `setf_rem1`                      |
| `filterm_set`      | Lemma    | No         | ?                                |
| `domm_rem`         | Lemma    | Close      | `domf_rem`                       |
| `domm_mkfmap`      | Lemma    | No         | ?                                |
| `domm_mkfmap'`     | Lemma    | No         | ?                                |
| `mkfmapE`          | Lemma    | No         | ?                                |
| `mkfmapfE`         | Lemma    | Close      | `rewrite /= ffunE`               |
| `mkfmapfpE`        | Lemma    | No         | ?                                |
| `domm_mkfmapf`     | Lemma    | Close      | `rewrite /=`                     |
| `domm_mkfmapfp`    | Lemma    | No         |                                  |
| `setm_union`       | Lemma    | Close      | `setf_catr`                      |
| `filterm_union`    | Lemma    | Close      | `remf_cat`                       |
| `eq_mkfmapf`       | Lemma    | No         | ?                                |
| `eq_mkfmapfp`      | Lemma    | No         | ?                                |
| `eq_filterm`       | Lemma    | No         | ?                                |
| `domm_filter`      | Lemma    | Close      | `domf_filterf`                   |
| `domm_filter_eq`   | Lemma    | Close      | `domf_filterf`                   |
| `setmI`            | Lemma    | Close      | `setf_get`                       |
| `union0m`          | Lemma    | Close      | `cat0f`                          |
| `unionm0`          | Lemma    | Close      | `catf0`                          |
| `unionmA`          | Lemma    | Close      | `catfA`                          |
| `unionmI`          | Lemma    | No         | ?                                |
| `unionmC`          | Lemma    | Close      | `disjoint_catfC`                 |
| `unionmK`          | Lemma    | Close      | `restrictf_cat_domr`             |
| `fmap_rect`        | Lemma    | No         |                                  |
| `fmap_ind`         | Lemma    | No         |                                  |
| `val_domm`         | Lemma    | No         | ?                                |
| `fmvalK`           | Lemma    | No         | ?                                |
| `mkfmapK`          | Lemma    | No         | ?                                |
| `getm_nth`         | Lemma    | No         | ?                                |
| `eq_setm`          | Lemma    | No         | ?                                |
| `splitm`           | Function | No         | ?                                |
| `sizeES`           | Lemma    | No         |                                  |
| `dommES`           | Lemma    | No         | ?                                |
| `filter_map`       | Function | No         |                                  |
| `filter_mapE`      | Lemma    | No         |                                  |
| `domm_filter_map`  | Lemma    | No         |                                  |
| `mapimK`           | Lemma    | No         |                                  |
| `domm_mapi`        | Lemma    | No         |                                  |
| `domm_map`         | Lemma    | No         |                                  |
| `mapim_map`        | Lemma    | No         |                                  |
| `eq_mapm`          | Lemma    | No         |                                  |
| `mapm_comp`        | Lemma    | No         |                                  |
| `mapm_mkfmapf`     | Lemma    | No         |                                  |
| `mapm2`            | Function | No         |                                  |
| `mapm2E`           | Lemma    | No         |                                  |
| `domm_map2`        | Lemma    | No         |                                  |
| `mapm2_comp`       | Lemma    | No         |                                  |
| `in_fmapP`         | Lemma    | No         |                                  |
| `mkfmap_Some`      | Lemma    | No         |                                  |
| `injectivem`       | Function | No         |                                  |
| `injectivemP`      | Lemma    | No         |                                  |
| `eq_domm0`         | Lemma    | Close      | `fmap_nil`                       |
| `invm`             | Function | No         |                                  |
| `codomm`           | Function | Close      | `codomf`                         |
| `getm_inv`         | Lemma    | No         |                                  |
| `codommP`          | Lemma    | Close      | `codomfP`                        |
| `codommPn`         | Lemma    | Close      | `codomfPn`                       |
| `codomm0`          | Lemma    | Close      | `codomf0`                        |
| `codomm_rem`       | Lemma    | Close      | `codomf_rem`                     |
| `invmE`            | Lemma    | No         |                                  |
| `invmEV`           | Lemma    | No         |                                  |
| `invm_inj`         | Lemma    | No         |                                  |
| `invmK`            | Lemma    | No         |                                  |
| `fmap_of_seq`      | Function | No         |                                  |
| `fmap_of_seqE`     | Lemma    | No         |                                  |
| `currym`           | Function | No         |                                  |
| `uncurrym`         | Function | No         |                                  |
| `currymP`          | Lemma    | No         |                                  |
| `currymE`          | Lemma    | No         |                                  |
| `domm_curry`       | Lemma    | No         |                                  |
| `uncurrymP`        | Lemma    | No         |                                  |
| `uncurrymE`        | Lemma    | No         |                                  |
| `currymK`          | Lemma    | No         |                                  |
| `enum_fmap`        | Function | No         |                                  |
| `enum_fmapP`       | Lemma    | No         |                                  |

### `ffun`

| Extructures Name     | What?    | In finmap? | Closest analogue                    |
|----------------------|----------|------------|-------------------------------------|
| `ffun d`             | Type     | Close      | `{fsfun for d}`                     |
| `appf`               | Function | Close      | `fun_of_fsfun`                      |
| `f x`                | Notation | Yes        |                                     |
| `eq_ffun`            | Lemma    | Close      | `fsfunP`                            |
| `finsupp`            | Function | Yes        |                                     |
| `mem_finsupp`        | Lemma    | Yes        |                                     |
| `mem_finsuppN`       | Lemma    | Close      | `memNfinsupp`                       |
| `finsuppPn`          | Lemma    | Close      | `finsuppP`                          |
| `emptyf`             | Function | Close      | `[fsfun]`                           |
| `emptyfE`            | Lemma    | Close      | `fsfun0E`                           |
| `finsupp0`           | Lemma    | Yes        |                                     |
| `upd`                | Function | Close      | `[fsfun f with x \|-> y]`           |
| `updE`               | Lemma    | Close      | `fsfun_withE`                       |
| `mkffun`             | Function | Close      | `[fsfun x in S => F]`               |
| `mkffunE`            | Lemma    | Close      | `fsfunE`                            |
| `finsupp_mkffun`     | Lemma    | Close      | `finsupp_fsfun`                     |
| `finsupp_mkffun_sub` | Lemma    | Close      | `finsupp_sub`                       |
| `updfm`              | Function | No         |                                     |
| `updfmE`             | Lemma    | No         |                                     |
| `mkffunm`            | Function | No         | `[fsfun x in domf f => F]`          |
| `mkffunmE`           | Lemma    | No         |                                     |
| `val_mkffun`         | Lemma    | No         |                                     |
| `mapf`               | Function | Close      | `[fsfun x in finsupp f => g (f x)]` |
| `mapfE`              | Lemma    | No         |                                     |
| `val_mapf`           | Lemma    | No         |                                     |


  [finmap]: https://github.com/math-comp/finmap
