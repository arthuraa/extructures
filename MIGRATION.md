# Migration guide from Extructures to Finmap

## Equivalence table

The following table maps definitions in Extructures to their counterparts in
Finmap.

| Extructures                     | Finmap                               |
|---------------------------------|--------------------------------------|
| `` X `#` Y ``                   | `[disjoint X & Y]`                   |
| `f x` where `f : {fmap X -> Y}` | `f.[? x]`                            |
| `fset xs` where `xs : seq T`    | `[fset x in xs], [fset x | x in xs]` |
| `in_fset`                       | `inE, in_fsetE`                      |
| `eq_fset`                       | `fsetP`                              |
| `fsubsetxx`                     | `fsubset_refl`                       |
| `uniq_fset`                     | `fset_uniq`                          |
|                                 |                                      |


## Things that do not exist in Finmap

### Results that rely on `fset : seq T -> {fset T}`

- `all_fset, has_fset`.  If `A : {fset T}`, consider writing `[forall x : A, P
  (val x)]` instead of `all P x`.
  
- `fset_eqP`.  The closest result in Finmap, also called `fset_eqP`, has a
  different statement.

- `fsvalK`, `fset0E`, `fset1E`, `fset_cat`, `all_fsetU`, `fset_eq0E`,
  `fset_cons`.

### Results that rely on `val X` being sorted

Extructures uses sorted lists to represent functions and sets. Because of this,
we can expose lemmas such as `val_fset_filter` that explain how the
representation is affected by certain operations.  In finmap, everything is up
to a choice of representative, so these lemmas cannot be used.

Affected lemmas: `val_fset_filter`.

### Others

- `fsetP`

- `fsubU1set`.  Use `fsubUset` and `fsub1set`.

- `in_fset_filter`

## Things that exist on both libraries

- A coercion `fset -> seq` that extracts a sequence of non duplicate elements.

- A canonical structure of `predType` on `fset`, allowing you to write `x \in
  X`.

- `in_fset0`, `in_fset1`, `fset1P`, `fset1_inj`, `in_fsetU`, `in_fsetI`,
  `in_fset2`, `fset21`, `fset22`, `fset2P`, `fsetUP`, `fsetUid`, `fsubsetP`,
  `fsubset_trans`, `fsubsetUl`, `fsubsetUr`, `fsubUset`, `fsetUS`, `fsetSU`,
  `fsetUSS`, `fsub1set`, `in_fsetI`, `fsetIP`, `fsetIC`, `fsetIA`, `fsetIid`,
  `fset0I`, `fsetI0`, `fsetUIl`, `fsetUIr`, `fsetIUl`, `fsetIUr`, `fsubsetIl`,
  `fsubsetIr`, `fsubsetI`, `fsubIset`, `fsetIS`, `fsetSI`, `fsetISS`.

- A notation `[fset x1; ...; xn]`

# Compatibility layer to add to Finmap

- A notation `fset xs` to turn a list into a set.

- An equivalent of the current `fsetP`.

- Change the canonicalization function so that singletons are preserved.

- `fsub1Uset`.
