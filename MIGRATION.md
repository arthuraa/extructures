# Migration guide from Extructures to Finmap

## Equivalence table

The following table maps definitions in Extructures to their counterparts in
Finmap.

| Extructures                     | Finmap                               |
|---------------------------------|--------------------------------------|
| `:<=:, :|:, |:, :&:, :\:, :\`   | `` `<=`, `|`, |`, `&`, `\`, `\ ``    |
| `X :#: Y`                       | `[disjoint X & Y]`                   |
| `f x` where `f : {fmap X -> Y}` | `f.[? x]`                            |
| `[fset x1; ...; xn]`            | `[fset x1; ...; xn]`                 |
| `supp f`                        | `finsupp f`                          |
| `fset xs` where `xs : seq T`    | `[fset x in xs], [fset x | x in xs]` |
| `in_fset`                       | `inE, in_fsetE`                      |
| `eq_fset`                       | `fsetP`                              |
| `in_fsetU1`                     | `in_fset1U`                          |
| `fset_rect, fset_ind`           | `fset1U_rect`                        |
| `fsetU1P`                       | `fset1UP`                            |
| `fsubsetxx`                     | `fsubset_refl`                       |
|                                 |                                      |

## Things that do not exist in Finmap

### Results that rely on `fset : seq T -> {fset T}`

- `all_fset, has_fset`.  If `A : {fset T}`, consider writing `[forall x : A, P
  (val x)]` instead of `all P x`.
  
- `fset_eqP`.  The closest result in Finmap, also called `fset_eqP`, has a
  different statement.

- `fsvalK`, `fset0E`, `fset1E`, `fset_cat`, `all_fsetU`, `fset_eq0E`

### Results that rely on `val X` being sorted

Extructures uses sorted lists to represent functions and sets. Because of this,
we can expose lemmas such as `val_fset_filter` that explain how the
representation is affected by certain operations.  In finmap, everything is up
to a choice of representative, so these lemmas cannot be used.

Affected lemmas: `val_fset_filter`.

### Others

- `fsetP`

- `fsubU1set`.  Use `fsubUset` and `fsub1set`.

## Things that exist on both libraries

- A coercion `fset -> seq` that extracts a sequence of non duplicate elements.

- A canonical structure of `predType` on `fset`, allowing you to write `x \in
  X`.

- `in_fset0`, `in_fset1`, `fset1P`, `fset1_inj`, `in_fsetU`, `in_fsetI`,
  `in_fset2`, `fset21`, `fset22`, `fset2P`, `fsetUP`, `fsetUid`, `fsubsetP`,
  `fsubset_trans`, `fsubsetUl`, `fsubsetUr`, `fsubUset`

# Compatibility layer to add to Finmap

- A notation `fset xs` to turn a list into a set.

- An equivalent of the current `fsetP`.

- Change the canonicalization function so that singletons are preserved.

- `fsub1Uset`.
