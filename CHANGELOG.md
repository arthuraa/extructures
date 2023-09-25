# Unreleased

## Added

- Lemmas `fset_eqP`, `fset_eq0E` and `domm_filter_eq`.

## Changed

## Deprecated

## Fixed

## Removed

# 0.4.0 (2023/09/25)

## Added

- Infix notations for `fsubset` (`:<=:`) and `fdisjoint` (`:#:`).

## Changed

- Use Hierarchy Builder to define the ordType interface.

- `ordMixin` has been replaced with `hasOrd`

- Use maximally implicit arguments for the type arguments of `getm`, `setm`,
  `repm`, `updm`, `mapim`, `mapm`, `filterm`, `remm`, `mkfmap`, `mkfmapf`,
  `mkfmapfp` and `domm`.

## Deprecated

- `InjOrdMixin`, `PcanOrdMixin` and `CanOrdMixin` have been deprecated in favor
  of `InjHasOrd`, `PcanHasOrd` and `CanHasOrd`.

- The `[ordMixin of T by <:]` notation has been deprecated in favor of `[Ord of
  T by <:]`.

- The `[derive [<flag>] ordMixin for T]` notations have been deprecated in favor
  of `[derive [<flag>] hasOrd for T]`.

## Fixed

- Make implicit arguments for `bigcupP` valid globally.

# 0.3.1. (2021/10/28)

## Added

- Support for SSReflect 1.13.0

## Removed

- Support for SSReflect 1.11.0 and earlier.

# 0.3.0 (2021/08/31)

## Added

- Type of finitely supported functions `ffun`.

- A Deriving instance for `ordType` (cf. https://github.com/arthuraa/deriving).

### Functions

`splits` and `splitm`, for extracting an element of a set or map.

`filter_map`

`pimfset`, an image operator for partial functions.

### Lemmas

`sizesD`, about the size of a set difference

`filterm0`, `remmI`, `setm_rem`, `filterm_set`, `domm_mkfmap'`, `val_domm`,
`fmvalK`, `mkfmapK`, `getm_nth`, `eq_setm`, `sizeES`, `dommES`, `filter_mapE`,
`domm_filter_map`, `mapimK`, `mapim_map`, `eq_mapm`, `mapm_comp`,
`mapm_mkfmapf`, `fset1_inj`, `fsetUDr`, `val_fset_filter`, `fset_filter_subset`,
`in_pimfset`, `bigcupS`, `in_bigcup`, `bigcup1_cond`, `bigcup1`.

## Changed

- Implicit arguments for `fdisjointP`, `fsetIidPl`, `fsetIidPr`, `fsetUidPl`,
  `fsetUidPr`, `fsetDidPl`, `bigcupP`.

- Implement `fperm` using `ffun`.

- Generalize `supp` and `mem_suppN` to `ffun`.

## Removed

- Support for Coq 8.10

# 0.2.2 (2020/08/13)

- Fix compatibility issues with Coq 8.12 and Ssreflect 1.11.

# 0.2.1 (2019/10/26)

- Fix compatibility issue with Coq 8.10

# 0.2.0 (2019/08/21)

- Separate phantom argument from the definitions of `fset`, `fmap` and `fperm`.

- Add `ordType` instances for `mathcomp.choice.GenTree.tree` and `tuple`.

- Add more implicit arguments for `fsubsetP`, `fset2P`, `imfsetP`, `dommP`,
  `dommPn`, `codommP` and `codommPn`.

- Miscellaneous lemmas for finite sets.

- Version of `mapm` that allows modifying the domain of a map.

# 0.1.0 (2018/04/26)

Initial release
