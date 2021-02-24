# Unreleased

## Added

- Type of finitely supported functions `ffun`.

## Changed

- Implicit arguments for `fsetIidPl`, `fsetIidPr`, `fsetUidPl`, `fsetUidPr`,
  `fsetDidPl`.

- Moved `mem_suppN` to `ffun`.

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
