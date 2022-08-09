# Extensional Structures

[![arthuraa](https://circleci.com/gh/arthuraa/extructures.svg?style=shield)](https://circleci.com/gh/arthuraa/extructures)

This package provides Coq data structures that support extensional reasoning,
for which the notion of equality coincides with exhibiting the same _observable
behavior_: sets are equal when they contain the same elements; functions are
equal when that produce the same outputs; etc.

## Features

*Axiom independent* ─ Unlike the case of built-in functions and predicates,
these extensionality principles do not rely on any axioms beyond Coq's theory.

*Executable* ─ Data structures are implemented as ordered lists and behave
reasonably when extracted (as long as you do not have high expectations for
performance).

*Compatible with Mathematical Components* ─ The design is inspired by
[SSReflect][1] and the [Mathematical Components libraries][2], and attempts to
follow their style and philosophy.

## Usage

Currently, four data structures are supported:

- `{fset T}`, the type of finite sets of elements of `T` (defined in `fset`)

- `{fmap T -> S}`, the type of maps, or partial functions from `T` to `S` with
  finite domain (defined in `fmap`)

- `ffun def`, the type of finitely supported functions, which agree with `def :
  T -> S` on all but finitely many inputs

- `{fperm T}`, the type of finitely supported permutations on `T`; that is,
  functions `f` from `T` to `T` that have a right and left inverse and such that
  `f x != x` only for finitely many values of `x` (defined in `fperm`)

Here, `T` ranges over instances of `ordType` (defined in `ord`), which are types
endowed with a decidable total order relation.  (For `ffun def`, the codomain of
`def` must be an `eqType` as well.) Basic data types such as `nat`, `bool`,
`option`, products, and sums are all pre-declared as instances of `ordType`.
Instances for other types can be transported via subtyping, injective functions,
etc., as for other MathComp classes, or derived automatically using
[Deriving][7].

The function-like structures coerce into Coq functions, allowing us to write
`f x` to retrieve the value of the map `f` at `x`.  Similarly, sets coerce to
SSReflect collective predicates, allowing us to write `x \in A` to express that
`x` belongs to the set `A`.

Extensional reasoning is provided by the following lemmas:

    eq_fset  : forall T   (A B : {fset T}),      A =i B <-> A = B
    eq_fmap  : forall T S (f g : {fmap T -> S}), f =1 g <-> f = g
    eq_ffun  : forall T S (def : T -> S) (f g : ffun def),
                                                 f =1 g <-> f = g
    eq_fperm : forall T   (f g : {fperm T}),     f =1 g <-> f = g

Documentation for the libraries is currently scarce, but will be progressively
added as comments in the headers of the files.  Once the package is installed,
it can be required using the `extructures` qualifier.

    From extructures Require Import ord fset.

Check the `tests/` directory for detailed examples.

## Installation

The easiest way to install the package is through the [OPAM Coq archive][3].
After installing OPAM and adding the Coq archive, run:

    opam install coq-extructures

Alternatively, you can compile the package by hand.  You'll need the following
dependencies:

- Coq v8.11 -- v8.15
- [Ssreflect][2] v1.12 -- v1.15 (`coq-mathcomp-ssreflect` on OPAM).
- `deriving` v0.1 (https://github.com/arthuraa/deriving)

To compile the package, simply run

    make

After compilation, you can install the package by running

    make install

## Alternatives

Other packages with similar goals are available out there.

- Mathematical Components also includes implementations of sets and functions
  with extensional equality, but they only work for finite types.  In contrast,
  the above definitions work with infinite types as well.

- Cyril Cohen's `finmap` library, [available here][4].

- Pierre-Yves Strub's library, [available here][5].

- Christian Doczkal's library, [available here][6].

  [1]: https://coq.inria.fr/distrib/current/refman/ssreflect.html
  [2]: https://github.com/math-comp/math-comp
  [3]: https://github.com/coq/opam-coq-archive
  [4]: https://github.com/math-comp/finmap
  [5]: https://github.com/strub/ssrmisc/blob/master/fset.v
  [6]: https://www.ps.uni-saarland.de/formalizations/fset/html/libs.fset.html
  [7]: https://github.com/arthuraa/deriving
