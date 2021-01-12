# Extensional Structures

[![arthuraa](https://circleci.com/gh/arthuraa/extructures.svg?style=shield)](https://circleci.com/gh/arthuraa/extructures/tree/v0.2)

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

Currently, three data structures are supported:

- `{fset T}`, the type of finite sets of elements of `T` (defined in `fset`);

- `{fmap T -> S}`, the type of maps, or partial functions from `T` to `S` with
  finite domain (defined in `fmap`); and

- `{fperm T}`, the type of finitely supported permutations on `T`; that is,
  functions `f` from `T` to `T` that have a right and left inverse and such that
  `f x != x` only for finitely many values of `x` (defined in `fperm`).

Here, `T` ranges over instances of `ordType` (defined in `ord`), which are types
endowed with a decidable total order relation.  Basic data types such as `nat`,
`bool`, `option`, products, and sums are all pre-declared as instances of
`ordType`, and instances for other types can be derived from old ones (following
the design patterns of Mathematical Components).

The function-like structures coerce into Coq functions, allowing us to write
`f x` to retrieve the value of the map `f` at `x`.  Similarly, sets coerce to
SSReflect collective predicates, allowing us to write `x \in A` to express that
`x` belongs to the set `A`.

Extensional reasoning is provided by the following lemmas:

    eq_fset  : forall T   (A B : {fset T}),      A =i B <-> A = B
    eq_fmap  : forall T S (f g : {fmap T -> S}), f =1 g <-> f = g
    eq_fperm : forall T   (f g : {fperm T}),     f =1 g <-> f = g

Documentation for the libraries is currently scarce, but will be progressively
added as comments in the headers of the files.  Once the package is installed,
it can be required using the `extructures` qualifier.

    From extructures Require Import ord fset.

## Installation

The easiest way to install the package is through the [OPAM Coq archive][3].
After installing OPAM and adding the Coq archive, run:

    opam install coq-extructures

Alternatively, you can compile the package by hand.  You'll need the following
dependencies:

- Coq versions 8.10, 8.11, or 8.12
- [Ssreflect][2] versions 1.10, 1.11 or 1.12 (`coq-mathcomp-ssreflect` on OPAM).

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
