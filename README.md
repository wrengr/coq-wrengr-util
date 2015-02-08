<!---
[![Build Status](https://api.travis-ci.org/HoTT/HoTT.png?branch=master)](https://travis-ci.org/HoTT/HoTT)
-->

## DESCRIPTION

This library provides a collection of utility tactics and lemmas.
There's nothing particularly special going on here, but they're
pretty helpful and often used in my code.

#### `./src/Tactics`

The `Tactics.Core` module contains some very simple tactics that I
use extremely often, such as introducing a variable just to call
destruct/inversion/induction on it, or the `insist` tactic which
is like `exact` except that it will use `congruence` to prove that
the hypothesis you insist on can be rewritten into the current goal.

The `Tactics.Destroy` module defines the `destruct_if` tactic which
will look for if-then-else terms in the goal, destruct their
scrutinee, and then do some cleanup which is often helpful for
discharging the subgoals.

The `Tactics.ExFalso` module defines the `ex_falso` tactic which
seeks out contradictions and uses them to discharge the current
goal.

The `Tactics.Fequal` module defines the `fequal` tactic, which is
an improved version of the built-in `f_equal` tactic.

The `Tactics.Introv` module defines the `introv` tactic described
in the [UseTactics][] chapter of _Software Foundations_ and implemented
in [TLC][]. This is an introduction tactic that lets you get away
with only naming the non-dependent hypotheses. Any preceeding
dependent hypotheses are introduced with their default names.

The `Tactics.Jauto` module defines some improvements on `auto` based
on the [UseAuto][] chapter of _Software Foundations_ and implemented
in [TLC][]. These tactics are still pretty experimental in my
opinion, and I don't use them very much, but they can be nice to
see or to have on hand. The `iauto` tactic just is a shorthand for
`intuition eauto`. The `jauto` tactic (Chargueraud's `jauto_fast`)
is like `iauto` except that it handles existentials and ignores
disjunctions. The `jjauto` tactic is my highly experimental enhancement
of `jauto`.

[UseTactics]: http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html
[UseAuto]: http://www.cis.upenn.edu/~bcpierce/sf/UseAuto.html
[TLC]: http://www.chargueraud.org/softs/tlc


#### `./src/CoqExtras`

These modules contain various lemmas missing from the standard
library. Mostly these are uninteresting: discrimination, dependent
case/inversion with equality, trivial arithmetic, etc. However, one
of the modules is in fact interesting...

The `CoqExtras.ListSet` module contains a large swath of tools for
working with ListSets. First we prove a bunch of intro/elim lemmas
which are oddly missing from the standard library. Then we define
some hint databases for use with `auto`, so that we can automate
away needing to remember the names for all the different lemmas
about ListSets. In the future, I may add an `intuition`-like tactic
for more efficiently proving all the things that rely on intuitionistic
properties of finite sets.


#### `./src/Relations`

The `Relations.Core` module defines various closure operators on
binary relations. These are given as Parametric Relations so you
can use the `reflexivity`, `symmetry`, and `transitivity` tactics
as appropriate.

The `Relations.Properties` module defines some properties of relations
we'd often like to prove; e.g., various confluence-like properties.

The `Relations.Temporal` module defines some of the modalities of
temporal logic (e.g., the property that some predicate holds
eventually, forever, or until some other property holds). The exact
implementations are a bit experiemental and may change in the future,
but they are usable in their present state.


----------------------------------------------------------------
## INSTALLATION

Installation should be pretty straightforward. All you have to do
is the standard incantation:

    make
    sudo make install

If time is of the essence, you can do `make compile` instead of
`make`. Doing so will only compile the code, instead of also
generating the documentation.


## USAGE

Honestly, I'm not entirely sure how Coq works with regards to linking
up against installed libraries. For me, after doing `make install`
things seem to just work. But that's creepy since I don't need to
tell my other code that it explicitly depends on this library; which
seems like an error-prone way to handle libraries. But then, Coq's
tooling has always been rough around the edges.


## CONTRIBUTING

Contributions to the library are very welcome! For style guidelines
and further information, see the file `STYLE.md`.


## LICENSING

The library is released under the permissive BSD 3-clause license,
see the file `LICENSE` for further information. In brief, this means
you can do whatever you like with it, as long as you preserve the
Copyright messages. And of course, no warranty!
