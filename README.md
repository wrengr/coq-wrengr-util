<!---
[![Build Status](https://api.travis-ci.org/HoTT/HoTT.png?branch=master)](https://travis-ci.org/HoTT/HoTT)
-->

This library provides a collection of utility tactics and lemmas.
There's nothing special going on here, but these are utilities I
use often in my other Coq code.

## INSTALLATION

Installation details are explained in the file `INSTALL.txt`.

## USAGE

It is possible to use the HoTT library directly on the command line
with the `hoqtop` script, but who does that?

It is probably better to use [Proof
General](http://proofgeneral.inf.ed.ac.uk) and
[Emacs](http://www.gnu.org/software/emacs/). When Proof General
asks you where to find the `coqtop` executable, just point it to
the `hoqtop` script. If Emacs runs a `coqtop` without asking, you
should probably customize set the variable `proof-prog-name-ask`
to `nil` (in Emacs type `C-h v proof-prog-name-ask RET` to see what
this is about).

At the moment there is no `hoqide` equivalent of `coqide`, but
getting one is high on our to-do list.

## CONTRIBUTING

Contributions to the HoTT library are very welcome!  For style
guidelines and further information, see the file `STYLE.md`.

## LICENSING

The library is released under the permissive BSD 3-clause license,
see the file `LICENSE` for further information. In brief, this means
you can do whatever you like with it, as long as you preserve the
Copyright messages. And of course, no warranty!
