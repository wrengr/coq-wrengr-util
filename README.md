<!---
[![Build Status](https://api.travis-ci.org/HoTT/HoTT.png?branch=master)](https://travis-ci.org/HoTT/HoTT)
-->

This library provides a collection of utility tactics and lemmas.
There's nothing particularly special going on here, but they're
pretty helpful and often used in my code.

## INSTALLATION

Installation should be pretty straightforward. All you have to do
is the standard incantation:

    make
    sudo make install

If time is of the essence, you can do `make compile` instead of
`make`. Doing so will only compile the code, instead of also
generating the documentation.

## USAGE

Honestly, I'm not sure how to link against the library after it's
installed. Installation will put things in "`coqtop
-where`/user-contrib/WrengrUtil", but who knows what happens after
that?

## CONTRIBUTING

Contributions to the library are very welcome! For style guidelines
and further information, see the file `STYLE.md`.

## LICENSING

The library is released under the permissive BSD 3-clause license,
see the file `LICENSE` for further information. In brief, this means
you can do whatever you like with it, as long as you preserve the
Copyright messages. And of course, no warranty!
