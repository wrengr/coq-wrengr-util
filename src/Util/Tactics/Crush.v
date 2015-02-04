(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [crush] tactic.

This implementation is inspired by
    <http://adam.chlipala.net/cpdt/repo/file/ded318830bb0/src/CpdtTactics.v>
which is licensed under
    <http://creativecommons.org/licenses/by-nc-nd/3.0/>
and by
    <http://adam.chlipala.net/cpdt/html/Match.html>
    
See also section 10.8 of
    <http://flint.cs.yale.edu/cs430/coq/doc/Reference-Manual012.html>
and also
    <http://www.cl.cam.ac.uk/~pes20/CompCertTSO/doc/html/Libtactics.html>

Regarding JMeq and ways around needing it, see
    <http://osdir.com/ml/science.mathematics.logic.coq.club/2008-07/msg00069.html>

For stronger inversion principles, see
    <http://pages.cs.wisc.edu/~mulhern/Mul2010/slides.pdf>
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
