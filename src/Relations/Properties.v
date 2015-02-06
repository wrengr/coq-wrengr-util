(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Properties of relations. *)
Require Import Relations.Core.


Definition Confluent {A:Type} (R : relation A) := 
    forall a b b', R a b -> R a  b' ->
    exists c,      R b c /\ R b' c.
Hint Unfold      Confluent.
Hint Transparent Confluent.


Definition WeakChurchRosser {A:Type} (R : relation A) :=
    forall a b b', R   a b -> R   a  b' ->
    exists c,      R^* b c /\ R^* b' c.
Hint Unfold      WeakChurchRosser.
Hint Transparent WeakChurchRosser.


Definition ChurchRosser {A:Type} (R : relation A) :=
    forall a b b', R^* a b -> R^* a  b' ->
    exists c,      R^* b c /\ R^* b' c.
Hint Unfold      ChurchRosser.
Hint Transparent ChurchRosser.


(* BUG: no no no...
Definition StronglyNormalizing {A:Type} (R : relation A) :=
    forall t t', (R costar) t t' -> R^* t t'.
Hint Unfold StronglyNormalizing.
Hint Transparent StronglyNormalizing.


(* I'm not going to bother proving Newman's lemma *)
Axiom Newman's_lemma : forall {A:Type} (R : relation A),
    WeakChurchRosser R -> StronglyNormalizing R -> ChurchRosser R.
*)


(*
(* According to Chargueraud... *)
Definition church_rosser {A:Type} (R : relation A) :=
  forall t1 t2, R^= t1 t2 -> 
  exists t, R^* t1 t /\ R^* t2 t.

Definition subject_reduction (R : relation Term) :=
  forall E t t' T,
  R t t' -> 
  typing E t  T -> 
  typing E t' T.
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
