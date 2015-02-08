(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions to [Coq.Sets.Multiset] *)

(* cf <http://coq.inria.fr/stdlib/Coq.Sets.Multiset.html> *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Coq.Sets.Multiset.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** The multiset difference operator. *)
Definition mdiff {A:Type} (m1 m2 : multiset A) : multiset A :=
    Bag (fun a:A => multiplicity m1 a - multiplicity m2 a).

Delimit Scope multiset_scope with multiset.
Bind Scope multiset_scope with multiset.
Open Scope multiset_scope.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Notations for common multiset relationships. *)

(** Subset for multisets. N.B., _not_ submultiset! *)
Notation "xs \c ys" :=
    (forall a:_, IsSucc (multiplicity xs a) -> IsSucc (multiplicity ys a))
    (at level 38):multiset_scope.

(** Submultiset. *)
Notation "xs [<=] ys" :=
    (forall a:_, multiplicity xs a <= multiplicity ys a)
    (at level 38):multiset_scope.

(** Strict submultiset. *)
Notation "xs [<] ys" :=
    (forall a:_, multiplicity xs a < multiplicity ys a)
    (at level 38):multiset_scope.

(** Extensional syntactic identity. *)
Notation "xs [=] ys" :=
    (forall a:_, multiplicity xs a = multiplicity ys a)
    (at level 38):multiset_scope.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Transitivity for common multiset relationships. *)

Lemma msubset_trans
    : forall {A : Type} {xs ys zs : multiset A}
    , xs \c ys -> ys \c zs -> xs \c zs.
Proof. intros; auto. Qed.


Lemma submultiset_trans
    : forall {A : Type} {xs ys zs : multiset A}
    , xs [<=] ys -> ys [<=] zs -> xs [<=] zs.
Proof. intros; apply (le_trans _ (multiplicity ys a) _); auto. Qed.
(* BUG: [le] isn't setoid!! *)


Lemma strict_submultiset_trans
    : forall {A : Type} {xs ys zs : multiset A}
    , xs [<] ys -> ys [<] zs -> xs [<] zs.
Proof. intros; apply (lt_trans _ (multiplicity ys a) _); auto. Qed.
(* BUG: [le] isn't setoid!! *)


Lemma eq_multiset_trans
    : forall {A : Type} {xs ys zs : multiset A}
    , xs [=] ys -> ys [=] zs -> xs [=] zs.
Proof. intros; transitivity (multiplicity ys a); auto. Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
