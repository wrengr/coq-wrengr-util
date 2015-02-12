(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Normalization properties for reduction relations. *)
Require Import Relations.Core.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** A term is reducible if there's some term it can reduce to.

    We take [Reducible] as the primitive, rather than [Irreducible],
    since it is better behaved in the intuitionistic setting. Many
    of lemmas require that this proposition satisfy LEM for all
    [a]. *)
Definition Reducible {A:Type} (R : relation A) a :=
    exists b, R a b.
Hint Unfold Reducible.
Hint Transparent Reducible.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Definition of weakly normalizing *)

(** *** [b] is a normal form of [a]. *)
Definition NormalizesTo {A:Type} (R : relation A) a b :=
    R^* a b /\ ~Reducible R b.
Hint Unfold      NormalizesTo.
Hint Transparent NormalizesTo.


(** *** [a] has some normal form. *)
Definition Normalizes {A:Type} (R : relation A) a :=
    exists b, NormalizesTo R a b.
Hint Unfold      Normalizes.
Hint Transparent Normalizes.


(** *** Every term has some normal form.

    Some sources simply call this "normalizing", particularly when
    they call [StronglyNormalizing] "terminating". *)
Definition WeaklyNormalizing {A:Type} (R : relation A) :=
    forall a, Normalizes R a.
Hint Unfold      WeaklyNormalizing.
Hint Transparent WeaklyNormalizing.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Definition of strongly normalizing *)


(** *** Every reduction sequence from [a] is finite.

    This clever definition of [Terminates] is essentially due to
    Huet, but can be traced back to Gentzen. This is the key trick
    that makes induction on the _length_ of reduction derivations
    so clean and easy.
    
    Compare this to [Acc] in [Coq.Init.Wf]. We have that [Terminates
    R] is essentially the same thing as [Acc (converse R)]. *)

Inductive Terminates {A:Type} (R : relation A) (a:A) : Prop :=
    terminates : (forall b, R a b -> Terminates R b) -> Terminates R a.


(** *** Every term terminates.

    Some sources call this "terminating", particularly when they
    call [WeaklyNormalizing] "normalizing". In the context of term
    rewriting systems, it's also called "Noetherian".
    
    Compare this to [well_founded] in [Coq.Init.Wf]. We have that
    [StronglyNormalizing R] is essentially the same thing as
    [well_founded (converse R)]. *)
Definition StronglyNormalizing {A:Type} (R : relation A) :=
    forall a, Terminates R a.
Hint Unfold      StronglyNormalizing.
Hint Transparent StronglyNormalizing.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Strong normalization implies weak normalization *)

Lemma Terminates_implies_Normalizes
    : forall {A:Type} (R : relation A),
    (forall a, Reducible R a \/ ~Reducible R a) ->
    forall {a}, Terminates R a -> Normalizes R a.
(*
(* This proof also works, provided the two lemmas are in scope. *)
Proof
  intros.
  apply NormalizesIn_to_Normalizes'.
  apply Terminates_is_finite; assumption.
Qed.
*)
Proof.
  intros A R Reducible_lem a Ta.
  induction Ta as [a _ N].
  destruct (Reducible_lem a) as [[b Rab] | ?].
    destruct (N b Rab) as [c [Rbc Nc]].
    exists c; split; [transitivity b; [constructor|] |]; assumption.
    
    exists a; split; [reflexivity | assumption].
Qed.


Theorem SN_implies_WN
    : forall {A:Type} (R : relation A),
    (forall a, Reducible R a \/ ~Reducible R a) ->
    StronglyNormalizing R -> WeaklyNormalizing R.
Proof.
    intros A R Reducible_lem SN a.
    apply Terminates_implies_Normalizes; auto.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Finiteness of reduction sequences

    There's nothing particularly interesting going on here. We just
    do this for the sake of showing that it can be done. *)

(** ** The term [a] can normalize in exactly [n] steps. *)
Fixpoint NormalizesIn {A:Type} (R : relation A) n a :=
    match n with
    | 0    => ~Reducible R a
    | S n' => exists b, R a b /\ NormalizesIn R n' b
    end.


(** *)
Lemma Normalizes_to_NormalizesIn
    : forall {A:Type} (R : relation A) (a:A),
    Normalizes R a -> exists n, NormalizesIn R n a.
Proof.
  intros A R a [b [Rab H]].
  apply RTC_optimize in Rab.
  induction Rab.
    exists 0; assumption.
    
    destruct (IHRab H) as [n NInb].
    exists (S n); exists b; split; assumption.
Qed.


Lemma NormalizesIn_to_Normalizes
    : forall {A:Type} (R : relation A) n a,
    NormalizesIn R n a -> Normalizes R a.
Proof.
  intros A R n; induction n; simpl.
    intros a Ha; exists a; split; [reflexivity | assumption].
    
    intros a [b [Rab NInb]].
    destruct (IHn b NInb) as [c [Rbc Hc]].
    exists c; split; [ transitivity b; [constructor|] |]; assumption.
Qed.


Corollary NormalizesIn_to_Normalizes'
    : forall{A:Type} (R : relation A) (a:A),
    (exists n, NormalizesIn R n a) -> Normalizes R a.
Proof.
  intros A R a [n NIna].
  eapply NormalizesIn_to_Normalizes.
  eassumption.
Qed.


Theorem Normalizes_iff_NormalizesIn
    : forall {A:Type} (R : relation A) (a:A),
    Normalizes R a <-> (exists n, NormalizesIn R n a).
Proof.
  intros A R a.
  split;
    [ apply Normalizes_to_NormalizesIn
    | apply NormalizesIn_to_Normalizes'
    ].
Qed.


(** *)
Theorem Terminates_is_finite
    : forall {A:Type} (R : relation A),
    (forall a, Reducible R a \/ ~Reducible R a) ->
    forall a, Terminates R a -> exists n, NormalizesIn R n a.
(*
(* This proof also works, provided the two lemmas are in scope. *)
Proof.
  intros.
  apply Normalizes_to_NormalizesIn.
  apply Terminates_implies_Normalizes; assumption.
Qed.
*)
Proof.
  intros A R Reducible_lem a Ta.
  induction Ta as [a _ NI].
  destruct (Reducible_lem a) as [[b Rab] | ?].
    destruct (NI b Rab) as [n NInb].
    exists (S n); exists b; split; assumption.
    
    exists 0; assumption.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
