(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions to [Coq.Lists.ListSet]

This module provides a handful of lemmas for ListSets which aren't
included in the standard library. More particularly, we provide the
[listset] and [listset_star] hint databases for teaching [auto] how
to reason about ListSets. The [listset] database covers all the
syntax-directed lemmas, and so is very lightweight to use. The
[listset_star] database adds a few extra tactics for handling certain
forms of non-syntax-directed reasoning, however this makes it much
slower to use. *)

(* cf <http://coq.inria.fr/stdlib/Coq.Lists.ListSet.html>

Also see the discussion at:
<http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/1663> *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Coq.Lists.ListSet.
Require Export Tactics.Core.
Require Import Tactics.Destroy.
Require Import Tactics.Introv.
Require Import Tactics.Jauto.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Theorems *)

(** Introduction rule for [set_remove]. *)
Lemma set_remove_intro : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (E   : x <> y)
    (xs  : set A)
    (I   : set_In x xs)
    , set_In x (set_remove eq_dec y xs).
Proof.
  induction xs as [ | x0 xs0 IHxs0 ].
    identity. (*absurd*)
    
    simpl; destruct_if; intro H; destruct H;
        [ congruence (*absurd*)
        | 
        | left
        | right; apply IHxs0
        ]; assumption.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* TODO:
(** Negated introduction rule for [set_remove]. *)
Lemma set_remove_complete1 : forall
    {A   : Set}
    {eq_dec : forall x y : A, {x = y} + {x <> y}}
    {x  : A}
    (xs : set A)
    , ~ set_In x (set_remove eq_dec x xs).
Proof.
  induction xs as [ | x0 xs0 IHxs0 ]; simpl.
    identity. (*absurd*)
    
    destruct_if; simpl.
      (* BUG: goal [~ set_In x (set_remove eq_dec x xs0) |- ~ set_In x xs0]
      [set_remove] only removes the first instance of [y]!!! *)
      
      Focus 2.
      intro_destruct; [congruence | apply IHxs0; assumption].
Abort.
*)

(** The strong/classical contrapositive of [set_remove_intro]. *)
Lemma set_remove_complete2 : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (xs  : set A)
    (I  : set_In x xs)
    (H  : ~ set_In x (set_remove eq_dec y xs))
    , x = y.
Proof.
  induction xs as [| x0 xs0 IHxs0]; simpl; intros.
    contradiction.
    destruct_if in H; simpl in *.
      destruct I.
        congruence.
        contradiction.
      destruct I.
        contradict H; auto.
        apply IHxs0; auto.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Elimination rule for [set_remove]. *)
Lemma set_remove_elim : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (xs  : set A)
    (I   : set_In x (set_remove eq_dec y xs))
    , set_In x xs.
Proof.
  induction xs as [ | x0 xs0 IHxs0 ];
    [ identity (*absurd*)
    | simpl; destruct_if; intro H;
      [ right
      | destruct H; [left | right; apply IHxs0]
      ]; assumption
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* TODO: intro rules via subset relation (probably needs to be extern). *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Discrimination based on set membership. *)
Lemma needs_a_good_name : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (xs  : set A)
    (Ix  : set_In x xs)
    (Iy  : ~ set_In y xs)
    , x <> y.
Proof.
  induction xs as [ | x0 xs0 IHxs0 ];
    [ identity (*absurd*)
    | simpl; destruct (eq_dec x x0); destruct (eq_dec y x0); congruence
    ].
    (* BUG: why doesn't [destruct_if] work here? *)
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Elimination rule for [set_add]. *)
Lemma set_add_elim : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (ys  : set A)
    (I   : set_In x (set_add eq_dec y ys))
    , x=y \/ set_In x ys.
Proof.
  intros; induction ys; simpl in *;
    [ destruct I
    | destruct_if in I; destruct I; auto; destruct (IHys H)
    ]; auto.
Qed.


(** The disjunctive syllogism applied to [set_add_elim]. *)
Corollary set_add_elim1 : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (ys  : set A)
    (I   : set_In x (set_add eq_dec y ys))
    (H   : ~set_In x ys)
    , x=y.
Proof.
  intros; destruct (set_add_elim eq_dec x y ys I);
    [assumption | contradiction].
Qed.


(** The disjunctive syllogism applied to [set_add_elim]. *)
Corollary set_add_elim2 : forall
    {A   : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x y : A)
    (ys  : set A)
    (N   : x<>y)
    (I   : set_In x (set_add eq_dec y ys))
    , set_In x ys.
Proof.
  intros; destruct (set_add_elim eq_dec x y ys I);
    [contradiction | assumption].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** *)
Lemma set_not_union_elim1 : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : ~ set_In x (set_union eq_dec xs ys))
    , ~set_In x xs.
Proof.
  unfold not; intros; induction xs; auto; destruct H;
    [ apply I; apply set_union_intro1; left; assumption
    | apply IHxs; [ intro; apply I; apply set_union_intro1; right |]; exact H
    ].
Qed.


(** *)
Lemma set_not_union_elim2 : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : ~ set_In x (set_union eq_dec xs ys))
    , ~set_In x ys.
Proof.
  unfold not; intros; induction ys; auto; destruct H;
    [ apply I; apply set_union_intro2; left; assumption
    | apply IHys; [ intro; apply I; apply set_union_intro2; right |]; exact H
    ].
Qed.


(** *)
Lemma set_not_diff_elim1 : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : ~ set_In x (set_diff eq_dec xs ys))
    , ~set_In x xs \/ set_In x ys.
Proof.
  intros; induction xs; auto; destruct (eq_dec x a);
    [ subst; destruct (set_In_dec eq_dec a ys)
    ; [ right | left; intro; apply I; apply set_diff_intro ]
    ; assumption
    | unfold not in *; simpl in *; destruct_if in I;
      [| assert (~set_In x xs \/ set_In x ys)
          by (apply IHxs; intro; apply I; apply set_add_intro1; exact H)
      ]; intuition
    ].
Qed.


(** The strong/classical contrapositive of [set_diff_intro]; aka
    disjunctive syllogism applied to [set_not_diff_elim1]. *)
Lemma set_not_diff_elim2 : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : set_In x xs)
    (N : ~ set_In x (set_diff eq_dec xs ys))
    , set_In x ys.
Proof.
  intros; induction xs;
    [ contradiction
    | simpl in I; destruct I;
      [ simpl in N; destruct (set_In_dec eq_dec a ys);
        [ subst
        | contradict N; rewrite set_mem_complete2; [ apply set_add_intro |]
        ]
      | apply IHxs;
        [| intro
        ;  apply N
        ;  simpl; destruct (set_mem eq_dec a ys)
        ;  [| apply set_add_intro1 ]
        ]
      ]; auto
    ].
Qed.


Lemma set_diff_monotone : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (xs xs' ys : set A)
    (I : forall x, set_In x xs -> set_In x xs')
    (x : A)
    (I : set_In x (set_diff eq_dec xs ys))
    , set_In x (set_diff eq_dec xs' ys).
Proof.
  intros; induction xs; simpl in *.
    contradiction.
    
    (* N.B., Can't use [destruct (set_mem eq_dec a ys)], because
        it yields no evidence! *)
    destruct (set_In_dec eq_dec a ys) as [s|n].
      rewrite (set_mem_correct2 eq_dec a ys s) in I0.
      apply IHxs; auto.
      
      rewrite (set_mem_complete2 eq_dec a ys n) in I0.
      destruct (set_add_elim eq_dec _ _ _ I0).
        subst; apply set_diff_intro; auto. (* the evidence is needed here. *)
        
        apply IHxs; auto.
Qed.


Lemma set_diff_antitone : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (xs ys ys' : set A)
    (I : forall x, set_In x ys -> set_In x ys')
    (x : A)
    (I : set_In x (set_diff eq_dec xs ys'))
    , set_In x (set_diff eq_dec xs ys).
Proof.
  intros; induction xs.
    contradiction.
    
    simpl in *; destruct (set_In_dec eq_dec a ys) as [s|n].
      rewrite (set_mem_correct2 eq_dec a ys s).
      rewrite (set_mem_correct2 eq_dec a ys' (I a s)) in I0.
      auto.
      
      rewrite (set_mem_complete2 eq_dec a ys n).
      apply set_add_intro.
      destruct (set_mem eq_dec a ys');
        [| destruct (set_add_elim eq_dec _ _ _ I0) ]; auto.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Lemma set_union_diff_intro : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : set_In x (set_union eq_dec xs ys))
    , set_In x (set_union eq_dec xs (set_diff eq_dec ys xs)).
Proof.
  intros; destruct (set_union_elim eq_dec x xs ys I);
    [ apply set_union_intro1
    | destruct (set_In_dec eq_dec x xs);
      [ apply set_union_intro1
      | apply set_union_intro2
      ; apply set_diff_intro
      ]
    ]; assumption.
Qed.


Lemma set_union_diff_elim : forall
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A)
    (xs ys : set A)
    (I : set_In x (set_union eq_dec xs (set_diff eq_dec ys xs)))
    , set_In x (set_union eq_dec xs ys).
Proof.
  intros; induction ys; simpl in *;
    [ exact I
    | destruct_if in I;
      [ apply set_add_intro1; auto
      | induction xs; simpl in *; auto;
        [ destruct (set_union_elim eq_dec x _ _ I);
          [ contradiction
          | destruct (set_add_elim eq_dec x a _ H);
            [ apply set_add_intro2; assumption
            | apply set_add_intro1
            ; apply set_union_intro2
            ; exact (set_diff_elim1 eq_dec x ys _ H0) ] ]
        | destruct_if in E
        ; destruct (set_union_elim eq_dec x _ _ I);
          [ apply set_add_intro1
          ; apply set_union_intro1
          ; assumption
          | destruct (set_add_elim eq_dec x a _ H);
            [ apply set_add_intro2; assumption
            | apply set_add_intro1
            ; apply set_union_intro2
            ; exact (set_diff_elim1 eq_dec x ys _ H0) ] ] ] ] ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Tactics *)
(* BUG: these are being listed as for "any goal" instead of their specific ones! (excepting ones for and, eq, & or) *)

Create HintDb listset      discriminated. (* For light tactics. *)
Create HintDb listset_star discriminated. (* For the big guns. *)

(** Syntax-directed lemmata for [set_In] *)
Hint Resolve
    @set_add_intro1
    @set_add_intro2
    @set_remove_intro
    @set_union_intro1
    @set_union_intro2
    @set_inter_intro
    @set_diff_intro
    :listset.

(** Non-syntax-directed lemmata for [set_In]... a bad idea? *)
(* BUG: We get warnings that these three are [eauto]-only. Why are they? *)
Hint Resolve
    @set_mem_correct1
    @set_union_emptyL
    @set_union_emptyR
    :listset_star.

(* TODO: do these succeed in avoiding evars and exponential explosion? *)
(* BUG: they may avoid them, but they cannot fail and backtrack!

Lemma TestCase_set_add_elim2 : forall
    {A:Type} (Aeq_dec : forall x y : A, {x = y} + {x <> y})
    (a b c : A) (xs : set A) (E : a <> b)
    (H0 : set_In a (set_add Aeq_dec b xs))
    (H1 : set_In a (set_add Aeq_dec c xs)) (* Note the order of H0 vs H1! *)
    , set_In a xs.
*)
Hint Extern 3 (set_In ?x ?xs) =>
    match goal with
    | I : set_In x (set_remove ?eq_dec ?y xs) |- _ =>
        apply (@set_remove_elim _ eq_dec x y xs I)
    end :listset_star.

Hint Extern 2 (set_In ?x ?xs) =>
    match goal with
    | I : set_In x (set_add ?eq_dec ?y xs) |- _ =>
        refine (@set_add_elim2 _ eq_dec x y xs _ I); congruence
    end :listset_star.

Hint Extern 7 (set_In ?x ?xs) =>
    match goal with
    (* N.B., we must eta over [I]. And must [eapply] to infer [eq_dec] *)
    | N : x<>?y |- _ =>
        eapply (fun I => @set_add_elim2 _ _ x y xs N I)
    | N : ?y<>x |- _ =>
        eapply (fun I => @set_add_elim2 _ _ x y xs (sym_eq N) I)
    end :listset_star.

Hint Extern 3 (set_In ?x ?xs) =>
    match goal with
    | I : set_In x (set_inter ?eq_dec xs ?ys) |- _
        => apply (@set_inter_elim1 _ eq_dec x xs ys I)
    | I : set_In x (set_inter ?eq_dec ?ys xs) |- _
        => apply (@set_inter_elim2 _ eq_dec x ys xs I)
    end :listset_star.

Hint Extern 3 (set_In ?x ?xs) =>
    match goal with
    | I : set_In x (set_diff ?eq_dec xs ?ys)  |- _ =>
        apply (@set_diff_elim1 _ eq_dec x xs ys I)
    end :listset_star.

(** Syntax-directed lemmata for [~ set_In]. *)
(* TODO: these may need the [not] unfolded... *)
Hint Resolve
    @set_diff_trivial
    :listset.

(** Non-syntax-directed lemmata for [~ set_In]... a bad idea? *)
(* BUG: We get warnings that this one is [eauto]-only. Why is it? *)
Hint Resolve
    @set_mem_complete1
    :listset_star.

Hint Extern 3 (~ set_In ?x ?xs) =>
    match goal with
    | I : set_In x (set_diff ?eq_dec ?ys xs)  |- _ =>
        apply (@set_diff_elim2 _ eq_dec x xs ys I)
    end :listset_star.


(** Logical-syntax directed lemmata. May require [intuition]. *)

(* Conjunctive conclusions. Isn't strictly necessary... *)
(* BUG: We get warnings that this one is [eauto]-only. Why is it? *)
Hint Resolve
    @set_inter_elim
    :listset.

(* Disjunctive conclusions. *)
(* TODO: Deconstruct the disjunctions... *)
(* BUG: We get warnings that these two are [eauto]-only. Why are they? *)
Hint Resolve
    @set_add_elim
    @set_union_elim
    :listset.

(*
(* Disjunctive hypotheses. Isn't strictly necessary if [intuition]... *)
Hint Resolve
    @set_add_intro
    @set_union_intro
    :listset_star.
*)

(** Congruence lemmata. *)
Hint Resolve
    @set_add_not_empty
    @set_mem_correct2
    @set_mem_complete2
    :listset.


(** Others. *)
(* TODO:
(* N.B., the weight should be high, since this will apply to all goals! *)
Hint Extern 10 =>
    match goal with
    | |- context P [if set_mem ?eq_dec ?x ?xs then ?a else ?b] =>
        (* Use [context P\[c\]] in order to substitute into it. *)
        (* BUG: I'm not sure how we can turn [P] into a Gallina function though... *)
        first
            [ apply (@set_mem_ind  _ eq_dec _ ?P a b x xs)
            | apply (@set_mem_ind2 _ eq_dec _ ?P a b x xs)
            | fail 2 ] (* or should it be [fail 3] ? *)
    end :listset_star.
*)

(*
@set_In_dec

(* from <http://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.12.html> *)
Require EqDecide.
Require PolyList.
Hint eqdec1 : eqdec :=
    Extern 5 {?1=?2}+{~ (?1=?2)} 
        Generalize ?1 ?2; Decide Equality.
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* BUG: sometimes this clears too much! *)
(** Experimental tactic like [jauto_set_hyps] for crushing hypotheses. *)
Ltac listset_destruct_hyps :=
    repeat match goal with
    | I: set_In ?x (set_add ?eq_dec ?y ?ys) |- _ =>
        destruct (@set_add_elim _ eq_dec x y ys I);
        try clear I
    | I: set_In ?x (set_union ?eq_dec ?xs ?ys) |- _ =>
        destruct (@set_union_elim _ eq_dec x xs ys I);
        try clear I
    | I: set_In ?x (set_diff ?eq_dec ?xs ?ys) |- _ =>
        let I1 := fresh I in
        pose (I1 := @set_diff_elim1 _ eq_dec x xs ys I); clearbody I1;
        let I2 := fresh I in
        pose (I2 := @set_diff_elim2 _ eq_dec x xs ys I); clearbody I2;
        try clear I
    | I: set_In ?x (set_remove ?eq_dec ?y ?xs) |- _ =>
        let I1 := fresh I in
        pose (I1 := @set_remove_elim _ eq_dec x y xs I); clearbody I1;
        try (clear I; rename I1 into I)
    | I: set_In ?x (set_inter ?eq_dec ?xs ?ys) |- _ =>
        let I1 := fresh I in
        pose (I1 := @set_inter_elim1 _ eq_dec x xs ys I); clearbody I1;
        let I2 := fresh I in
        pose (I2 := @set_inter_elim2 _ eq_dec x xs ys I); clearbody I2;
        try clear I
    
    (* | I: ~ set_In ?x (set_add ?eq_dec ?y ?ys) |- _ =>
        x<>y /\ ~set_In x ys
    *)
    | I: ~ set_In ?x (set_union ?eq_dec ?xs ?ys) |- _ =>
        let I1 := fresh I in
        pose (I1 := @set_not_union_elim1 _ eq_dec x xs ys I); clearbody I1;
        let I2 := fresh I in
        pose (I2 := @set_not_union_elim1 _ eq_dec x xs ys I); clearbody I2;
        try clear I
    | I: ~ set_In ?x (set_diff ?eq_dec ?xs ?ys) |- _ =>
        destruct (@set_not_diff_elim1 _ eq_dec x xs ys I);
        try clear I;
        try solve [contradiction]
    (* | I: ~ set_In ?x (set_remove ?eq_dec ?y ?xs) |- _ =>
        x=y \/ ~set_In x xs
    *)
    (* | I: ~ set_In ?x (set_inter ?eq_dec ?xs ?ys) |- _ =>
        ~set_In x xs \/ ~set_In x ys
    *)
    end.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* TODO: rules/tactic for handling contradictions especially. *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* TODO: a tactic for tearing apart all syntax in both hyps and the goal. *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
