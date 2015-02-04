(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [introv] tactic.

This implementation is from <http://www.chargueraud.org/softs/tlc>
and so released under the LGPLv3. For more information about the
tactic and its uses, see the tutorial:

    <http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html>   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(** [introv] is used to name only the non-dependent hypothesis.
  - If [introv] is called on a goal of the form [forall x, H],
    it should introduce all the variables quantified with a [forall]
    at the head of the goal, but it does not introduce hypotheses
    that preceed an arrow constructor, like in [P -> Q].
  - If [introv] is called on a goal that is not of the form [forall x, H]
    nor [P -> Q], the tactic unfolds definitions until the goal
    takes the form [forall x, H] or [P -> Q]. If unfolding definitions
    does not produces a goal of this form, then the tactic [introv]
    does nothing at all. *)


(* [introv__rec] introduces all visible variables. It does not try
    to unfold any definition. *)
Ltac introv__rec :=
    match goal with
    | |- ?P -> ?Q    => idtac
    | |- forall _, _ => intro; introv__rec
    | |- _           => idtac
    end.
(* N.B., using the metavariable [?Q] ensures that the [->] isn't
    actually a [forall]. If we change the [?Q] to [_], then it will
    match a [forall] as well as [->]. *)


(* [introv__noarg] forces the goal to be a [forall] or an [->], and
    then calls [introv__rec] to introduces variables (possibly none,
    in which case [introv] is the same as [hnf]). If the goal is
    not a product, then it does not do anything. *)
Ltac introv__noarg :=
    match goal with
    | |- ?P -> ?Q    => idtac
    | |- forall _, _ => introv__rec
    | |- ?G          => hnf;
        match goal with
        | |- ?P -> ?Q    => idtac
        | |- forall _, _ => introv__rec
        end
    | |- _           => idtac
    end.

    (* simpler yet perhaps less efficient imlementation *)
    Ltac introv__noarg_unoptimized :=
        intro; match goal with H:_|-_ => revert H end; introv__rec.


(* [introv__arg H] introduces one non-dependent hypothesis under
    the name [H], after introducing the variables quantified with
    a [forall] that preceeds this hypothesis. This tactic fails if
    there does not exist a hypothesis to be introduced. *)
Ltac introv__arg H :=
    hnf;
    match goal with
    | |- ?P -> ?Q    => intros H    (* TODO: Why not [intro H]? *)
    | |- forall _, _ => intro; introv__arg H
    end.


(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv__noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv__arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
