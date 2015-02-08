(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [jauto] tactic.

The tactic is described in the tutorial:

This implementation is from <http://www.chargueraud.org/softs/tlc>
and so released under the LGPLv3. For more information about the
tactic and its uses, see the tutorial:

    <http://www.cis.upenn.edu/~bcpierce/sf/UseAuto.html>      *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(*
(* the [@?X] notation is necessary to allow applying it to Gallina-quantified variables. *)
Tactic Notation "jauto_set__debug" :=
    let rec go H A :=
        match A with
        | forall x, @?B x => go H (B x)
        | ?B -> ?C        => go H C
        | and _ _         => idtac H " matches!"
        end in
    match goal with
    | H : forall x, @?A x |- _ => go H (A x) (* BUG: the [A x] will explode on pattern matching because [x:=n] and [n] isn't in scope there... *)
    | H : ?A -> ?B        |- _ => go H B
    end.
Lemma everything_fails (P Q : nat -> Prop) (H : forall n, P n /\ Q n) : P 2.
Set Ltac Debug.

cf <http://adam.chlipala.net/cpdt/html/LogicProg.html>
(* N.B., the weight should be high, since this will apply to all goals! *)
Hint Extern 10 => (* their [P] was defined in scope *)
    match goal with
    | H : forall x, ?P x /\ _ |- ?P ?X => apply (proj1 (H X))
    | H : forall x, _ /\ ?P x |- ?P ?X => apply (proj2 (H X))
    end.
*)
    

(* cf vs [destruct_conjs] in <http://coq.inria.fr/stdlib/Coq.Program.Tactics.html> *)
(** * Common tactics for simplifying goals like [intuition]. *)
Ltac jauto_set_hyps :=
    repeat
        match goal with
        H : ?T |- _ =>
            match T with
            (* TODO: why weren't these ones included?
            | prod _ _    => destruct H (* tuples *)
            | sigT _ _    => destruct H (* strong-sigma *)
            | sig  _ _    => destruct H (* weak-sigma *)
            *)
            | and  _ _    => destruct H (* propositional pairs *)
            | exists a, _ => destruct H (* existentials *)
            (*
            | ?A -> ?B =>
                match B with
                | context [and ?C ?D] => TODO: Now what? We need to be more specific to ensure that the conjunction is really the result!
                end
            | forall a, ?B a =>
                match B a with
                | context [and (?C a) (?D a)] => BUG: doesn't match
                end
            *)
            | _           => generalize H; clear H (* TODO: why do this? *)
            end
        end.

Ltac jauto_set_goal :=
    repeat
        match goal with
        (* TODO: why weren't these ones included?
        | |- prod _ _    => split
        | |- sigT _ _    => esplit
        | |- sig  _ _    => esplit
        *)
        | |- and  _ _    => split
        | |- exists a, _ => esplit
        end.

Ltac jauto_set :=
    intros; jauto_set_hyps;
    intros; jauto_set_goal;
    unfold not in *.


(** [jauto] is better at [intuition eauto] because it can open
    existentials from the context. At the same time, [jauto] can
    be faster than [intuition eauto] because it does not destruct
    disjunctions from the context. The strategy of [jauto] can be
    summarized as follows:

    - open all existentials and conjunctions from the context.
    - call [esplit] and [split] on the existentials and conjunctions
        in the goal.
    - call [eauto]. *)

Tactic Notation "jauto" :=
    try solve [ auto | eauto | jauto_set; eauto ].
    (* This is Chargueraud's "jauto_fast"; except we remove the
       inner [try solve]. *)


(** [iauto] is a shorthand for [intuition eauto] *)
Tactic Notation "iauto" :=
    try solve [ intuition eauto ].
    (* This is Chargueraud's "iauto". *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** An experimental tactic for improving upon [jauto]. *)

(*
BUG: how can we get the information of [info] to be complete?
When using [info jauto] it only shows the intro steps. But when
using [info (try jauto)] (or [progress] or [solve]) it prints
everything...

TODO: even though [auto] is simpler than [eauto], it can fail by instantiating existentials/metas inappropriately (See the "Automation for Proving Absurd Goals" section of the tutorial). Because we try [eauto] next, we should be able to handle those cases too; however, this may be slower than just trying [eauto] in the first place... Is there any problem with doing so? If so, then we'd probably want to define separate tactics for using [auto], using [eauto], and trying both.

BUG: I don't know why we can't lift the abstractions from below into this definition a~la:
    Ltac jjauto__ Depth Hints :=
        let do_auto  := auto  Depth with Hints in
        let do_eauto := eauto Depth with Hints in ... .
but if we try that then it will fail on some things that [jauto] succeeds on.

N.B., in order to write a hint database literal, try [ipattern:(core,v62)]. It parses fine at least; not sure if this is the cause of the bug above though... *)

Ltac jjauto__ do_auto do_eauto :=
    try solve
        [ do_auto
        | do_eauto
        | jauto_set
        ; solve
            [ do_auto
            | do_eauto
            | intuition (try solve [ do_auto | do_eauto ])
            ]
        ].

Tactic Notation "jjauto" :=
    jjauto__ ltac:(auto) ltac:(eauto).

Tactic Notation "jjauto" integer(Depth) :=
    jjauto__ ltac:(auto Depth) ltac:(eauto Depth).

Tactic Notation "jjauto" "with" ne_ident_list(Hints) :=
    jjauto__ ltac:(auto with Hints) ltac:(eauto with Hints).

Tactic Notation "jjauto" "with" "*" :=
    jjauto__ ltac:(auto with * ) ltac:(eauto with * ).

Tactic Notation "jjauto" integer(Depth) "with" ne_ident_list(Hints) :=
    jjauto__ ltac:(auto Depth with Hints) ltac:(eauto Depth with Hints).

Tactic Notation "jjauto" integer(Depth) "with" "*" :=
    jjauto__ ltac:(auto Depth with * ) ltac:(eauto Depth with * ).

(*
Lemma auto_fails (P Q : Prop) : P /\ Q -> P.

Lemma solving_conj_more :
  forall (P Q R : nat -> Prop) (F : Prop),
  (F /\ (forall n m, (Q m /\ R n) -> P n)) -> 
  (F -> R 2) ->
  Q 1 -> 
  P 2 /\ F.

Lemma everything_fails (P Q : nat -> Prop) : (forall n, P n /\ Q n) -> P 2.

Lemma jauto_fails (P Q R : Prop) : (P -> Q /\ R) -> P -> R.

Lemma iauto_fails : forall
  (f g : nat -> Prop),
  (forall x, f x -> g x) ->
  (exists a, f a) ->
  (exists a, g a).
  (* [jauto_set] is needed to open the existential hypotheses; [eauto] is needed to open the existential goal. *)
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
