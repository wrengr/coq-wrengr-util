(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Various [destruct] related tactics.

This implementation is inspired by <http://www.chargueraud.org/softs/tlc>
and so released under the LGPLv3. For more information about the
tactic and its uses, see the tutorial:

    <http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html>   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Tactics.ExFalso.


(** [destruct_if] looks for a pattern of the form [if ?B then _ else _]
	in the goal, and perform a case analysis on [B] by calling
	[destruct B]. After the [destruct B], [ex_falso] is attempted
	in order to prune absurd branches (it will also prove
	non-absurd branches via [congruence]).
  - If the [remember] keyword is used, then it will [remember B]
    before calling [destruct B]; thereby providing an equality proof
    for what [B] is in each branch. N.B., if the type of [B] is
    [bool] then this keyword is automatically enabled.
  - If an [as] clause is provided, the given names will be used for
    the equality proof in both branches.
  - If an [in] clause is provided, then does the search in the given
    hypothesis rather than in the goal. *)

(* BUG: We need better names than [remember] comes up with. *)
Tactic Notation "destruct_if" "remember" "as" simple_intropattern(Eq) :=
    match goal with
    | |- context [if ?B then _ else _] =>
        let B0 := fresh "B" in 
        (remember B as B0; destruct B0 as [Eq|Eq])
    end;
    try solve [ex_falso].
    
Tactic Notation "destruct_if" "as" simple_intropattern(Eq) :=
    match goal with
    | |- context [if ?B then _ else _] =>
        match type of B with
        | bool =>
            let B0 := fresh "B" in
            ( set (B0 := B) in *
            ; assert (Eq : B = B0) by reflexivity
            ; destruct B0
            )
        | _ =>
            destruct B as [Eq|Eq]
        end
    end;
    try solve [ex_falso].

Tactic Notation "destruct_if" "remember" :=
    let Eq := fresh "E" in destruct_if remember as Eq.

Tactic Notation "destruct_if" :=
    let Eq := fresh "E" in destruct_if as Eq.

Tactic Notation "destruct_if" "remember" "as" simple_intropattern(Eq) "in" hyp(H) :=
    match type of H with
    context [if ?B then _ else _] =>
        let B0 := fresh "B" in 
        (remember B as B0; destruct B0 as [Eq|Eq])
    end;
    try solve [ex_falso].

Tactic Notation "destruct_if" "as" simple_intropattern(Eq) "in" hyp(H) :=
    match type of H with
    context [if ?B then _ else _] =>
        match type of B with
        | bool =>
            let B0 := fresh "B" in
            ( set (B0 := B) in *
            ; assert (Eq : B = B0) by reflexivity
            ; destruct B0
            )
        | _ =>
            destruct B as [Eq|Eq]
        end
    end;
    try solve [ex_falso].

Tactic Notation "destruct_if" "remember" "in" hyp(H) :=
    let Eq := fresh "E" in destruct_if remember as Eq in H.

Tactic Notation "destruct_if" "in" hyp(H) :=
    let Eq := fresh "E" in destruct_if as Eq in H.

Tactic Notation "destruct_if" "in" "*" :=
    match goal with
    | H : _ |- _ => try destruct_if in H
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** A shorthand for a common invocation of [destruct] which behaves like [case_eq]. *)
Tactic Notation "destruct_eq" constr(T) :=
    destruct T as [] _eqn.
    (* BUG: this has the same horrible names as using [remember]. *)
    (* TODO: try to use the patter we did above for [destruct_if] on [bool]. *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Call [injection] on all equality hypotheses. Also uses
    [discriminate] and [ex_falso] to try to prune absurd cases.
    Beware, this can make for enormous proofs. *)
Tactic Notation "injection_hyps" :=
    let go H := first
            (* TODO: can we flip this to do [elimtype False; discriminate H]? *)
            [ discriminate H; contradiction
            | injection H; clear H
            ]
    in
    repeat
        match goal with
        H : ?T |- _ =>
            match T with
            | _ _ _ _ _ _ = _ _ _ _ _ _ => go H
            | _ _ _ _ _   = _ _ _ _ _   => go H
            | _ _ _ _     = _ _ _ _     => go H
            | _ _ _       = _ _ _       => go H
            | _ _         = _ _         => go H
            | _           = _           => fail 1
            | _                         => fail 1
            end
        end; intros; try solve [ex_falso].

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)