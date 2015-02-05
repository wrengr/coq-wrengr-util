(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [ex_falso] tactic, and related things.

This implementation is inspired by <http://www.chargueraud.org/softs/tlc>
and so released under the LGPLv3. For more information about the
tactic and its uses, see the tutorial:

    <http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html>   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Export Tactics.Core.


(* TODO: improve this if possible. *)
(* TODO: move to core? *)
Ltac elimtype_False :=
    match goal with
    | |- False => idtac
    | |- not _ => unfold not; intros
    | |- _     => elimtype False
    end.


(* TODO: how can we define this so the versions that don't pass [E] can use it? *)

(** [ex_falso E by T] tries to exploit lemma [E] to prove the goal
    false, and uses the tactic [T] to try to make progress. If the
    tactic cannot solve the goal, it will leave the proof state
    unaltered. *)
Tactic Notation "ex_falso" constr(E) "by" tactic(T) :=
    solve
        [ contradiction
        | congruence (* Hoisted out to avoid redundant [False_ind False]. *)
        | intros
        ; elimtype_False
        ; apply E
        (* TODO: Is that the best we can do? How would we make it
            so we could pass the [try solve...] part to [intuition]?
        
        N.B., the extra [try solve] wrapping is necessary in order
            to define the non-[by] versions via passing [idtac] for
            [T]. *)
        ; try solve
            [ repeat progress
                ( T
                ; try solve [ assumption | discriminate | congruence ]
                )
            ]
        ].


(** [ex_falso E] tries to exploit lemma [E] to prove the goal false
    (using no special tactic to make progress). If the tactic cannot
    solve the goal, it will leave the proof state unaltered. *)
Tactic Notation "ex_falso" constr(E) :=
    ex_falso E by idtac.


(** [ex_falso by T] tries to prove the goal false, and uses the
    tactic [T] to try to make progress. If the tactic cannot solve
    the goal, it will leave the proof state unaltered. *)
Tactic Notation "ex_falso" "by" tactic(T) :=
    solve
        [ contradiction
        | congruence
        | intros
        ; elimtype_False
        ; try solve
            [ repeat progress
                ( T
                ; try solve [ assumption | discriminate | congruence ]
                )
            ]
        ].


(** [ex_falso] tries to prove the goal false (using no special
    tactic to make progress). If the tactic cannot solve the goal,
    it will leave the proof state unaltered. *)
Tactic Notation "ex_falso" :=
    ex_falso by idtac.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** [ex_falso_invert H] proves any goal if it absurd after calling
    [inversion H] and [ex_falso]. Use [try (ex_falso_invert H)] to
    leave the goal unchanged if the tactic doesn't solve it. *)
Tactic Notation "ex_falso_invert" constr(H) :=
    solve
        [ let M := fresh in pose (M := H); inversion H; ex_falso
        | ex_falso
        ].


(** [ex_falso_invert] proves any goal provided there is at least
    one hypothesis [H] in the context that can be proved absurd by
    calling [inversion H]. *)
Tactic Notation "ex_falso_invert" :=
    let rec ex_falso_invert__loop :=
        match goal with
        H : _ |- _ =>
            solve [ inversion H; ex_falso
                  | clear H; ex_falso_invert__loop
                  | fail 2
                  ]
        end
    in 
    solve [ ex_falso_invert__loop | ex_falso ].


(** [ex_falso__neq_self_hyp] proves any goal if the context contains
    an hypothesis of the form [E <> E]. It is a restricted and
    optimized version of [ex_falso]. It is intended to be used by
    other tactics only. *)
Ltac ex_falso__neq_self_hyp :=
    match goal with
    H : ?x <> ?x |- _ => elimtype False; apply H; reflexivity
    end.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
