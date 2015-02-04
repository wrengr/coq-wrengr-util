(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Basic tactics too simple to bother breaking out.

To improve debugging of tactics, see [show_goal] and [show_hyps] in <http://coq.inria.fr/stdlib/Coq.Program.Tactics.html>. For more ideas about doing tactics, see:
- <http://www.cis.upenn.edu/~bcpierce/sf/UseAuto.html>
- <http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html>
- <http://adam.chlipala.net/cpdt/html/Match.html>
- <http://adam.chlipala.net/cpdt/repo/file/ded318830bb0/src/CpdtTactics.v>
- <http://flint.cs.yale.edu/cs430/coq/doc/Reference-Manual012.html> section 10.8
- <http://www.cl.cam.ac.uk/~pes20/CompCertTSO/doc/html/Libtactics.html>
- <http://osdir.com/ml/science.mathematics.logic.coq.club/2008-07/msg00069.html>
- <http://pages.cs.wisc.edu/~mulhern/Mul2010/slides.pdf>
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Even simpler than using [tauto]. Also solves constant functions. *)
Tactic Notation "identity" :=
    solve [clear; unfold not; intros; assumption].

(** Like [exact], but allows rewriting via [congruence]. *)
Ltac insist H :=
    match goal with
    | |- ?G =>
        match type of H with
        | ?T =>
            let E := fresh "E" in
            assert (E : G = T); [ try congruence | rewrite E; exact H ]
        end
    end.

(* TODO: move to [Util.Eq] *)
(** For legibility, because the argument order of [eq_ind] is inscrutable. *)
Definition rewrite {A:Type} {x y:A} (E:x=y) (P:A->Prop) (p:P x) : P y :=
    @eq_ind A x P p y E.


Tactic Notation "rca" := solve [repeat (try assumption; constructor)].


(* TODO: add support for [intro H; apply F in H; inversion H] *)
Tactic Notation "intro_inversion" :=
    let H := fresh "H" in intro H; inversion H.
Tactic Notation "intro_induction" :=
    let H := fresh "H" in intro H; induction H.
Tactic Notation "intro_destruct" :=
    let H := fresh "H" in intro H; destruct H.

(* See [Coq.Logic.Decidable] for these tactics:
Tactic Notation "solve_decidable" "using" ident(HintDb)
Tactic Notation "solve_decidable"
*)

(*
<http://coq.inria.fr/V8.2pl1/refman/Reference-Manual030.html>
Add Parametric Relation (A : Type) : A (fun x y => not (@eq A x y))
    symmetry proved by (@not_eq_sym A)
    as not_eq_rel.
*)

(* TODO: [generalize_eq], like [generalize] but with equality proofs; e.g.,

    > foo bar
    $ generalize_eq bar.
    > forall x, x = bar -> foo x

as opposed to:

    > foo bar
    $ generalize bar.
    > forall x, foo x
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
