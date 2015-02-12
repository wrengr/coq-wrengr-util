(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Require Import Relations.Core.
Require Import Relations.Normalization.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Definition of (weak) Church--Rosser

    All these intermediate names like [Joinable], [WeakChurchRosser_],
    and [ChurchRosser_] are to simplify the types that show up in
    inductive hypotheses when proving Newman's Lemma. *)

Definition Joinable {A:Type} (R : relation A) b b' :=
    exists c, R^* b c /\ R^* b' c.
Hint Unfold      Joinable.
Hint Transparent Joinable.


Definition WeakChurchRosser_ {A:Type} (R : relation A) a :=
    forall {b}, R a b ->
    forall {c}, R a c ->
    Joinable R b c.
Hint Unfold      WeakChurchRosser_.
Hint Transparent WeakChurchRosser_.


Definition WeakChurchRosser {A:Type} (R : relation A) :=
    forall a, WeakChurchRosser_ R a.
Hint Unfold      WeakChurchRosser.
Hint Transparent WeakChurchRosser.


Definition ChurchRosser_ {A:Type} (R : relation A) a :=
    forall {b}, R^* a b ->
    forall {c}, R^* a c ->
    Joinable R b c.
Hint Unfold      ChurchRosser_.
Hint Transparent ChurchRosser_.


Definition ChurchRosser {A:Type} (R : relation A) :=
    forall a, ChurchRosser_ R a.
Hint Unfold      ChurchRosser.
Hint Transparent ChurchRosser.


(*
(* According to Chargueraud... *)
Definition church_rosser {A:Type} (R : relation A) :=
    forall a b, R^= a b -> Joinable R a b.
(* This follows from [ChurchRosser], of course, but isn't the standard definition... *)
*)



(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Some properties arising from Church--Rosser *)

(** *** If [R] is Church--Rosser, then every term has at most one normal form. *)
Theorem CR_implies_NF_unicity
    : forall {A:Type} (R : relation A),
    ChurchRosser R ->
    forall {a b c}, NormalizesTo R a b -> NormalizesTo R a c -> b = c.
Proof.
  intros A R.
  assert (MainLemma : forall a b, R^* a b -> a=b \/ (exists c, R a c)).
    intros a b Rab.
    apply RTC_optimize in Rab.
    induction Rab;
      [ left; reflexivity
      | intuition eauto
      ].
  
  intros CR a b c [Rab Hb] [Rac Hc].
  destruct (CR a b Rab c Rac) as [d [Rbd Rcd]].
  destruct (MainLemma b d Rbd);
    [ destruct (MainLemma c d Rcd);
      [ congruence
      | contradiction
      ]
    | contradiction
    ].
Qed.


(** *** If [R] is Church--Rosser and weakly normalizing, then every term has exactly one normal form. *)
Corollary CR_and_WN_implies_NF_uniqueness
    : forall {A:Type} (R : relation A),
    ChurchRosser R -> WeaklyNormalizing R ->
    forall a, exists! b, NormalizesTo R a b.
Proof.
  intros A R CR WN a.
  destruct (WN a) as [b NFab].
  exists b; split;
    [ assumption
    | intros; eapply CR_implies_NF_unicity; eassumption
    ].
Qed.


Corollary CR_and_SN_implies_NF_uniqueness
    : forall {A:Type} (R : relation A),
    (forall a, Reducible R a \/ ~Reducible R a) ->
    ChurchRosser R -> StronglyNormalizing R ->
    forall a, exists! b, NormalizesTo R a b.
Proof.
  intros A R Reducible_lem CR SN a.
  apply CR_and_WN_implies_NF_uniqueness;
    [| apply SN_implies_WN ]; assumption.
Qed.


(* TODO: CR_and_WN_implies_SN *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Newman's lemma *)

(* HACK: we define this tactic because for some reason we're not
   allowed to do [destruct (RTC_optimize H)], and because using
   [RTC_optimize_case] is too ugly. *)
Tactic Notation "RTC_optimize_destruct" hyp(H) :=
    let H0 := fresh "H" in (
    pose (H0 := RTC_optimize H);
    clearbody H0;
    destruct H0;
    repeat
        (match goal with
        | H1 : RTC_opt _ _ _ |- _ => apply RTC_unoptimize in H1
        end)).

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** A strongly normalizing relation is Church--Rosser if and only if it is weak Church--Rosser. *)
Theorem Newman's_Lemma
    : forall {A:Type} (R : relation A),
    StronglyNormalizing R -> WeakChurchRosser R -> ChurchRosser R.
Proof.
    intros A R SN WCR a.
    induction (SN a) as [a _ IH].
    intros c0 Rac0 c1 Rac1.
    RTC_optimize_destruct Rac0.
      exists c1; split; [assumption | reflexivity].
      
      rename b into b0, c into c0, H0 into Rb0c0, H into Rab0.
      RTC_optimize_destruct Rac1.
        exists c0; split; [reflexivity | assumption].
        
        rename b into b1, c into c1, H0 into Rb1c1, H into Rab1.
        assert (Joinable R b0 b1)
          as [b2 [Rb0b2 Rb1b2]]
          by (apply (WCR a); assumption).
        assert (Joinable R c0 b2)
          as [d [Rc0d Rb2d]]
          by (apply (IH b0 Rab0); assumption).
        assert (R^* b1 d) by (transitivity b2; assumption).
        assert (Joinable R d c1)
          as [f [Rdf Rc1f]]
          by (apply (IH b1 Rab1); assumption).
        assert (R^* c0 f) by (transitivity d; assumption).
        exists f; split; assumption.
Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
