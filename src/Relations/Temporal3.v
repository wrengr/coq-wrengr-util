(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Temporal-logic modalities for relations. *)
Require Import Relations.Core.
Require Import Util.Nat.
Require Import Coq.Arith.Le.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** The universal-affirmative syllogism with existential import. *)
Definition forall1 {A:Type} (P Q : A -> Prop) :=
    (exists a, P a) /\ (forall (a:A), P a -> Q a).
Hint Unfold      forall1.
Hint Transparent forall1.
(* The dual of [forall1] is a non-temporal version of [release]... *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* BUG: can't use [forall1] in [Eventually_Soon] if we want the right IH *)
Inductive Eventually {A:Type} (R : relation A) (P : A -> Prop)
    : nat -> A -> Prop :=
    | Eventually_Now
        :  forall {n a}
        ,  P a
        -> Eventually R P n a
    | Eventually_Soon
        :  forall {n a}
        ,  (exists a', R a a')
        -> (forall a', R a a' -> Eventually R P n a')
        -> Eventually R P (S n) a
    .
Implicit Arguments Eventually_Now   [A R P n a].
Implicit Arguments Eventually_Soon  [A R P n a].
Definition eventually {A:Type} R P (a:A) := exists n, Eventually R P n a.


Lemma Eventually_is_monotonic
    : forall {A:Type} R P n n' (a:A),
    n <= n' -> Eventually R P n a -> Eventually R P n' a.
Proof.
  intros; revert n' H; induction H0; intros;
    [ apply Eventually_Now
    | destruct n';
      [ inversion H2
      | apply Eventually_Soon;
        [| intros; apply H1;
          [| apply le_S_n ]]]]; assumption.
Qed.


(** Unlikely to be helpful, but... *)
Lemma Eventually_is_idempotent
    : forall {A:Type} R P n m (a:A),
    Eventually R (Eventually R P n) m a -> Eventually R P (m + n) a.
Proof.
  induction 1;
    [ apply (Eventually_is_monotonic R P n (n0 + n) a); [ apply le_plus |]
    | simpl; apply Eventually_Soon
    ]; assumption.
Qed.

(*
Theorem eventually_is_idempotent
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a : A),
    eventually R (eventually R P) a -> eventually R P a.
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* BUG: can't use [forall1] in [Until_Soon] if we want the right IH *)
Inductive Until {A:Type} (R : relation A) (P Q : A -> Prop)
    : nat -> A -> Prop :=
    | Until_Now
        :  forall {n a}
        ,  Q a
        -> Until R P Q n a
    | Until_Soon
        :  forall {n a}
        ,  P a
        -> (exists a', R a a')
        -> (forall a', R a a' -> Until R P Q n a')
        -> Until R P Q (S n) a
    .
Implicit Arguments Until_Now  [A R P n a].
Implicit Arguments Until_Soon [A R P n a].
Definition until {A:Type} R P Q (a:A) := exists n, Until R P Q n a.


Lemma Until_is_monotonic
    : forall {A:Type} R P Q n n' (a:A),
    n <= n' -> Until R P Q n a -> Until R P Q n' a.
Proof.
  intros; revert n' H; induction H0; intros;
    [ apply Until_Now
    | destruct n';
      [ inversion H3
      | apply Until_Soon;
        [| | intros; apply H2; [| apply le_S_n ]]]]; assumption.
Qed.


(** Unlikely to be helpful, but... *)
Lemma Until_is_idempotent
    : forall {A:Type} R P Q n m (a:A),
    Until R P (Until R P Q n) m a -> Until R P Q (m + n) a.
Proof.
  induction 1;
    [ apply (Until_is_monotonic R P Q n (n0 + n) a); [ apply le_plus |]
    | simpl; apply Until_Soon
    ]; assumption.
Qed.

(*
Lemma until_is_idempotent
    : forall {A:Type} R P Q n (a:A),
    until R P (until R P Q) a -> until R P Q a.
*)

Lemma Until_is_strong
    : forall {A:Type} R P Q n (a:A), 
    Until R P Q n a -> Eventually R Q n a.
Proof.
  induction 1;
    [ apply Eventually_Now
    | apply Eventually_Soon; [| intros; apply H2]
    ]; assumption.
Qed.

Corollary until_is_strong
    : forall {A:Type} R P Q (a:A),
    until R P Q a -> eventually R Q a.
Proof.
  intros; destruct H as [n H]; exists n;
  eapply Until_is_strong; eexact H.
Qed.

(*
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


Lemma forever_and_Eventually_implies_Until
    :  forall (n:nat) {A:Type} (R : relation A) (P Q : A -> Prop) (a:A)
    ,  (forall b, R^* a b -> P b) (* [forever R P a] *)
    -> Eventually R Q n a
    -> Until R P Q n a.
Proof.
  intro n; induction n; simpl; intros A R P Q a p H;
    [ exact H
    | destruct H as [Qa | [[b aRb] H]];
      [ left; exact Qa
      | right; split;
        [ exact (p a (RTC_refl a))
        | split;
          [ exists b; exact aRb
          | intros c aRc; apply IHn;
            [ intros; apply p; transitivity c; [ constructor |]; assumption
            | apply H; exact aRc ]]]]].
Qed.

Corollary forever_and_eventually_implies_until
    :  forall {A:Type} (R : relation A) (P Q : A -> Prop) (a:A)
    ,  (forall b, R^* a b -> P b) (* [forever R P a] *)
    -> eventually R Q a
    -> until R P Q a.
Proof.
  intros; destruct H0 as [n H0]; exists n;
  apply forever_and_Eventually_implies_Until; assumption.
Qed.


Theorem eventually_iff_true_until
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    eventually R P a <-> until R (fun _ => True) P a.
Proof.
  intros; split; intro; destruct H as [n H]; exists n;
    [ apply forever_and_Eventually_implies_Until; [ trivial | exact H ]
    | eapply until_is_strong; eexact H
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Traditionally called "globally". This is the "AG" modality in CTL. *)
Inductive forever {A:Type} (R : relation A) (P : A -> Prop) (a:A) : Prop :=
    | forever_intro :
        P a -> (forall a', R a a' -> forever R P a') -> forever R P a
    .
    (* Why not use: [forall b, R^* a b -> P b]? *)

(*
Definition weakuntil
    {A:Type} (R : relation A) (P Q : A -> Prop) (a:A) : Prop :=
    until R Q P a \/ forever R Q a.

(* release is like weakuntil, except that both P and Q must hold at the transition point (if there is one). *)
Defintion release
    {A:Type} (R : relation A) (P Q : A -> Prop) (a:A) : Prop :=
    _ (* forall i, Q (a i) \/ (exists j, j < i /\ P (a j)) *).
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* BUG: this says "AG P => ~AF~P". But we want "AG P <=> ~EF~P". *)
Lemma forever_implies_not_eventually_not
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    forever R P a -> ~eventually R (fun a' => ~P a') a.
Proof.
  intros; intro; destruct H0 as [n H0]; revert a H H0; 
    induction n; intros; simpl in *;
      [ apply H0; destruct H; assumption
      | destruct H0 as [notPa | [[b aRb] H0]];
        [ apply notPa; destruct H; assumption
        | refine (IHn _ _ (H0 b aRb)); destruct H as [_ H]; apply H; exact aRb
        ]
      ].
Qed.


(* BUG: what sort of induction can we use to prove this? This requires classical reasoning doesn't it?
Lemma not_eventually_not_implies_forever
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    ~eventually R (fun a' => ~P a') a -> forever R P a.
Proof.
  intros.
Abort.

Corollary eventually_not_implies_not_forever
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    eventually R (fun a' => ~P a') a -> ~forever R P a.
Proof.
  intros; intro;
  refine (forever_implies_not_eventually_not R P a _ _); assumption.
Qed.


Theorem forever_iff_not_eventually_not
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    forever R P a <-> ~eventually R (fun a' => ~P a') a.
Proof.
  intros; split;
    [ apply forever_implies_not_eventually_not
    | apply not_eventually_not_implies_forever
    ].
Qed.
*)

(* TODO: NextStep, All, Exists *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
*)
