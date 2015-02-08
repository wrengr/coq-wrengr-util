(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Temporal-logic modalities for relations.

This is experimental code to try to make the [eventually] quantifier
of [Relations.Temporal] behave more nicely. If/once the code actually
works as desired, it will be folded into the [Relations.Temporal]
module. *)
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


Inductive Eventually_ {A:Type} (R : relation A) (P : A -> Prop)
    : nat -> nat -> A -> Prop :=
    | Eventually_Now
        :  forall {m n a}
        ,  P a
        -> Eventually_ R P m n a
    | Eventually_Soon
        :  forall {m n a}
        (* BUG: can't use [forall1] if we want the right IH *)
        ,  (exists a', R a a')
        -> (forall a', R a a' -> Eventually_ R P m n a')
        -> Eventually_ R P m (S n) a
    
    (* This constructor is to try to deal with infinitely-wide branching... *)
    | Eventually_Later
        :  forall {m n a}
        (* BUG: can't use [forall1] if we want the right IH *)
        ,  (exists a', R a a')
        -> (forall a', R a a' -> exists n', Eventually_ R P m n' a')
        -> Eventually_ R P (S m) n a
    .
Implicit Arguments Eventually_Now   [A R P m n a].
Implicit Arguments Eventually_Soon  [A R P m n a].
Implicit Arguments Eventually_Later [A R P m n a].


Inductive Eventually {A:Type} R P (a:A) : Prop :=
    | eventually : forall {m n}, Eventually_ R P m n a -> Eventually R P a.
Implicit Arguments eventually [A R P a m n].


Lemma Eventually_is_monotonic_r
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m n n' : nat) (a:A),
    n <= n' -> Eventually_ R P m n a -> Eventually_ R P m n' a.
Proof.
  intros; revert n' H; induction H0; intros;
    [ apply Eventually_Now; assumption
    | destruct n';
      [ inversion H2
      | apply Eventually_Soon;
        [ assumption
        | intros; apply H1;
          [ assumption
          | apply le_S_n; assumption ]]]
    | apply Eventually_Later;
      [ assumption
      | intros; apply H0; assumption ]].
Qed.


Fixpoint Eventually_can_be_Later0
    {A:Type} (R : relation A) (P : A -> Prop) (m n : nat) (a:A)
    (H : Eventually_ R P m n a) {struct H} : Eventually_ R P (S m) 0 a
    :=
    match H
        in (Eventually_ _ _ m0 n0 a0)
        return (Eventually_ R P (S m0) O a0)
    with
    | Eventually_Now  m0 _  a0 p    => Eventually_Now p
    | Eventually_Soon m0 n0 a0 X H' =>
        Eventually_Later X
            (fun a' (r : R a0 a') =>
                ex_intro (fun n' => Eventually_ R P m0 n' a') n0 (H' a' r))
    | Eventually_Later m0 _ a0 X H' =>
        Eventually_Later X
            (fun a' (r : R a0 a') =>
                ex_intro (fun n' => Eventually_ R P (S m0) n' a') O
                (let '(ex_intro n' H') := H' a' r in
                Eventually_can_be_Later0 R P m0 n' a' H'))
    end.


Corollary Eventually_can_be_Later
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m n n' : nat) (a:A)
    , Eventually_ R P m n a -> Eventually_ R P (S m) n' a.
Proof.
  intros; induction n'.
    eapply Eventually_can_be_Later0; eexact H.
    eapply Eventually_is_monotonic_r;
      [eapply le_S; eapply le_n | exact IHn'].
Qed.


Corollary Eventually_is_strict_monotonic_l
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m m' n n' : nat) (a:A),
    m < m' -> Eventually_ R P m n a -> Eventually_ R P m' n' a.
Proof.
  induction 1; intros; eapply Eventually_can_be_Later;
    [eexact H | eapply IHle; exact H0].
Qed.


Corollary Eventually_is_monotonic_l
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m m' n n' : nat) (a:A),
    m <= m' -> Eventually_ R P m n a -> Eventually_ R P m' n a.
Proof.
  intros; induction H;
    [ assumption
    | eapply Eventually_is_strict_monotonic_l; [apply le_n | eexact IHle]].
Qed.



Theorem Eventually_is_monotonic_
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m m' n n': nat) (a:A),
    m <= m' -> n <= n' -> Eventually_ R P m n a -> Eventually_ R P m' n' a.
Proof.
  intros; induction H.
    eapply Eventually_is_monotonic_r; [eexact H0 | exact H1].
    eapply Eventually_can_be_Later; eexact IHle.
Qed.

(*
BUG: this one is still too tricksy to prove...
TODO: we may need induction on omega^omega rather than just on omega^2...
Lemma Eventually_is_idempotent
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a : A),
    Eventually R (Eventually R P) a -> Eventually R P a.


(* TODO: is this right for the ordering on omega^omega ? *)
Inductive nats_le (xs : list nat) : list nat -> Prop :=
    | nats_le_refl : nats_le xs xs
    | nats_le_succ : forall y ys, nats_le xs (cons y ys) -> nats_le xs (cons (S y) ys)
    | nats_le_pop : forall ys, nats_le xs ys -> nats_le xs (cons 0 ys)
    | nats_le_push : forall y y' ys, nats_le xs (cons y' (cons y ys)) -> nats_le xs (cons (S y) ys)
    .
Lemma foo : forall ms n ns, nats_le ms ns -> nats_le ms (cons n ns).
Proof.
  intros; induction n; [apply nats_le_pop | apply nats_le_succ]; assumption.
Qed.

Lemma bar : forall m ms n ns,
    nats_le (cons (S m) ms) (cons (S n) ns) -> nats_le ms ns.


(* BUG: """Warning: Ignoring recursive call""" *)
Inductive Eventually {A:Type} (R : relation A) (P : A -> Prop)
    : list nat -> A -> Prop :=
    | Eventually_Now
        :  forall {ns a}
        ,  P a
        -> Eventually R P ns a
    | Eventually_Soon
        :  forall {n ns a}
        ,  (exists a', R a a')
        -> (forall a', R a a' -> Eventually R P (cons n ns) a')
        -> Eventually R P (cons (S n) ns) a
    | Eventually_Later
        :  forall {n ns a}
        ,  (exists a', R a a')
        -> (forall a', R a a'
            -> exists n', Eventually R P (cons n' (cons n ns)) a')
        -> Eventually R P (cons (S n) ns) a
    .
Definition eventually {A:Type} R P (a:A) := exists ns, Eventually R P ns a.

Lemma Eventually_is_monotonic
    : forall {A:Type} R P ns ns' (a:A),
    nats_le ns ns' -> Eventually R P ns a -> Eventually R P ns' a.

Theorem eventually_is_idempotent
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a : A),
    eventually R (eventually R P) a -> eventually R P a.
*)


(*
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Fixpoint until_
    {A:Type} (R : relation A) (P Q : A -> Prop) (n:nat) (a:A) {struct n} :=
        match n with
        | O    => Q a
        | S n' => Q a \/ (P a /\ forall1 (R a) (until_ R P Q n'))
        end.

(** The property [P] holds along all paths from [a], until eventually
    [Q] holds. This is the strong until operator: it requires that
    [Q] holds eventually. This is the "AU" modality in CTL. *)
Definition until
    {A:Type} (R : relation A) (P Q : A -> Prop) (a:A) :=
        exists n, until_ R P Q n a.


Theorem until_is_monotonic_
    : forall {A:Type} (R : relation A) (P Q : A -> Prop) (m n : nat) (a:A),
    m <= n -> until_ R P Q m a -> until_ R P Q n a.
Proof.
  intros; revert m H a H0.
  induction n; intros; destruct m; simpl in *;
    [ assumption
    | inversion H (* absurd *)
    | left; assumption
    | destruct H0 as [Qa | [Pa [[b aRb] H0]]];
      [ left; assumption
      | right; split;
        [ assumption
        | split;
          [ exists b; exact aRb
          | intros c aRc; exact (IHn m (le_S_n _ _ H) c (H0 c aRc)) ]]]].
Qed.

(*
Lemma until_is_idempotent_
    : forall {A:Type} (R : relation A) (P : A -> Prop) (n m : nat) (a : A),
    until_ R P (until_ R P Q n) m a -> until_ R P Q (m+n) a.
    
Lemma until_is_idempotent
    : forall {A:Type} (R : relation A) (P Q : A -> Prop) (a : A),
    until R P (until R P Q) a <-> until R P Q a.
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Lemma until_is_strong_
    : forall {A:Type} (R : relation A) (P Q : A -> Prop) (n:nat) (a:A),
    until_ R P Q n a -> eventually_ R Q n a.
Proof.
  intros; revert a H;
  induction n; simpl in *; intros;
    [ exact H
    | destruct H as [Qa | [Pa [[b aRb] H]]];
      [ left; exact Qa
      | right; split;
        [ exists b; exact aRb
        | intros; apply IHn; apply H; assumption ]]].
Qed.

Corollary until_is_strong
    : forall {A:Type} (R : relation A) (P Q : A -> Prop) (a:A),
    until R P Q a -> eventually R Q a.
Proof.
  intros; destruct H as [n H]; exists n;
  eapply until_is_strong_; eexact H.
Qed.


Lemma forever_and_eventually_implies_until_
    :  forall (n:nat) {A:Type} (R : relation A) (P Q : A -> Prop) (a:A)
    ,  (forall b, R^* a b -> P b) (* [forever R P a] *)
    -> eventually_ R Q n a
    -> until_ R P Q n a.
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
  apply forever_and_eventually_implies_until_; assumption.
Qed.


Theorem eventually_iff_true_until
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    eventually R P a <-> until R (fun _ => True) P a.
Proof.
  intros; split; intro; destruct H as [n H]; exists n;
    [ apply forever_and_eventually_implies_until_; [ trivial | exact H ]
    | eapply until_is_strong_; eexact H
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
