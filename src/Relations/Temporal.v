(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Temporal-logic modalities for relations. *)
Require Import Relations.Core.
Require Import Coq.Arith.Le.
Require Import CoqExtras.Nat.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** The universal-affirmative syllogism with existential import. *)
Definition forall1 {A:Type} (P Q : A -> Prop) :=
    (exists a, P a) /\ (forall (a:A), P a -> Q a).
Hint Unfold      forall1.
Hint Transparent forall1.
(* The dual of [forall1] is a non-temporal version of [release]... *)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Fixpoint eventually_
    {A:Type} (R : relation A) (P : A -> Prop) (n:nat) (a:A) {struct n} :=
        match n with
        | O    => P a
        | S n' => P a \/ forall1 (R a) (eventually_ R P n')
        end.

(** The property [P] must hold eventually, on every path starting
    from [a]. This is the "AF" modality in CTL. *)
Definition eventually
    {A:Type} (R : relation A) (P : A -> Prop) (a:A) :=
        exists n, eventually_ R P n a.


Lemma eventually_is_monotonic_
    : forall {A:Type} (R : relation A) (P : A -> Prop) (m n : nat) (a:A),
    m <= n -> eventually_ R P m a -> eventually_ R P n a.
Proof.
  intros; revert m H a H0.
  induction n; intros; destruct m; simpl in *;
    [ assumption
    | inversion H (* absurd *)
    | left; assumption
    | destruct H0 as [Pa | [[b aRb] H0]];
      [ left; assumption
      | right; split;
        [ exists b; exact aRb
        | intros c aRc; exact (IHn m (le_S_n _ _ H) c (H0 c aRc)) ]]].
Qed.


(** This is unlikely to be useful, since in general the particular
    [n] can depend on the [a'] s.t. [eventually R P a']. Proving
    the general version of this (i.e., for [eventually]) would
    require being able to take the maximum/supremum of all such
    [n], in order to hoist the existential to the front. *)
Lemma eventually_is_idempotent_
    : forall {A:Type} (R : relation A) (P : A -> Prop) (n m : nat) (a : A),
    eventually_ R (eventually_ R P n) m a -> eventually_ R P (m + n) a.
Proof.
  intros; revert n a H; induction m; simpl; intros;
    [ assumption
    | destruct H as [H | [[b aRb] H]];
      [ revert a H; induction n; simpl in *; intros;
        [ left; assumption
        | destruct H;
          [ left; assumption
          | destruct H as [[b aRb] H]; right; split;
            [ exists b; exact aRb
            | intros c aRc
            ; refine (eventually_is_monotonic_ R P n (m + S n) c _ (H c aRc))
            ; apply (le_trans n (S n) (m + S n));
              [ apply le_n_Sn
              | apply le_plus ]]]]
      | right; split;
        [ exists b; exact aRb
        | intros; apply IHm; apply H; assumption ]]].
Qed.


(*
Lemma foo
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a : A),
    eventually R (eventually R P) a
    -> exists m, exists n, eventually_ R (eventually_ R P n) m a.
(* BUG: the particular [n] can depend on the particular [b] transitioned to *)
Proof.
    destruct H as [m H].
    exists m.
    set (ns := { n:nat | exists b, R a b /\ eventually_ R P n b }). (* or something like that *)
    exists (max ns). (* the maximum may not exist; if we used [sup] then it would exist, but it could be omega when [R] has non-finite out-degree *)
    ...
Abort.

Inductive Fin : nat -> Set :=
    | Zero : forall n, Fin (S n)
    | Succ : forall n, Fin n -> Fin (S n).
Inductive IsFinite A :=
    | isFinite : forall
        (n : nat)
        (f : A -> Fin n)
        (g : Fin n -> A)
        (gf : forall a : A,     g (f a) = a)
        (fg : forall x : Fin n, f (g x) = x)
        , IsFinite A.
Lemma foo
    :  forall {A:Type} (P : A -> nat -> Prop)
    ,  (forall a n, P a n -> P a (S n)) (* monotonicity *)
    -> IsFinite A                       (* rule out omega *)
    -> (forall a b:A, {a=b}+{a<>b})     (* to prove IsFinite for the IH *)
    -> (forall a, exists n, P a n)
    -> (exists m, forall a, P a m).
Proof.
    intros A P monotonicity [n f g gf fg] eq_dec H.


Theorem eventually_is_idempotent
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    eventually R P a <-> eventually R (eventually R P) a.
Proof.
  intros; split; intro.
    exists 0; exact H.
    
    destruct H as [n H]; revert a H; induction n; simpl; intros.
      exact H.
      destruct H as [H | [[b aRb] H]].
        exact H.
(* Abort. *)
*)
    
    
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
    (* TODO: Why not actually use [forall b, R^* a b -> P b]? *)


Theorem forever_is_sound
    :  forall {A:Type} (R : relation A) (P : A -> Prop) (a:A)
    ,  forever R P a
    -> (forall b, R^* a b -> P b).
Proof.
  intros.
  apply RTC_optimize in H0.
  induction H0. (* BUG: can't use semicolon after [apply]... *)
    destruct H; assumption.
    
    apply IHRTC_opt.
    destruct H as [pa H].
    apply H.
    exact H0.
Qed.

(* TODO:
Theorem forever_is_complete
    :  forall {A:Type} (R : relation A) (P : A -> Prop) (a:A)
    ,  (forall b, R^* a b -> P b)
    -> forever R P a.
Proof.
  intros.
  constructor. (* BUG: we need some kind of coinduction *)
    apply H; reflexivity.
    
    intros.
Abort.

(* Alas, this doesn't work since [forever] isn't a CoInductive... *)
CoFixpoint forever_is_complete
    {A:Type} (R : relation A) (P : A -> Prop) (a:A)
    (H: forall b, R^* a b -> P b)
    : forever R P a
    :=
    forever_intro R P a (H a (RTC_refl a))
        (fun b (aRb : R a b) => forever_is_complete R P b
            (fun c bRc => H c (RTC_trans (RTC_step aRb) bRc))) .
*)
    

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


Corollary eventually_not_implies_not_forever
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    eventually R (fun a' => ~P a') a -> ~forever R P a.
Proof.
  intros; intro;
  refine (forever_implies_not_eventually_not R P a _ _); assumption.
Qed.


(* BUG: what sort of induction can we use to prove either of these two? They require classical reasoning don't they?
Lemma not_eventually_not_implies_forever
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    ~eventually R (fun a' => ~P a') a -> forever R P a.
Proof.
  intros.
  assert (H': forall n, ~eventually_ R (fun a' => ~P a') n a)
    by (intro n; intro H0; apply H; exists n; exact H0).
  constructor. (* Nope. Need to do some sort of coinduction... *)
    (* Need [~~P a -> P a] to make use of [H' 0] *)
    
    (* need *)
Abort.

Lemma not_forever_implies_eventually_not
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    ~forever R P a -> eventually R (fun a' => ~P a') a.
Proof.
  intros.
  assert (H' : P a -> (forall a', R a a' -> forever R P a') -> False)
    by (intros; apply H; constructor; assumption).
  (* Need [{P a}+{~P a}] in order to decide on the [n] that exists. *)
Abort.

Theorem not_forever_iff_eventually_not
    : forall {A:Type} (R : relation A) (P : A -> Prop) (a:A),
    ~forever R P a <-> eventually R (fun a' => ~P a') a.
Proof.
  intros; split;
    [ apply not_forever_implies_eventually_not
    | apply eventually_not_implies_not_forever
    ].
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
