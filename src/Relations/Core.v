(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Relation combinators

In the unoptimized combinators, the [*_step] constructor comes
first, so that you can use the [constructor] tactic to get down to
the base relation. For easy access to the other constructors you
can use the [reflexivity], [symmetry], or [transitivity] tactics
as appropriate. For the sake of induction, the "RST" ordering is
used. The [*_case] functions are provided because the [case] tactic
is worthless, and [inversion] breaks [induction].
*)

(* BUG: we can't use these for relations on [Term] because the
[*_step] should take an additional proof that [LC t]... *)

(* [Add Parametric Relation] declarations automatically generate
and define [Instance]s for [Reflexive], [Symmetric], [Transitive],
[PreOrder], [PER], [Equivalence], and [RewriteRelation]. If we add
the relation as [foo] then the first three declarations are called
[foo_Blah], the next three are [foo], and the last one is [foo_relation].
I'm not sure why they don't declare instances for [Setoid] and
[PartialSetoid] from [Coq.Classes.SetoidClass]...

N.B. the argument to [transitivity proved by] requires the [a b c]
argument ordering.*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* cf., <http://coq.inria.fr/V8.3pl3/refman/Reference-Manual031.html> *)
Require Import Coq.Setoids.Setoid.
Require Import Tactics.Core.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* N.B., [Constant Coq.Relations.Relation_Definitions] gives a
    [Definition] for this... *)
Notation relation A := ((A : Type) -> A -> Prop).


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* N.B., [Coq.Classes.RelationClasses] calls this [inverse] and
    also defines it as a notation. Though they use
    [Coq.Program.Basics.flip] which may be why they give the type
    signatures... *)
(* BUG: sometimes the notation unfolds too easily, introducing problems in proofs... *)
(** ** The converse/inverse of a relation. *)
Notation converse R := ((fun a b => (R : relation _) b a) : relation _).

(* TODO: because we're using a notation instead of a definition,
clients should automatically inherit the appropriate setoid tactics,
right? *)


(** Standard constructor for [converse] relations. *)
Definition fliprel
    {A : Type} {R : relation A} {a b} (r : R a b) : (converse R) b a := r.
Hint Unfold      fliprel.
Hint Transparent fliprel.


(** [converse] is involutive. *)
Definition converse_invol
    {A:Type} {R:relation A} {a b} (r : converse (converse R) a b) : R a b := r.
Hint Unfold      converse_invol.
Hint Transparent converse_invol.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** The reflexive closure of a relation. *)
Inductive RC {A : Type} (R : relation A) : relation A :=
    | RC_step  : forall a b, R a b -> RC R a b
    | RC_refl  : forall a,            RC R a a
    .
Notation "R ^?" := (RC R) (at level 31, left associativity) :type_scope.
Implicit Arguments RC_step [A R a b].
Implicit Arguments RC_refl [A R].
Implicit Arguments RC_ind  [A R].

Add Parametric Relation A R : A (@RC A R)
    reflexivity  proved by (@RC_refl A R)
    as RC_rel.

Definition RC_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : R^? a b)
    (P : relation A)
    (pstep : forall a0 b0, R a0 b0 -> a=a0 -> b=b0 -> P a0 b0)
    (prefl : forall a0,               a=a0 -> b=a0 -> P a0 a0)
    : P a b
    :=
    match H in (_^? a' b') return (a=a' -> b=b' -> P a' b') with
    | RC_step a0 b0 r0 => pstep a0 b0 r0
    | RC_refl a0       => prefl a0
    end (eq_refl a) (eq_refl b).

Definition RC_fmap
    {A  : Type}
    {R  : relation A}
    (f  : A -> A)
    (Rf : forall a b, R a b -> R (f a) (f b))
    {a b} (r : R^? a b) : R^? (f a) (f b) :=
        match r in (_^? a0 b0) return (R^? (f a0) (f b0)) with
        | RC_step a0 b0 r0 => RC_step (Rf a0 b0 r0)
        | RC_refl a0       => RC_refl (f a0)
        end.

Definition RC_join
    {A : Type}
    {R : relation A}
    {a b} (r : (R^?)^? a b) : R^? a b :=
        match r in (_^? a' b') return (R^? a' b') with
        | RC_step a0 b0 r0 => r0
        | RC_refl a0       => RC_refl a0
        end.

(* TODO: [(converse R)^? a b <-> converse (R^?) a b] ?? *)

Definition RC_converse
    {A : Type}
    {R : relation A}
    {a b} (r : R^? a b) : (converse R)^? b a :=
        match r in (_^? a' b') return ((converse R)^? b' a') with
        | RC_step a0 b0 r0 => RC_step (fliprel r0)
        | RC_refl a0       => RC_refl a0
        end.

Definition RC_unconverse
    {A : Type}
    {R : relation A}
    {a b} (r : (converse R)^? a b) : R^? b a :=
        match r in (_^? a' b') return (R^? b' a') with
        | RC_step a0 b0 r0 => @RC_step A R b0 a0 (fliprel r0)
        | RC_refl a0       => RC_refl a0
        end.

(** If every point is accessible by [RC R], then every point was
    accessible by [R] to begin with. Thus, we can use the reflexive
    reduction of any well-founded relation in lieu of that relation
    itself. Which is good, since [Acc_irrefl] indicates that
    accessible points can't be reflexive. *)
Lemma RC_inv_wf
    : forall {A : Type} {R : relation A}
    , well_founded (R^?) -> well_founded R.
Proof.
  intros A R H a; induction (H a) as [x _ H0];
  constructor; intros y H1; apply H0; constructor; assumption.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** The transitive closure of a relation. *)

(** This is the obvious definition of transitive closure; however,
    it gives a terrible inductive principle. The [TC_optR] closure
    gives a much better inductive principle, and perhaps the [R ^+]
    notation would be better reserved for that implementation. *)

(* BUG: we can't seem to do the [Inductive...with] to codefine the notation. *)
Inductive TC {A:Type} (R : relation A) : relation A :=
    | TC_step  : forall a b,   R a b -> TC R a b
    | TC_trans : forall a b c, TC R a b -> TC R b c -> TC R a c
    .
Notation "R ^+" := (TC R) (at level 31, left associativity) :type_scope.
Implicit Arguments TC_step  [A R a b].
Implicit Arguments TC_trans [A R a b c].
Implicit Arguments TC_ind   [A R].

Add Parametric Relation A R : A (@TC A R)
    transitivity proved by (@TC_trans A R)
    as TC_rel.

Definition TC_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : R^+ a b)
    (P : relation A)
    (pstep  : forall a0 b0,
        R a0 b0 -> a=a0 -> b=b0 -> P a0 b0)
    (ptrans : forall a0 b0 c0,
        R^+ a0 b0 -> R^+ b0 c0 -> a=a0 -> b=c0 -> P a0 c0)
    : P a b
    :=
    match H in (_^+ a' b') return (a=a' -> b=b' -> P a' b') with
    | TC_step  a0 b0    r0    => pstep  a0 b0 r0
    | TC_trans a0 b0 c0 l0 r0 => ptrans a0 b0 c0 l0 r0
    end (eq_refl a) (eq_refl b).

Fixpoint TC_fmap
    {A  : Type}
    {R  : relation A}
    (f  : A -> A)
    (Rf : forall  a b,  R   a b -> R   (f a) (f b))
    {a b} (r : R^+ a b) {struct r}: R^+ (f a) (f b) :=
        match r in (_^+ a' b') return (R^+ (f a') (f b')) with
        | TC_step  a0 b0    r0    => TC_step (Rf a0 b0 r0)
        | TC_trans a0 b0 c0 l0 r0 =>
            TC_trans
                (@TC_fmap A R f Rf a0 b0 l0)
                (@TC_fmap A R f Rf b0 c0 r0)
        end.

Fixpoint TC_join
    {A : Type}
    {R : relation A}
    {a b} (r : (R^+)^+ a b) {struct r}: R^+ a b :=
        match r in (_^+ a' b') return (R^+ a' b') with
        | TC_step  a0 b0    r0    => r0
        | TC_trans a0 b0 c0 l0 r0 =>
            TC_trans
                (@TC_join A R a0 b0 l0)
                (@TC_join A R b0 c0 r0)
        end.

(* TODO: [(converse R)^+ a b <-> converse (R^+) a b] ?? *)

Fixpoint TC_converse
    {A : Type}
    {R : relation A}
    {a b} (r : R^+ a b) {struct r}: (converse R)^+ b a :=
        match r in (_^+ a' b') return ((converse R)^+ b' a') with
        | TC_step  a0 b0    r0    => TC_step (fliprel r0)
        | TC_trans a0 b0 c0 l0 r0 =>
            @TC_trans A (converse R) c0 b0 a0
                (@TC_converse A R b0 c0 r0)
                (@TC_converse A R a0 b0 l0)
        end.

Fixpoint TC_unconverse
    {A : Type}
    {R : relation A}
    {a b} (r : (converse R)^+ a b) {struct r}: R^+ b a :=
        match r in (_^+ a' b') return (R^+ b' a') with
        | TC_step  a0 b0    r0    => @TC_step A R b0 a0 (fliprel r0)
        | TC_trans a0 b0 c0 l0 r0 =>
            @TC_trans A R c0 b0 a0
                (@TC_unconverse A R b0 c0 r0)
                (@TC_unconverse A R a0 b0 l0)
        end.


Definition TC_ind_prop_l : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_l : forall a b, R a b -> P a -> P b)
    , forall {a b}, R^+ a b -> P a -> P b.
Proof.
  fix 7; intros A R P step_l a b r p;
  apply (@TC_case A R a b r (fun _ b' => P b')); clear r; intros;
    [ apply (step_l a0 b0); [ exact H | insist p ]
    | apply (TC_ind_prop_l A R P step_l b0 c0 H0)
    ; apply (TC_ind_prop_l A R P step_l a0 b0 H)
    ; insist p
    ].
Defined.

Definition TC_ind_prop_r : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_r : forall a b, R a b -> P b -> P a)
    , forall {a b}, R^+ a b -> P b -> P a.
Proof.
  fix 7; intros A R P step_r a b r p;
  apply (@TC_case A R a b r (fun a' _ => P a')); clear r; intros;
    [ apply (step_r a0 b0); [ exact H | insist p ]
    | apply (TC_ind_prop_r A R P step_r a0 b0 H)
    ; apply (TC_ind_prop_r A R P step_r b0 c0 H0)
    ; insist p
    ].
Defined.

(* TODO:
Lemma TC_split
    {A : Type}
    {R : relation A}
    (P : A)
    (P_dec : forall a, {P a}+{~P a})
    (P_mon : forall a b, P a -> R a b -> P b)
    : forall a d, ~P a -> P d -> R^+ a d ->
    exists b c, R^+ a b /\ R b c /\ R^+ c d /\ ~P b /\ P c.
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** A flattened version of [TC], which can sometimes be easier
    to reason with since it linearizes the use of [TC_trans] to
    guarantee progress. Beware, this is a snoc definition, in order
    to simplify proving [TC_optR_wf]. *)
Inductive TC_optR {A:Type} (R : relation A) : relation A :=
    | TC_optR_step : forall a b,   R a b -> TC_optR R a b
    | TC_optR_snoc : forall a b c, TC_optR R a b -> R b c -> TC_optR R a c.
Implicit Arguments TC_optR_step [A R a b].
Implicit Arguments TC_optR_snoc [A R a b c].
Implicit Arguments TC_optR_ind  [A R].

Fixpoint TC_optR_trans
    {A : Type} {R : relation A} {a b c : A}
    (l : TC_optR R a b) (r : TC_optR R b c)
    {struct r}: TC_optR R a c :=
        match r in (TC_optR _ b' c') return (b'=b -> TC_optR R a c') with
        | TC_optR_step b0 c0 r0 => fun Eb =>
            @TC_optR_snoc A R a b c0 l
                (@rewrite A b0 b Eb (fun b' => R b' c0) r0)
        | TC_optR_snoc a0 b0 c0 l0 r0 => fun Eb =>
            @TC_optR_snoc A R a b0 c0
                (@TC_optR_trans A R a b b0 l
                    (@rewrite A a0 b Eb (fun a' => TC_optR R a' b0) l0)) r0
        end (eq_refl b).

Add Parametric Relation A R : A (@TC_optR A R)
    transitivity proved by (@TC_optR_trans A R)
    as TC_optR_rel.


Fixpoint TC_optimizeR
    {A} {R : relation A} {a b : A} (r : R^+ a b) {struct r} : TC_optR R a b
    :=
    match r in (_^+ a' b') return (TC_optR R a' b') with
    | TC_step  a0 b0 r0       => @TC_optR_step A R a0 b0 r0
    | TC_trans a0 b0 c0 l0 r0 =>
        @TC_optR_trans A R a0 b0 c0
            (@TC_optimizeR A R a0 b0 l0)
            (@TC_optimizeR A R b0 c0 r0)
    end.

(* TODO: Definition TC_unoptimizeR *)
(* TODO: Definition TC_optR_case *)
(* TODO: Definition TC_optR_fmap *)
(* TODO: Definition TC_optR_join *)


(* <http://permalink.gmane.org/gmane.science.mathematics.logic.coq.club/8609> *)
Lemma TC_optR_wf
    : forall {A : Type} {R : relation A}
    , well_founded R -> well_founded (TC_optR R).
Proof.
  intros A R H a; induction (H a) as [x _ H0];
  constructor; intros y H1; destruct H1 as [a b H1 | a b c H1 H2];
    [ eauto | apply (H0 b H2); trivial ].
Qed.

(* TODO: move to [Util.Wf]? *)
(* Wait, what? Every well-founded relation is irreflexive? *)
Lemma Acc_irrefl : forall {A:Type} (R : relation A) (x : A), Acc R x -> ~R x x.
Proof. intros; induction H; intro; exact (H0 x H1 H1). Qed.

(* TODO: move to [Util.Wf]? *)
Corollary wf_R_impl_neq
    : forall {A : Type} (R : relation A) (a b : A)
    , well_founded R -> R a b -> a <> b.
Proof. intros; red; destruct 1; exact (@Acc_irrefl _ _ _ (H a) H0). Qed.

Corollary wf_R_TC_optR_impl_neq
    : forall {A : Type} (R : relation A) (a b : A)
    , well_founded R -> TC_optR R a b -> a <> b.
Proof. eauto using @wf_R_impl_neq, @TC_optR_wf. Qed.


Corollary TC_wf
    : forall {A : Type} {R : relation A}
    , well_founded R -> well_founded (R^+).
Proof.
  intros A R H x; induction (@TC_optR_wf A R H x) as [x _ H0];
  constructor; intros y H1; destruct H1 as [a b H1 | a b c H1 H2];
    [ apply H0; constructor; assumption
    | apply (H0 b (TC_optimizeR H2)); trivial
    ].
Qed.

Corollary wf_R_TC_impl_neq
    : forall {A : Type} (R : relation A), well_founded R ->
    forall (a b : A), R^+ a b -> a <> b.
Proof. eauto using @wf_R_impl_neq, @TC_wf. Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** The reflexive transitive closure of a relation. *)


(** This is the obvious definition of reflexive transitive closure;
    however, it gives a terrible inductive principle. The [RTC_opt]
    closure gives a much better inductive principle, and perhaps
    the [R ^*] notation would be better reserved for that implementation.
    *)

Inductive RTC {A:Type} (R : relation A) : relation A :=
    | RTC_step  : forall a b,   R a b -> RTC R a b
    | RTC_refl  : forall a,     RTC R a a
    | RTC_trans : forall a b c, RTC R a b -> RTC R b c -> RTC R a c
    .
Notation "R ^*" := (RTC R) (at level 31, left associativity) :type_scope.
Implicit Arguments RTC_step  [A R a b].
Implicit Arguments RTC_refl  [A R].
Implicit Arguments RTC_trans [A R a b c].
Implicit Arguments RTC_ind   [A R].

Add Parametric Relation A R : A (@RTC  A R)
    reflexivity  proved by (@RTC_refl  A R)
    transitivity proved by (@RTC_trans A R)
    as RTC_rel.


Definition lift_RC_to_RTC
    {A} {R : relation A} : forall {a b}, R^? a b -> R^* a b
    := @RC_ind A R (R^*)
        (fun a b H0 => @RTC_step A R a b H0)
        (fun a      => @RTC_refl A R a).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lift_RC_to_RTC [[A][R] a b].


Definition lift_TC_to_RTC
    {A} {R : relation A} : forall {a b}, R^+ a b -> R^* a b
    := @TC_ind A R (R^*)
        (fun a b H0              => @RTC_step  A R a b H0)
        (fun a b c H0 IH0 H1 IH1 => @RTC_trans A R a b c IH0 IH1).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lift_TC_to_RTC [[A][R] a b].


Definition lower_RTC_to_TC
    {A} {R : relation A} : forall {a b}, R^* a b -> a=b \/ R^+ a b
    := @RTC_ind A R (fun a b => a=b \/ R^+ a b)
        (fun a b H0            => or_intror (a=b) (@TC_step A R a b H0))
        (fun a                 => or_introl (R^+ a a) (@eq_refl A a))
        (fun a b c _ IH0 _ IH1 =>
            match IH0, IH1 with
            | or_introl H0, or_introl H1 =>
                or_introl (R^+ a c) (@eq_trans A a b c H0 H1)
            | or_introl H0, or_intror H1 =>
                or_intror (a=c) (eq_ind_r (fun a0 => R^+ a0 c) H1 H0)
            | or_intror H0, or_introl H1 =>
                or_intror (a=c) (eq_ind b (fun c0 => R^+ a c0) H0 c H1)
            | or_intror H0, or_intror H1 =>
                or_intror (a=c) (@TC_trans A R a b c H0 H1)
            end).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lower_RTC_to_TC [[A][R] a b].


Definition RTC_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : R^* a b)
    (P : relation A)
    (pstep  : forall a0 b0, R a0 b0 -> a=a0 -> b=b0 -> P a0 b0)
    (prefl  : forall a0,               a=a0 -> b=a0 -> P a0 a0)
    (ptrans : forall a0 b0 c0,
        R^* a0 b0 -> R^* b0 c0 -> a=a0 -> b=c0 -> P a0 c0)
    : P a b
    :=
    match H in (_^* a' b') return (a=a' -> b=b' -> P a' b') with
    | RTC_step  a0 b0    r0    => pstep  a0 b0 r0
    | RTC_refl  a0             => prefl  a0
    | RTC_trans a0 b0 c0 l0 r0 => ptrans a0 b0 c0 l0 r0
    end (eq_refl a) (eq_refl b).

Fixpoint RTC_fmap
    {A  : Type}
    {R  : relation A}
    (f  : A -> A)
    (Rf : forall  a b,  R   a b -> R   (f a) (f b))
    {a b} (r : R^* a b) {struct r}: R^* (f a) (f b) :=
        match r in (_^* a0 b0) return (R^* (f a0) (f b0)) with
        | RTC_step  a0 b0    r0    => RTC_step (Rf a0 b0 r0)
        | RTC_refl  a0             => RTC_refl (f a0)
        | RTC_trans a0 b0 c0 l0 r0 =>
            RTC_trans
                (@RTC_fmap A R f Rf a0 b0 l0)
                (@RTC_fmap A R f Rf b0 c0 r0)
        end.

Fixpoint RTC_join
    {A : Type}
    {R : relation A}
    {a b} (r : (R^*)^* a b) {struct r}: R^* a b :=
        match r in (_^* a' b') return (R^* a' b') with
        | RTC_step  a0 b0    r0    => r0
        | RTC_refl  a0             => RTC_refl a0
        | RTC_trans a0 b0 c0 l0 r0 =>
            RTC_trans
                (@RTC_join A R a0 b0 l0)
                (@RTC_join A R b0 c0 r0)
        end.

(* TODO: [(converse R)^* a b <-> converse (R^* ) a b] ?? *)

Fixpoint RTC_converse
    {A : Type}
    {R : relation A}
    {a b} (r : R^* a b) {struct r}: (converse R)^* b a :=
        match r in (_^* a' b') return ((converse R)^* b' a') with
        | RTC_step  a0 b0    r0    => RTC_step (fliprel r0)
        | RTC_refl  a0             => RTC_refl a0
        | RTC_trans a0 b0 c0 l0 r0 =>
            @RTC_trans A (converse R) c0 b0 a0
                (@RTC_converse A R b0 c0 r0)
                (@RTC_converse A R a0 b0 l0)
        end.

Fixpoint RTC_unconverse
    {A : Type}
    {R : relation A}
    {a b} (r : (converse R)^* a b) {struct r}: R^* b a :=
        match r in (_^* a' b') return (R^* b' a') with
        | RTC_step  a0 b0    r0    => @RTC_step A R b0 a0 (fliprel r0)
        | RTC_refl  a0             => RTC_refl a0
        | RTC_trans a0 b0 c0 l0 r0 =>
            @RTC_trans A R c0 b0 a0
                (@RTC_unconverse A R b0 c0 r0)
                (@RTC_unconverse A R a0 b0 l0)
        end.


Definition RTC_ind_prop_l : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_l : forall a b, R a b -> P a -> P b)
    , forall {a b}, R^* a b -> P a -> P b.
Proof.
  fix 7; intros A R P step_l a b r p;
  apply (@RTC_case A R a b r (fun _ b' => P b')); clear r; intros;
    [ apply (step_l a0 b0); [ exact H | insist p ]
    | insist p
    | apply (RTC_ind_prop_l A R P step_l b0 c0 H0)
    ; apply (RTC_ind_prop_l A R P step_l a0 b0 H)
    ; insist p
    ].
Defined.

Definition RTC_ind_prop_r : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_r : forall a b, R a b -> P b -> P a)
    , forall {a b}, R^* a b -> P b -> P a.
Proof.
  fix 7; intros A R P step_r a b r p;
  apply (@RTC_case A R a b r (fun a' _ => P a')); clear r; intros;
    [ apply (step_r a0 b0); [ exact H | insist p ]
    | insist p
    | apply (RTC_ind_prop_r A R P step_r a0 b0 H)
    ; apply (RTC_ind_prop_r A R P step_r b0 c0 H0)
    ; insist p
    ].
Defined.

(* TODO: RC (TC R) <-> RTC R *)
(* TODO: TC (RC R) <-> RTC R *)
(* TODO: TC (RC R) <-> RC (TC R), for convenience? *)
(* TODO:

Lemma RTC_wf
    : forall {A : Type} {R : relation A}
    , well_founded (R^?) -> well_founded (R^* )
Proof. TC_wf. TC (RC R) -> RTC R. Qed.

Lemma RTC_inv_wf
    : forall {A : Type} {R : relation A}
    , well_founded (R^* ) -> well_founded (R^+)
Proof. RTC R -> RC (TC R). RC_inv_wf. Qed.
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** A flattened version of [RTC], which can sometimes be easier
    to reason with since it (1) removes extraneous uses of [RTC_refl],
    and (2) linearizes the use of [RTC_trans] to guarantee progress. *)
Inductive RTC_opt {A:Type} (R : relation A) : relation A :=
    | RTC_opt_refl : forall a,     RTC_opt R a a
    | RTC_opt_cons : forall a b c, R a b -> RTC_opt R b c -> RTC_opt R a c.
Implicit Arguments RTC_opt_refl [A R].
Implicit Arguments RTC_opt_cons [A R a b c].
Implicit Arguments RTC_opt_ind  [A R].


Definition RTC_opt_step
    {A : Type} {R : relation A} {a b : A}
    (r : R a b) : RTC_opt R a b :=
        @RTC_opt_cons A R a b b r (@RTC_opt_refl A R b).

Fixpoint RTC_opt_snoc
    {A : Type} {R : relation A} {a b c : A}
    (l : RTC_opt R a b) (r : R b c) {struct l}: RTC_opt R a c :=
        match l in (RTC_opt _ a' b') return (b=b' -> RTC_opt R a' c) with
        | RTC_opt_refl a0 => fun Eb =>
            @rewrite A b a0 Eb (fun a' => RTC_opt R a' c)
                (@RTC_opt_step A R b c r)
        | RTC_opt_cons a0 b0 c0 l0 r0 => fun Eb =>
            @RTC_opt_cons A R a0 b0 c l0
                (@RTC_opt_snoc A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => R b' c) r))
        end (eq_refl b).

Fixpoint RTC_opt_trans
    {A : Type} {R : relation A} {a b c : A}
    (l : RTC_opt R a b) (r : RTC_opt R b c) {struct l}: RTC_opt R a c :=
        match l in (RTC_opt _ a' b') return (b=b' -> RTC_opt R a' c) with
        | RTC_opt_refl a0 => fun Eb =>
            @rewrite A b a0 Eb (fun a' => RTC_opt R a' c) r
        | RTC_opt_cons a0 b0 c0 l0 r0 => fun Eb =>
            @RTC_opt_cons A R a0 b0 c l0
                (@RTC_opt_trans A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => RTC_opt R b' c) r))
        end (eq_refl b).

Add Parametric Relation A R : A (@RTC_opt  A R)
    reflexivity  proved by (@RTC_opt_refl  A R)
    transitivity proved by (@RTC_opt_trans A R)
    as RTC_opt_rel.


Fixpoint RTC_optimize
    {A} {R : relation A} {a b} (r : R^* a b) {struct r} : RTC_opt R a b
    :=
    match r in (_^* a' b') return (RTC_opt R a' b') with
    | RTC_refl  a0             => @RTC_opt_refl A R a0
    | RTC_step  a0 b0 r0       => @RTC_opt_step A R a0 b0 r0
    | RTC_trans a0 b0 c0 l0 r0 =>
        @RTC_opt_trans A R a0 b0 c0
            (@RTC_optimize A R a0 b0 l0)
            (@RTC_optimize A R b0 c0 r0)
    end.

Fixpoint RTC_unoptimize
    {A} {R : relation A} {a b} (r : RTC_opt R a b) {struct r} : R^* a b
    :=
    match r in (RTC_opt _ a' b') return (R^* a' b') with
    | RTC_opt_refl a0             => @RTC_refl A R a0
    | RTC_opt_cons a0 b0 c0 l0 r0 =>
        @RTC_trans A R a0 b0 c0
            (@RTC_step A R a0 b0 l0)
            (@RTC_unoptimize A R b0 c0 r0)
    end.


(* TODO: Definition lift_TC_to_RTC_opt *)

Definition RTC_opt_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : RTC_opt R a b)
    (P : relation A)
    (prefl : forall a0,
        a=a0 -> b=a0 -> P a0 a0)
    (pcons : forall a0 b0 c0, R a0 b0 -> RTC_opt R b0 c0 ->
        a=a0 -> b=c0 -> P a0 c0)
    : P a b
    :=
    match H in (RTC_opt _ a' b') return (a=a' -> b=b' -> P a' b') with
    | RTC_opt_refl a0             => prefl a0
    | RTC_opt_cons a0 b0 c0 l0 r0 => pcons a0 b0 c0 l0 r0
    end (eq_refl a) (eq_refl b).

(* TODO: Definition RTC_opt_fmap *)
(* TODO: Definition RTC_opt_join *)


(** *** Use [RTC_opt_case] directly on something of type [RTC].

    N.B., you can't use this via [case Rab using @RTC_optimize_case]
    because it has the "wrong" number of arguments for the [case]
    tactic. Instead, it should be used via [apply (RTC_optimize_case
    Rab P)]. *)
Definition RTC_optimize_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : R^* a b)
    (P : relation A)
    (prefl : forall a0,                               a=a0 -> b=a0 -> P a0 a0)
    (pcons : forall a0 b0 c0, R a0 b0 -> R^* b0 c0 -> a=a0 -> b=c0 -> P a0 c0)
    : P a b
    :=
    @RTC_opt_case A R a b (RTC_optimize H) P
        (fun x             Ea Eb => prefl x Ea Eb)
        (fun x y z rxy ryz Ea Eb =>
            pcons x y z rxy (RTC_unoptimize ryz) Ea Eb).


(** *** Use [RTC_opt_ind] directly on something of type [RTC].

    N.B., to make use of this use the tactic [induction Rab using
    @RTC_optimize_ind]. The [@] is necessary since we make [A] and
    [R] implicit arguments. *)
Definition RTC_optimize_ind
    {A : Type} {R : relation A} (P : relation A)
    (refl : forall a, P a a)
    (cons : forall a b c, R a b -> R^* b c -> P b c -> P a c)
    {a b} (rab : R^* a b)
    : P a b
    :=
    @RTC_opt_ind A R P
        refl
        (fun x y z rxy ryz pyz => cons x y z rxy (RTC_unoptimize ryz) pyz)
        a b (RTC_optimize rab).


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** The symmetric reflexive transitive closure of a relation. *)

(** This is the obvious definition of symmetric reflexive transitive
    closure; however, it gives a terrible inductive principle. The
    [RSTC_opt] closure gives a much better inductive principle, and
    perhaps the [R ^=] notation would be better reserved for that
    implementation. *)

Inductive RSTC {A:Type} (R : relation A) : relation A :=
    | RSTC_step  : forall a b,   R a b -> RSTC R a b
    | RSTC_refl  : forall a,     RSTC R a a
    | RSTC_sym   : forall a b,   RSTC R a b -> RSTC R b a
    | RSTC_trans : forall a b c, RSTC R a b -> RSTC R b c -> RSTC R a c
    .
Notation "R ^=" := (RSTC R) (at level 31, left associativity) :type_scope.
Implicit Arguments RSTC_step  [A R a b].
Implicit Arguments RSTC_refl  [A R].
Implicit Arguments RSTC_sym   [A R a b].
Implicit Arguments RSTC_trans [A R a b c].
Implicit Arguments RSTC_ind   [A R].

Add Parametric Relation A R : A (@RSTC  A R)
    reflexivity  proved by (@RSTC_refl  A R)
    symmetry     proved by (@RSTC_sym   A R)
    transitivity proved by (@RSTC_trans A R)
    as RSTC_rel.


Definition lift_RC_to_RSTC
    {A} {R : relation A} : forall {a b}, R^? a b -> R^= a b
    := @RC_ind A R (R^=)
        (fun a b H0 => @RSTC_step A R a b H0)
        (fun a      => @RSTC_refl A R a).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lift_RC_to_RSTC [[A][R] a b].


Definition lift_TC_to_RSTC
    {A} {R : relation A} : forall {a b}, R^+ a b -> R^= a b
    := @TC_ind A R (R^=)
        (fun a b H0              => @RSTC_step  A R a b H0)
        (fun a b c H0 IH0 H1 IH1 => @RSTC_trans A R a b c IH0 IH1).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lift_TC_to_RSTC [[A][R] a b].


Definition lift_RTC_to_RSTC
    {A} {R : relation A} : forall {a b}, R^* a b -> R^= a b
    := @RTC_ind A R (R^=)
        (fun a b H0              => @RSTC_step  A R a b H0)
        (fun a                   => @RSTC_refl  A R a)
        (fun a b c H0 IH0 H1 IH1 => @RSTC_trans A R a b c IH0 IH1).
(* BUG: Coq ignores our [{a b}] above... *)
Implicit Arguments lift_RTC_to_RSTC [[A][R] a b].


Definition RSTC_case
    {A : Type}
    {R : relation A}
    {a b : A}
    (H : R^= a b)
    (P : relation A)
    (pstep  : forall a0 b0, R   a0 b0 -> a=a0 -> b=b0 -> P a0 b0)
    (prefl  : forall a0,                 a=a0 -> b=a0 -> P a0 a0)
    (psym   : forall a0 b0, R^= a0 b0 -> a=b0 -> b=a0 -> P b0 a0)
    (ptrans : forall a0 b0 c0,
        R^= a0 b0 -> R^= b0 c0 -> a=a0 -> b=c0 -> P a0 c0)
    : P a b
    :=
    match H in (_^= a' b') return (a=a' -> b=b' -> P a' b') with
    | RSTC_step  a0 b0    r0    => pstep  a0 b0 r0
    | RSTC_refl  a0             => prefl  a0
    | RSTC_sym   a0 b0    r0    => psym   a0 b0 r0
    | RSTC_trans a0 b0 c0 l0 r0 => ptrans a0 b0 c0 l0 r0
    end (eq_refl a) (eq_refl b).

Fixpoint RSTC_fmap
    {A  : Type}
    {R  : relation A}
    (f  : A -> A)
    (Rf : forall  a b,  R   a b -> R   (f a) (f b))
    {a b} (r : R^= a b) {struct r}: R^= (f a) (f b) :=
        match r in (_^= a0 b0) return (R^= (f a0) (f b0)) with
        | RSTC_step  a0 b0    r0    => RSTC_step (Rf a0 b0 r0)
        | RSTC_refl  a0             => RSTC_refl (f a0)
        | RSTC_sym   b0 a0    r0    =>
            RSTC_sym (@RSTC_fmap A R f Rf b0 a0 r0)
        | RSTC_trans a0 b0 c0 l0 r0 =>
            RSTC_trans
                (@RSTC_fmap A R f Rf a0 b0 l0)
                (@RSTC_fmap A R f Rf b0 c0 r0)
        end.

Fixpoint RSTC_join
    {A : Type}
    {R : relation A}
    {a b} (r : (R^=)^= a b) {struct r}: R^= a b :=
        match r in (_^= a' b') return (R^= a' b') with
        | RSTC_step  a0 b0    r0    => r0
        | RSTC_refl  a0             => RSTC_refl a0
        | RSTC_sym   b0 a0    r0    =>
            RSTC_sym (@RSTC_join A R b0 a0 r0)
        | RSTC_trans a0 b0 c0 l0 r0 =>
            RSTC_trans
                (@RSTC_join A R a0 b0 l0)
                (@RSTC_join A R b0 c0 r0)
        end.

Fixpoint RSTC_converse
    {A : Type}
    {R : relation A}
    {a b} (r : R^= a b) {struct r}: (converse R)^= b a :=
        match r in (_^= a' b') return ((converse R)^= b' a') with
        | RSTC_step  a0 b0    r0    => RSTC_step (fliprel r0)
        | RSTC_refl  a0             => RSTC_refl a0
        | RSTC_sym   b0 a0    r0    =>
            @RSTC_sym A (converse R) a0 b0 (@RSTC_converse A R b0 a0 r0)
        | RSTC_trans a0 b0 c0 l0 r0 =>
            @RSTC_trans A (converse R) c0 b0 a0
                (@RSTC_converse A R b0 c0 r0)
                (@RSTC_converse A R a0 b0 l0)
        end.

Fixpoint RSTC_unconverse
    {A : Type}
    {R : relation A}
    {a b} (r : (converse R)^= a b) {struct r}: R^= b a :=
        match r in (_^= a' b') return (R^= b' a') with
        | RSTC_step  a0 b0    r0    => @RSTC_step A R b0 a0 (fliprel r0)
        | RSTC_refl  a0             => RSTC_refl a0
        | RSTC_sym   b0 a0    r0    =>
            @RSTC_sym A R a0 b0 (@RSTC_unconverse A R b0 a0 r0)
        | RSTC_trans a0 b0 c0 l0 r0 =>
            @RSTC_trans A R c0 b0 a0
                (@RSTC_unconverse A R b0 c0 r0)
                (@RSTC_unconverse A R a0 b0 l0)
        end.


Lemma RSTC_ind_prop_l : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_l : forall a b, R a b -> P a -> P b)
    (step_r : forall a b, R a b -> P b -> P a)
    , forall {a b}, R^= a b -> P a -> P b
with RSTC_ind_prop_r : forall
    {A : Type} {R : relation A} (P : A -> Prop)
    (step_l : forall a b, R a b -> P a -> P b)
    (step_r : forall a b, R a b -> P b -> P a)
    , forall {a b}, R^= a b -> P b -> P a.
Proof.
  intros A R P step_l step_r a b r p;
  apply (@RSTC_case A R a b r (fun _ b' => P b')); clear r; intros;
    [ apply (step_l a0 b0); [ exact H | insist p ]
    | insist p
    | apply (RSTC_ind_prop_r A R P step_l step_r a0 b0 H)
    ; insist p
    | apply (RSTC_ind_prop_l A R P step_l step_r b0 c0 H0)
    ; apply (RSTC_ind_prop_l A R P step_l step_r a0 b0 H)
    ; insist p
    ].
  intros A R P step_l step_r a b r p;
  apply (@RSTC_case A R a b r (fun a' _ => P a')); clear r; intros;
    [ apply (step_r a0 b0); [ exact H | insist p ]
    | insist p
    | apply (RSTC_ind_prop_l A R P step_l step_r a0 b0 H)
    ; insist p
    | apply (RSTC_ind_prop_r A R P step_l step_r a0 b0 H)
    ; apply (RSTC_ind_prop_r A R P step_l step_r b0 c0 H0)
    ; insist p
    ].
Defined.

(* TODO: RC (SC (TC R)) <-> RSTC R <->... only do hub/spokes! *)
(* TODO:

Lemma RSTC_wf
    : forall {A : Type} {R : relation A}
    , well_founded (RSC R) -> well_founded (R^=)

Lemma RSTC_inv_wf
    : forall {A : Type} {R : relation A}
    , well_founded (R^=) -> well_founded (STC R)
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** A flattened version of [RSTC], which can sometimes be easier
    to reason with (1) removes extraneous uses of [RSTC_refl], (2)
    removes extraneous uses of [RSTC_sym], and (3) linearizes the
    use of [RSTC_trans] to guarantee progress. *)
Inductive RSTC_opt {A:Type} (R : relation A) : relation A :=
    | RSTC_opt_refl : forall a, RSTC_opt R a a
    | RSTC_opt_cons : forall a b c,
        R a b -> RSTC_opt R b c -> RSTC_opt R a c
    | RSTC_opt_rcons : forall a b c,
        R b a -> RSTC_opt R b c -> RSTC_opt R a c.
Implicit Arguments RSTC_opt_refl  [A R].
Implicit Arguments RSTC_opt_cons  [A R a b c].
Implicit Arguments RSTC_opt_rcons [A R a b c].
Implicit Arguments RSTC_opt_ind   [A R].


Definition RSTC_opt_step
    {A : Type} {R : relation A} {a b : A}
    (r : R a b) : RSTC_opt R a b :=
        @RSTC_opt_cons A R a b b r (@RSTC_opt_refl A R b).

Definition RSTC_opt_rstep
    {A : Type} {R : relation A} {a b : A}
    (r : R b a) : RSTC_opt R a b :=
        @RSTC_opt_rcons A R a b b r (@RSTC_opt_refl A R b).

Fixpoint RSTC_opt_snoc
    {A : Type} {R : relation A} {a b c : A}
    (l : RSTC_opt R a b) (r : R b c) {struct l}: RSTC_opt R a c :=
        match l in (RSTC_opt _ a' b') return (b=b' -> RSTC_opt R a' c) with
        | RSTC_opt_refl a0 => fun Eb =>
            @rewrite A b a0 Eb (fun a' => RSTC_opt R a' c)
                (@RSTC_opt_step A R b c r)
        | RSTC_opt_cons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_cons A R a0 b0 c l0
                (@RSTC_opt_snoc A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => R b' c) r))
        | RSTC_opt_rcons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_rcons A R a0 b0 c l0
                (@RSTC_opt_snoc A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => R b' c) r))
        end (eq_refl b).

Fixpoint RSTC_opt_rsnoc
    {A : Type} {R : relation A} {a b c : A}
    (l : RSTC_opt R a b) (r : R c b) {struct l}: RSTC_opt R a c :=
        match l in (RSTC_opt _ a' b') return (b=b' -> RSTC_opt R a' c) with
        | RSTC_opt_refl a0 => fun Eb =>
            @rewrite A b a0 Eb (fun a' => RSTC_opt R a' c)
                (@RSTC_opt_rstep A R b c r)
        | RSTC_opt_cons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_cons A R a0 b0 c l0
                (@RSTC_opt_rsnoc A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => R c b') r))
        | RSTC_opt_rcons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_rcons A R a0 b0 c l0
                (@RSTC_opt_rsnoc A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => R c b') r))
        end (eq_refl b).

Fixpoint RSTC_opt_trans
    {A : Type} {R : relation A} {a b c : A}
    (l : RSTC_opt R a b) (r : RSTC_opt R b c) {struct l}: RSTC_opt R a c :=
        match l in (RSTC_opt _ a' b') return (b=b' -> RSTC_opt R a' c) with
        | RSTC_opt_refl a0 => fun Eb =>
            @rewrite A b a0 Eb (fun a' => RSTC_opt R a' c) r
        | RSTC_opt_cons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_cons A R a0 b0 c l0
                (@RSTC_opt_trans A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => RSTC_opt R b' c) r))
        | RSTC_opt_rcons a0 b0 c0 l0 r0 => fun Eb =>
            @RSTC_opt_rcons A R a0 b0 c l0
                (@RSTC_opt_trans A R b0 c0 c r0
                    (@rewrite A b c0 Eb (fun b' => RSTC_opt R b' c) r))
        end (eq_refl b).

Fixpoint RSTC_opt_sym
    {A : Type} {R : relation A} {a b : A}
    (r : RSTC_opt R a b) {struct r}: RSTC_opt R b a :=
        match r in (RSTC_opt _ a' b') return (RSTC_opt R b' a')
        with
        | RSTC_opt_refl  a0 =>
            @RSTC_opt_refl A R a0
        | RSTC_opt_cons  a0 b0 c0 l0 r0 =>
            @RSTC_opt_rsnoc A R c0 b0 a0 (@RSTC_opt_sym A R b0 c0 r0) l0
        | RSTC_opt_rcons a0 b0 c0 l0 r0 =>
            @RSTC_opt_snoc  A R c0 b0 a0 (@RSTC_opt_sym A R b0 c0 r0) l0
        end.

Add Parametric Relation A R : A (@RSTC_opt  A R)
    reflexivity  proved by (@RSTC_opt_refl  A R)
    symmetry     proved by (@RSTC_opt_sym   A R)
    transitivity proved by (@RSTC_opt_trans A R)
    as RSTC_opt_rel.


Fixpoint RSTC_optimize
    {A} {R : relation A} {a b} (r : R^= a b) {struct r} : RSTC_opt R a b
    :=
    match r in (_^= a' b') return (RSTC_opt R a' b') with
    | RSTC_step  a0 b0 r0       => @RSTC_opt_step A R a0 b0 r0
    | RSTC_refl  a0             => @RSTC_opt_refl A R a0
    | RSTC_sym   b0 a0    r0    =>
        @RSTC_opt_sym A R b0 a0
            (@RSTC_optimize A R b0 a0 r0)
    | RSTC_trans a0 b0 c0 l0 r0 =>
        @RSTC_opt_trans A R a0 b0 c0
            (@RSTC_optimize A R a0 b0 l0)
            (@RSTC_optimize A R b0 c0 r0)
    end.

Fixpoint RSTC_unoptimize
    {A} {R : relation A} {a b} (r : RSTC_opt R a b) {struct r} : R^= a b
    :=
    match r in (RSTC_opt _ a' b') return (R^= a' b') with
    | RSTC_opt_refl a0             => @RSTC_refl A R a0
    | RSTC_opt_cons a0 b0 c0 l0 r0 =>
        @RSTC_trans A R a0 b0 c0
            (@RSTC_step A R a0 b0 l0)
            (@RSTC_unoptimize A R b0 c0 r0)
    | RSTC_opt_rcons a0 b0 c0 l0 r0 =>
        @RSTC_trans A R a0 b0 c0
            (@RSTC_sym A R b0 a0 (@RSTC_step A R b0 a0 l0))
            (@RSTC_unoptimize A R b0 c0 r0)
    end.


(* TODO: Definition lift_RC_to_RSTC_opt *)
(* TODO: Definition lift_TC_to_RSTC_opt *)
(* TODO: Definition lift_RTC_to_RSTC_opt *)
(* TODO: Definition RSTC_opt_case *)
(* TODO: Definition RSTC_opt_fmap *)
(* TODO: Definition RSTC_opt_join *)
(* TODO: RC (SC (TC R)) <-> RSTC_opt R <->... *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
