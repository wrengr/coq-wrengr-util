(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions to [Wf]                                      *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Accessability implies irreflexivity. *)
Lemma Acc_irrefl :
    forall {A : Type} (R : A -> A -> Prop) {a : A}, Acc R a -> ~R a a.
Proof.
  intros; induction H as [a _ H0]; intro H1; exact (H0 a H1 H1).
Qed.


(* The [red] serves to [unfold not] *)
(** Every well-founded relation is irreflexive. *)
Corollary wf_R_irrefl :
    forall {A : Type} {R : A -> A -> Prop}, well_founded R ->
    forall {a : A}, ~R a a.
Proof. red; intros; exact (@Acc_irrefl A R a (H a) H0). Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* The [destruct 1] serves to [intro E; rewrite E] but is much cleaner. It inlines the [eq_ind_r] to [eq_ind] to [eq_rect] definitions, and then evaluates away a case-of-constructor. *)
Lemma irrefl_implies_neq :
    forall {A} (R : A -> A -> Prop),
    (forall {a : A}, ~R a a) -> 
    forall {a b : A}, R a b -> a <> b.
Proof. intros; red; destruct 1; exact (H a H0). Qed.

Corollary wf_R_implies_neq :
    forall {A} (R : A -> A -> Prop), well_founded R ->
    forall {a b}, R a b -> a <> b.
Proof. eauto using @irrefl_implies_neq, @wf_R_irrefl. Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)