(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions for the [nat] type, arithmetical and otherwise. *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.BoolEq.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Arithmetic on [nat] *)

(** This was added in 8.3 under the name [plus_Snm_nSm]. *)
Definition plus_Sn_m_n_Sm (n m : nat) : S n + m = n + S m :=
    eq_ind_r (fun n' => n' = n + S m) (plus_n_Sm n m) (plus_Sn_m n m).

Definition plus_Snm_n_Sm (n m : nat) : S (n + m) = n + S m :=
    nat_ind (fun n' => S (n' + m) = n' + S m)
        (refl_equal (S m)) (fun n' IHn' => f_equal S IHn') n.

Definition plus_Snm_Sn_m (n m : nat) : S (n + m) = S n + m :=
    trans_equal (plus_Snm_n_Sm n m) (sym_eq (plus_Sn_m_n_Sm n m)).

Definition lt_Sn_lt (n m : nat) (H : S n < m) : n < m :=
    lt_S_n n m (lt_S (S n) m H).

Definition le_plus (n m : nat) : n <= m+n :=
    nat_ind
        (fun m' => n <= m'+n)
        (le_refl n)
        (fun m' IHm' =>
            le_trans n (m' + n) (S m' + n) IHm' (le_n_Sn (m' + n)))
        m.

(* TODO: Is this wise? *)
Hint Resolve
    plus_Sn_m_n_Sm plus_Snm_n_Sm plus_Snm_Sn_m lt_Sn_lt le_plus
    :arith.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Ordered arithmetic on [nat] *)

(** These two are defined for [min] but not for [max], in Coq 8.2; they were added to [Coq.Arith.MinMax] in 8.3. *)

Definition max_0_l (n : nat) : max 0 n = n := max_r 0 n (le_O_n n).
Hint Resolve max_0_l :arith.

Definition max_0_r (n : nat) : max n 0 = n := max_l n 0 (le_O_n n).
Hint Resolve max_0_r :arith.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Lemma mult_gt_1 : forall i j : nat, i>1 -> j>1 -> i*j>1.
Proof. intros; destruct i; simpl; auto with arith. Qed.
Hint Resolve mult_gt_1 :arith.

Lemma mult_gt_0 : forall i j : nat, i>0 -> j>0 -> i*j>0.
Proof. intros; destruct i; simpl; auto with arith. Qed.
Hint Resolve mult_gt_0 :arith.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** A much needed generalization of [lt_0_neq]. *)
Definition lt_neq {i j : nat} (LT : i < j) : i <> j :=
    match LT in (_ <= j0) return (i <> j0) with
    | le_n        => n_Sn i
    | le_S j' LT' =>
        fun (E : i = S j') =>
            nat_ind (fun j0 => ~ S j0 < j0)
                (le_Sn_0 1)
                (fun j'' IHj'' H => IHj'' (gt_S_le (S (S j'')) j'' H))
                j'
                (eq_ind i (fun i0 => i0 < j') LT' (S j') E)
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Induction and elimination. *)

(** Dependent case analysis for [nat]. Because sometimes you want
    to rewrite the goal with the actual value of [n], but you don't
    need the power of recursion from [nat_rect]. The reason we've
    defined this is that you can't use the [dependent inversion]
    tactic when the [nat] you're interested in doesn't appear overtly
    in the goal; but you can do [inversion n using nat_depcase]. *)
Definition nat_depcase
    (P : nat -> Type)
    (zero : P O)
    (succ : forall (n : nat), P (S n))
    (n : nat)
    : P n :=
        match n as n0 return P n0 with
        | O   => zero
        | S n => succ n
        end.


(** Dependent case analysis with proof of equality for [nat]. But
    note that since we've moved the [n] argument you can't use the
    [inversion n using nat_depcaseeq] tactic, alas. Instead use
	[apply (nat_depcaseeq n P)]. *)
Definition nat_depcaseeq
    (n : nat)
    (P : nat -> Type)
    (zero : forall (En : n = O), P O)
    (succ : forall (m : nat) (En : n = S m), P (S m))
    : P n :=
        match n as n0 return (n = n0 -> P n0) with
        | O   => zero
        | S m => succ m
        end (refl_equal n).

(** Dependent inversion for [nat]. *)
Definition nat_depinv (n : nat) (P : nat -> Type) :=
    match n as n0 return (
        match n0 with
        | O   => P O -> P n0
        | S _ => (forall n', P (S n')) -> P n0
        end)
    with
    | O    => fun zero => zero
    | S n' => fun succ => succ n'
    end.

(** Dependent inversion with proof of equality for [nat]. *)
Definition nat_depinveq (n : nat) (P : nat -> Type) :=
    match n as n0 return (
        match n0 with
        | O   => (n0 = O -> P 0) -> P n0
        | S _ => (forall n', n0 = S n' -> P (S n')) -> P n0
        end)
    with
    | O    => fun zero => zero    (refl_equal _)
    | S n' => fun succ => succ n' (refl_equal _)
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Decidable equality. *)

(* For [eq_nat_dec] needed by ListSet, see [Coq.Arith.Peano_dec]. *)
(*
Variable n m : nat.
    ...EqNat     eq_nat_decide : {eq_nat n m} + {~ eq_nat n m}
    ...Peano_dec eq_nat_dec    : {n = m} + {n <> m}
    ...Peano_dec dec_eq_nat    : (n = m) \/ (n <> m)
    
    ...EqNat     eq_eq_nat        (n = m)               : eq_nat n m
    ...EqNat     eq_nat_eq        (eq_nat n m)          : n = m
    
    ...EqNat     beq_nat_eq       (true = beq_nat n m)  : n = m.
    ...EqNat     beq_nat_true     (beq_nat n m = true)  : n = m.
    ___                           (n=m)                 : beq_nat n m = true
    ...EqNat     beq_nat_false    (beq_nat n m = false) : n<>m
    ___          nat_eq_beq_false (n<>m)                : beq_nat n m = false


Coq.Bool.BoolEq
    Variable A   : Set.
    Variable beq : A -> A -> bool.
    Variable x y : A.
    
    Variable   beq_refl                           : true = beq x x
    Variable   beq_eq           (true = beq x y)  : x = y
    Definition beq_eq_true      (x = y)           : true = beq x y
    Definition beq_eq_not_false (x = y)           : false <> beq x y (*??*)
    Definition beq_false_not_eq (false = beq x y) : x <> y
    Definition not_eq_false_beq (x <> y)          : false = beq x y
    
    Definition eq_dec           : {x = y} + {x <> y}
    Definition exists_beq_eq    : {b : bool | b = beq x y}


(* To symmetrize things so they're pretty; also unfolding opaque things *)
Section BoolEq_symm.
    Context  {A : Set}.
    Context  {beq : A -> A -> bool}.
    Variable beq_refl : forall x,   beq x x = true.
    Variable beq2eq   : forall x y, beq x y = true -> x = y.
    
    Definition eq2beq (x y : A) (E : x = y) : beq x y = true :=
        eq_ind x (fun y0 => beq x y0 = true) (beq_refl x) y E.
    
    Definition beq2neq (x y : A) (B : beq x y = false) : x<>y :=
        fun E:x=y =>
            eq_ind true (fun b0 => b0 <> false)
                (eq_ind true (fun b => if b then True else False) I false)
                (beq x y) (sym_eq (eq2beq x y E)) B.
    
    Definition neq2beq (x y : A) (N : x <> y) : beq x y = false :=
        (if beq x y as b0 return (b0<>true -> b0=false)
        then fun N1 => False_ind (true=false) (N1 (eq_refl true))
        else fun _  => eq_refl false)
            (fun B  => N (beq2eq x y B)).
End BoolEq_symm.

Section BoolEq_class.
    (* BUG: the [A] and [beq] aren't generalizable, so we can't actually use this class. *)
    Class BoolEq (A : Set) (beq : A -> A -> bool) :=
        { beq_refl : forall x,   beq x x = true
        ; beq2eq   : forall x y, beq x y = true  -> x = y
        ; beq2neq  : forall x y, beq x y = false -> x<>y
        ; eq2beq   : forall x y, x = y  -> beq x y = true
        ; neq2beq  : forall x y, x <> y -> beq x y = false
        }.
End BoolEq_class.
*)

(** The converse to [beq_nat_false]. *)
Lemma nat_eq_beq_false : forall {m n : nat} (E : m <> n), beq_nat m n = false.
Proof.
  (* N.B., Coq 8.3 automatically [intros] whatever's to the left of [:] *)
  intro m; induction m; intro n; destruct n; intros;
    [ elimtype False; apply E; reflexivity
    | reflexivity
    | reflexivity
    | simpl; apply IHm; unfold not; intro; apply E; apply f_equal; assumption
    ].
Qed.


(* TODO: how can we extend this to all setoid Boolean-equivalences? *)
(** Convert all hypotheses of the form [beq_nat i j = b] ---where
    [b] is known, and for symmetric hypotheses as well--- into
    Leibniz equalities. *)
Tactic Notation "beq_nat_hyps" :=
    repeat
        match goal with
        H : ?T |- _ =>
            match T with
            | beq_nat _ _ = true  => apply beq_nat_true  in H
            | beq_nat _ _ = false => apply beq_nat_false in H
            | true  = beq_nat _ _ => apply beq_nat_eq    in H
            | false = beq_nat _ _ =>
                (symmetry in H; apply beq_nat_false in H)
            end
        end.

(* TODO: a version which doesn't destroy the old hypotheses. BUG: this one doesn't work.
Tactic Notation "beq_eq_nat_hyps" :=
    repeat
        match goal with
        H : ?T |- _ =>
            match T with
            | beq_nat ?i ?j = true  => pose (beq_nat_true  i j H); revert H
            | beq_nat ?i ?j = false => pose (beq_nat_false i j H); revert H
            | true  = beq_nat ?i ?j => pose (beq_nat_eq    i j H); revert H
            | false = beq_nat ?i ?j =>
                let E := fresh "E" in
                ( pose H as E
                ; symmetry in E
                ; apply beq_nat_false in E
                ; revert H)
            end
        end; intros.
*)


(** A helper lemma for evaluating [beq_nat] in conditionals.

    N.B., the [destruct_if remember] tactic followed by [beq_nat_hyps]
    will usually handle whatever you needed [apply if_beq_nat] to
    solve. However, in practice, sometimes the details can be a bit
    hairier. *)
Definition if_beq_nat
    (m n : nat)
    {A : Type}
    {P : A -> Type}
    (x y : A)
    (tt : m=n  -> P x)
    (ff : m<>n -> P y)
    : P (if beq_nat m n then x else y)
    := 
    let b := beq_nat m n in
    match b as b0 return (b = b0 -> P (if b0 then x else y)) with
    | true  => fun Eb => tt (beq_nat_true  m n Eb)
    | false => fun Eb => ff (beq_nat_false m n Eb)
    end (refl_equal b).


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
Coq.Bool.Zerob
    zerob (n:nat) : bool := match n with | O => true | S _ => false end.
    
    zerob_true_intro  (n:nat) (n = 0)           : zerob n = true
    zerob_true_elim   (n:nat) (zerob n = true)  : n = 0
    zerob_false_intro (n:nat) (n <> 0)          : zerob n = false
    zerob_false_elim  (n:nat) (zerob n = false) : n <> 0


Coq.Bool.BoolEq (* TODO: usable for generalizing [if_beq_nat]? *)

    beq_eq_true
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, x = y -> true = beq x y

    beq_eq_not_false
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, x = y -> false <> beq x y

    beq_false_not_eq
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, false = beq x y -> x <> y

    exists_beq_eq
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, {b : bool | b = beq x y}

    not_eq_false_beq
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, x <> y -> false = beq x y

    eq_dec
        (A:Set)
        (beq : A -> A -> bool)
        (beq_refl : forall x:A, true = beq x x)
        (beq_eq : forall x y:A, true = beq x y -> x = y)
        : forall x y:A, {x = y} + {x <> y}
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
Coq.Init.Peano
    IsSucc (n:nat) : Prop := match n with | O => False | S p => True end.

    O_S (n : nat) (0 = S n) : False
    
Coq.Arith.EqNat
    eq_nat (n m : nat) : Prop  ""propositional equality""
    eq_nat_refl   (n : nat) : eq_nat n n
    
    eq_eq_nat     (n m : nat) (n = m) : eq_nat n m
    eq_nat_eq     (n m : nat) (eq_nat n m) : n = m
    eq_nat_is_eq  (n m : nat) : eq_nat n m <-> n = m
    eq_nat_decide (n m : nat) : {eq_nat n m} + {~ eq_nat n m}
    eq_nat_elim   (n:nat) (P:nat -> Prop) (P n) (m:nat) (H:eq_nat n m) : P m
    
    
    beq_nat (n m : nat) : bool  ""boolean equality""
    beq_nat_refl (n : nat) : true = beq_nat n n
    
    beq_nat_eq    (n m : nat) (true = beq_nat n m) : n = m (* Definition *)
    beq_nat_true  (n m : nat) (beq_nat n m = true) : n = m (* Lemma *)
    beq_nat_false (n m : nat) (beq_nat x y = false) (x=y) : False (* Lemma *)

Coq.Arith.Le
    le_refl  (n : nat) : n <= n
    le_trans (n m p : nat) (n <= m) (m <= p) : n <= p
    le_antisym (n m : nat) (n <= m) (m <= n) : n = m
    
    le_O_n    (n : nat)                : 0 <= n
    le_Sn_O   (n : nat)   (S n <= 0)   : False
    le_n_O_eq (n : nat)   (n <= 0)     : 0 = n
    
    le_n_S    (n m : nat) (n <= m)     : S n <= S m
    le_n_Sn   (n : nat)                : n <= S n
    le_Sn_le  (n m : nat) (S n <= m)   : n <= m
    le_S_n    (n m : nat) (S n <= S m) : n <= m
    le_Sn_n   (n : nat)   (S n <= n)   : False
    
    le_pred_n (n : nat)                : pred n <= n
    le_pred   (n m : nat) (n <= m)     : pred n <= pred m
    
    le_elim_rel
        (P : nat -> nat -> Prop)
        (forall (p : nat), P 0 p)
        (forall (p q : nat) (p <= q) (P p q), P (S p) (S q))
        (n m : nat)
        (n <= m)
        : P n m

Coq.Arith.Max
    max_case:     forall (n m : nat) (P : nat -> Type), P n -> P m -> P (n ^^ m)
    
    max_SS:       forall n m,           S (n ^^ m) = S n ^^ S m
    max_assoc:    forall m n p,      m ^^ (n ^^ p) = m ^^ n ^^ p
    max_comm:     forall n m,               n ^^ m = m ^^ n
    max_identity: forall n,                 0 ^^ n = n
    max_refl:     forall n,                 n ^^ n = n
    max_l:        forall n m,   m <= n  ->  n ^^ m = n
    max_r:        forall n m,   n <= m  ->  n ^^ m = m
    le_max_l:     forall n m,   n <= n ^^ m
    le_max_r:     forall n m,   m <= n ^^ m
    
???
    S_pred:      forall n m,    m < n    ->  n = S (pred n)
    pred_Sn:     forall n,                   n = pred (S n)
    lt_pred:     forall n m,  S n <   m  ->       n < pred m
    lt_pred_n_n: forall n,      0 <   n  ->  pred n < n
    
    le_lt_or_eq: forall n m,  n <= m  ->  n < m \/ n = m
    lt_le_weak:  forall n m,  n < m   ->  n <= m
    le_or_lt:    forall n m,  n <= m \/ m < n
    
    le_ind:
      forall (n : nat) (P : nat -> Prop),
      P n ->
      (forall m,  n <= m  ->  P m  ->  P (S m))
      -> forall n0,  n <= n0  ->  P n0
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
