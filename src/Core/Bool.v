(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions to [Coq.Bool.Bool]                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(** Dependent case analysis with proof of equality for [bool]. But
    note that since we've moved the [b] argument you can't use the
    [inversion b using bool_depcaseeq] tactic, alas. Instead use
    [apply (bool_depcaseeq b P)].
    
    N.B., the [destruct_if remember] tactic can be used instead,
    and often does what we want by this term. However, the plain
    [destruct_if] tactic does not, since it doesn't give the equality
    proof.
    
    N.B., if you don't need the equality, note that you can do
    regular dependent inversion via [inversion b using bool_rect]. *)
Definition bool_depcaseeq
    (b  : bool)
    (P  : bool -> Type)
    (tt : b = true  -> P true)
    (ff : b = false -> P false)
    : P b :=
        match b as b0 return (b = b0 -> P b0) with
        | true  => tt
        | false => ff
        end (refl_equal b).


(** Dependent inversion with proof of equality for [bool]. *)
Definition bool_depinveq (b : bool) (P : bool -> Type) :=
    if b as b0 return (
        if b0
        then (b0 = true  -> P true)  -> P b0
        else (b0 = false -> P false) -> P b0)
    then fun tt => tt (refl_equal _)
    else fun ff => ff (refl_equal _).


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
Coq.Bool.Bool
    Is_true : bool -> Prop.
    
    diff_true_false (true = false) : False.
    diff_false_true (false = true) : False
    eq_true_false_abs (b:bool) (b = true) (b = false) : False
    
    not_true_is_false (b:bool) (b <> true) : b = false
    not_false_is_true (b:bool) (b <> false) : b = true
    
    eqb (a b:bool) : bool
    eqb_reflx (b:bool) : eqb b b = true
    eqb_prop (a b:bool) (eqb a b = true) : a = b.
    eqb_subst (P:bool -> Prop) (a b:bool) (eqb a b = true) (P a) : P b
    
    ...etc...

Coq.Bool.IfProp
    IfProp (A B:Prop) : bool -> Prop
    Iftrue : A -> IfProp A B true
    Iffalse : B -> IfProp A B false
    ...etc...
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
