(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions to [Coq.Bool.Sumbool]                        *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* For reference for ADTs like this, given [x : {A}+{B}] we have

[case x] |- C
    match x with
    | left  a => ?1 x a
    | right b => ?2 x b
    end
[case x] |- P x
    match x as x0 return (P x0) with
    | left  a => ?1 x a
    | right b => ?2 x b
    end
[destruct x] |- C
    match x with
    | left  a => ?1 a
    | right b => ?2 b
    end
[destruct x] |- P x
    match x as x0 return (P x0) with
    | left  a => ?1 a
    | right b => ?2 b
    end
[case_eq x] |- C
    match x as x0 return (x = x0 -> C) with
    | left  a => ?1 x a
    | right b => ?2 x b
    end (eq_refl x)
[case_eq x] |- P x
    match x as x0 return (x = x0 -> P x0) with
    | left  a => ?1 x a
    | right b => ?2 x b
    end (eq_refl x)
[inversion x] |- C
    let H :=
      match x with
      | left  a => (fun a0 : A => ?1 x a) a
      | right b => (fun b0 : B => ?2 x b) b
      end in
    H
[inversion x] |- P x
    let H :=
      match x with
      | left  a => (fun a0 : A => ?1 x a) a
      | right b => (fun b0 : B => ?2 x b) b
      end in
    H
[dependent inversion x] |- P x
    let H :=
      match x as x0 return (P x0) with
      | left  a => (fun a0 : A => ?1 x a) a
      | right b => (fun b0 : B => ?2 x b) b
      end in
    H
*)


(** Dependent case analysis with proof of equality for [sumbool].
    This is equivalent to using the [destruct x as [a|b] _eqn Ex]
    tactic, which is just like [case_eq x] except it doesn't pass
    the scrutinee along to the subgoals. Note that since we've moved
    the [x] argument you can't use the [inversion x using
    sumbool_depcaseeq] tactic, alas. Instead use
    [apply (sumbool_depcaseeq A B x P)].
    
    N.B., the [destruct_if remember] tactic can be used instead,
    and often does what we want by this term. However, the plain
    [destruct_if] tactic does not, since it doesn't give the equality
    proof.
    
    N.B., if you don't need the equality, note that you can do
    regular dependent inversion via [inversion x using sumbool_rect]. *)
Definition sumbool_depcaseeq
    {A B : Prop}
    (x  : {A} + {B})
    (P  : {A} + {B} -> Type)
    (ll : forall a, x = left  B a -> P (left  B a))
    (rr : forall b, x = right A b -> P (right A b))
    : P x :=
        match x as x0 return (x = x0 -> P x0) with
        | left  a => ll a
        | right b => rr b
        end (refl_equal x).


(** Dependent inversion with proof of equality for [sumbool]. *)
Definition sumbool_depinveq {A B : Prop} (x : {A}+{B}) (P : {A}+{B} -> Type) :=
    match x as x0 return (
        match x0 with
        | left  _ => (forall a, x0 = left  B a -> P (left  B a)) -> P x0
        | right _ => (forall b, x0 = right A b -> P (right A b)) -> P x0
        end)
    with
    | left  a => fun ll => ll a (refl_equal _)
    | right b => fun rr => rr b (refl_equal _)
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
Coq.Bool.Sumbool
    sumbool_of_bool (b:bool) : {b = true} + {b = false}
    bool_of_sumbool {A B:Prop} : {A} + {B} -> {b : bool | if b then A else B}
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
