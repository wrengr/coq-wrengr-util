(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Extensions for the [option] type.                       *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(* N.B., the [discriminate] tactic will handle these. Their term
    is the same as [diff_some_none] too, except it's eta-long in
    the hypothesis. *)

(** ** The [option] type *)

Definition diff_some_none {A:Type} (a:A) : Some a <> None :=
    eq_ind (Some a)
        (fun o : option A =>
            match o with
            | Some _ => True
            | None   => False
            end)
        I None.

Definition diff_none_some {A:Type} (a:A) : None <> Some a :=
    sym_not_eq (diff_some_none a).

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
