(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [fequal] tactic.

This implementation is inspired by <http://www.chargueraud.org/softs/tlc>
and so released under the LGPLv3. For more information about the
tactic and its uses, see the tutorial:

    <http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html>   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(** [fequal] improves upon the built-in [f_equal] tactic. For
    equations of the form [f a1...aN = f b1...bN] we directly apply
    the [f_equal]_N_ functions from [Coq.Init.Logic], thereby
    cleaning up the generated proofs. For equations between tuples,
    we fully unfold the tuple notation. And finally, we attempt to
    solve all branches with [reflexivity] and [congruence]. *)

Ltac fequal__core :=
    match goal with
    (* Clean up the proofs for functions. *)
    | |-  _ _            =  _ _            => apply f_equal;  [fequal__core|]
    | |-  _ _ _          =  _ _ _          => apply f_equal2; [fequal__core|]
    | |-  _ _ _ _        =  _ _ _ _        => apply f_equal3; [fequal__core|]
    | |-  _ _ _ _ _      =  _ _ _ _ _      => apply f_equal4; [fequal__core|]
    | |-  _ _ _ _ _ _    =  _ _ _ _ _ _    => apply f_equal5; [fequal__core|]
    (* Unfold tuple notations all the way (they're snoc-lists). *)
    | |- (_,_,_)         = (_,_,_)         => f_equal; [fequal__core|]
    | |- (_,_,_,_)       = (_,_,_,_)       => f_equal; [fequal__core|]
    | |- (_,_,_,_,_)     = (_,_,_,_,_)     => f_equal; [fequal__core|]
    | |- (_,_,_,_,_,_)   = (_,_,_,_,_,_)   => f_equal; [fequal__core|]
    | |- (_,_,_,_,_,_,_) = (_,_,_,_,_,_,_) => f_equal; [fequal__core|]
        (* ... *)
    (* Fall back to the built-in [f_equal] tactic. *)
    | |- _ => f_equal
    end.
    
Tactic Notation "fequal" :=
    fequal__core; first [ reflexivity | congruence | idtac ].
    (* TODO: use [eapply eq_refl] in lieu of [reflexivity]? *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
