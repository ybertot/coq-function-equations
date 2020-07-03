Require Import FunInd.

(* Version 1 *)

Inductive B:=
| B0 | B1 | B2 .

Inductive A :=
| N : (B*nat) -> (list A) -> A.

Definition isB2 (a : A) :=
  match a with N (B2, _) _ => true | _ => false end.

Function is_valid a: bool :=
  match a with
  | N (B0,_) nil => true
  | N (B1,_) (d1::d2::_) => andb (andb (isB2 d1) (isB2 d2))
      (andb (is_valid d2) (is_valid d1))
  | _ => false
  end.

(*
is_valid is defined
is_valid is recursively defined (decreasing on 1st argument)
Warning: Cannot define graph(s) for is_valid [funind-cannot-define-graph,funind]
Warning: Cannot build inversion information [funind-cannot-build-inversion,funind]
*)


(* Version 2 *)

Inductive C :=
| Nc : B -> (list C) -> C.

(* Error: Anomaly "Cannot find a way to prove recursive property." Please report at http://coq.inria.fr/bugs/. *)
Function is_validc a: bool :=
  match a with
  | Nc B0 nil => true
  | Nc B1 ((Nc B2 _ as d1)::(Nc B2 _ as d2)::_) => andb (is_validc d2) (is_validc d1)
  | _ => false

  end.
