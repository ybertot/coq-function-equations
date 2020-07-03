Require Import Recdef FunInd List Bool Lia.

Inductive B:=
| B0 | B1 | B2 .

Inductive A :=
| N : (B*nat) -> (list A) -> A.


Section some_context.

Variables b1 b2 b3 : A -> bool.

(* This is the function you wish to define. *)
Fixpoint is_valid0 (t : A) : bool :=
  match t with
    N((B0 | B1), _) nil => true
  | N((B0 | _), _) ((N (B2, _) _ as t1) :: (N (B2, _) _ as t2) :: nil) =>
    b1 t && is_valid0 t1 && is_valid0 t2
  | N(B2, _) ((N (B1, _) _ as t1) :: (N (B1, _) _ as t2) :: nil) =>
    b2 t && is_valid0 t1 && is_valid0 t2
  | N((B1 | B2), _) ((N(B0, _) _ as t1):: (N(B2, _) _ as t2) :: nil) =>
    b3 t && is_valid0 t1 && is_valid0 t2
  | _ => false
  end.

(* This use of Function is unsatisfactory, because none of the
  attached lemmas are generated. *)
Function is_valid1 (t : A) : bool :=
  match t with
    N((B0 | B1), _) nil => true
  | N((B0 | _), _) ((N (B2, _) _ as t1) :: (N (B2, _) _ as t2) :: nil) =>
    b1 t && is_valid1 t1 && is_valid1 t2
  | N(B2, _) ((N (B1, _) _ as t1) :: (N (B1, _) _ as t2) :: nil) =>
    b2 t && is_valid1 t1 && is_valid1 t2
  | N((B1 | B2), _) ((N(B0, _) _ as t1):: (N(B2, _) _ as t2) :: nil) =>
    b3 t && is_valid1 t1 && is_valid1 t2
  | _ => false
  end.

(* The next three test functions each correspond to one
   pattern-matching rule of is_valid0. *)
Definition rule1_test (t : A) : bool :=
  match t with
    N((B0 | _), _) ((N (B2, _) _ as t1) :: (N (B2, _) _ as t2) :: nil) => true
  | _ => false
  end.

Definition rule2_test (t : A) : bool :=
  match t with
    N(B2, _) ((N (B1, _) _ as t1) :: (N (B1, _) _ as t2) :: nil) => true
  | _ => false
  end.

Definition rule3_test (t : A) : bool :=
  match t with
    N((B1 | B2), _) ((N(B0, _) _ as t1):: (N(B2, _) _ as t2) :: nil) => true
  | _ => false
  end.

(* Now there is a single pattern-matching rule for all the cases with two
   subtrees, the body if each of the pattern-matching rule is in the
   'then' part of an if-then-else construct.  Function is happy with it
   and can detect that the function is structurally recursive. *)
Function is_valid2 (t : A) : bool :=
  match t with
    N((B0 | B1), _) nil => true
  | N((B0 | _), _) (t1 :: t2 :: nil) =>
    if rule2_test t then
      b1 t && is_valid1 t1 && is_valid1 t2
    else if rule3_test t then
      b2 t && is_valid1 t1 && is_valid1 t2
    else if rule3_test t then
           b3 t && is_valid1 t1 && is_valid1 t2
    else false
  | _ => false
  end.

(* Second solution. We devise an inductive type that captures exactly the
  cases of the intended function. *)

Inductive valid_internal_patterns : Type :=
| Case1 | Case2 (t1 t2 : A) | Case3 (t1 t2 : A) | Case4 (t1 t2 : A) | Default.

(* The function is_valid_cases computes in which case each of the tree
  will fall.  At the same time, it selects the subtrees that will be used
  in recursive calls. *)
Definition is_valid_cases (t : A) : valid_internal_patterns :=
  match t with
    N((B0 | B1), _) nil => Case1
  | N(B0, _) ((N (B2, _) _ as t1) :: (N (B2, _) _ as t2) :: nil) => Case2 t1 t2
  | N(B2, _) ((N (B1, _) _ as t1) :: (N (B1, _) _ as t2) :: nil) => Case3 t1 t2
  | N((B1 | B2), _) ((N(B0, _) _ as t1):: (N(B2, _) _ as t2) :: nil) => Case4 t1 t2
  | _ => Default
  end.

(* Now, Function will use a proof-based termination criterion instead of
  structural recursion.  Here, I choose to use size (number of N nodes) *)
Fixpoint size (t : A) :=
  match t with
    N _ l => 1 + fold_right (fun x n => Nat.add (size x) n) 0 l
  end.

Function is_valid3 (t : A) {measure size} : bool :=
  match is_valid_cases t with
    Case1 => true
  | Case2 t1 t2 => b1 t && is_valid3 t1 && is_valid3 t2
  | Case3 t1 t2 => b2 t && is_valid3 t1 && is_valid3 t2
  | Case4 t1 t2 => b3 t && is_valid3 t1 && is_valid3 t2
  | _ => false
  end.
(* Il y a 6 appels récursifs, donc 6 buts pour prouver que la mesure décroit,
  mais toutes ces preuves sont résolues automatiquement par la même tactique.
*)
all: destruct t as [[[ | | ] ?] [ | [[[ | | ] ?] ?] [ | [[[ | | ] ?] ?] [ | [[[ | | ] ?] ?]]]]]; simpl; try discriminate;
(intros t1 t2 ceq; injection ceq; intros ceq1 ceq2; rewrite <- ?ceq1, <- ?ceq2; simpl; lia).
Defined.


