Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(*                     Result                                *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Inductive Result (A : Type) : Type := 
  | Bottom : Result A       (* divergence *)
  | Wrong  : Result A       (* runtime type error *)
  | Value  : A -> Result A.

Arguments Bottom {_}.
Arguments Wrong {_}.
Arguments Value  {_}.

(* Note: *failure* is the absence of any result in the set so is not included
   as a constructor in the result type.

   This design simplifies the operation of "One" --- we only need to find the
   result with the smallest label in the set, not the smallest label with a
   nonfailing result.

   The cost for not modelling failure is that it is difficult to say when one
   *set* of results approximates another. Labeled bottoms can disappear when
   given more fuel, because they could fail.  *)


Module R. 

Definition isWrong {A} (r : Result A) : bool := 
  match r with | Wrong => true | _ => false end.
Definition isBottom {A} (r: Result A) : bool := 
  match r with | Bottom => true | _ => false end.
Definition isValue {A} (r: Result A) : bool := 
  match r with | Value _ => true | _ => false end.

(* Parameterized by an approximation function for 
   the value type *)
Definition approx {A} (R : A -> A -> Prop) (r1 r2 : Result A) : Prop := 
  match r1 , r2 with 
  | Bottom , _ => True
  | Wrong , Wrong => True
  | Value w1 , Value w2 => R w1 w2
  | _ , _ => False
end.

Definition approxb {A} (R : A -> A -> bool) (r1 : Result A) (r2 : Result A) : bool := 
  match r1 , r2 with
  | Value w1 , Value w2 => R w1 w2
  | Wrong , Wrong => true
  | Bottom , _ => true
  | _ , _  => false
  end.

End R.

Lemma bottom_cases {A} (w : Result A) : w = Bottom \/ w <> Bottom.
Proof. destruct w. left. auto. right. done. right. done. Qed. 
