(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Length indexed vectors *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Require Import fintype.

Inductive vec (A:Type) : nat -> Type := 
  | nil : vec A 0
  | cons : forall {n}, A -> vec A n -> vec A (S n)
.

Arguments nil {_}.
Arguments cons {_}{_}.

Fixpoint nth {A}{n} (v : vec A n) : fin n -> A := 
  match v in vec _ n return fin n -> A with 
        | nil => null
        | cons x xs => fun f => match f with 
                            | Some g => nth xs g
                            | None => x
                            end
        end.

(* 
Fixpoint eqb {A} {n} (eqA : A -> A -> bool) := 
  match n return vec _ n -> vec A n -> bool with 
  | 0 => fun v1 v2 => true
  | S m => fun v1 v2 => 
            match v1 , v2 in vec _ m with 
            | cons x xs , cons y ys => (eqA x y && eqb eqA xs ys)%bool
            | nil , nil => true
            | _ , _ => false
            end
  end.
*)

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Bind Scope vec_scope with vec.

Open Scope vec_scope.

Module VectorNotation.
Infix "::" := cons (at level 60, right associativity) : vec_scope.
Notation "[ ]" := nil (format "[ ]") : vec_scope.
Notation "[ x ]" := (cons x nil) : vec_scope.
(*
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : vec_scope.
*)
End VectorNotation.

