Require Export ssreflect.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Require Coq.Sorting.Sorted.
Require Coq.Lists.List.

Require structures.Option.
Require Import structures.Sets.
Require Import structures.Monad.

(* autosubst2 "generated" syntax *)
Require Import fintype.
Require Import verse.syntax.

Set Implicit Arguments.

(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* "deriving" Eq for syntax                                  *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Module EqSyntax.

Module Op. 

Definition eqb (x y : Op) : bool :=
  match  x , y with
  | opAdd , opAdd => true
  | opGt , opGt => true
  | opInt , opInt => true
  | _ , _ => false
  end.

Lemma eqb_eq : forall x y, 
  eqb x y = true <-> x = y.
Proof.
  intros x y. split; destruct x; destruct y; simpl; done.
Qed. 

Lemma eqb_neq : forall x y, 
  eqb x y = false <-> x <> y.
Proof. 
  intros x y. split; destruct x; destruct y; simpl; done.
Qed.

End Op.

Fixpoint fin_eqb {n} := 
  match n return fin n -> fin n -> bool with 
  | 0 => fun x y => match x with end
  | S m => fun x y =>
      match x , y with 
      | Some x' , Some y' => fin_eqb x' y'
      | None , None => true
      | _ , _ => false
      end
  end.

Fixpoint Val_eqb {n} (x y : Val n) : bool := 
  let fix Vals_eqb {n} (xs ys : list (Val n)) := 
  match xs , ys with
  | cons x xs , cons y ys => (Val_eqb x y && Vals_eqb xs ys)%bool
  | nil , nil => true
  | _ , _ => false
  end in
  match x , y with 
  | var_Val f1 , var_Val f2 => fin_eqb f1 f2
  | Int n1 , Int n2 => Nat.eqb n1 n2
  | Prim o1 , Prim o2 => Op.eqb o1 o2
  | Tuple vs1 , Tuple vs2 => Vals_eqb vs1 vs2
  | Lam e1 , Lam e2 => Exp_eqb e1 e2
  | _ , _ => false
  end
with Exp_eqb {n} (x y : Exp n) : bool := 
  match x, y with 
  | Ret v1 , Ret v2 => Val_eqb v1 v2
  | App v1 u1 , App v2 u2 => Val_eqb v1 v2 && Val_eqb u1 u2
  | Seq e1 e2 , Seq e1' e2' => Exp_eqb e1 e1' && Exp_eqb e2 e2'
  | Unify v1 e2 , Unify v1' e2' => Val_eqb v1 v1' && Exp_eqb e2 e2'
  | Exists e1 , Exists e1' => Exp_eqb e1 e1'
  | Or e1 e2 , Or e1' e2' => Exp_eqb e1 e1' && Exp_eqb e2 e2'
  | Fail , Fail => true
  | One e1 , One e1' => Exp_eqb e1 e1'
  | All e1 , All e1' => Exp_eqb e1 e1'
  | _ , _ => false
  end.


End EqSyntax.
Import EqSyntax.


(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)
(* Syntactic sugar                                           *)
(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

Definition var_one {n : nat} : fin (S (S n)) := Some None. 
Definition var_two {n : nat} : fin (S (S (S n))) := Some (Some None). 

Definition bind1 {n} : Exp n -> Exp (S n) -> Exp n := 
  fun e1 e2 =>
    Exists (Seq (Unify (var_Val var_zero) (ren_Exp shift e1)) e2).

Definition bind2 {n} : Exp n -> Exp n -> Exp (S (S n)) -> Exp n := 
  fun e1 e2 e3 =>
    Exists (Seq (Unify (var_Val var_zero) (ren_Exp shift e1))
                (Exists (Seq (Unify (var_Val var_zero) (ren_Exp (shift >> shift) e2))
                          e3))).

Definition app {n} : Exp n -> Exp n -> Exp n := 
  fun e1 e2 => bind2 e1 e2 (App (var_Val var_one) (var_Val var_zero)).


Module VerseNotations.

Declare Scope verse_syntax.
Delimit Scope verse_syntax with Exp.
Open Scope verse_syntax.

Notation x0 := (var_Val var_zero).
Notation x1 := (var_Val var_one).
Notation x2 := (var_Val var_two).

Notation "⟨⟩" := (Tuple nil) : verse_syntax.

Infix ";;" := Seq (at level 100, right associativity) : verse_syntax.

Infix "≡" := Unify (at level 100, right associativity) : verse_syntax.

Coercion Ret : Val >-> Exp.

Infix "@" := app (at level 71, left associativity) : verse_syntax.

Definition ifthenelse {n} (e1 e2 e3 : Exp n) : Exp n := 
  One ( Or ( e1 ;; Lam ( ⟨⟩ ≡ x0 ;; ren_Exp shift e2 ) )
                 ( Lam ( ⟨⟩ ≡ x0 ;; ren_Exp shift e3 ) )) @ ⟨⟩.

Notation "e1 ?? e2 :: e3" := (ifthenelse e1 e2 e3) (at level 70) : verse_syntax.

End VerseNotations.
