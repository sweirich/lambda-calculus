Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Monad.

Import MonadNotation.
Open Scope monad_scope.

Inductive Comp (v : Type) : Type := 
  (* dynamic type error *)
  | c_wrong : Comp v

  (* multiple results *)
  | c_multi : list v -> Comp v

.

#[export] Hint Constructors Comp : core.

Arguments c_wrong {_}.
Arguments c_multi {_}.

(* ----------------------------------------------------------- *)

(* Comp is a monad *)

Definition pure_Comp {A} (x : A) : Comp A := c_multi (x :: nil).

Definition fmap_Comp {A B} (f : A -> B) (m : Comp A) : Comp B :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => c_multi (List.map f xs)
  end.

Definition append_Comp {A} (m : Comp A) (n : Comp A) : Comp A :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => match n with 
                 | c_wrong => c_wrong
                 | c_multi ys => c_multi (xs ++ ys)
                 end
  end.
      
Definition concat_Comp {A} (l : list (Comp A)) : Comp A :=
  fold_right append_Comp (c_multi nil) l.

Definition join_Comp {A} (m : Comp (Comp A)) : Comp A :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => concat_Comp xs
  end.
      
Definition bind_Comp {A B} (m : Comp A) (k : A -> Comp B) : Comp B :=
  join_Comp (fmap_Comp k m).

Definition ap_Comp {A B} (m : Comp (A -> B)) (n : Comp A) : Comp B :=
  match m with 
  | c_wrong => c_wrong
  | c_multi xs => match n with 
                 | c_wrong => c_wrong
                 | c_multi ys => c_multi (ap xs ys)
                 end
  end.


#[export] Instance Functor_Comp : Functor Comp.
split. exact @fmap_Comp. Defined.

#[export] Instance Applicative_Comp : Applicative Comp.
split. exact @pure_Comp. exact @ap_Comp. Defined.

#[export] Instance Monad_Comp : Monad Comp.
split. exact @pure_Comp. exact @bind_Comp. Defined.

#[export] Instance Alternative_Comp : Alternative Comp.
split. exact (fun t => @c_multi t nil). exact @append_Comp. Defined.


(* ------------------------------------------------------- *)

Lemma append_Comp_nil {A} : forall (x : Comp A), append_Comp x (c_multi nil) = x.
Proof.
  intros.
  destruct x; simpl; auto.
  rewrite app_nil_r.
  auto.
Qed.


Lemma monad_law {A} {y : Comp A} : y = x <- y;; ret x.
Admitted.

(* ------------------------------------------------------- *)

Definition Comp_In {A} (x : A) (u : Comp A) := 
  match u with 
  | c_wrong => False
  | c_multi vs => List.In x vs
  end.

Require Import structures.List.

Definition Exists {A} (P : A -> Prop) (u : Comp A) : Prop := 
  match u with 
  | c_wrong => False
  | c_multi vs => List.Exists P vs
  end.

Definition ExistsT {A} (P : A -> Type) (u : Comp A) : Type := 
  match u with 
  | c_wrong => False
  | c_multi vs => List.ExistsT P vs
  end.

Definition Exists2 {A B: Type} (P : A -> B -> Prop)  
  (u1 : Comp A) (u2: Comp B) : Prop :=
  match u1, u2 with 
  | c_multi vs1 , c_multi vs2 => List.Exists2 P vs1 vs2
  | _ , _ => False
  end.

Definition Forall {A} (P : A -> Prop) (u : Comp A) : Prop :=
  match u with 
  | c_wrong => True
  | c_multi vs => List.Forall P vs
  end.

Definition ForallT {A} (P : A -> Type) (u : Comp A) : Type :=
  match u with 
  | c_wrong => True
  | c_multi vs => List.ForallT P vs
  end.

Definition Forall2 {A B} (P : A -> B -> Prop) (u1 : Comp A) (u2 : Comp B) : Prop :=
  match u1, u2 with 
  | c_multi vs1 , c_multi vs2 => List.Forall2 P vs1 vs2
  | _ , _ => True
  end.
 

Definition Forall2_any {A B:Type} : 
  forall (P : A -> B -> Prop), Comp A -> Comp B -> Prop :=
  fun P XS YS =>
      forall x y, Comp_In x XS -> Comp_In y YS -> P x y.

Definition Exists2_any {A B:Type} : 
  forall (P : A -> B -> Prop), Comp A -> Comp B -> Prop :=
  fun P XS YS =>
      exists x y, Comp_In x XS /\ Comp_In y YS /\ P x y.
