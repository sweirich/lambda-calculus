Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Definition In {A : Type} (x:A) (o : option A) : Prop :=
  match o with 
  | Some y => x = y
  | None => False
  end.

Inductive Forall {A : Type} (P : A -> Prop) : option A -> Prop :=
  | Forall_Some : forall x, P x -> Forall P (Some x)
  | Forall_None : Forall P None.

Inductive ForallT {A : Type} (P : A -> Type) : option A -> Type :=
  | ForallT_Some : forall x, P x -> ForallT P (Some x)
  | ForallT_None : ForallT P None.

(* This version requires the shapes of the two options to match. *)
Inductive Forall2 {A : Type} (P : A -> A -> Prop) : option A -> option A -> Prop :=
  | Forall2_Some : forall x y, P x y -> Forall2 P (Some x) (Some y)
  | Forall2_None : Forall2 P None None.

Inductive Exists {A : Type} (P : A -> Prop) : option A -> Prop :=
  | Exists_Some : forall x, P x -> Exists P (Some x).
Inductive ExistsT {A : Type} (P : A -> Type) : option A -> Type :=
  | ExistsT_Some : forall x, P x -> ExistsT P (Some x).

#[export] Hint Constructors Forall ForallT Forall2 Exists ExistsT : core.

Lemma Forall_forall : forall {A} (P : A -> Prop) (l : option A), 
      Forall P l <-> (forall x, In x l -> P x).
Proof.
  intros. split. 
  intro h. inversion h. subst. intros y IN. inversion IN. subst. auto.
  intros y IN.  inversion IN.
  intro h. 
  destruct l. econstructor. eapply h. econstructor. eauto.
Qed.

Lemma Exists_exists : forall {A} (P : A -> Prop) (l : option A), 
      Exists P l <-> (exists x, In x l /\ P x).
Proof.
  intros. split.
  intro h; inversion h. subst. inversion h. subst.
  exists x. split; eauto. econstructor.
  intro h. destruct h as [x [xIn Px]]. 
  destruct l. inversion xIn. subst. econstructor; eauto.
  inversion xIn.
Qed.

Definition rec_option {A} (P : A -> Prop) (rec : forall (v:A), P v) 
  (vs : option A) : Forall P vs :=
    match vs with 
    | None => Forall_None P
    | Some w => Forall_Some P w (rec w)
    end.

Definition recT_option {A} (P : A -> Type) (rec : forall (v:A), P v) 
  (vs : option A) : ForallT P vs :=
    match vs with 
    | None => ForallT_None P
    | Some w => ForallT_Some P w (rec w)
    end.


Definition liftA1 {A B} (f : A -> B) : option A -> option B := 
  fun x => 
    match x with 
    | Some s1 => Some (f s1)
    | _ => None
    end.
Definition liftA2 {A B C} (f : A -> B -> C) : option A -> option B -> option C := 
  fun x y => 
    match x , y with 
    | Some s1 , Some s2 => Some (f s1 s2)
    | _ , _ => None
    end.

Definition bind {A B} (m : option A) (k : A -> option B) := 
  match m with 
  | Some s => k s 
  | None => None
  end.
