Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.List.


Class Container (M : Type -> Type) :=  {
  (* does the container hold the element *)
  In : forall {A}, A -> M A -> Prop;

  (* Property holds of all elements in the container *)
  Forall  : forall {A} (P : A -> Prop), M A -> Prop ;

  (* Property holds of some element in the container *)
  Exists :  forall {A} (P : A -> Prop), M A -> Prop ;

  (* Versions in Type *)
  ForallT : forall {A} (P : A -> Type), M A -> Type ;
  ExistsT :  forall {A} (P : A -> Type), M A -> Type ;

  Forall_forall : forall {A} (P : A -> Prop) (l : M A), 
      Forall P l <-> (forall x, In x l -> P x) ;
  Exists_exists : forall {A} (P : A -> Prop) (l : M A), 
      Exists P l <-> (exists x, In x l /\ P x) ;

 }.

Definition Forall2_any {M : Type -> Type}`{Container M} {A B:Type} : 
  forall (P : A -> B -> Prop), M A -> M B -> Prop :=
  fun P XS YS =>
      forall x y, In x XS -> In y YS -> P x y.

Definition Exists2_any {M : Type -> Type}`{Container M} {A B:Type} : 
  forall (P : A -> B -> Prop), M A -> M B -> Prop :=
  fun P XS YS =>
      exists x y, In x XS /\ In y YS /\ P x y.


Class PointwiseContainer (M : Type -> Type) `{Container M} := {
  (* Pointwise combination: prop only holds when the two 
     containers have the same structure, and for corresponding 
     elements *)
  Forall2 : forall {A B} (P : A -> B -> Prop), M A -> M B -> Prop ;

  (* Property holds of some corresponding pair of elements *)
  Exists2 : forall {A B} (P : A -> B -> Prop), M A -> M B -> Prop;

  Forall_Forall2 : forall {A} (P : A -> A -> Prop) (l:M A), 
       Forall (fun x => P x x) l <-> Forall2 P l l ;
  Exists_Exists2 : forall {A} (P : A -> A -> Prop) (l:M A), 
       Exists (fun x => P x x) l <-> Exists2 P l l 
}.

Fixpoint rec_list {A} (P : A -> Prop)  (rec : forall v, P v) 
  (vs : list A) : List.Forall P vs :=
  match vs with 
  | nil => Forall_nil _
  | cons w ws => @Forall_cons A P w ws (rec w) (rec_list P rec ws)
    end.
Fixpoint recT_list {A} (P : A -> Type)  (rec : forall v, P v) 
  (vs : list A) : List.ForallT P vs :=
  match vs with 
  | nil => ForallT_nil _
  | cons w ws => @ForallT_cons A P w ws (rec w) (recT_list P rec ws)
    end.



#[export] Instance Container_list : Container list :=
  { In := List.In;
    Forall  := List.Forall;
    Exists := List.Exists;
    ForallT := @List.ForallT;
    ExistsT := @List.ExistsT;
    Forall_forall := @List.Forall_forall;
    Exists_exists := @List.Exists_exists;
  }.

#[export] Instance PointwiseContainer_list : PointwiseContainer list := {
    Forall2 := List.Forall2;
    Exists2 := @List.Exists2;
    Forall_Forall2 := @List.Forall_Forall2;
    Exists_Exists2 := @List.Exists_Exists2
}.


Definition option_In {A : Type} (x:A) (o : option A) : Prop :=
  match o with 
  | Some y => x = y
  | None => False
  end.

Inductive When {A : Type} (P : A -> Prop) : option A -> Prop :=
  | When_Some : forall x, P x -> When P (Some x)
  | When_None : When P None.

Inductive WhenT {A : Type} (P : A -> Type) : option A -> Type :=
  | WhenT_Some : forall x, P x -> WhenT P (Some x)
  | WhenT_None : WhenT P None.

(* This version requires the shapes of the two options to match. *)
Inductive When2 {A : Type} (P : A -> A -> Prop) : option A -> option A -> Prop :=
  | When2_Some : forall x y, P x y -> When2 P (Some x) (Some y)
  | When2_None : When2 P None None.

Inductive option_Exists {A : Type} (P : A -> Prop) : option A -> Prop :=
  | Exists_Some : forall x, P x -> option_Exists P (Some x).
Inductive option_ExistsT {A : Type} (P : A -> Type) : option A -> Type :=
  | ExistsT_Some : forall x, P x -> option_ExistsT P (Some x).

#[export] Hint Constructors When WhenT When2 option_Exists option_ExistsT.

Lemma When_forall : forall {A} (P : A -> Prop) (l : option A), 
      When P l <-> (forall x, option_In x l -> P x).
Admitted.

Lemma option_Exists_exists : forall {A} (P : A -> Prop) (l : option A), 
      option_Exists P l <-> (exists x, option_In x l /\ P x).
Admitted.

Definition rec_option {A} (P : A -> Prop) (rec : forall (v:A), P v) 
  (vs : option A) : When P vs :=
    match vs with 
    | None => When_None P
    | Some w => When_Some P w (rec w)
    end.

Definition recT_option {A} (P : A -> Type) (rec : forall (v:A), P v) 
  (vs : option A) : WhenT P vs :=
    match vs with 
    | None => WhenT_None P
    | Some w => WhenT_Some P w (rec w)
    end.


#[export] Instance Container_option : Container option :=
 {  In := @option_In;
    Forall  := @When;
    Exists := @option_Exists;
    ForallT := @WhenT;
    ExistsT := @option_ExistsT;
    Forall_forall := @When_forall;
    Exists_exists := @option_Exists_exists;
  }. 

#[export] Instance PointwiseContainer_option : PointwiseContainer option.
Admitted.


