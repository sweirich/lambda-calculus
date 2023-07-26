Require Export ssreflect.
Require Import ssrbool.

Require Export Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Program.Equality.  (* for dependent induction *) 
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.EquivDec.


From Coq Require Import Eqdep_dec.


(* Representing sets by their characteristic functions. 

   It includes notations, Relation classes instances, and a bridge to 
   finite sets represented by lists.

*)

(* Inspired by 
   https://github.com/jsiek/denotational_semantics/agda/SetsAsPredicates.agda *)

Definition P := fun A => A -> bool.

Section BasicOps.

Variable A : Type.
Context `{EQ : EqDec A eq}.

Definition In (x : A) (X : P A) := X x = true.

Definition Included (X : P A) (Y : P A) := forall x, In x X -> In x Y.

Definition Union (X : P A) (Y : P A) := fun x => X x || Y x.

Definition Intersection (X : P A) (Y : P A) := fun x => X x && Y x.

Definition Singleton (x : A) : P A := 
  fun y => if y == x then true else false.

Definition Same_set (X : P A) (Y : P A) := 
  Included X Y /\ Included Y X.

Definition Empty_set := fun (x:A) => false.

Inductive Inhabited (B:P A) : Prop :=
    Inhabited_intro : forall x:A, In x B -> Inhabited B.

Lemma eq_dec_refl (x : A) : EQ x x = left eq_refl.
  destruct (EQ x x) as [|[]]; trivial.
  f_equal.
  now apply K_dec_type with (P := fun prf => prf = eq_refl).
  done.
Qed.

(*  
Lemma eq_dec_refl (x:A) :
  x == x = left eq_refl.
Proof.
  destruct (x == x) as [|[]]; trivial.
  f_equal.
  now apply K_dec_type with (P := fun prf => prf = eq_refl).
  done.
Qed.
*)

End BasicOps.

Declare Scope set_scope.

Arguments In {_}.
Arguments Included {_}.
Arguments Union {_}.
Arguments Intersection {_}.
Arguments Same_set {_}.
Arguments Singleton {_}{_}{_}.
Arguments Empty_set {_}.


Module SetNotations. 
  Notation "∅"  := Empty_set : set_scope.
  Notation "x ∈ s"  := (In x s) (at level 90) : set_scope.
  Notation "⌈ x ⌉" := (Singleton x) : set_scope.
  Infix "⊆"  := Included (at level 90) : set_scope.
  Infix "∪"  := Union (at level 90) : set_scope.
  Infix "∩"  := Intersection (at level 90) : set_scope.
  Infix "≃"  := Same_set (at level 90) : set_scope.
End SetNotations. 


Import SetNotations.
Open Scope set_scope.

(* Test cases for notations *)
Check (1 ∈ ⌈ 1 ⌉).
Check (∅ ⊆ ⌈ 1 ⌉).
Check (∅ ∪ ⌈ 1 ⌉).
Check (∅ ∪ ⌈ 1 ⌉ ≃ ∅).

Lemma in_singleton {A:Type}{_:EqDec A eq} {v : A} : 
  v ∈ ⌈ v ⌉.
Proof. cbv. rewrite eq_dec_refl. reflexivity. Qed.

#[export] Hint Resolve in_singleton : core.

(* A proposition that a set is inhabited. Due to the restrictions
   of Coq, the witness cannot be extracted except to produce a 
   proof of a different proposition. *)
Definition nonempty {A} : P A -> Prop := @Inhabited A.

(* This is in Type so that we can extract the witness *)
Definition nonemptyT {A} (s : P A) : Type :=
   {x : A & x ∈ s}.

Arguments nonempty {_}.
Arguments nonemptyT {_}.

Lemma nonemptyT_nonempty {A}{S : P A} : 
  nonemptyT S -> nonempty S.
Proof. intros h. destruct h. econstructor; eauto. Qed.


(* Relation classes *)

#[export] Instance Refl_Incl {A} : Reflexive (@Included A).
intros x. unfold Included. eauto. Qed.

#[export] Instance Trans_Incl {A} : Transitive (@Included A).
intros x y z S1 S2. unfold Included. intro w. eauto. Qed.

#[export] Instance Equivalence_Same_set {A} : Equivalence (@Same_set A) .
constructor.
- unfold Reflexive, Same_set, Included in *. tauto. 
- unfold Symmetric, Same_set, Included in *. tauto.
- unfold Transitive, Same_set, Included in *. intros x y z [h1 h2] [k1 k2]. 
  split; eauto.
Qed.

(* Proper instances: allow rewriting *)

#[export] Instance Union_Included_Proper {A} : Proper (@Included A ==> @Included A ==> @Included A) Union.
Proof. intros a1 a2 Ea b1 b2 Eb.
unfold Included, Union, In in *. intros x h.
destruct (a1 x) eqn:E. apply Ea in E; rewrite E. done.
simpl in h. eapply Eb in h. rewrite h.
rewrite Bool.orb_true_r. done.
Qed.

#[export] Instance Union_Same_set_Proper {A} : Proper (@Same_set A ==> @Same_set A ==> @Same_set A) Union.
Proof. intros a1 a2 Ea b1 b2 Eb.
unfold Same_set in Ea. unfold Same_set in Eb. move: Ea => [Sa1 Sa2]. move: Eb => [Sb1 Sb2].
split. rewrite -> Sa1. rewrite -> Sb1. reflexivity. rewrite -> Sa2. rewrite -> Sb2. reflexivity. Qed.

#[export] Instance Included_Same_set_Proper {A} : Proper (@Same_set A ==> @Same_set A ==> Logic.iff) Included.
Proof. intros a1 a2 Ea. intros b1 b2 Eb.
       unfold Same_set in Ea. unfold Same_set in Eb. move: Ea => [Sa1 Sa2]. move: Eb => [Sb1 Sb2].
       split. intro h. transitivity a1; auto. transitivity b1; auto. 
       intros h. transitivity a2; auto. transitivity b2; auto. Qed.

#[export] Instance In_Proper {A} : Proper (Logic.eq ==> @Same_set A ==> Logic.iff) (@In A).
Proof. 
  intros b1 b2 ->. intros a1 a2 [E1 E2]. 
  split; intro x; eauto.
Qed.


(* Facts about union *)

Lemma sub_union_left {A} (X Y : P A) : X ⊆ (X ∪ Y).
Proof. intros x I.  cbv. rewrite I. done. Qed.

Lemma sub_union_right {A} (X Y : P A) : Y ⊆ (X ∪ Y).
Proof. intros x I. cbv. rewrite I. destruct (X x); done. Qed.

#[export] Hint Resolve sub_union_left sub_union_right : core.

Lemma union_idem {A:Type}{E : P A} : (E ∪ E) ≃ E.
Proof.
  unfold Union, In.
  split. intros x h. destruct (E x) eqn:Ex. auto.  
  unfold In in h. rewrite Ex in h. done.
  intros x h. unfold In. rewrite h. done.
Qed.

#[export] Hint Resolve union_idem : core.



(* Finite lists `mem` as sets *)

Require Coq.Lists.List.

Section Mem.

Variable A : Type.
Context `{EQ : EqDec A eq}.

Definition mem : list A -> P A :=
  fun ls x => List.existsb (equiv_decb x) ls.

Lemma mem_one_inv : forall (h v : A),  
 h ∈ mem (v :: nil) -> h = v.
Proof. 
  intros. cbv in H.
  destruct (EQ h v). done. done.
Qed. 

(* E≢[]⇒nonempty-mem *)
Lemma nonnil_nonempty_mem : forall{E : list A}, 
    E <> nil -> nonemptyT (mem E).
Proof. intros. destruct E; cbv. done.
       exists a. rewrite eq_dec_refl. done.
Qed.

Lemma mem_head a (V : list A) :
   a ∈ mem (a :: V).
Proof. 
  unfold mem.
  cbv. rewrite eq_dec_refl.
  reflexivity.
Qed.

Lemma mem_cons d a (V : list A) :
    d ∈ mem V ->
    d ∈ mem (a :: V).
Proof. 
  unfold mem. unfold In.
  intro h.
  cbn.
  destruct (d ==b a). auto.
  apply h.
Qed.

Lemma union_mem {E1 E2 : list A} : mem (E1 ++ E2) ≃ (mem E1 ∪ mem E2).
Proof. unfold mem. 
       split.
       + intros x.
         induction E1. 
         ++ simpl. intro h. unfold Union. simpl. auto.
         ++ simpl. intro h.
            unfold In, Union in *.
            destruct (x ==b a) eqn:E. 
            reflexivity.
            rewrite IHE1; eauto.
       + intros x.
         induction E1. 
         ++ intro h. inversion h. done. 
         ++ simpl.
            unfold In, Union in *.
            intro h. destruct (x ==b a) eqn:E. done.
            rewrite IHE1; eauto.
Qed.

Lemma singleton_mem : forall v : A,  ⌈ v ⌉ ≃ mem (v :: nil).
Proof. split.
       + intros x Ix.
         unfold mem, In, Singleton in *.
         simpl.
         unfold equiv_decb.
         destruct (x == v) eqn:E; try done.  
       + unfold mem, In, Singleton in *.
         simpl.
         unfold equiv_decb.
         intros x Ix.
         destruct (x == v) eqn:E; try done.  
Qed.    

Lemma mem_In : forall (x:A) l, x ∈ mem l -> List.In x l.
Proof. intros. induction l. cbv in H. done.
       unfold mem, In in H. simpl in H.
       destruct (x==b a) eqn:E.
       econstructor. admit.
       simpl. right. eauto. 
Admitted.
   

End Mem.

#[export] Hint Resolve mem_head mem_cons mem_one_inv mem_In : core.

(* ----------------------------------------- *)


Definition Forall  : forall {A} (Pr : A -> Prop), P A -> Prop := 
  fun {A} Pr p => forall x, In x p -> Pr x.

Definition Exists : forall {A} (Pr : A -> Prop), P A -> Prop :=
  fun {A} Pr p => exists x, In x p /\ Pr x.

Definition  ForallT : forall {A} (Pr : A -> Type), P A -> Type := 
  fun {A} Pr p => forall x, In x p -> Pr x.

Definition ExistsT :  forall {A} (Pr : A -> Type), P A -> Type :=
  fun {A} Pr p => { x & (In x p * Pr x)%type }.

Definition Forall_forall : forall {A} (Pr : A -> Prop) (l : P A), 
      Forall Pr l <-> (forall x, In x l -> Pr x).
Proof. intros. unfold Forall. reflexivity. Qed.

Definition Exists_exists : forall {A} (Pr : A -> Prop) (l : P A), 
      Exists Pr l <-> (exists x, In x l /\ Pr x).
Proof. intros. unfold Exists. reflexivity. Qed.



(* ----------------------------------------- *)

Lemma Forall_mem {A}{V : list A}`{EQ : EqDec A eq}{Pr} : 
  List.Forall Pr V -> Forall Pr (mem _ V).
Proof.
  induction V; intro h; intros y yIn. 
  inversion yIn. 
  inversion h. subst.
  inversion yIn. subst. auto. eapply IHV; eauto.
Admitted.

Lemma Forall_sub_mem : forall {A}{D:list A}`{EQ : EqDec A eq}{Pr}{X}, 
    mem _ D ⊆ X -> 
    Forall Pr X ->
    List.Forall Pr D.
Proof.
  intros A D.
  induction D; intros X Pr SUB F.
  eauto.
  econstructor; eauto. admit.
Admitted.

