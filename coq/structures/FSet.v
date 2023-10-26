Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Import structures.Sets.
Require Import structures.List.
Require Export lc.tactics.

Import SetNotations.

Inductive fset (A:Type) := FSet : (list A) -> fset A.
Arguments FSet {_}.

Definition In_fset {A: Type} (x: A) : fset A -> Prop := fun '(FSet X) => List.In x X.
Definition empty_fset {A:Type} : fset A := FSet nil.
Definition singleton_fset {A:Type} (x : A) : fset A := FSet (x :: nil).
Definition union_fset {A:Type} '(FSet x) '(FSet y) : fset A := FSet (x ++ y).
Definition nonempty_fset {A:Type} : fset A -> Prop := fun '(FSet xs) => xs <> nil.
Definition Forall_fset {A:Type} (f : A -> Prop) : (fset A) -> Prop := 
  fun '(FSet xs) => List.Forall f xs.
Definition ForallT_fset {A:Type} (f : A -> Type) : (fset A) -> Type := 
  fun '(FSet xs) => List.ForallT f xs.

Definition mem {A: Type} : fset A -> P A := fun xs => fun x => In_fset x xs.
Definition valid_mem {A} (V : fset A) : Prop :=
  match V with FSet XS => XS <> nil end.

Definition Included_fset {A:Type} : fset A -> fset A -> Prop :=
  fun x y => mem x ⊆ mem y.

Definition Equal_fset {A:Type} : fset A -> fset A -> Prop :=
  fun x y => mem x ≃ mem y.



Section FSetTheory.

Context {A : Type} {E : fset A}.

#[export] Instance Reflexive_Included_fset : Reflexive (@Included_fset A).
Admitted.
#[export] Instance Transitive_Included_fset : Transitive (@Included_fset A).
Admitted.


#[export] Instance Reflexive_Equal_fset : Reflexive (@Equal_fset A).
Admitted.
#[export] Instance Symmetric_Equal_fset : Symmetric (@Equal_fset A).
Admitted.
#[export] Instance Transitive_Equal_fset : Transitive (@Equal_fset A).
Admitted.


Lemma mem_one_inv : forall (h v : A),  h ∈ mem (singleton_fset v) -> h = v.
Proof. intros. cbn in H. destruct H; try done. Qed. 

Lemma nonnil_nonempty_mem : nonempty_fset E -> nonemptyT (mem E).
Proof. intros. destruct E; destruct l; cbv. done.
       econstructor. econstructor. eauto.
Qed.

Lemma In_Sub {x:A}{D : P A} : x ∈ D <-> mem (singleton_fset x) ⊆ D.
Proof. split. intros h y yIn. inversion yIn. subst; auto. inversion H. 
       intros h. cbv in h. specialize (h x). tauto.
Qed.


Lemma union_mem {E1 E2 : fset A} : mem (union_fset E1 E2) = (mem E1 ∪ mem E2).
Proof. unfold mem, union_fset. destruct E1 as [E1], E2 as [E2].
       eapply Extensionality_Ensembles.
       split.
       + intros x.
         induction E1. 
         ++ simpl. intro h. right. auto.
         ++ simpl. intro h. inversion h.
            left. unfold In. econstructor; eauto.
            apply IHE1 in H.
            inversion H. subst.
            left. unfold In. eapply in_cons. auto.
            subst. right. auto.
       + intros x.
         induction E1. 
         ++ intro h. inversion h. subst. done. subst. auto.
         ++ simpl. intro h. inversion h; subst.
            destruct H.  left. auto.
            lapply IHE1. intro h2. right. eauto.
            left. eauto. right. apply in_or_app. right. auto.
Qed.


Lemma singleton_mem : forall v : A,  ⌈ v ⌉ ⊆ mem (singleton_fset v).
Proof. intro v. econstructor. inversion H. done. Qed.

Lemma mem_singleton : forall v : A, mem (singleton_fset v) ⊆ ⌈ v ⌉.
Proof. intro v. cbv. intros. inversion H. subst. econstructor; eauto. done. Qed.

Lemma mem_singleton_eq {x:A} : mem (singleton_fset x) ≃ ⌈ x ⌉.
Proof. split; eauto using mem_singleton, singleton_mem. Qed.


Lemma Forall_mem {Pr} : Forall_fset Pr E -> Sets.Forall Pr (mem E).
Proof.
  destruct E as [V].
  induction V; intro h; intros y yIn. 
  inversion yIn. 
  inversion h. subst.
  inversion yIn. subst. auto. eapply IHV; eauto.
Qed.

Lemma Forall_sub_mem : forall  X Pr, 
    mem E ⊆ X -> 
    Sets.Forall Pr X ->
    Forall_fset Pr E.
Proof.
  destruct E as [D].
  induction D; intros X Pr SUB F.
  eauto.
  econstructor; eauto. simpl.
  unfold mem in SUB.
  econstructor. eapply F. eapply SUB. cbn. left; auto.
  eapply IHD with (X:=X); auto. intros x xIn. 
  unfold mem in xIn. eapply SUB; eauto. 
  cbn. right. eapply xIn.
Qed.

Lemma mem_In : forall (x:A), x ∈ mem E -> In_fset x E.
Proof. intros. destruct E as [l]. induction l. cbv in H. done.
       destruct H. subst. econstructor. auto. 
       simpl. right. eauto. Qed.


Lemma valid_mem_valid {V : fset A} : valid_mem V -> valid (mem V).
Proof.
  intros V1.
  destruct V; cbn in *.
  destruct l; try done.
  exists a. left; auto.
Qed.


(* A finite, inhabited subset of a valid set is valid *)
Lemma valid_sub_valid_mem {D : fset A}{X} :
 nonempty_fset D -> valid X -> mem D ⊆ X -> valid_mem D.
Proof.
  intros NE V1 S.
  inversion V1.
  induction D. try done. 
Qed.


Lemma valid_nonempty_mem : forall (V : fset A), 
      valid_mem V -> nonemptyT (mem V).
Proof. 
  intros. eapply valid_mem_valid. auto. Qed.

Lemma valid_mem_nonnil (V : list A) : valid_mem (FSet V) -> V <> nil.
Proof. intros h; auto. Qed.



Lemma In_mem_Included {d:A}{D} : 
    d ∈ D ->
    mem (singleton_fset d) ⊆ D.
Proof.
  intros.
  intros y yIn. destruct yIn. subst; auto. done.
Qed.

Lemma Included_mem_In {d:A}{D} : 
    mem (singleton_fset d) ⊆ D ->
    d ∈ D.

Proof.
  intros.
  specialize (H d). eapply H. 
  cbv. left; auto.
Qed.

Lemma mem_union_Included {D1 D2 : fset A}{w} : 
 mem D1 ⊆ w ->
 mem D2 ⊆ w ->
 mem (union_fset D1 D2) ⊆ w.
Proof. 
  intros.
  rewrite union_mem. intros y yIn. induction yIn; eauto.
Qed.

Lemma nonempty_fset_union1 {E1 E2 : fset A} : 
  nonempty_fset E1 ->
  nonempty_fset (union_fset E1 E2).
Proof.
  intros. destruct E1. destruct E2. cbv in H. cbn.
  destruct l. done.  done.
Qed.

Lemma mem_union_valid {D1 D2 : fset A}: 
  valid_mem D1 ->
  valid_mem D2 ->
  valid_mem (union_fset D1 D2).
Proof. intros.
 unfold valid_mem in *. 
Admitted.

Lemma singleton_valid (x : A) :
 valid_mem (singleton_fset x).
Admitted.


Lemma fset_induction (P : fset A -> Prop) : 
       P empty_fset -> 
       (forall (a:A) (l : fset A), P l -> P (union_fset (singleton_fset a) l)) -> 
       forall f, P f.
Admitted.


End FSetTheory.

#[export] Hint Resolve nonempty_fset_union1 : core.
#[export] Hint Resolve mem_one_inv nonnil_nonempty_mem In_Sub : core.
#[export] Hint Resolve singleton_mem mem_singleton singleton_valid
  valid_mem_valid valid_sub_valid_mem valid_nonempty_mem valid_mem_valid : core. 
#[export] Hint Resolve In_mem_Included Included_mem_In mem_union_Included mem_union_valid : core.
