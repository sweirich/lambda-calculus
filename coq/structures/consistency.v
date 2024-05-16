Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.
Require Import structures.FSet.

Class Consistency (A : Type) : Type := 
  { Consistent : A -> A -> Prop ;
    Inconsistent : A -> A -> Prop ;
  }.

Section List.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_list := List.Forall2 f.
Definition Inconsistent_list := fun XS YS => 
  length XS <> length YS \/ List.Exists2 g XS YS.

End List.

#[export] Instance Consistency_list { A : Type } `{ Consistency A } : Consistency (list A) := 
  { Consistent := Consistent_list (f := Consistent) ;
    Inconsistent := Inconsistent_list (g := Inconsistent) ;
  }.

Section FSet.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Definition Consistent_fset := fun '(FSet XS) '(FSet YS) => List.Forall2_any f XS YS.
Definition Inconsistent_fset := fun '(FSet XS) '(FSet YS) => List.Exists2_any g XS YS.

End FSet.

#[export] Instance Consistency_fset { A : Type}  `{ Consistency A } : Consistency (fset A) := 
  { Consistent := Consistent_fset (f := Consistent) ;
    Inconsistent := Inconsistent_fset (g := Inconsistent) ;
  }.

Section Computations.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Inductive ConsistentComp  : Comp A -> Comp A -> Prop :=
  | cc_wrong : ConsistentComp c_wrong c_wrong
  | cc_multi : forall AS BS, 
      List.Forall2 f AS BS ->
      ConsistentComp (c_multi AS) (c_multi BS).

Inductive InconsistentComp : Comp A -> Comp A -> Prop :=
  | i_wrong_multi : forall AS, InconsistentComp c_wrong (c_multi AS)
  | i_multi_wrong : forall AS, InconsistentComp (c_multi AS) c_wrong
  | i_multi : forall AS BS, 
      (length AS <> length BS \/ List.Exists2 g AS BS) -> 
      InconsistentComp (c_multi AS) (c_multi BS).

End Computations.

#[export] Instance Consistency_Comp {A:Type} `{Consistency A} : Consistency (Comp A) := 
  { Consistent := ConsistentComp (f:=Consistent) ; Inconsistent := InconsistentComp (g := Inconsistent) }.

#[export] Hint Constructors ConsistentComp InconsistentComp : core.


Import SetNotations.

(* Two sets are consistent if all of their elements 
   are consistent. *)
Definition ConsistentSets {A:Type} `{Consistency A} V1 V2 := 
    forall x y, x ∈ V1 -> y ∈ V2 -> Consistent x y.

Definition InconsistentSets {A:Type} `{Consistency A} V1 V2 := 
  exists x, exists y, (x ∈ V1) /\ (y ∈ V2) /\ (Inconsistent x y).

#[export] Instance Consistency_P {A:Type} `{Consistency A} : Consistency (P A) :=
   { Consistent := ConsistentSets ; Inconsistent := InconsistentSets }.


(* ------------------------------------------------- *)

Class ConsistencyTheory (A : Type) `{Consistency A} := 
  {  exclusive : forall x y, Consistent x y -> Inconsistent x y -> False ;
     decidable : forall x y, {Consistent x y} + {Inconsistent x y}
  }.

Definition Exclusive {A} (f g : A -> A -> Prop) :=  forall x y, f x y -> g x y -> False .
Definition Decidable {A} (f g : A -> A -> Prop) :=  forall x y, {f x y} + {g x y}.


Section List.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Lemma exclusive_list :
  Exclusive f g -> 
  Exclusive (@Consistent_list A f) (@Inconsistent_list A g).
Proof.
  intros efg. intros x y FF. 
  induction FF; intros EG; inversion EG; eauto.
  - inversion H.
  - move: (Forall2_length FF) => eq. 
    simpl in H0. rewrite eq in H0. done.
  - inversion H0; subst. eauto.
    eapply IHFF. right. eauto.
Qed.

Lemma exclusive_list2: forall l, 
  List.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@Consistent_list A f) l YS -> (@Inconsistent_list A g) l YS -> False.
Proof.
  induction l; intros h YS h1 h2.
  - inversion h1. subst. inversion h2. done.
    inversion H.
  - inversion h1. subst. inversion h. subst.
    specialize (IHl H4 l' H3).
    destruct h2. unfold Consistent_list in h1. 
    apply Forall2_length in h1. done.
    inversion H; subst; eauto.
    eapply IHl. right. auto.
Qed.    

Lemma decidable_list : 
  Decidable f g ->
  Decidable (@Consistent_list A f) (@Inconsistent_list A g).
Proof.
  intros dfg. intros x.
  induction x; intros y; destruct y.
  - left; eauto. econstructor.
  - right; eauto. left. done.
  - right; eauto. left. done.
  - destruct (IHx y). destruct (dfg a a0).
    left. econstructor; eauto.
    right. right. econstructor; eauto.
    right. destruct i. left. eauto. right. eauto.
Qed.

End List.

#[export] Instance Consistency_list_theory { A : Type } `{ ConsistencyTheory A } : ConsistencyTheory (list A) := 
  { exclusive := exclusive_list (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_list (f := Consistent)(g := Inconsistent) decidable ;
  }.

Section FSet.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.


Lemma exclusive_fset :
  Exclusive f g ->
  Exclusive (@Consistent_fset A f) (@Inconsistent_fset A g).
Proof.
  intros efg. intros x. destruct x as [x].
  induction x; intros y FF EG; destruct y as [y]; destruct y; 
    unfold Consistent_fset, List.Forall2_any in FF;
    unfold Inconsistent_fset, List.Exists2_any in EG.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h1.
  - destruct EG as [x0 [y0 [h1 [h2 _]]]]. inversion h2.
  - destruct EG as [x0 [y0 [h1 [h2 gg]]]]. 
    specialize (FF x0 y0 h1 h2).
    eapply efg; eauto.
Qed.

Lemma decidable_fset :
  Decidable f g ->
  Decidable (@Consistent_fset A f) (@Inconsistent_fset A g).
Proof.
  intros dfg. intros x. destruct x as [x].
  induction x; intros y; destruct y as [y].
     unfold Consistent_fset, List.Forall2_any;
     unfold Inconsistent_fset, List.Exists2_any.
  - left. done.
  - destruct (IHx (FSet y)). 
    + simpl in c. simpl.
      induction y. unfold List.Forall2_any in c.
      left. intros x0 y0 h1 h2. inversion h2. 
      have CE: (List.Forall2_any f x y). { intros x0 y0 h1 h2. eapply c; eauto. simpl. eauto. }
      specialize (IHy CE). destruct IHy.
      ++ destruct (dfg a a0).
         left.
         { intros x0 y0 i1 i2.
           destruct i1; destruct i2; subst. 
           -- auto.
           -- apply f0; eauto. simpl; auto.
           -- apply c; eauto. simpl; auto.
           -- apply CE; eauto.
         }
         right.
         exists a. exists a0. simpl. split; auto.
      ++ right. destruct e as [x0 [y0 [h1 [h2 h3]]]].
         exists x0. exists y0. simpl. eauto.
    + right. destruct i as [x0 [y0 [i1 [i2 h]]]]. 
      exists x0. exists y0. 
      repeat split; try right; auto. 
Qed.

Lemma exclusive_fset2: forall l, 
  Forall_fset (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@Consistent_fset A f) l YS -> (@Inconsistent_fset A g) l YS -> False.
Proof.
  intro l. destruct l. 
  move=> h YS. destruct YS as [l']. simpl in *.
  move: h l'.
  induction l; intros h l' h1 h2;  unfold List.Forall2_any in h1; destruct h2 as [x0 [y0 [I0 [I1 IC]]]]. 
  - inversion I0.
  - inversion h. subst. 
    specialize (IHl H2).
    rewrite Forall_forall in H2.
    destruct I0; subst.
    -- specialize (h1 x0 y0 ltac:(left; auto) I1).
       eauto.
    -- eapply (IHl l').
       intros x1 y1 I3 I4. eapply  h1. right; eauto. eauto.
       exists x0. exists y0. repeat split; eauto.
Qed. 

(* Consistency is reflexive ?? *)

End FSet.

#[export] Instance ConsistencyTheory_fset { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (fset A) := 
  { exclusive := exclusive_fset (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_fset (f := Consistent)(g := Inconsistent) decidable ;
  }.

Section Computations.

Context 
  { A : Type }
  { f : A -> A -> Prop }
  { g : A -> A -> Prop }.

Lemma exclusive_Comp : 
  Exclusive f g ->
  Exclusive (@ConsistentComp A f) (@InconsistentComp A g).
Proof.
  intros efg x y CC IC.
  induction CC; inversion IC.
  eapply exclusive_list; eauto.
Qed.


Lemma exclusive_Comp2: forall l, 
  Comp.Forall (fun x : A => forall y : A, f x y -> g x y -> False) l ->
  forall YS, (@ConsistentComp A f) l YS -> (@InconsistentComp A g) l YS -> False.
Proof.
  destruct l. intros.
Admitted.

Lemma decidable_Comp : 
  Decidable f g ->
  Decidable (@ConsistentComp A f) (@InconsistentComp A g).
Proof.
  intros dfg x y.
  destruct x eqn:EX; destruct y eqn:EY.
  - left; econstructor.
  - right; econstructor.
  - right; econstructor.
  - destruct (decidable_list dfg l l0).
    left; econstructor; eauto.
    right; econstructor; eauto.
Qed.


End Computations.

#[export] Instance ConsistencyTheory_Comp { A : Type}  `{ ConsistencyTheory A } : ConsistencyTheory (Comp A) := 
  { exclusive := exclusive_Comp (f := Consistent)(g := Inconsistent) exclusive ;
    decidable := decidable_Comp (f := Consistent)(g := Inconsistent) decidable ;
  }.
