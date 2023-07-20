(* Properties and definitions about Environments: i.e. association lists from
   atoms (Metalib) to values. *)

Require Import ssreflect.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.

Require Import Metalib.Metatheory.

Require structures.Container.

Open Scope list_scope.

Section Definitions.

Polymorphic Variable A : Type.

Polymorphic Definition Env := list (atom * A).
   
Polymorphic Fixpoint access (d : A) (e : Env) (x : atom) : A :=
  match e with 
  | nil => d
  | cons ( y , p ) e => 
      match x == y with
      | left _ => p
      | right _ => access d e x 
      end
  end.

Polymorphic Fixpoint update (x : atom) (D : A) (ρ : Env) : Env :=
  match ρ with 
  | nil => nil
  | cons (y, E) ρ => match (x == y) with
                 | left _ => cons (x, D) ρ
                 | right _ => cons (y, E) (update x D ρ)
                 end
  end.

Polymorphic Inductive ForallT (f : A -> Type) : list (atom * A) -> Type :=
  | ForallT_nil :
      ForallT f nil
  | ForallT_cons : forall x a E,
      ForallT f E ->
      x `notin` (dom E) ->
      f a ->
      ForallT f (x ~ a ++ E).

Polymorphic Inductive ForallT2 {B} (f : A -> B -> Type) : list (atom * A) -> list (atom * B) -> Type :=
  | ForallT2_nil :
      ForallT2 f nil nil
  | ForallT2_cons : forall x a1 a2 E1 E2,
      ForallT2 f E1 E2 ->
      x `notin` (dom E1) ->
      f a1 a2 ->
      ForallT2 f (x ~ a1 ++ E1) (x ~ a2 ++ E2).

Polymorphic Inductive ExistsT (f : A -> Type) : list (atom * A) -> Type :=
  | ExistsT_cons1 : forall x a E,
      f a ->
      ExistsT f (x ~ a ++ E)
  | ExistsT_cons2 : forall x a E,
      ExistsT f E ->
      ExistsT f (x ~ a ++ E).

Polymorphic Inductive ExistsT2 {B} (f : A -> B -> Type) : list (atom * A) -> list (atom * B) -> Type :=
  | ExistsT2_cons1 : forall x a1 a2 E1 E2,
      f a1 a2 ->
      ExistsT2 f (x ~ a1 ++ E1)(x ~ a2 ++ E2)
  | ExistsT2_cons2 : forall x a1 a2 E1 E2,
      ExistsT2 f E1 E2 ->
      ExistsT2 f (x ~ a1 ++ E1)(x ~ a2 ++ E2).

(* NOTE:  ForallT (fun _ => True) is isomorphic to "uniq" *)

Polymorphic Fixpoint map2 (f : A -> A -> A) ρ1 ρ2 := 
  match ρ1, ρ2 with 
  | cons (x1 , v1) e1 , cons (x2 , v2) e2 =>
      match (x1 == x2) with
      | left _ => x1 ~ (f v1 v2) ++ map2 f e1 e2
      | right _ => map2 f e1 e2
      end
  | _ , _ => nil
  end.

End Definitions.

Fixpoint In_rng {A : Type} (d : A) (e : Env A)  : Prop := 
  match e with 
  | nil => False 
  | cons ( y , p ) e => d = p \/ In_rng d e
  end.

Inductive Forall {A} (f : A -> Prop) : list (atom * A) -> Prop :=
  | Forall_nil :
      Forall f nil
  | Forall_cons : forall x a E,
      Forall f E ->
      x `notin` (dom E) ->
      f a ->
      Forall f (x ~ a ++ E).

Inductive Forall2 {A B : Type} 
  (f : A -> B -> Prop) : list (atom * A) -> list (atom * B) -> Prop :=
  | Forall2_nil :
      Forall2 f nil nil
  | Forall2_cons : forall x a1 a2 E1 E2,
      Forall2 f E1 E2 ->
      x `notin` (dom E1) ->
      f a1 a2 ->
      Forall2 f (x ~ a1 ++ E1) (x ~ a2 ++ E2).

Inductive Exists {A : Type} (f : A -> Prop) : list (atom * A) -> Prop :=
  | Exists_cons1 : forall x a E,
      f a ->
      Exists f (x ~ a ++ E)
  | Exists_cons2 : forall x a E,
      Exists f E ->
      Exists f (x ~ a ++ E).

Inductive Exists2 {A B} (f : A -> B -> Prop) : list (atom * A) -> list (atom * B) -> Prop :=
  | Exists2_cons1 : forall x a1 a2 E1 E2,
      f a1 a2 ->
      Exists2 f (x ~ a1 ++ E1)(x ~ a2 ++ E2)
  | Exists2_cons2 : forall x a1 a2 E1 E2,
      Exists2 f E1 E2 ->
      Exists2 f (x ~ a1 ++ E1)(x ~ a2 ++ E2).


Arguments access {_}.
Arguments update {_}.
Arguments map2 {_}.
Arguments Forall {_}.
Arguments ForallT {_}.
Arguments ForallT2 {_}{_}.
Arguments Forall2 {_}{_}.
Arguments ExistsT {_}.
Arguments ExistsT2 {_}{_}.
Arguments Exists2 {_}{_}.

#[export] Hint Constructors Forall ForallT ForallT2 Forall2 
  Exists ExistsT ExistsT2 Exists2 : core.

Lemma Forall_forall {A} (P : A -> Prop) (l : Env A) :
      Forall P l -> (forall x, In_rng x l -> P x).
Proof. induction l.
       intro h. intro x; simpl; intro I; inversion I.
       eauto.
       - intro h; inversion h; subst.
         intros y h1. inversion h1. subst. eauto.
         eapply IHl in H1. eapply H1. eauto.
Qed.

Lemma Exists_exists : forall {A} (P : A -> Prop) (l : Env A), 
      Exists P l -> (exists x, In_rng x l /\ P x).
Proof.
  induction l.
  intro h. inversion h.
  intros h. inversion h. subst.
  exists a0. split; eauto. econstructor. auto.
  subst. destruct IHl as [y [xIn Px]]; auto.
  exists y. split; eauto. simpl. right. auto.
Qed.


Lemma Forall_Forall2 : forall {A} (P : A -> A -> Prop) (l:Env A), 
       Forall (fun x => P x x) l <-> Forall2 P l l.
Proof.
  split.
  - induction 1; eauto.
  - intros h. dependent induction h. auto.
    eapply Forall_cons; eauto.
Qed.

Lemma Exists_Exists2 : forall {A} (P : A -> A -> Prop) (l:Env A), 
       Exists (fun x => P x x) l <-> Exists2 P l l.
Proof.
  split.
  - induction 1; eauto.
  - intro h. dependent induction h. auto.
    specialize (IHh P E1 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
    eapply Exists_cons2. auto.
Qed.

(*
#[export] Instance Container_Env : Container.Container Env := {
    Container.In := @In_rng;
    Container.Forall := @Forall;
    Container.Exists := @Exists;
    Container.ForallT := @ForallT;
    Container.ExistsT := @ExistsT;
    Container.Forall_forall := @Forall_forall;
    Container.Exists_exists := @Exists_exists
}.
    
#[export] Instance PWC_Env: Container.PointwiseContainer Env := {
    Container.Forall2 := @Forall2;
    Container.Exists2 := @Exists2;
    Container.Forall_Forall2 := @Forall_Forall2;
    Container.Exists_Exists2 := @Exists_Exists2
}. *)


Definition same_scope {A B : Type} := Forall2 (fun (v1 :A) (v2 : B) => True).
Arguments same_scope {_}{_}.

Section AllTProperties.
  Polymorphic Variable A : Type.

  Polymorphic Lemma ForallT_uniq {f}{ρ:Env A} : ForallT f ρ -> uniq ρ.
    Proof. induction 1; solve_uniq. Qed.

  Polymorphic Lemma Forall2_dom {f}{r1 r2 : Env A} : Forall2 f r1 r2 -> dom r1 = dom r2. 
  Proof. induction 1; simpl; f_equal; eauto. Qed.

  Polymorphic Lemma Forall2_uniq1 {f}{r1 r2 :Env A} : Forall2 f r1 r2 -> uniq r1. 
    Proof. induction 1; eauto. Qed.
  Polymorphic Lemma Forall2_uniq2 {f}{r1 r2 : Env A} : Forall2 f r1 r2 -> uniq r2. 
    Proof. induction 1; eauto. erewrite Forall2_dom in H0; eauto. Qed.

  Polymorphic Lemma Forall2_same_scope {f}{ρ1 ρ2 :Env A} : Forall2 f ρ1 ρ2 -> same_scope ρ1 ρ2.
    Proof.
      induction 1; econstructor; eauto.
    Qed.

Polymorphic Lemma Forall2_refl {F : A  -> A -> Prop} `{Reflexive _ F} {ρ} 
  : uniq ρ -> Forall2 F ρ ρ.
Proof. induction 1; eauto. Qed.

#[export] Polymorphic Instance Transitive_triv2 : Transitive (fun (_ _ : A) => True).
Proof. unfold Transitive. intros x y z. auto. Qed.

#[export] Polymorphic Instance Symmetric_triv2 : Symmetric (fun (_ _ : A) => True).
Proof. intros x y. auto. Qed.


  #[export] Polymorphic Instance Symmetric_Forall2 (f : Relation_Definitions.relation (A)) `{ Symmetric _ f } : Symmetric (Forall2 f).
  Proof. 
    unfold Symmetric. intros x y. 
    induction 1. econstructor; eauto.
    econstructor; eauto.
    erewrite <- Forall2_dom. eapply H1; eauto. eauto.
  Qed.

  #[export] Polymorphic Instance Transitive_Forall2 (f : Relation_Definitions.relation (A)) `{ Transitive _ f } : Transitive (Forall2 f).
  Proof. 
    unfold Transitive. intros x y. move: x. induction y.
    all: intros x z h1 h2; inversion h1; inversion h2; eauto.
    subst. inversion H6 ; subst. 
    eapply Forall2_cons; eauto.
  Qed.

#[export] Polymorphic Instance Transitive_same_scope : Transitive (@same_scope A A).
Proof. unfold same_scope. typeclasses eauto. Qed.


  (* Properties of map2 *)

  Polymorphic Lemma sub_dom1 {f}{ρ1 ρ2:Env A} : dom (map2 f ρ1 ρ2) [<=] dom ρ1.
  Proof.
    move: ρ2.
    induction ρ1; intro ρ2.
    - simpl. done.
    - move: a => [x v].
      destruct ρ2. simpl. fsetdec.
      move: p => [y u].
      simpl.
      destruct (x == y). simpl. 
      rewrite IHρ1. done.
      rewrite IHρ1. fsetdec.
  Qed.    

  Polymorphic Lemma sub_dom2 {f}{ρ1 ρ2 :Env A} : dom (map2 f ρ1 ρ2) [<=] dom ρ2.
  Proof. 
    move: ρ2.
    induction ρ1; intro ρ2.
    - simpl. fsetdec.
    - move: a => [x v].
      destruct ρ2. simpl. fsetdec.
      move: p => [y u].
      simpl.
      destruct (x == y). simpl. 
      rewrite IHρ1. fsetdec.
      rewrite IHρ1. fsetdec.
  Qed.    

  Polymorphic Lemma dom_update : forall x (D :A) ρ,  dom (update  x D ρ) = dom ρ.
  Proof. intros. induction ρ. simpl. auto. simpl.
         destruct a. destruct (x == a). subst. simpl. auto.
         simpl. f_equal. auto.
  Qed.

Polymorphic Lemma update_eq_var {x v w}{r :Env A}: update x v (x ~ w ++ r) = x ~ v ++ r.
Proof.
  induction r; simpl. destruct (x == x). auto. done.
  destruct (x==x). auto. done.
Qed.


Polymorphic Lemma update_neq_var {x y v w}{r : Env A}: x <> y -> update x v (y ~ w ++ r) = y ~ w ++ (update x v r).
Proof.
  induction r; simpl; intros NE;
  destruct (x == y); try done. 
Qed.


End AllTProperties.

#[export] Hint Resolve Forall2_refl : core.
#[export] Hint Rewrite dom_update : rewr_list.

Section AccessProperties.

  Polymorphic Variable A : Type.
  Polymorphic Variable d : A.

  Local Notation "ρ ⋅ x" := (access d ρ x) (at level 50) : list_scope.

  
  (* Properties of access *)

  Polymorphic Lemma access_eq_var {y}{X : A}{ρ} : (y ~ X ++ ρ) ⋅ y = X.
  Proof.
    unfold access. simpl. rewrite eq_dec_refl. auto.
  Qed.

  Polymorphic Lemma access_neq_var {x y}{X : A} {ρ} : x <> y -> (y ~ X ++ ρ) ⋅ x = ρ ⋅ x.
  Proof.
    intros. unfold access. simpl. destruct (x == y). done.
    done.
  Qed.

Polymorphic Lemma access_fresh {x}{ρ : Env A} :
  x `notin` dom ρ ->
  ρ ⋅ x = d.
Proof.
  induction ρ; simpl; intro h; try done.
  destruct a.
  (destruct (x == a) eqn:EQ).
  subst. fsetdec.
  rewrite IHρ. auto. auto.
Qed.


  Polymorphic Lemma access_app_fresh {x}{ρ1 ρ2:Env A}:  
      x `notin` dom ρ1 -> (ρ1 ++ ρ2) ⋅ x = ρ2 ⋅ x.
  Proof.
    induction ρ1; intros; simpl. auto.
    destruct a as [z v]. simpl in H. 
    destruct (x == z). subst. fsetdec.
    eauto.
  Qed.

  Polymorphic Lemma access_app {ρ1:Env A}{x}: 
    (forall ρ2, (ρ1 ++ ρ2) ⋅ x = ρ1 ⋅ x) \/ (forall ρ2, x `notin` dom ρ1 /\ (ρ1 ++ ρ2) ⋅ x = ρ2 ⋅ x).
  Proof.
    induction ρ1; intros; simpl. auto.
    destruct a as [z v]. 
    destruct (x == z). 
    + subst. left. auto. 
    + edestruct IHρ1 as [h1 | h2]. 
      left. eauto.
      right. intro ρ3.  edestruct h2. split. fsetdec. eauto.
  Qed.

  (* Properties of ForallT *)

  Polymorphic Lemma ForallT_access {f}{ρ:Env A} : ForallT f ρ -> forall x, x `in` dom ρ -> f (ρ ⋅ x).
    Proof. induction 1; intros z Fr. fsetdec.
           simpl in *. destruct (z == x); eauto. eapply IHX. fsetdec. 
    Qed.

  Polymorphic Lemma access_ForallT {f}{ρ:Env A} : uniq ρ -> (forall x, x `in` dom ρ -> f (ρ ⋅ x)) -> ForallT f ρ.
  Proof.
    induction ρ; intros h k; eauto.
    destruct a as [z B]. econstructor; eauto.
    eapply IHρ.
    solve_uniq.
    intros x0 Fr. have NE: x0 <> z. destruct_uniq. solve_uniq.
    specialize (k x0 ltac:(simpl; fsetdec)). 
    simpl_env in k. rewrite access_neq_var in k; auto.
    solve_uniq.
    specialize (k z ltac:(simpl; fsetdec)).
    rewrite access_eq_var in k; auto.
  Qed.

  (* Properties of Forall2 *)

  Polymorphic Lemma Forall2_access {f}{r1 r2 : Env A} : 
      Forall2 f r1 r2 -> forall x, x `in` dom r1 -> f (r1 ⋅ x) (r2 ⋅ x).
  Proof.    
    induction 1; intros y Fr; simpl. fsetdec.
    simpl in Fr.
    destruct (y == x); eauto. eapply IHForall2. fsetdec.
  Qed.

  Polymorphic Lemma access_Forall2 {g f : A -> A -> Prop}{r1 r2} : 
    Forall2 g r1 r2 -> (forall x, x `in` dom r1 -> f (r1 ⋅ x) (r2 ⋅ x)) -> Forall2 f r1 r2.
  Proof.
    induction 1; intros h; eauto. 
    econstructor; auto.
    eapply IHForall2. intros y Fr. have NE: x <> y. fsetdec.
    specialize (h y ltac:(simpl; auto)).
    repeat rewrite access_neq_var in h; auto.
    specialize (h x ltac:(simpl; auto)).
    repeat rewrite access_eq_var in h; auto.
  Qed.

End AccessProperties.

