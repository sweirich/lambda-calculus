Require Import ssreflect.

Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.

Require Import Metalib.Metatheory.

Require Import SetsAsPredicates.

Open Scope list_scope.

Section Definitions.

Polymorphic Variable A : Type.

Polymorphic Definition GEnv := list (atom * A).

Polymorphic Fixpoint access (d : A) (e : GEnv) (x : atom) : A :=
  match e with 
  | nil => d
  | cons ( y , p ) e => 
      match x == y with
      | left _ => p
      | right _ => access d e x 
      end
  end.

Polymorphic Fixpoint update (x : atom) (D : A) (ρ : GEnv) : GEnv :=
  match ρ with 
  | nil => nil
  | cons (y, E) ρ => match (x == y) with
                 | left _ => cons (x, D) ρ
                 | right _ => cons (y, E) (update x D ρ)
                 end
  end.

Polymorphic Inductive allT (f : A -> Type) : list (atom * A) -> Type :=
  | allT_nil :
      allT f nil
  | allT_cons : forall x a E,
      allT f E ->
      x `notin` (dom E) ->
      f a ->
      allT f (x ~ a ++ E).

Polymorphic Inductive allT2 (f : A -> A -> Type) : list (atom * A) -> list (atom * A) -> Type :=
  | allT2_nil :
      allT2 f nil nil
  | allT2_cons : forall x a1 a2 E1 E2,
      allT2 f E1 E2 ->
      x `notin` (dom E1) ->
      f a1 a2 ->
      allT2 f (x ~ a1 ++ E1) (x ~ a2 ++ E2).

Polymorphic Inductive all2 (f : A -> A -> Prop) : list (atom * A) -> list (atom * A) -> Prop :=
  | all2_nil :
      all2 f nil nil
  | all2_cons : forall x a1 a2 E1 E2,
      all2 f E1 E2 ->
      x `notin` (dom E1) ->
      f a1 a2 ->
      all2 f (x ~ a1 ++ E1) (x ~ a2 ++ E2).

(* NOTE:  allT (fun _ => True) is isomorphic to "uniq" *)

Polymorphic Definition same_scope := all2 (fun v1 v2 => True).

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

Arguments access {_}.
Arguments update {_}.
Arguments map2 {_}.
Arguments allT {_}.
Arguments allT2 {_}.
Arguments all2 {_}.
Arguments same_scope {_}.

#[export] Hint Constructors allT : core.
#[export] Hint Constructors allT2 : core.
#[export] Hint Constructors all2 : core.

(* Module EnvNotations.
Notation "ρ ⋅ x" := (access ρ x) (at level 50) : list_scope.
End EnvNotations.
Import EnvNotations. *)

Section AllTProperties.
  Polymorphic Variable A : Type.
  Polymorphic Local Definition Env := GEnv A.

  Polymorphic Lemma allT_uniq {f}{ρ:GEnv A} : allT f ρ -> uniq ρ.
    Proof. induction 1; solve_uniq. Qed.

  Polymorphic Lemma all2_dom {f}{r1 r2 : GEnv A} : all2 f r1 r2 -> dom r1 = dom r2. 
  Proof. induction 1; simpl; f_equal; eauto. Qed.

  Polymorphic Lemma all2_uniq1 {f}{r1 r2 :GEnv A} : all2 f r1 r2 -> uniq r1. 
    Proof. induction 1; eauto. Qed.
  Polymorphic Lemma all2_uniq2 {f}{r1 r2 : GEnv A} : all2 f r1 r2 -> uniq r2. 
    Proof. induction 1; eauto. erewrite all2_dom in H0; eauto. Qed.

  Polymorphic Lemma all2_same_scope {f}{ρ1 ρ2 :GEnv A} : all2 f ρ1 ρ2 -> same_scope ρ1 ρ2.
    Proof.
      induction 1; econstructor; eauto.
    Qed.


#[global] Polymorphic Instance Transitive_triv2 : Transitive (fun (_ _ : A) => True).
Proof. unfold Transitive. intros x y z. auto. Qed.

#[global] Polymorphic Instance Symmetric_triv2 : Symmetric (fun (_ _ : A) => True).
Proof. intros x y. auto. Qed.


  #[export] Polymorphic Instance Symmetric_all2 (f : Relation_Definitions.relation (A)) `{ Symmetric _ f } : Symmetric (all2 f).
  Proof. 
    unfold Symmetric. intros x y. 
    induction 1. econstructor; eauto.
    econstructor; eauto.
    erewrite <- all2_dom. eapply H1; eauto. eauto.
  Qed.

  #[global] Polymorphic Instance Transitive_all2 (f : Relation_Definitions.relation (A)) `{ Transitive _ f } : Transitive (all2 f).
  Proof. 
    unfold Transitive. intros x y. move: x. induction y.
    all: intros x z h1 h2; inversion h1; inversion h2; eauto.
    subst. inversion H6 ; subst. 
    eapply all2_cons; eauto.
  Qed.

#[global] Polymorphic Instance Transitive_same_scope : Transitive (@same_scope A).
Proof. unfold same_scope. typeclasses eauto. Qed.


  (* Properties of map2 *)

  Polymorphic Lemma sub_dom1 {f}{ρ1 ρ2:GEnv A} : dom (map2 f ρ1 ρ2) [<=] dom ρ1.
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

  Polymorphic Lemma sub_dom2 {f}{ρ1 ρ2 :GEnv A} : dom (map2 f ρ1 ρ2) [<=] dom ρ2.
  Admitted.

  Polymorphic Lemma dom_update : forall x (D :A) ρ,  dom (update  x D ρ) = dom ρ.
  Proof. intros. induction ρ. simpl. auto. simpl.
         destruct a. destruct (x == a). subst. simpl. auto.
         simpl. f_equal. auto.
  Qed.

Polymorphic Lemma update_eq_var {x v w}{r :GEnv A}: update x v (x ~ w ++ r) = x ~ v ++ r.
Proof.
  induction r; simpl. destruct (x == x). auto. done.
  destruct (x==x). auto. done.
Qed.


Polymorphic Lemma update_neq_var {x y v w}{r : GEnv A}: x <> y -> update x v (y ~ w ++ r) = y ~ w ++ (update x v r).
Proof.
  induction r; simpl; intros NE;
  destruct (x == y); try done. 
Qed.


End AllTProperties.

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

  Polymorphic Lemma access_app_fresh {x}{ρ1 ρ2:GEnv A}:  
      x `notin` dom ρ1 -> (ρ1 ++ ρ2) ⋅ x = ρ2 ⋅ x.
  Proof.
    induction ρ1; intros; simpl. auto.
    destruct a as [z v]. simpl in H. 
    destruct (x == z). subst. fsetdec.
    eauto.
  Qed.

  Polymorphic Lemma access_app {ρ1:GEnv A}{x}: 
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

  (* Properties of allT *)

  Polymorphic Lemma allT_access {f}{ρ:GEnv A} : allT f ρ -> forall x, x `in` dom ρ -> f (ρ ⋅ x).
    Proof. induction 1; intros z Fr. fsetdec.
           simpl in *. destruct (z == x); eauto. eapply IHX. fsetdec. 
    Qed.

  Polymorphic Lemma access_allT {f}{ρ:GEnv A} : uniq ρ -> (forall x, x `in` dom ρ -> f (ρ ⋅ x)) -> allT f ρ.
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

  (* Properties of all2 *)

  Polymorphic Lemma all2_access {f}{r1 r2 : GEnv A} : 
      all2 f r1 r2 -> forall x, x `in` dom r1 -> f (r1 ⋅ x) (r2 ⋅ x).
  Proof.    
    induction 1; intros y Fr; simpl. fsetdec.
    simpl in Fr.
    destruct (y == x); eauto. eapply IHall2. fsetdec.
  Qed.

  Polymorphic Lemma access_all2 {g f : A -> A -> Prop}{r1 r2} : 
    all2 g r1 r2 -> (forall x, x `in` dom r1 -> f (r1 ⋅ x) (r2 ⋅ x)) -> all2 f r1 r2.
  Proof.
    induction 1; intros h; eauto. 
    econstructor; auto.
    eapply IHall2. intros y Fr. have NE: x <> y. fsetdec.
    specialize (h y ltac:(simpl; auto)).
    repeat rewrite access_neq_var in h; auto.
    specialize (h x ltac:(simpl; auto)).
    repeat rewrite access_eq_var in h; auto.
  Qed.

End AccessProperties.

