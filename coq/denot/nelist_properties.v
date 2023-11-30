Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.
Require Import structures.NFSet.
Require Export structures.consistency.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

(* ------ library functions ----- *)

Fixpoint map2 {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C := 
  match xs , ys with 
  | x :: xs' , y :: ys' => f x y :: map2 f xs' ys' 
  | _ , _ => nil
  end.
#[export] Hint Constructors List.Forall2 : core.

Lemma Forall2_length {A} : forall f (l1 l2 : list A), List.Forall2 f l1 l2 -> length l1 = length l2.
Proof.  induction 1; eauto. simpl. f_equal. auto. Qed.


(* ------------------------ *)


Definition monotone {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* aka sub_preserving *)
Definition sub_reflecting {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, F D1 ⊆ F D2 -> (D1 ⊆ D2).

Definition finite {B} (X : P B) : Prop := 
  exists E, (X ≃ mem E).


(* ------------ environments ---------------------- *)

Definition atoms := nat.
Definition dom {A} : list A -> atoms := fun l => List.length l.
Definition same_scope {A} (ρ1 ρ2 : list A) := dom ρ1 = dom ρ2.

Fixpoint access {A} (d : A) (e : list A) (x : nat) : A :=
  match e with 
  | nil => d
  | cons p e => 
      match x with
      | 0 => p
      | S m => access d e m 
      end
  end.

Fixpoint update {A} (n : nat) (D: A) (xs : list A) {struct xs} : list A := 
  match xs with 
  | nil => nil
  | y :: ys => match n with 
               | 0 => D :: ys
               | S m => y :: update m D ys
             end
  end.

Lemma access_fresh{A}{d}{ρ : list A}{x}:
  not (x < dom ρ) ->
  access d ρ x = d.
Proof.
  move: x.
  induction ρ; simpl; intros x h; try done.
  destruct x.
  lia.
  rewrite IHρ. lia. done. Qed.


Lemma dom_update {A}{n:nat}{D:A}{xs:list A}: dom (update n D xs) = dom xs.
Proof. move: n. 
       induction xs; intro n; simpl; auto. 
       destruct n; simpl; auto.
Qed.

#[export] Hint Rewrite (@dom_update) : rewr_list.


Module EnvNotations.
Notation "ρ ⋅ x" := (access (fun y => False) ρ x) (at level 50) : list_scope.
Infix "⊆e" := (List.Forall2 Included) (at level 50) : list_scope.
Infix "≃e" := (List.Forall2 Same_set) (at level 50) : list_scope.
Infix "⊔e" := (map2 Union) (at level 60) : list_scope.
End EnvNotations.

Import EnvNotations.


Section EnvProperties.

Context {Value : Type}.

Definition Rho V := list (P V).

Definition Bottom : P Value := fun x => False.

Definition monotone_env {A} (XS: atoms) (D : Rho Value -> P A) := 
  forall ρ ρ' , dom ρ = XS -> ρ ⊆e ρ' -> (D ρ) ⊆ D ρ'.

Definition sub_env : Rho Value -> Rho Value -> Prop := List.Forall2 Included.

Definition same_env : Rho Value -> Rho Value -> Prop := List.Forall2 Same_set.

End EnvProperties.

#[export] Instance Proper_same_env_dom {A} : Proper (same_env ==> Logic.eq) (@dom (P A)).
Proof. 
  intros x y S. unfold dom, same_env in *. eapply Forall2_length; eauto. Qed.

#[export] Instance Proper_sub_env_dom {A} : Proper (sub_env ==> Logic.eq) (@dom (P A)).
Proof. 
  intros x y S. unfold dom, sub_env in *. eapply Forall2_length; eauto. Qed.

#[export] Instance Proper_same_env_scope {A} : Proper (same_env ==> same_env ==> Logic.eq) (@same_scope (P A)).
Proof. 
  intros x1 y1 S1 x2 y2 S2. unfold same_scope in *. rewrite -> S1. rewrite -> S2. done. Qed.

#[export] Instance Proper_sub_env_scope {A} : Proper (sub_env ==> sub_env ==> Logic.eq) (@same_scope (P A)).
Proof. 
  intros x1 y1 S1 x2 y2 S2. unfold same_scope in *. rewrite -> S1. rewrite -> S2. done. Qed.


(* Continuity: 
   
   Parameterized by a notion of validity for sets and their finite approximations. 

   Valid sets should be nonempty.

   Validity should also be closed under set union

   For every valid set, we can pick out a finite, inhabited subset of it.

 *)


Class Validity (V : Type) := 
  MkValid { validT_set : P V -> Type ; 
            pick : forall (X: P V), validT_set X -> 
               { V : nfset V & (validT_set (mem V) * (mem V ⊆ X))%type} ; 
            valid_nonempty : forall X , validT_set X -> nonemptyT X ;
            valid_union : forall X Y, validT_set X -> validT_set Y -> validT_set (X ∪ Y)
    }.

Section Continuity.

Context {Value : Type}
        `{Validity Value}.

Definition continuous {V}`{Validity V}{A} (F : P V -> P A) : Set :=
  forall X E, mem E ⊆ F X -> validT_set X 
         -> exists D, exists _:validT_set (mem D), (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)).

Definition validT_env : Rho Value -> Type := List.ForallT validT_set.

Definition finite_env : Rho Value -> Prop := List.Forall finite.
  
Definition continuous_In {A} (D:Rho Value -> P A) (ρ:Rho Value) (v:A) : Prop :=
  v ∈ D ρ -> validT_env ρ -> 
  exists ρ' , exists _:validT_env ρ' ,  (finite_env ρ') /\ ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_Sub {A} (D:Rho Value -> P A) (ρ:Rho Value) (V:nfset A) : Prop :=
  mem V ⊆ D ρ -> validT_env ρ ->
  exists ρ', exists _: validT_env ρ' , finite_env ρ' /\ ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').

(*
Definition continuous_env {A} (D:Rho Value -> P A) (ρ:Rho Value) : Prop :=
  forall (v : A), continuous_In D ρ v.
*)

Definition continuous_env {A} `{Validity A} (D:Rho Value -> P A) (ρ:Rho Value) : Prop :=
  forall (V :nfset A), validT_set (mem V) -> continuous_Sub D ρ V.


End Continuity.


Section EnvResults.

Context {Value : Type} {VV : Validity Value}.

(* Nonempty environments *)

Lemma extend_nonempty_env {ρ : Rho Value}{X} : 
  validT_set X -> 
  validT_env ρ -> validT_env (X :: ρ).
Proof. intros NEP NEX. eapply List.ForallT_cons; eauto. Qed.


Lemma join_finite_env {ρ1 ρ2 : Rho Value} : 
  same_scope ρ1 ρ2 
  -> finite_env ρ1
  -> finite_env ρ2
  -> finite_env (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1 as [| v1 r1].
  all: intros ρ2 sc h1; destruct ρ2 as [| v2 r2]; intros h2; simpl; eauto.
  inversion h1; subst; clear h1.
  inversion h2; subst; clear h2.
  econstructor; eauto. 
  2: { 
    eapply IHr1; eauto. inversion sc. auto.
  } 
  match goal with 
  | [ H4 : finite v1 |- _ ] =>  destruct H4 as [E1 [s1 u1 ]] end.
  match goal with 
  | [ H4 : finite v2 |- _ ] =>  destruct H4 as [E2 [s2 u2 ]] end.
  exists (union_nfset E1 E2).
  split.
  rewrite -> s1.
  rewrite -> s2.
  rewrite mem_union. reflexivity.
  eapply mem_union_Included; eauto.
  transitivity v1; eauto using sub_union_left.
  transitivity v2; eauto using sub_union_right.
Qed.

Lemma valid_join {ρ1 ρ2} :
    same_scope ρ1 ρ2
    -> validT_env ρ1  
    -> validT_env ρ2 
    -> validT_env (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1 as [| v1 r1].
  all: intros ρ2 sc h1; destruct ρ2 as [| v2 r2]; intros h2; simpl; eauto.
  inversion h1; subst; clear h1.
  inversion h2; subst; clear h2.
  inversion sc; subst; clear sc.
  econstructor; eauto. 
  eapply valid_union; eauto.
  eapply IHr1; eauto.
Qed.


Lemma join_lub {ρ ρ1 : Rho Value} :
  ρ1 ⊆e ρ -> forall ρ2, ρ2 ⊆e ρ -> (ρ1 ⊔e ρ2) ⊆e ρ.
Proof.
  intro SS1.
  induction SS1; intros ρ2 SS2; inversion SS2; subst.
  simpl. auto.
  simpl.
  eapply List.Forall2_cons; eauto.
  match goal with [ H4 : ?x ⊆ _ |- (_ ∪ ?x) ⊆ _ ] => rewrite -> H4 end.
  match goal with [ H : ?x ⊆ _ |- (?x ∪ _) ⊆ _ ] => rewrite -> H end.
  rewrite union_idem.
  reflexivity.
Qed.
  
Lemma join_sub_left {ρ1 ρ2 : Rho Value} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1; intros ρ2 h. 
  - destruct ρ2; simpl; simpl in h; eauto.
  - destruct ρ2; inversion h. 
    econstructor. auto.
    eapply IHρ1. eauto.
Qed.

Lemma join_sub_right {ρ1 ρ2 : Rho Value} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1; intros ρ2 h. 
  - destruct ρ2; inversion h. simpl; auto.
  - destruct ρ2; inversion h. 
    econstructor. auto.
    eapply IHρ1. eauto.
Qed.

Definition initial_finite_env (ρ : Rho Value) (NE : validT_env ρ) : Rho Value.
  induction NE.
  - exact nil.
  - move: (@pick _ _ x p) => [V [h1 h2]].
    exact (cons (mem V) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct (pick x p) as [v [w1 w2]].  simpl. congruence.
Qed. 

Lemma finite_singleton : forall {B} (v : B), finite ⌈ v ⌉.
Proof. intros B v. exists (singleton_nfset v).
       repeat split; eauto. 
       intros x xIn. inversion xIn; subst; done.
Qed.



Lemma initial_fin (ρ : Rho Value) (NE : validT_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct (pick x p) as [v [w1 w2]].
  econstructor; eauto.
  exists v; reflexivity.
Qed.

Lemma initial_valid (ρ : Rho Value) (NE : validT_env ρ) :
  validT_env (initial_finite_env ρ NE).
Proof. 
  induction NE.
  simpl. econstructor.
  simpl. destruct (pick x p) as [v [w1 w2]].
  econstructor; eauto.  
Qed.

Lemma initial_fin_sub (ρ : Rho Value) (NE : validT_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct (pick x p) as [v [fx ?]].
  econstructor; auto.
Qed.


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : nat) (D : P Value) (ρ : Rho Value) 
  (NE : validT_env ρ) : Rho Value :=
  update x D (initial_finite_env ρ NE).

Lemma single_fin { X x ρ NE } : 
  finite X ->
  finite_env (single_env x X ρ NE).
Proof.
  move: x. induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env. cbn. econstructor.
  unfold single_env. simpl. destruct (pick x p) as [v1 [v2 v3]].
  destruct FIN eqn:EQ.
  + subst. simpl.
    econstructor; eauto.
    eapply initial_fin. 
  + simpl in *.
    econstructor; eauto.
    exists v1; reflexivity.
    eapply IHNE; eauto.
Qed.


Lemma single_valid { X x ρ NE } : 
  validT_set X ->
  validT_env (single_env x X ρ NE).
Proof.
  move: x. induction NE; intros y VAL; unfold finite_env; eauto.
  unfold single_env. cbn. econstructor.
  unfold single_env. simpl. destruct (pick x p) as [v1 [v2 v3]].
  destruct y eqn:EQ.
  + subst. simpl.
    econstructor; eauto.
    eapply initial_valid. 
  + simpl in *.
    econstructor; eauto.
    eapply IHNE; eauto.
Qed.

Lemma single_sub { ρ x V } :
  forall (NE : validT_env ρ),
    V ⊆ ρ ⋅ x 
  -> (single_env x V ρ NE) ⊆e ρ.
Proof.
  intros NE. 
  move: x.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) cbn. eauto.
    
  + (* cons case *)
    unfold single_env in *.
    simpl in *.
    destruct (pick x p) as [w [h1 h2]]. simpl.
    destruct vpe.
    ++ econstructor; eauto.
       eapply initial_fin_sub. 
    ++ econstructor; eauto.
Qed.



Lemma update_access : forall {x ρ NE X},
  x < dom ρ ->
  X ≃ (single_env x X ρ NE) ⋅ x.
Proof.
  intros.
  unfold single_env.
  move: NE x H.
  induction NE. intros x H. simpl in H. lia.
  simpl. destruct (pick x p) as [w [h1 h2]]. simpl.
  intros y H. destruct y eqn:EQ. subst. reflexivity.
  specialize (IHNE n ltac:(lia)).
  simpl.
  auto.
Qed.  




(* v∈single[xv]x  *)
Lemma single_access {X x ρ NE} : 
  x < dom ρ ->
  (single_env x X ρ NE ⋅ x) = X.
Proof.
  unfold single_env.
  move: NE x.
  induction NE; intros y h. simpl in h. lia.
  simpl. destruct (pick x p) as [w [h1 h2]]. simpl.
  destruct y. simpl. auto.
  simpl in *. eapply IHNE. lia.
Qed.  


(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x < dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE x.
  induction NE; intros y h. simpl in h. lia.
  simpl. destruct (pick x p) as [w [h1 h2]]. simpl.
  destruct y. simpl. eauto.
  simpl in *. eapply IHNE. lia.
Qed.  

(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub {A} (E : Rho Value -> (P A)) ρ (NE : validT_env ρ) :
   monotone_env (dom ρ) E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists _: validT_env ρ',  finite_env ρ' /\  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me [a l].
  induction l.
  - move=> VE vcont.
    move: (VE a ltac:(left; auto)) => h. 
    destruct (vcont a) as [ ρ1 [vρ1 [ fρ1  [ ρ1ρ VEρ1 ]]]]; try left; eauto.
    exists ρ1. repeat split; auto. 
    intros x xIn. inversion xIn; subst; try done.
  - move=> VE vcont.
    have X:  mem (NFSet a l) ⊆ mem (NFSet a (a0 :: l)).
    { move=> v vIn. destruct vIn; subst. left; auto. right. right. auto. }
    destruct IHl as [ ρ1 [ vρ1 [ fρ1  [ ρ1ρ VEρ1 ]]]]; eauto.
    transitivity (mem (NFSet a (a0 :: l))); auto.
    destruct (vcont a0 ltac:(right;left; auto)) as [ρ2 [vρ2 [fρ2  [ρ2ρ VEρ2]]]]; auto.
    apply VE. right; left; auto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. admit.
    have S2: same_scope ρ2 ρ. admit.
    have SS: same_scope ρ1 ρ2. admit. 
    repeat split.
    + eapply valid_join; eauto. 
    + eapply join_finite_env; eauto. 
    + eapply join_lub; eauto.
    + intros d dm.
      inversion dm; subst; try destruct H; subst.
      ++ eapply me with (ρ := ρ1); eauto using join_sub_left.
         eapply VEρ1. left; auto.
      ++ eapply me with (ρ := ρ2); eauto using join_sub_right.
      ++ eapply me with (ρ := ρ1); eauto using join_sub_left.
         eapply VEρ1. right; auto.
Admitted.

Lemma access_continuous_env { ρ x } : 
  continuous_env (fun ρ0 : Rho Value => ρ0 ⋅ x) ρ.
Proof. 
  move=> V VAL vIn NE.
  cbn in vIn.
  destruct (Nat.lt_decidable x (dom ρ)).
  exists (single_env x (mem V) ρ NE).
  repeat split.
  eapply single_valid; eauto. 
  eapply single_fin; eauto.
  exists V; reflexivity.
  eapply single_sub; auto.
  erewrite -> (single_access H). reflexivity.
  exists (initial_finite_env ρ NE).
  rewrite access_fresh in vIn. auto. 
  apply valid_nonempty in VAL. destruct VAL.
  specialize (vIn _ i).
  done.
Qed.

(* ⟦⟧-continuous-⊆ *) 
Lemma generic_continuous_sub {A}`{Validity A}{ρ}{F : Rho Value -> P A} : 
    continuous_env F ρ 
  -> validT_env ρ
  -> forall V, validT_set (mem V) -> mem V ⊆ F ρ
  -> exists ρ', exists _ : validT_env ρ' , finite_env ρ' /\
        ρ' ⊆e ρ  /\  (mem V ⊆ F ρ').
Proof.
  intros Fcont NE_ρ V VAL VinEρ.
  eapply Fcont; eauto.
Qed.


End EnvResults.

#[export] Hint Resolve extend_nonempty_env : core.
#[export] Hint Resolve single_sub : core. 
#[export] Hint Resolve single_fin : core. 
#[export] Hint Resolve single_valid : core. 

#[export] Hint Resolve initial_fin_sub : core. 
#[export] Hint Resolve initial_fin : core. 
#[export] Hint Resolve initial_valid : core. 

#[export] Hint Rewrite @initial_finite_dom : rewr_list.
#[export] Hint Rewrite @single_access : core.
#[export] Hint Resolve v_single_xvx : core. 

(* Sub environments ⊆e *)

Section EnvCongruence.

Context {Value : Type}.

Lemma Reflexive_sub_env {ρ:list (P Value)} : ρ ⊆e ρ.
Proof.
  induction ρ; econstructor; eauto. reflexivity.
Qed.

Lemma extend_sub_env {ρ ρ': list (P Value)}{X} :
  ρ ⊆e ρ' -> (X :: ρ) ⊆e (X :: ρ' ).
Proof. intros; econstructor; eauto. reflexivity. Qed.

Lemma access_mono_sub : forall (ρ1 ρ2 : list (P Value)) (x : nat),
   ρ1 ⊆e ρ2 ->
   ρ1 ⋅ x ⊆ ρ2 ⋅ x.
intros. 
destruct (Nat.lt_decidable  x (dom ρ1)).
Admitted.
(*
+ apply Forall2_access with (f := Included); auto.
    + rewrite access_fresh. auto.
      rewrite access_fresh. erewrite Forall2_dom in H0; eauto.
      reflexivity.
Qed.  *)

Lemma same_env_sub_env : forall (x y : list (P Value)), x ≃e y <-> (x ⊆e y) /\ (y ⊆e x).
Proof. 
intros x y. split.
induction 1. split; eauto. 
move: H => [r1 r2].
move: IHForall2 => [h1 h2]. 
split; econstructor; eauto.
intros [h1 h2]. 
induction h1. eauto.
inversion h2. subst.
econstructor; eauto.
split; auto.
Qed. 


End EnvCongruence.


#[export] Instance Proper_access_sub {Value} : 
  Proper (sub_env ==> Logic.eq ==> Included) (@access (P Value) (fun x => False)). 
Proof.
  intros x2 y2 S2 x3 y3 ->. eapply access_mono_sub. eauto.
Qed.  

#[export] Instance Proper_access_eq {Value} : 
  Proper (same_env ==> Logic.eq ==> Same_set) (@access (P Value) (fun x => False)). 
Proof.
  intros x2 y2 EQ x3 y3 ->. 
  apply same_env_sub_env in EQ. destruct EQ as [S1 S2].
  split; eapply access_mono_sub; eauto.  
Qed.  

#[export] Instance Transitive_sub_env {Value}  : 
  Transitive (@List.Forall2 (P Value) (P Value) Included).
Proof. typeclasses eauto. Qed.

#[export] Hint Resolve Reflexive_sub_env : core.
#[export] Hint Resolve extend_sub_env : core.



Section ValidTheory.

Context {Value : Type} `{Validity Value}.

Lemma valid_nil : validT_env nil.
Proof. econstructor; eauto. Qed.


Lemma extend_valid_env {ρ : list (P Value)}{X} : 
  validT_set X -> 
  validT_env ρ -> validT_env (X :: ρ).
Proof. intros NEP NEX. eapply List.ForallT_cons; eauto. Qed.

End ValidTheory.

#[export] Hint Resolve valid_nil : core.
#[export] Hint Resolve extend_valid_env : core.
