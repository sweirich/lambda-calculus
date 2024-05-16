Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.
Require Import structures.FSet.
Require Export structures.consistency.


Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.

Fixpoint map2 {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C := 
  match xs , ys with 
  | x :: xs' , y :: ys' => f x y :: map2 f xs' ys' 
  | _ , _ => nil
  end.
#[export] Hint Constructors List.Forall2 : core.


Lemma Forall2_length {A} : forall f (l1 l2 : list A), List.Forall2 f l1 l2 -> length l1 = length l2.
Proof.  induction 1; eauto. simpl. f_equal. auto. Qed.


Definition monotone {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

(* aka sub_preserving *)
Definition sub_reflecting {A}{B} (F : P A -> P B) : Set := 
  forall D1 D2, F D1 ⊆ F D2 -> (D1 ⊆ D2).

Definition finite {B} (X : P B) : Prop := 
  exists E, (X ≃ mem E) /\ nonempty_fset E.


Definition continuous {V}{A} (F : P V -> P A) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.



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

Definition finite_env : Rho Value -> Prop := List.Forall finite.
  
Definition nonempty_env : Rho Value -> Type := List.ForallT nonemptyT.

Definition sub_env : Rho Value -> Rho Value -> Prop := List.Forall2 Included.

Definition same_env : Rho Value -> Rho Value -> Prop := List.Forall2 Same_set.

Definition continuous_In {A} (D:Rho Value -> P A) (ρ:Rho Value) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho Value -> P A) (ρ:Rho Value) : Prop :=
  forall (v : A), continuous_In D ρ v.

Definition continuous_Sub {A} (D:Rho Value -> P A) (ρ:Rho Value) (V:fset A) : Prop :=
  mem V ⊆ D ρ -> 
  exists ρ', exists (pf : finite_env ρ'),
    ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').

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


Section EnvResults.

Context {Value : Type}.

(* Nonempty environments *)

Lemma extend_nonempty_env {ρ : Rho Value}{X} : 
  nonemptyT X -> 
  nonempty_env ρ -> nonempty_env (X :: ρ).
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
  exists (union_fset E1 E2).
  split.
  rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    eauto.
Qed.

Lemma join_lub {ρ ρ1 : Rho Value} :
  ρ1 ⊆e ρ -> forall ρ2, ρ2 ⊆e ρ -> (ρ1 ⊔e ρ2) ⊆e ρ.
Proof.
  intro SS1.
  induction SS1; intros ρ2 SS2; inversion SS2; subst.
  simpl. auto.
  simpl.
  eapply List.Forall2_cons; eauto.
  rewrite -> H3.
  rewrite -> H.
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

Definition initial_finite_env (ρ : Rho Value) (NE : nonempty_env ρ) : Rho Value.
  induction NE. exact nil.
  destruct p as [V _].
  exact (cons ⌈ V ⌉ IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct p as [v w].  simpl. congruence.
Qed. 

Lemma finite_singleton : forall {B} (v : B), finite ⌈ v ⌉.
Proof. intros B v. exists (singleton_fset v).
       repeat split; eauto. done. 
Qed.



Lemma initial_fin (ρ : Rho Value) (NE : nonempty_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct p as [v w1 ].
  econstructor; eauto.
  eapply finite_singleton.
Qed.

Lemma initial_fin_sub (ρ : Rho Value) (NE : nonempty_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct p as [v fx].
  econstructor; auto.
Qed.


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : nat) (D : P Value) (ρ : Rho Value) 
  (NE : nonempty_env ρ) : Rho Value :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { X x ρ NE } : 
  finite X ->
  finite_env (single_env x X ρ NE).
Proof.
  move: x. induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env. simpl. destruct p as [v1 v2].
  destruct FIN eqn:EQ.
  + subst. simpl.
    econstructor; eauto.
    eapply initial_fin. 
  + simpl in *.
    econstructor; eauto.
    eapply finite_singleton.
    eapply IHNE; eauto.
Qed.




Lemma single_sub { ρ x V } :
  forall (NE : nonempty_env ρ),
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
    destruct p as [w h2]. simpl.
    destruct vpe.
    ++ simpl in *.
       econstructor; eauto.
       eapply initial_fin_sub. 
    ++ simpl in *.
       econstructor; eauto.
Qed.



Lemma update_access : forall {x ρ NE X},
  x < dom ρ ->
  X ≃ (single_env x X ρ NE) ⋅ x.
Proof.
  intros.
  unfold single_env.
  move: NE x H.
  induction NE. intros x H. simpl in H. lia.
  simpl. destruct p as [w h2]. simpl.
  intros y H. destruct y eqn:EQ. subst. reflexivity.
  specialize (IHNE n ltac:(lia)).
  simpl.
  auto.
Qed.  



(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x < dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE x.
  induction NE; intros y h. simpl in h. lia.
  simpl. destruct p as [w h2]. simpl.
  destruct y. simpl. eauto.
  simpl in *. eapply IHNE. lia.
Qed.  

(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub {A} (E : Rho Value -> (P A)) ρ (NE : nonempty_env ρ) :
   monotone_env (dom ρ) E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me VS.
  eapply fset_induction with (f := VS).
  Unshelve. 3: exact VS.
  - move=> VE vcont.
    exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - move=> a f IHVS VE vcont.
    rewrite union_mem in VE.
    destruct IHVS as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]]; eauto.
    move=> v vIn. eapply vcont. rewrite union_mem. eapply Union_intror. auto.
    destruct (vcont a) as [ρ2 [fρ2 [ρ2ρ VEρ2]]].
    rewrite union_mem. econstructor; eauto. rewrite mem_singleton_eq. eauto.
    eapply VE. econstructor; eauto. 
    rewrite mem_singleton_eq. eauto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. admit.
    have S2: same_scope ρ2 ρ. admit.
    have SS: same_scope ρ1 ρ2. admit. 
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
      rewrite union_mem in dm.
      rewrite mem_singleton_eq in dm.
      inversion dm; subst.
      eapply me with (ρ := ρ2). rewrite -> ρ2ρ. auto. 
      eapply join_sub_right; eauto. inversion H. subst. auto.
      eapply me with (ρ := ρ1). rewrite -> ρ1ρ. auto. eapply join_sub_left; eauto. auto.
Admitted.


Lemma access_continuous_env { ρ x } : 
  nonempty_env ρ -> continuous_env (fun ρ0 : Rho Value => ρ0 ⋅ x) ρ.
Proof. 
  move=> NE v vIn.
  cbn in vIn.
  destruct (Nat.lt_decidable x (dom ρ)).
  exists (single_env x ⌈ v ⌉ ρ NE).
  repeat split.
  eapply single_fin; eauto.
  eapply finite_singleton; eauto.
  eapply single_sub; auto.
  eapply v_single_xvx; eauto.
  exists (initial_finite_env ρ NE).
  rewrite access_fresh in vIn. auto. done.
Qed.

(* ⟦⟧-continuous-⊆ *) 
Lemma generic_continuous_sub {A}{ρ}{F : Rho Value -> P A} : 
    continuous_env F ρ 
  -> monotone_env (dom ρ) F
  -> nonempty_env ρ
  -> forall V, mem V ⊆ F ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ F ρ').
Proof.
  intros Fcont Fmono NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
Qed.


End EnvResults.

#[export] Hint Resolve extend_nonempty_env : core.
#[export] Hint Resolve single_sub : core. 
#[export] Hint Resolve single_fin : core. 
#[export] Hint Resolve initial_fin_sub : core. 
#[export] Hint Resolve initial_fin : core. 
#[export] Hint Resolve finite_singleton : core. 
#[export] Hint Rewrite @initial_finite_dom : rewr_list.
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


(* valid sets are inhabited *)
Definition valid_is_nonempty {A} (V : P A) : valid V -> nonemptyT V := id.

Lemma valid_join : forall {A} ( v1 v2 : P A), 
    valid v1 -> 
    valid v2 ->
    valid (v1 ∪ v2).
Proof.
  intros A v1 v2 [x1 h1] [x2 h2].
  exists x1. eapply Union_introl; eauto.
Qed.

Section ValidTheory.

Context {Value : Type}.

Lemma valid_nil : @nonempty_env Value nil.
Proof. unfold nonempty_env. eauto. Qed.


Lemma extend_valid_env {ρ : list (P Value)}{X} : 
  valid X -> 
  nonempty_env ρ -> nonempty_env (X :: ρ).
Proof. intros NEP NEX. eapply List.ForallT_cons; eauto. Qed.

End ValidTheory.

#[export] Hint Resolve valid_nil : core.
#[export] Hint Immediate valid_is_nonempty : core.
#[export] Hint Resolve extend_valid_env : core.
