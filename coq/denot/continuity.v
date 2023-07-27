(* 

This section proves that the denotation function is monotonic and continuous.

Monotonicity

   Definition monotone (F : P Value -> P Value) : Set := 
         forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

   Lemma denot_monotone_one : forall ρ t x, 
    uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot (t ^ x) (x ~ D ++ ρ)).

Continuity:

   A semantic function is continuous if its finite result can be produced
   by a finite and valid subset of its input.

   Alex: this is algebraicity, equivalent to continuity for this kind of model.
   To produce a finite output you only need a finite input.
   
   Definition continuous (F : P Value -> P Value) : Set :=
     forall (X : P Value) (E : list Value), 
           mem E ⊆ F X -> valid X ->
           exists (D : list Value), 
               (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

   Lemma denot_continuous_one { t ρ x } :
     valid_env ρ ->
     x `notin` dom ρ ->
     continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).

The payoff for this section is a lemma for understanding how LAMBDA and APPLY interact.
The general lemma looks like this:

Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> valid X ->
  (Λ F) ▩ X ≃ F X.

With the above results, we can instantiate it to reason about the denotation function.

Lemma Λ_denot_APPLY_id : forall t ρ x X,
    valid X ->
    valid_env ρ ->
    x `notin` dom ρ ->
    ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) ≃ denot (t ^ x) (x ~ X ++ ρ).

 *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import structures.Structures.

Require Import denot.definitions.
Require Import denot.denot.
Require Import denot.congruence_theory.
Require Import denot.valid_theory.

Import MonadNotation.
Open Scope monad_scope.
Import SetNotations.
Local Open Scope set_scope.
Import LCNotations.
Open Scope tm.

Import EnvNotations.

(* Definitions related to continuity *)

Definition continuous {B} (F : P Value -> P B) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

Definition finite_env : Rho -> Type := Env.ForallT finite.

Definition continuous_In {B} (D:Rho -> P B) (ρ:Rho) (v:B) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_Included {B} (D:Rho -> P B) (ρ:Rho) (X: P B) : Prop :=
  finite X -> X ⊆ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (X ⊆ D ρ').

Definition continuous_env {B} (D:Rho -> P B) (ρ:Rho) : Prop :=
  forall v, continuous_Included D ρ v.

(* -------------------------------------- *)


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).

(* -------------------------------------- *)


(* -- monotonicity -- *)

(*
Lemma access_monotone {ρ ρ':Rho}{x} : ρ ⊆e ρ' -> ρ ⋅ x ⊆ ρ' ⋅ x.
Proof.
  induction 1. simpl. reflexivity.
  simpl. destruct (x == x0) eqn:E. auto.
  auto. 
Qed. *)

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: 
  monotone_env (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
Qed.


(* denot-monotone-one *)
Lemma denot_monotone_one : forall ρ t x, 
    uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone; simpl; auto.
  econstructor; eauto.
Qed.
  

(* ----------------------------------------------------- *)

(* Join environments *)

Lemma join_finite_env {ρ1 ρ2} : 
  same_scope ρ1 ρ2 
  -> finite_env ρ1
  -> finite_env ρ2
  -> finite_env (ρ1 ⊔e ρ2).
Proof.
  move: ρ2.
  induction ρ1 as [|[x1 v1] r1].
  all: intros ρ2 sc h1; destruct ρ2 as [|[x2 v2] r2]; intros h2; simpl; eauto.
  inversion h1; subst; clear h1.
  inversion h2; subst; clear h2.
  destruct (x1 == x2); subst.
  + econstructor; eauto. eapply IHr1; eauto. inversion sc. auto.
    rewrite sub_dom1; auto.
    destruct H3 as [E1 [s1 u1 ]].
    destruct H5 as [E2 [s2 u2 ]].
    exists (E1 ++ E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    ++ intro h.
    apply u2. 
    destruct E1. simpl in h. auto.
    done.
  + assert False. inversion sc. subst. done. done.
Qed.

Lemma join_lub {ρ ρ1 : Rho} :
  same_scope ρ1 ρ ->
  forall ρ2, same_scope ρ2 ρ ->
  ρ1 ⊆e ρ -> ρ2 ⊆e ρ -> (ρ1 ⊔e ρ2) ⊆e ρ.
Proof.
  intro SS1.
  induction SS1; intros ρ2 SS2; inversion SS2; subst.
  simpl. auto.
  intros.
  simpl.
  inversion H1. inversion H2. subst.
  rewrite eq_dec_refl.
  eapply Env.Forall2_cons; eauto.
  rewrite sub_dom1. auto.
  rewrite -> H21.
  rewrite -> H13.
  rewrite union_idem.
  reflexivity.
Qed.
  
Lemma join_sub_left {ρ1 ρ2 : Rho} : 
  same_scope ρ1 ρ2 ->
  ρ1 ⊆e (ρ1 ⊔e ρ2).
Proof.
  intros h.
  induction h; simpl; eauto.
  rewrite eq_dec_refl.
  econstructor; eauto. 
Qed.

Lemma join_sub_right {ρ1 ρ2 : Rho} : 
  same_scope ρ1 ρ2 ->
  ρ2 ⊆e (ρ1 ⊔e ρ2).
Proof.
  induction 1; simpl; eauto. 
  rewrite eq_dec_refl.
  econstructor; eauto. 
  erewrite Forall2_dom in H0; eauto.
Qed.

(* --------------------------------------- *)

(* Initial environment. *)

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Rho) (NE : valid_env ρ) : Rho.
  induction NE. exact nil.
  destruct f as [V _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [v w].  simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma finite_singleton : forall {B} (v : B), finite ⌈ v ⌉.
Proof. intros B v.  exists (cons v nil).
       repeat split; eauto. done. 
Qed.

#[export] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Rho) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [v w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Rho) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [v fx].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho) 
  (NE : valid_env ρ) : Rho :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { X x ρ NE } : 
  finite X ->
  finite_env (single_env x X ρ NE).
Proof.
  induction NE; intro FIN; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. 
  destruct f as [v1 v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto. auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    eapply IHNE; eauto.
    simpl_env. auto.
Qed.

#[global] Hint Resolve single_fin : core. 


Lemma single_sub { ρ x V } :
  forall (NE : valid_env ρ),
    V ⊆ ρ ⋅ x 
  -> x `in` dom ρ
  -> (single_env x V ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) auto. 
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [w h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env.  eauto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. auto.
       intros y h. inversion h. subst. unfold In. auto.
Qed.

#[export] Hint Resolve single_sub : core. 


Lemma update_access : forall {x ρ NE X},
  x `in` dom ρ ->
  X ≃ (single_env x X ρ NE) ⋅ x.
Proof.
  intros.
  unfold single_env.
  move: NE.
  induction NE. fsetdec.
  simpl. destruct f as [w h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. reflexivity.
  simpl. rewrite EQ. eapply IHNE; auto. simpl in H. fsetdec.
Qed.  

(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f as [w h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[export] Hint Resolve v_single_xvx : core. 

(* continuous-∈⇒⊆ *)
(*
Lemma continuous_In_sub {A} (E : Rho -> (P A)) ρ (NE : valid_env ρ) :
   monotone_env E
   -> forall V, mem V ⊆ E ρ
   -> (forall v, v ∈ mem V -> continuous_In E ρ v)
   -> exists ρ', exists (pf : finite_env ρ') ,  ρ' ⊆e ρ /\ (mem V ⊆ E ρ').
Proof.
  intros me V VE vcont.
  induction V.
  - exists (initial_finite_env ρ NE).
    repeat split.
    eapply (initial_fin ρ NE).
    eapply initial_fin_sub; eauto. 
    done.
  - destruct IHV as [ ρ1 [ fρ1 [ ρ1ρ VEρ1 ]]].
    intros d z. eapply VE; eauto.
    intros v VM. eapply vcont; eauto.
    destruct (vcont a) as [ρ2 [fρ2 [ρ2ρ VEρ2]]].
    econstructor; eauto.
    eapply VE. econstructor; eauto.
    exists (ρ1 ⊔e ρ2).
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto. 
    have SS: same_scope ρ1 ρ2. 
    { transitivity ρ; auto. symmetry; auto. }
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
    inversion dm; subst.
    eapply me. eapply join_sub_right; eauto. auto. 
    eapply me. eapply join_sub_left; eauto. auto.
Qed.
*)
(* --------------------------------------- *)

(* Operations are continuous *)

Search Singleton.

Lemma In_Included : forall {A}{x:A}{D},  x ∈ D -> ⌈ x ⌉ ⊆ D.
Proof. 
  intros.
  intros y h.
  inversion h. subst. auto.
Qed.

Lemma Included_In : forall {A}{x:A} {D},   ⌈ x ⌉ ⊆ D -> x ∈ D.
Proof. 
  intros.
  apply H. eauto.
Qed.

Lemma finite_Singleton : forall {A}{x:A}, finite ⌈ x ⌉.
Proof.
  econstructor; eauto.
  instantiate (1 := (x :: nil)). split; auto.
  split; eauto using mem_singleton, singleton_mem.
  done.
Qed. 

Lemma CONS_continuous {D E ρ}{w} :
    w ∈ (CONS (D ρ) (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ /\ (w ∈ (CONS (D ρ3) (E ρ3))).
Proof.  
  intros C. unfold CONS, In in C. destruct w.
  all: try done.
  destruct l. try done.
  move: C => [Dv El].
  intros IHD IHE mD mE.
  destruct (IHD ⌈ v ⌉ finite_Singleton (In_Included Dv)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE ⌈ v_list l ⌉ finite_Singleton (In_Included El)) as 
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - eapply mD. instantiate (1:= ρ1). 
    eapply join_sub_left; eauto. auto.
  - eapply mE. instantiate (1:= ρ2).
    eapply join_sub_right; eauto. auto.
Qed.



(*  BIND2 S K := exists U : P A, (RET2 U ⊆ S) /\ K U t *)

Lemma BIND2_continuous {A B}{D : Rho -> M A}{K : P A -> M B}{ρ}{v} :
  valid_env ρ ->
  v ∈ BIND2 (D ρ) K -> 
  continuous_env D ρ ->
  monotone_env D  ->
  forall E, K = (fun v => E v ρ) ->
  (forall v, continuous_env (E v) ρ) ->
  (forall v, monotone_env (E v)) ->
  exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\ (v ∈ BIND2 (D ρ') (fun v => E v ρ')). 
Proof.
  intros VE H IHD mD E -> IHE mE. 
  move: H => [U [h1 [h2 h3]]].
  specialize (IHE U).
  specialize (mE U).
  have NE : finite (RET2 U). { inversion h1. destruct H. unfold RET2. econstructor; eauto. rewrite H. 
                               instantiate (1 := fmap pure_Comp x). split. admit. admit. }
  edestruct (IHD _  NE h2) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  edestruct (IHE ⌈ v ⌉ finite_Singleton (In_Included h3)) as 
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
  repeat split.
  + eapply join_finite_env; eauto.
  + eapply join_lub; eauto.
  + unfold Ensembles.In.
    unfold BIND2.
    exists U. repeat split. auto. transitivity (D ρ1). auto.
    eapply mD.
    eapply join_sub_left; eauto.
    eapply Included_In.
    transitivity (E U ρ2); auto.
    apply mE. eapply join_sub_right; eauto. 
Admitted.

Lemma APPLY_continuous {D E ρ}{w} :
  (valid_env ρ)
  -> w ∈ ((D ρ) ▩ (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , 
    exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ 
                             /\ (w ∈ ((D ρ3) ▩ (E ρ3))).
Proof.  
  intros NE APP. inversion APP; subst. 
  all: intros IHD IHE mD mE.
  + destruct (IHD ⌈ V ↦ w ⌉ finite_Singleton (In_Included H)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    have NEV: finite (mem V). admit. (* {  unfold valid_mem in H1. destruct V; try done. econstructor; eauto. } *)
    destruct (IHE (mem V) ltac:(eauto) H0) as 
      [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - have VwDp3 : ⌈ V ↦ w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
 + destruct (IHD ⌈ v_list VS ⌉ ) as [ρ1 [F1 [h1 h2]]]; auto using In_Included, finite_Singleton.
   destruct (IHE ⌈ v_nat k ⌉ ) as [ρ2 [F2 [h3 h4]]]; auto using In_Included, finite_Singleton.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
   exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.    
  - eapply join_lub; eauto.
  - eapply PROJ with (VS := VS) (k:=k); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
 +  destruct (IHD ⌈ x ⌉) as [ρ1 [F1 [h1 h2]]]; auto using In_Included, finite_Singleton.
    eexists.
    eexists.
    eauto.
    split; eauto.
    eapply APPWRONG with (x:=x); auto.
 +  destruct (IHE ⌈ x ⌉) as [ρ2 [F1 [h1 h2]]]; auto using In_Included, finite_Singleton.
    destruct (IHD ⌈ v_list VS ⌉) as [ρ1 [F2 [h01 h02]]]; auto using In_Included, finite_Singleton.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    - eapply join_finite_env; eauto.    
    - eapply join_lub; eauto.
    - eapply PROJWRONG with (VS := VS); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
Admitted.



Lemma env_tail {ρ' x v ρ} :  
  ρ' ⊆e (x ~ v ++ ρ) -> finite_env ρ' -> 
  nonempty_env ρ ->
  exists w, exists ρ'', ρ' = (x ~ w ++ ρ'') /\
                (w ⊆ v) /\
                exists (pf : finite_env ρ''), 
                ρ'' ⊆e ρ.                
Proof.
  intros h k ne.
  inversion h. subst.
  exists a1.  exists E1.
  repeat split; auto. inversion k.  auto.
Qed.

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma Lambda_continuous {E ρ} {NE : valid_env ρ}{ v x} :
  v ∈ Λ (fun D => E (x ~ D ++ ρ)) 
  -> (forall V, valid_mem V -> continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\  (v ∈ (Λ (fun D => E (x ~ D ++ ρ')))).
Proof.
  induction v.
  all: try solve [intros; cbv in H; done].
  - (* v is l ↦ v *)
    intros [ wEVρ NW ] IH mE.
    have VV: valid_mem l. unfold valid_mem. eauto.
    destruct (IH l ltac:(eauto) ⌈ c ⌉ finite_Singleton (In_Included wEVρ)) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    eapply Included_In.
    transitivity (E (x ~ a1 ++ E1)); auto.
    eapply mE. 
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply Forall2_uniq1; eauto. 
    auto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.


(* ---------------- Denotation is continuous ----------------- *)

Lemma Included_RET2 {A}{v:M A}{Y}: (v ⊆ RET2 Y) ->  exists X, (v ≃ RET2 X) /\ (X ⊆ Y).
Proof.
  intros.
  cbv in H.
  exists (fun x => Y x /\ v (ret x)).
  repeat split.
  - cbv. intros x vx.
    move: (H x vx) => [b [Yb mm]].
    exists b. repeat split; auto. inversion mm. subst. auto.
  - cbv. intros x [b [[Yb vb] xb]]. 
    inversion xb. subst. auto.
  - intros y Iny.
    destruct Iny. auto.
Qed.
  


(* ⟦⟧-continuous *)
Lemma denot_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros m NEm mSub.
  all: autorewrite with denot in mSub.
  all: try solve [ exists (initial_finite_env ρ NE);
    eexists; eauto] .
  + exfalso. destruct NEm. admit. (* eapply mSub.  eauto.  *)
  + move: (Included_RET2 mSub) => [X [E S]].
    destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
    - exists (single_env x X ρ NE).
      split.
      have FX: finite X. admit.
      eapply single_fin; eauto.
      split.
      ++ eapply single_sub; auto.
      ++ rewrite denot_var. 
         rewrite E.
         eapply RET2_monotone.

         move: (@v_single_xvx a x ρ NE ltac:(auto)) => h.
         
         transitivity (RET2 (ρ ⋅ x)); auto.
         eapply RET2_monotone.
         intros w wIn.
         eapply v_single_xvx. auto. 
    - exists (initial_finite_env ρ NE).
      eexists; eauto. split. eauto.
      rewrite denot_var.
      rewrite <- ret_In_RET2.
      rewrite access_fresh. simpl_env. auto.
      rewrite access_fresh in h1. auto. done.
  + edestruct (BIND2_continuous NE vIn) as [ρ' [F [SS BB]]]; eauto.
    instantiate (1 :=  (fun ρ v1 => BIND2 (denot t2 ρ) (fun v2 : P Value => v1 ▩ v2))). reflexivity.
    eapply denot_monotone.
    (* edestruct (APPLY_continuous NE vIn) as [ρ' [F SS]]; eauto. *)
    simpl in BB.
    exists ρ'. exists F.
    rewrite denot_app. auto.
  + pick fresh x.
    rewrite (denot_abs x) in vIn. fsetdec.
    move: vIn => [v1 [h1 h2]].
    inversion h2; subst; clear h2.
    move: (@Lambda_continuous _ _ NE v1 x h1) => h.    
    destruct h as [ρ' [Fρ' [S vvIn]]].
    ++ intros V NEV NW.
       move: (valid_nonempty_mem _ NEV) => [w h0]. 
       eapply IH; eauto.
    ++ eapply denot_monotone.
    ++ exists ρ'. exists Fρ'. 
       erewrite <- Forall2_dom in Fr. 2: eapply S.
       rewrite (denot_abs x). fsetdec.
       repeat split; auto.
       erewrite <- ret_In_RET2.
       auto.
  + edestruct (BIND2_continuous NE vIn) as [ρ' [F [SS BB]]]; eauto.
    instantiate (1 :=  (fun ρ v1 => BIND2 (denot t2 ρ) (fun v2 : P Value => RET2 (CONS v1 v2)))). reflexivity.
    eapply denot_monotone.

    edestruct (CONS_continuous vIn) as [ρ' [F SS]]; eauto.

    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_tcons. auto.
Qed.


(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  valid_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
  eapply denot_monotone; eauto.
  intros v InV.
  eapply denot_continuous; auto.
Qed.

(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  valid_env ρ 
  -> x `notin` dom ρ 
  -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros NE_ρ Fr.
  unfold continuous.
  intros X E E_sub_denot NE_X.
  edestruct (@denot_continuous_sub (x ~ X ++ ρ)) as 
    [ρ' [pf [h1 h2]]]. 3: eauto.
  + eapply extend_valid_env; eauto.
  + eauto.
  + inversion h1. subst. inversion pf. subst.
    move: H6 => [D [S NN]].
    exists D. split.
    rewrite <- S. auto.
    split. 
    have SUB: Env.Forall2 Included (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    rewrite <- SUB.
    auto.
    eapply valid_sub_valid_mem; eauto. rewrite <- S. auto.
Qed.

(*  Abstraction followed by Application is the identity ------------------- *)

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> valid X
  -> (Λ F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w APP. inversion APP; subst. 
    - inversion H.
    - exfalso; eapply valid_not_wrong; eauto. 
    - inversion H.
      eapply (Fmono (mem V) X); eauto. 
    - inversion H.
    - destruct x; try done.
    - destruct x; try done.
  + intros w wInFX.
    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    move: NEX => [ [x h0] h1].
    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
    eapply Forall_sub_mem; eauto.
Qed.


(* Λ⟦⟧-▪-id *)
Lemma Λ_denot_APPLY_id :
  forall t ρ x X,
    valid X
    -> valid_env ρ
    -> x `notin` dom ρ 
    -> ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) ≃
      denot (t ^ x) (x ~ X ++ ρ).
Proof.
  intros.
  move: (@Λ_APPLY_id (fun D => denot (t ^ x) (x ~ D ++ ρ)) X) => h.
  eapply h; auto.
  +  (* continuity *)
    eapply denot_continuous_one; auto.
  + eapply denot_monotone_one; auto.
    eapply ForallT_uniq; eauto.
Qed.
