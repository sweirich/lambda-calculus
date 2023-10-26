(*

This section proves that the denotation function is monotonic and continuous.

Monotonicity

   Definition monotone (F : P Value -> P Value) : Set := 
      forall D1 D2, (D1 ⊆ D2) -> F D1 ⊆ F D2.

   Lemma denot_monotone_one : forall ρ t x, uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot (t ^ x) (x ~ D ++ ρ)).

Continuity:

   A semantic function is continuous if any finite subset of any result of X
   can be produced by a finite and valid subset of X.

   [Alex notes: this is algebraicity, equivalent to continuity for this kind
   of model.  To produce a finite output you only need a finite input.]
   
   If our functions only concerned sets of values, then we might define
   continuous as:

        Definition continuous (F : P Value -> P Value) : Set := 
          forall (X : P Value) (E : Comp (list B)), 
             mem E ⊆ F X -> valid X -> 
                exists (D : list Value), 
                    (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

   However, our denotation function, used in the following lemma,

       Lemma denot_continuous_one { t ρ x } : valid_env ρ 
          -> x `notin` dom ρ
          -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).

   has type `P Value -> P (Comp (P Value))`.

   Furthermore, in showing that this function is continuous, we also need to
   reason about the continuity of the 'bind' operator.

Why continuous and monotone?
   
   The payoff for this section is a lemma for understanding how LAMBDA and
   APPLY interact.  The general lemma looks like this:

        Lemma Λ_APPLY_id { F X } : 
             continuous F -> monotone F -> valid X -> 
             (Λ F) ▩ X ≃ F X.

   With the above results, we can instantiate it to reason about the denotation
   function.

        Lemma Λ_denot_APPLY_id : forall t ρ x X, 
            valid X -> 
            valid_env ρ -> x `notin` dom ρ -> 
               ((Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))) ▩ X) 
                 ≃ denot (t ^ x) (x ~ X ++ ρ).

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

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  let E := gather_atoms_with (fun x : Rho => dom x) in
  constr:(A \u B \u C \u D \u E).



(* Definitions related to continuity 

   For every finite approximation of an output, 
   there is a finite approximation
   of an input.

   If the type is P Value, then the approx is list Value
   If the type is P (Comp (P Value)), then the approx is list (Comp (list Value))

*)

Definition continuous {A} (F : P Value -> P A) : Set :=
  forall X E, mem E ⊆ F X -> valid X 
         -> exists D, (mem D ⊆ X) /\ ((mem E) ⊆ F (mem D)) /\ valid_mem D.

Definition finite_env : Rho -> Type := Env.ForallT finite.

Definition continuous_In {A} (D:Rho -> P A) (ρ:Rho) (v:A) : Prop :=
  v ∈ D ρ -> exists ρ' , exists (pf : finite_env ρ'),  ρ' ⊆e ρ /\ (v ∈ D ρ').

Definition continuous_env {A} (D:Rho -> P A) (ρ:Rho) : Prop :=
  forall (v : A), continuous_In D ρ v.

Definition continuous_Sub {A} (D:Rho -> P A) (ρ:Rho) (V:fset A) : Prop :=
  mem V ⊆ D ρ -> 
  exists ρ', exists (pf : finite_env ρ'),
    ρ' ⊆e ρ  /\ (mem V ⊆ D ρ').


(* ----------------------------------------------------- *)

(* -- monotonicity WRT environments -- *)

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: 
  monotone_env (denot t).
Proof.
  unfold monotone_env.
  intros. 
  eapply Proper_sub_denot; auto.
Qed.

(* -- monotonicity WRT argument -- *)

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
  

Lemma RET_monotone_env {D: Rho -> (P Value)} : 
  monotone_env D -> 
  monotone_env (fun ρ => RET (D ρ)).
Proof.
  intros.
  intros ρ1 ρ2 S.
  specialize (H ρ1 ρ2 S).
  eapply RET_mono; auto.
Qed.

Lemma BIND_monotone_env {A B} 
  {D : Rho -> P (Comp (fset A))} 
  {K : Rho -> P A -> P (Comp B)} : 
  monotone_env D ->
  (forall v, monotone_env (fun ρ => K ρ v)) ->
  monotone_env (fun ρ => (BIND (D ρ) (K ρ))). 
Proof.
  intros mE mK. 
  intros ρ1 ρ2 S1.
  eapply BIND_mono. eapply mE; eauto.
  intros x. eapply mK. auto.
Qed.

Lemma CONS_monotone_env {D E} :
    monotone_env D 
  -> monotone_env E
  -> monotone_env (fun ρ => (CONS (D ρ) (E ρ))).
Proof. intros. intros ρ1 ρ2 S. eapply CONS_mono_sub; eauto. Qed.

Lemma CONST_monotone_env {A}{v : P A}: monotone_env (fun _ : Rho => v).
Proof. intros ρ1 ρ2 SUB. reflexivity. Qed.


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
    exists (union_fset E1 E2).
    split.
    rewrite -> s1.
    rewrite -> s2.
    rewrite union_mem. reflexivity.
    eauto.
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
Proof. intros B v. exists (singleton_fset v).
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


(* --------------------------------------- *)
(* continuous-∈⇒⊆ *)

Lemma union_left_inv1 {A}{X Y Z: P A} : X ∪ Y ⊆ Z -> X ⊆ Z.
Admitted.

Lemma union_left_inv2 {A}{X Y Z: P A} : X ∪ Y ⊆ Z -> Y ⊆ Z.
Admitted.

#[export] Hint Resolve union_left_inv1 union_left_inv2 : core.

Lemma continuous_In_sub {A} (E : Rho -> (P A)) ρ (NE : valid_env ρ) :
   monotone_env E
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
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto. 
    have SS: same_scope ρ1 ρ2. 
    { transitivity ρ; auto. symmetry; auto. }
    eexists. eapply join_finite_env; eauto.
    repeat split.
    + eapply join_lub; eauto.
    + intros d dm.
      rewrite union_mem in dm.
      rewrite mem_singleton_eq in dm.
      inversion dm; subst.
      eapply me. eapply join_sub_right; eauto. inversion H. subst. auto.
      eapply me. eapply join_sub_left; eauto. auto.
Qed.



(* --------------------------------------- *)

(* Operations are continuous in the environment *)

Lemma const_continuous_env {A} {v:P A}{ρ} : 
  valid_env ρ 
  -> continuous_env (fun _ : Rho => v) ρ.
Proof.
   intros NE.  unfold continuous_env, continuous_In.
   intros v1 vIn. 
   exists (initial_finite_env ρ NE); eexists; eauto.
Qed.

Lemma access_continuous_env { ρ x } : 
  valid_env ρ -> continuous_env (fun ρ0 : Rho => ρ0 ⋅ x) ρ.
Proof. 
  move=> NE v vIn.
  cbn in vIn.
  destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
  exists (single_env x ⌈ v ⌉ ρ NE).
  repeat split.
  eapply single_fin; eauto.
  eapply single_sub; auto.
  eapply v_single_xvx; eauto.
  exists (initial_finite_env ρ NE).
  rewrite access_fresh in vIn. auto. done.
Qed.



Lemma APPLY_continuous_env {D E ρ} :
  (valid_env ρ)
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> continuous_env (fun ρ => (D ρ ▩ E ρ)) ρ.
Proof.  
  intros NE IHD IHE mD mE.
  intros w APP.
  inversion APP; subst.
  - destruct (IHD ( V ↦ w ) ltac:(auto)) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    -- eapply join_finite_env; eauto.
    -- eapply join_lub; eauto.
    -- have VwDp3 : ⌈ V ↦ w ⌉ ⊆ D (ρ1 ⊔e ρ2).
    { transitivity (D ρ1); auto. eapply mD. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { transitivity (E ρ2); auto. eapply mE.
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
  - destruct (IHD (v_list VS) ) as [ρ1 [F1 [h1 h2]]]; auto.
    destruct (IHE (v_nat k) ) as [ρ2 [F2 [h3 h4]]]; auto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    -- eapply join_finite_env; eauto.    
    -- eapply join_lub; eauto.
    -- eapply PROJ with (VS := VS) (k:=k); eauto.
       eapply mD. eapply join_sub_left; auto. auto.
       eapply mE. eapply join_sub_right; auto. auto.
  - destruct (IHD x) as [ρ1 [F1 [h1 h2]]]; auto.
    eexists.
    eexists.
    eauto.
    split; eauto.
    eapply APPWRONG with (x:=x); auto.
  - destruct (IHE x) as [ρ2 [F1 [h1 h2]]]; auto.
    destruct (IHD (v_list VS)) as [ρ1 [F2 [h01 h02]]]; auto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    -- eapply join_finite_env; eauto.    
    -- eapply join_lub; eauto.
    -- eapply PROJWRONG with (VS := VS); eauto.
    eapply mD. eapply join_sub_left; auto. auto.
    eapply mE. eapply join_sub_right; auto. auto.
Qed.

(* Algebraicity.  
   Only need finite information from the environment.
*)

Lemma LAMBDA_continuous_env {E ρ x} {NE : valid_env ρ} :
    x `notin` dom ρ
  -> (forall V, valid_mem V -> continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> continuous_env (fun ρ => Λ (fun D => E (x ~ D ++ ρ))) ρ.
Proof.
  intros Fr IH mE.
  intros v vIn.
  destruct v; try done.
  - (* v is l ↦ c *)
    move: vIn => [ wEVρ NW ]. 
    have VV: valid_mem f. unfold valid_mem. eauto.
    have NEx: valid_env (x ~ mem f ++ ρ). econstructor; eauto.

    specialize (IH f ltac:(eauto) c wEVρ).
    destruct IH as [ρ' [F' [S' h']]].
    inversion S'. subst. inversion F'. subst.
    exists E1. eexists. eauto.
    repeat split; auto.
    eapply mE. 2 : eapply h'.
    econstructor; eauto. eapply Reflexive_sub_env. eapply Forall2_uniq1; eauto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.



Lemma CONS_continuous_env {D E ρ} :
    continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> continuous_env (fun ρ => (CONS (D ρ) (E ρ))) ρ.
Proof.  
  intros IHD IHE mD mE.
  intros v vIn.
  destruct v; cbn in vIn; try done.
  destruct l; cbn in vIn; try done. 
  move: vIn => [vIn lIn].
  destruct (IHD v vIn) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE (v_list l) lIn) as
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

Lemma ONE_continuous_env {D ρ} : 
  continuous_env D ρ ->
  monotone_env D ->
  continuous_env (fun ρ => ONE (D ρ)) ρ.
Proof.
  intros IHD mD.
  intros v vIn.
  unfold ONE in vIn.
  destruct vIn as [l mIn].
  destruct (IHD _ mIn) as    [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  exists ρ1 . exists fρ1 . split. auto. 
  exists l. auto.
Qed.

Lemma ALL_continuous_env {D ρ} : 
  continuous_env D ρ ->
  monotone_env D ->
  continuous_env (fun ρ => ALL (D ρ)) ρ.
Proof.
  intros IHD mD.
  intros v vIn.
  unfold ALL in vIn.
  destruct v; try done. cbn in vIn.
  destruct (IHD _ vIn) as    [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  exists ρ1 . exists fρ1 . split. auto. 
  unfold ALL. cbn. auto.
Qed.

Lemma CHOOSE_continuous_env {D E ρ} : 
  continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> continuous_env (fun ρ => (CHOOSE (D ρ) (E ρ))) ρ.
Proof.  
  intros IHD IHE mD mE.
  intros v vIn.
  unfold CHOOSE in vIn.
  destruct v; try done.
  cbn in vIn.
  destruct vIn as [l1 [l2 [-> [h1 h2]]]].
  destruct (IHD _ h1) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE _ h2) as
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - exists l1. exists l2. 
    repeat split; eauto.
    eapply mD. instantiate (1:= ρ1). 
    eapply join_sub_left; eauto. auto.
    eapply mE. instantiate (1:= ρ2). 
    eapply join_sub_right; eauto. auto.
Qed. 


Lemma UNIFY_continuous_env {D E ρ} : 
  valid_env ρ
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> continuous_env (fun ρ => (UNIFY (D ρ) (E ρ))) ρ.
Proof.  
  intros VE IHD IHE mD mE.
  intros v vIn.
  unfold UNIFY in vIn.
  destruct v; try done.
  destruct l; try done.
  + cbn in vIn.
    unfold InconsistentSets in vIn.
    destruct vIn as [x [y [h1 [h2 W]]]].
    destruct (IHD _ h1) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE _ h2) as
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - cbn.
    exists x. exists y.
    repeat split; eauto.
    eapply mD. instantiate (1:= ρ1). 
    eapply join_sub_left; eauto. auto.
    eapply mE. instantiate (1:= ρ2). 
    eapply join_sub_right; eauto. auto.
  +
  destruct l; try done.
  cbn in vIn.
  destruct vIn as [l1 [l2 [-> [NE1 [NE2 [h1 [h2 h3]]]]]]].
  destruct (continuous_In_sub _ _ VE mD _ h1) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  { unfold continuous_In.
    intros v I1 I2.
    eapply IHD. auto. }
  destruct (continuous_In_sub _ _ VE mE _ h2) as
      [ ρ2 [ fρ2 [ ρ2ρ VwDp2 ]]].
  { unfold continuous_In.
    intros v I1 I2.
    eapply IHE. auto. }

  have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
  have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
  have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
  exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - exists l1. exists l2. 
    repeat split; eauto.
    move: (mD ρ1 (ρ1 ⊔e ρ2)) => SS1.
    rewrite <- SS1. auto.
    eapply join_sub_left; eauto. auto.
    move: (mE ρ2 (ρ1 ⊔e ρ2)) => SS2.
    rewrite <- SS2. auto.
    eapply join_sub_right; eauto. 
Qed. 



(* ------------------------------------------------------- *)

Lemma RET_continuous_env {D: Rho -> (P Value)}{ρ} : 
  valid_env ρ ->
  continuous_env D ρ ->
  monotone_env D ->
  continuous_env (fun ρ => RET (D ρ)) ρ.
Proof.
  intros VE IHD mD.
  intros c cIn.
  destruct c; try done.
  destruct l; try done.
  destruct l; try done.
  cbn in cIn. destruct cIn.
  have lemma: (exists ρ', exists _ : finite_env ρ', ρ' ⊆e ρ /\ ((mem f) ⊆ D ρ')).
  { 
    eapply continuous_In_sub; eauto.
  }
  destruct lemma as [ρ' [F' [S' h]]]. 
  exists ρ'. exists F'.
  split; auto.
  split; auto.
Qed.  

Lemma BIND_continuous_env {A B} 
  {D : Rho -> P (Comp (fset A))} 
  {K : Rho -> P A -> P (Comp B)} {ρ}: 
  valid_env ρ -> 
  continuous_env D ρ ->
  monotone_env D ->
  (forall v, continuous_env (fun ρ => K ρ v) ρ) ->
  (forall v, monotone_env (fun ρ => K ρ v)) ->
  continuous_env (fun ρ => (BIND (D ρ) (K ρ))) ρ. 
Proof.
  intros NE IHD mD IHK mK.
  intros c cIn.
  destruct cIn as [u [k [uIn [h1 h2]]]].
  destruct (IHD u uIn) as [ ρ1 [F1 [S1 uIn1]]].
  destruct u.
  + simpl in h1.
    subst.
    exists ρ1. exists F1. split; auto.
    cbn. unfold BIND.
    exists c_wrong. exists k.
    repeat split. eapply uIn1.
    intros a aIn. inversion aIn.
  + have lemma :
      forall l, 
         (forall a : fset A, Comp_In a (c_multi l) -> K ρ (mem a) (k a)) -> 
         exists ρ', exists (_ : finite_env ρ'), 
           ρ' ⊆e ρ /\
           (forall a : fset A, Comp_In a (c_multi l) -> K ρ' (mem a) (k a)).
    { clear uIn ρ1 F1 S1 uIn1 l h1 h2.
      induction l; intros h2.
      ++ exists (initial_finite_env ρ NE). eexists; repeat split; eauto.
         intros a inA. simpl in inA. done.
      ++ destruct IHl 
          as [ρ2 [F2 [S2 uIn2]]].
          { intros x xIn. apply h2. simpl. simpl in xIn. right.  auto. }
          move: (h2 a ltac:(econstructor; eauto)) => Ka.
          destruct (IHK (mem a) _ Ka) as
            [ρ1 [F1 [S1 uIn1]]].
          have SS1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
          have SS2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
          have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
          exists (ρ1 ⊔e ρ2).
          repeat split.
          - eapply join_finite_env; eauto.    
          - eapply join_lub; eauto.
          - intros x xIn. simpl in xIn. destruct xIn. 
            subst. eapply (mK (mem x)); try eassumption. eapply join_sub_left; auto.
            eapply (mK (mem x)). 2: { eapply uIn2; eauto. }
            eapply join_sub_right; eauto.
    }
    destruct (lemma l h2) as 
      [ρ2 [F2 [S2 In2]]]. clear lemma.
    have SS1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have SS2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
    - eapply join_finite_env; eauto.    
    - eapply join_lub; eauto.
    - exists (c_multi l). exists k.
    repeat split; eauto.
    eapply mD; try eassumption. eapply join_sub_left; auto.
    intros a aIn.
    eapply (mK (mem a)). 2: { eapply In2; eauto. }
    eapply join_sub_right; eauto.
Qed.                 



(* ---------------- Denotation is continuous ----------------- *)

(* ⟦⟧-continuous *)
Lemma denot_continuous_env {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros c cIn.
  all: autorewrite with denot in cIn.

  all: try solve [destruct c; try done].  

  all: try solve [ exists (initial_finite_env ρ NE); eexists; eauto].

  + destruct c; try done.  
    destruct l as [|V l]; try done. 
    destruct l; try done.
    eapply RET_continuous_env; eauto.
    ++ eapply access_continuous_env; eauto.
    ++ eapply (@monotone_env_denot_val (var_f x)). 

  + (* application case *)
    specialize (IH1 _ NE).
    specialize (IH2 _ NE).
    have C1: forall v1 v2, continuous_env (fun ρ => v1 ▩ v2) ρ.
    { 
      intros. unfold continuous_env, continuous_In.
      intros c1 c1In.
      eapply (@APPLY_continuous_env (fun ρ => v1) (fun ρ => v2)); 
        eauto using const_continuous_env, CONST_monotone_env.
    } 
    have C2: forall v1,
        continuous_env (fun ρ => BIND (denot t2 ρ) (fun v2 : P Value => v1 ▩ v2)) ρ.
    { 
      intros v1.
      eapply (BIND_continuous_env NE IH2 ltac:
                (eapply denot_monotone; eauto) (C1 v1));
        eauto using CONST_monotone_env.
    } 
   edestruct (BIND_continuous_env NE IH1 ltac:(eapply denot_monotone; eauto) C2) as 
     [ ρ' [F' [S' In']]].
   2: eapply cIn.
   intros v.  
   eapply BIND_monotone_env.
   eapply denot_monotone. 
   intros x. eauto using CONST_monotone_env.
   exists ρ'. exists F'. repeat split. auto.
   autorewrite with denot.
   auto.
  + pick fresh x.
    rewrite (denot_abs x) in cIn. fsetdec.

    remember (fun ρ => 
                Λ (fun D : P Value => denot (t' ^ x) (x ~ D ++ ρ))) 
              as D.
    have CE: (continuous_env D ρ). 
    {
      subst D. eapply LAMBDA_continuous_env; eauto.
      Unshelve. 2: { eauto.  }
      eapply denot_monotone.
    }
    destruct c; try done.
    destruct l; try done.
    destruct l; try done.
    cbn in cIn.
    destruct cIn as [cIn LV].
    (* This replicates part of continuous-∈-sub, but is necessary
       because we cannot show that D is monotonic in the environment.
       It is only monotonic in environments that don't mention x.
     *)
    have lemma: (exists ρ', exists _ : finite_env ρ', ρ' ⊆e ρ /\ ((mem f) ⊆ D ρ')).
    { 
      clear LV. move: cIn.
      eapply fset_induction with (f := f). Unshelve. 3: exact f. 
      - move=> cIn. exists (initial_finite_env ρ NE).
        repeat split.
        eapply (initial_fin ρ NE).
        eapply initial_fin_sub; eauto. 
        done.
      - move=> a f0 IHf cIn.
        rewrite union_mem in cIn.
        rewrite mem_singleton_eq in cIn.
        destruct (CE a) as [ρ1 [F1 [S1 h1]]].
        specialize (cIn a  ltac:(econstructor; eauto)).  subst D. auto.
        destruct IHf as [ρ2 [F2 [S2 h2]]].
        intros y yIn. eapply cIn; eauto. right. auto.
        have SS1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto. 
        have SS2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
        have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
        exists (ρ1 ⊔e ρ2).
        repeat split.
        eapply join_finite_env; eauto.    
        eapply join_lub; eauto.
        subst D.
        intros y yIn.
        rewrite union_mem in yIn.
        rewrite mem_singleton_eq in yIn.
        destruct yIn. inversion H. subst.
        + eapply Λ_ext_sub. 2: eapply h1.
        intros X VX. simpl.
        eapply denot_monotone.
        constructor; eauto.
        eapply join_sub_left; eauto.
        erewrite -> Forall2_dom. 2: eapply SS1. fsetdec.
        reflexivity.
        + specialize (h2 x0 H).
        eapply Λ_ext_sub. 2: eapply h2.
        intros X VX. simpl.
        eapply denot_monotone.
        constructor; eauto.
        eapply join_sub_right; eauto.
        erewrite -> Forall2_dom. 2: eapply SS2. fsetdec.
        reflexivity.
    }
    destruct lemma as [ρ' [F' [S' h']]].
    exists ρ'. exists F'. split; auto.
    rewrite (denot_abs x); auto. 
    rewrite (@Forall2_dom _ Included ρ' ρ); auto.
    cbn. subst D. 
    split; auto. 
  + (* CONS *)
    specialize (IH1 _ NE).
    specialize (IH2 _ NE).
    have C1: forall v1 v2, continuous_env (fun ρ => RET (CONS v1 v2)) ρ.
    { 
      intros. unfold continuous_env, continuous_In.
      intros c1 c1In.
      eapply RET_continuous_env; eauto.
      intros u uIn.
      eapply CONS_continuous_env; eauto
        using const_continuous_env, CONST_monotone_env.
      eapply CONS_monotone_env; eauto using CONST_monotone_env.
    } 
    have C2: forall v1,
        continuous_env (fun ρ => BIND (denot t2 ρ) (fun v2 : P Value => RET (CONS v1 v2))) ρ.
    { 
      intros v1.
      eapply (BIND_continuous_env NE IH2 ltac:
                (eapply denot_monotone; eauto) (C1 v1)); eauto using CONST_monotone_env.
    } 
   edestruct (BIND_continuous_env NE IH1 ltac:(eapply denot_monotone; eauto) C2) as 
     [ ρ' [F' [S' In']]].
   2: eapply cIn.
   intros v ρ1 ρ2 S.    
   eapply BIND_mono. 
   eapply denot_monotone; auto.
   intros x. reflexivity.
   exists ρ'. exists F'. repeat split. auto.
   autorewrite with denot.
   auto.
Qed.

(* ⟦⟧-continuous-⊆ *) 
Lemma generic_continuous_sub {A}{ρ}{F : Rho -> P A} : 
    continuous_env F ρ 
  -> monotone_env F
  -> valid_env ρ
  -> forall V, mem V ⊆ F ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ F ρ').
Proof.
  intros Fcont Fmono NE_ρ V VinEρ.
  eapply continuous_In_sub; eauto.
Qed.


(* ⟦⟧-continuous-⊆ *) 
Lemma denot_continuous_sub {ρ t} : 
  valid_env ρ
  -> forall V, mem V ⊆ denot t ρ
  -> exists ρ', exists (pf : finite_env ρ'),
        ρ' ⊆e ρ  /\  (mem V ⊆ denot t ρ').
Proof.
  intros NE_ρ V VinEρ.
  eapply generic_continuous_sub;
    eauto using denot_continuous_env, denot_monotone.
Qed.


(* ⟦⟧-continuous-one *)
Lemma denot_continuous_one { t ρ x } :
  valid_env ρ 
  -> x `notin` dom ρ 
  -> continuous (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros NE_ρ Fr.
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
    have SUB: Env.Forall2 Included 
                (x ~ a1 ++ E1) (x ~ mem D ++ ρ).
    econstructor; eauto. 
    rewrite <- S. reflexivity.
    rewrite <- SUB. eapply h2. 
    eapply valid_sub_valid_mem; eauto. rewrite <- S. auto. 
Qed.

(*  Abstraction followed by Application is the identity ------------------------------------------------------ *)

(* Λ-▪-id *)
Lemma Λ_APPLY_id { F X } :
  continuous F -> monotone F -> valid X
  -> (Λ F) ▩ X ≃ F X.
Proof. 
  intros Fcont Fmono NEX.
  split.
  + intros w APP. inversion APP; subst.
    - cbn in H. destruct H as [h1 h2].
      specialize (Fmono (mem V) X ltac:(auto)).
      eauto.
    - cbn in H. try done.
    - destruct x; try done.
    - destruct x; try done.
  + intros w wInFX.

    have M: mem (singleton_fset w) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }

    move: (Fcont X (singleton_fset w) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].

    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
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

(* --------------------------------------------------- *)
(* CHOOSE / FAIL is a monoid *)

Lemma choose_fail_left1 (c : P (Comp (fset Value))) : CHOOSE FAIL c ⊆ c.
Proof.
  intros x xIn.
  destruct x; try done.
  cbn in xIn.
  destruct xIn as [l1 [l2 [-> [h1 h2]]]].
  cbv in h1. inversion h1. cbn. auto.
Qed.

Lemma choose_fail_left2 (c : P (Comp (fset Value))) : 
  not (c_wrong ∈ c) ->
  c ⊆ CHOOSE FAIL c.
Proof.
  intros NW x xIn.
  destruct x; try done.
  cbn.
  exists nil. exists l.
  repeat split.  auto.
Qed.

Lemma choose_fail_left (c : P (Comp (fset Value))) : 
  not (c_wrong ∈ c) ->  
  CHOOSE FAIL c ≃ c.
Proof.
  intros. split. eapply choose_fail_left1; eauto. eapply choose_fail_left2; eauto. Qed.

Lemma choose_fail_right1 (c : P (Comp (fset Value))) : CHOOSE c FAIL ⊆ c.
  intros x xIn.
  destruct x; try done.
  cbn in xIn.
  destruct xIn as [l1 [l2 [-> [h1 h2]]]].
  cbv in h2. inversion h2. rewrite app_nil_r. auto.
Qed.

Lemma choose_fail_right2 (c : P (Comp (fset Value))) : 
  not (c_wrong ∈ c) ->
  c ⊆ CHOOSE c FAIL.
Proof.
  intros NW x xIn.
  destruct x; try done.
  cbn.
  exists l. exists nil. 
  repeat split. rewrite app_nil_r. auto. auto.
Qed.

Lemma choose_fail_right (c : P (Comp (fset Value))) : 
  not (c_wrong ∈ c) ->  
  CHOOSE c FAIL ≃ c.
Proof.
  intros. split. eapply choose_fail_right1; eauto. eapply choose_fail_right2; eauto. Qed.

Lemma choose_assoc1 (c1 c2 c3 : P (Comp (fset Value))) : 
  CHOOSE c1 (CHOOSE c2 c3) ⊆ CHOOSE (CHOOSE c1 c2) c3.
Proof.
  intros x xIn.
  destruct x; try done.
  cbn in xIn.
  destruct xIn as [l1 [l2' [-> [h1 h2]]]].
  destruct h2 as [l2 [l3 [-> [h3 h4]]]].
  exists (l1 ++ l2). exists l3.
  repeat split; eauto.
  exists l1. exists l2. split; eauto.
Qed.

Lemma choose_assoc2 (c1 c2 c3 : P (Comp (fset Value))) : 
  CHOOSE (CHOOSE c1 c2) c3 ⊆ CHOOSE c1 (CHOOSE c2 c3).
Proof.
  intros x xIn.
  destruct x; try done.
  cbn in xIn.
  destruct xIn as [l1' [l3 [-> [h1 h2]]]].
  destruct h1 as [l1 [l2 [-> [h3 h4]]]].
  exists l1. exists (l2 ++ l3).
  repeat split; eauto.
  exists l2. exists l3. split; eauto.
Qed.


Lemma choose_assoc  (c1 c2 c3 : P (Comp (fset Value))) : CHOOSE (CHOOSE c1 c2) c3 ≃ CHOOSE c1 (CHOOSE c2 c3).
intros. split. eapply choose_assoc2; eauto. eapply choose_assoc1; eauto. Qed.

(*  RETURN followed by BIND applies ------------------- *)

Lemma bind_ret_Comp : forall {A B} (x : A) (k : A -> Comp B), 
    bind (ret x) k = k x.
Proof.
  intros.
  cbv.
  destruct (k x); auto.
  f_equal.
  eapply app_nil_r.
Qed. 

Lemma BIND_RET1 : forall {A B} (x : P A) (k : P A -> P (Comp (fset B))), 
    monotone k ->  
    BIND (RET x) k ⊆ k x.
Proof.
  intros A B x k MK. 
  unfold BIND, RET.
  repeat split.
  intros y.
  move =>[U [k0 [h2 [h3 h4]]]]. 
  subst.
  destruct U; try done.
  destruct l; try done.
  destruct l; try done.
  cbn.
  move: h2 => [h2 NL].
  specialize (h4 f ltac:(cbv;eauto)).
  rewrite append_Comp_nil.
  eapply MK; eauto.
Qed.

Lemma BIND_RET2 : forall {B} (x : P Value) (k : P Value -> P (Comp (fset B))), 
    monotone k -> 
    continuous k ->
    valid x ->
    k x ⊆ BIND (RET x) k.
Proof. 
  intros B x k km kc vx.
  unfold continuous in kc. 
  unfold BIND, RET.
  intros y yIn.
  unfold Ensembles.In.
  have M: mem (singleton_fset y) ⊆ k x. intros z zIn.
  { destruct zIn; try done. subst. auto. }
  move: (kc x (singleton_fset y) M vx) => [D [S1 [S2 VD]]].
  exists (c_multi (D :: nil)).
  exists (fun _ => y).
  repeat split. 
  - eapply S1.
  - eauto.
  - cbn.
    destruct y; auto. 
    cbn. rewrite app_nil_r. auto.
  - intros v vIn.
    simpl in vIn. destruct vIn; try done.
    subst.
    eapply S2.
    rewrite mem_singleton_eq.
    eauto.
Qed.
  
Lemma BIND_RET : forall {B} (x : P Value) (k : P Value -> P (Comp (fset B))), 
    monotone k -> 
    continuous k ->
    valid x ->
    BIND (RET x) k ≃ k x.
Proof.
  intros.
  split.
  eapply BIND_RET1; eauto.
  eapply BIND_RET2; eauto.
Qed.


Lemma RET_BIND1 : forall {A B} (m : P (Comp (fset A))) (k : P A -> P (Comp (fset B))), 
    BIND m RET ⊆ m.
Proof.
  intros.
  unfold BIND, RET.
  intros y yIn.
  unfold Ensembles.In in yIn.
  move: yIn => [u1 [k1 [h1 [h2 h3]]]].
  destruct u1; cbn in h2.
  + subst. eauto.
  + subst. unfold concat_Comp.
    move: l h1 h3.
    induction l;
    move=> h1 h3.
    cbn. eauto.
    cbn.
    specialize (h3 a ltac:(simpl; eauto)).
    destruct (k1 a); try done.
    destruct l; try done. 
    destruct l0; try done.
    cbn.
Admitted.

(* -------------------------------------------------------- *)

Lemma ID_monotone {A} : monotone (fun x : P A => x).
Proof. intros x y S. auto. Qed.

Lemma ID_continuous : continuous (fun x : P Value => x).
Proof.
  unfold continuous.
  intros X E Ein VX.
  move: VX => [x xIn].
  have VM: valid_mem (union_fset (singleton_fset x) E).
  admit.
  exists (union_fset (singleton_fset x) E). repeat split; eauto.
  rewrite union_mem.
  intros y yIn. 
Admitted. (* more fset reasoning *)


Lemma CONST_monotone {A}{B} {V:P B} : monotone (fun x : P A => V).
Proof. intros x y S. reflexivity. Qed.

Lemma CONST_continuous {A}{V:P A} : continuous (fun x : P Value => V).
Proof.
  unfold continuous.
  intros X E Ein VX.
  move: VX => [x xIn].
  exists (singleton_fset x).
  repeat split; eauto.
Admitted.

Lemma APPLY_monotone {A}{D E : P A -> P Value} : 
    monotone D
  -> monotone E
  -> monotone (fun x => D x ▩ E x).
Proof.
  intros mD mE x y S.
  eapply APPLY_mono_sub; eauto.
Qed.

(* This is similar to APPLY_continuous_env. Maybe we can unify this reasoning??? *)
Lemma APPLY_continuous {D E : P Value -> P Value} :
    continuous D 
  -> continuous E
  -> monotone D 
  -> monotone E
  -> continuous (fun ρ => (D ρ ▩ E ρ)).
Proof.  
  intros IHD IHE mD mE.
  intros w F.
  eapply fset_induction with (f := F). Unshelve. 3: exact F.
  - move=> SUB VW. destruct VW as [v vIn].
    have VW : valid w. econstructor; eauto.
    destruct (IHD w empty_fset ltac:(cbv; done) VW) as [D1 [IS1 [OS1 V1]]].
    destruct (IHE w empty_fset ltac:(cbv; done) VW) as [D2 [IS2 [OS2 V2]]].
    exists (union_fset D1 D2).
    repeat split; eauto.
    rewrite union_mem.
    admit. (* mem empty_fset = emptyset *)
  - intros a f IHF SUB VW. 
    destruct IHF as [D1 [IS1 [OS1 V1]]].
    intros y yIn. eapply SUB. rewrite union_mem. right. auto. auto.
    have APP: a ∈ (D w ▩ E w). eapply SUB. rewrite union_mem. left. rewrite mem_singleton_eq.  auto. 
    inversion APP; subst.
    + unfold continuous in IHD.
      edestruct (IHD w (singleton_fset (V ↦ a)) ltac:(eauto) VW) as 
      [ D2 [ IS2 [ OS2 V2 ]]].
      edestruct (IHE w V ltac:(eauto) VW) as 
      [ D3 [ IS3 [ OS3 V3 ]]].
      exists (union_fset D1 (union_fset D2 D3)).
      repeat split; eauto.
      intros y yIn. 
      repeat rewrite union_mem.
      repeat rewrite union_mem in yIn.
      rewrite mem_singleton_eq in yIn.
      destruct yIn; subst.
      ++ inversion H2. subst.
         eapply BETA with (V := V); eauto.
         eapply mD with (D1 := mem D2).
         repeat rewrite union_mem.
         intros z zIn. right. left. auto.
         eauto.
         repeat rewrite union_mem.
         transitivity (E (mem D3)). auto.
         eapply mE. right. right. auto.
      ++ specialize (OS1 x H2). 
         eapply APPLY_mono_sub. 3: eapply OS1.
         eapply mD. intros z zIn. left. auto.
         eapply mE. intros z zIn. left. auto.
    + destruct (IHD w (singleton_fset (v_list VS))) as [D2 [IS2 [OS2 V2]]]; auto.
      destruct (IHE w (singleton_fset (v_nat k))) as [D3 [IS3 [OS3 V3]]]; auto.
      exists (union_fset D1 (union_fset D2 D3)).
      repeat split; eauto.
      intros y yIn. 
      repeat rewrite union_mem.
      repeat rewrite union_mem in yIn.
      rewrite mem_singleton_eq in yIn.
      destruct yIn.
      ++ inversion H2. subst. 
         eapply PROJ with (VS := VS) (k:= k); eauto.
         eapply mD with (D1 := mem D2); auto.
         intros z zIn. right. left. auto.
         eapply mE with (D1 := mem D3); auto.
         intros z zIn. right. right. auto.
      ++ specialize (OS1 x ltac:(eauto)).
         eapply APPLY_mono_sub. 3: eapply OS1.
         eapply mD. intros z zIn. left. auto.
         eapply mE. intros z zIn. left. auto.
    + destruct (IHD w (singleton_fset x)) as [D2 [IS2 [OS2 V2]]]; auto.
      exists (union_fset D1 D2).
      repeat split; eauto.
      repeat rewrite union_mem.
      repeat rewrite mem_singleton_eq.
      intros y yIn.
      destruct yIn; try inversion H1; subst.
      ++ eapply APPWRONG with (x:=x); auto.
         eapply mD with (D1 := mem D2); eauto.
      ++ specialize (OS1 x0 H1).
         eapply APPLY_mono_sub. 3: eapply OS1.
         eapply mD. intros z zIn. left. auto.
         eapply mE. intros z zIn. left. auto.
    + destruct (IHE w (singleton_fset x)) as [D2 [IS2 [OS2 V2]]]; auto.
      destruct (IHD w (singleton_fset (v_list VS))) as [D3 [IS3 [OS3 V3]]]; auto.
      exists (union_fset D1 (union_fset D2 D3)).
      repeat split; eauto.
      repeat rewrite union_mem.
      rewrite mem_singleton_eq.
      intros y yIn. 
      destruct yIn.
      ++ inversion H2. subst. 
         eapply PROJWRONG with (VS := VS); eauto.
         eapply mD with (D1 := mem D3). intros z zIn. right. right. auto.
         eauto.
         eapply mE with (D1 := mem D2). intros z zIn. right. left. auto. 
         eauto.
      ++ specialize (OS1 x0 H2).
         eapply APPLY_mono_sub. 3: eapply OS1.
         eapply mD. intros z zIn. left. auto.
         eapply mE. intros z zIn. left. auto.
Admitted.


Lemma CONS_monotone {A}{D E: P A -> P Value} :
    monotone D 
  -> monotone E
  -> monotone (fun ρ => CONS (D ρ) (E ρ)).
Proof. intros mD mE x y S. eapply CONS_mono_sub; eauto. Qed.
  

Lemma CONS_continuous {D E} :
    continuous D 
  -> continuous E
  -> monotone D 
  -> monotone E
  -> continuous (fun ρ => CONS (D ρ) (E ρ)).
Proof.
  intros IHD IHE mD mE.
  intros w F.
  eapply fset_induction with (f := F). Unshelve. 3: eauto.
  - move=> SUB VW. destruct VW as [v vIn].
    have VW : valid w. econstructor; eauto.
    destruct (IHD w empty_fset ltac:(cbv; done) VW) as [D1 [IS1 [OS1 V1]]].
    destruct (IHE w empty_fset ltac:(cbv; done) VW) as [D2 [IS2 [OS2 V2]]].
    exists (union_fset D1 D2).
    repeat split; eauto.
    cbv. done.
  - move=> a f IHF SUB VW. 
    rewrite union_mem in SUB. rewrite mem_singleton_eq in SUB.
    destruct IHF as [D1 [IS1 [OS1 V1]]]; auto.
    + intros y yIn. eapply SUB. right. auto.
    + have C: a ∈ CONS (D w)(E w). eapply SUB. left. auto.  
    destruct a; try done.
    destruct l; try done.
    move: C => [vIn lIn].
    destruct (IHD w (singleton_fset v) ltac:(auto) VW) as [D2 [IS2 [OS2 V2]]].
    destruct (IHE w (singleton_fset (v_list l)) ltac:(auto) VW) as [D3 [IS3 [OS3 V3]]].
    exists (union_fset D1 (union_fset D2 D3)).
    repeat rewrite union_mem.
    rewrite mem_singleton_eq.
    repeat split; eauto.
    ++ eapply union_left; eauto. eapply union_left; eauto.
    ++ repeat rewrite mem_singleton_eq in OS2, OS3. 
       intros y yIn.
       destruct yIn. 
       inversion H. subst.
       cbn. split.
       eapply mD with (D1 := mem D2); eauto.
       eapply mE. intros z zIn. right. right. eauto. eauto.
       eapply CONS_mono_sub. 3: eapply OS1; eauto.
       eapply mD. intros z zIn. left. auto.
       eapply mE. intros z zIn. left. auto.
Qed.

Lemma BIND_monotone {A B} 
  {D : P Value -> P (Comp (fset A))} 
  {K : P Value -> P A -> P (Comp B)}: 
  monotone D ->
  (forall v, monotone (fun x => K x v)) ->
  monotone (fun v => (BIND (D v) (K v))). 
Proof. 
  intros mD mK x y S.
  eapply BIND_mono; eauto. 
  intro z; eapply mK; auto.
Qed.
 
Lemma BIND_continuous {A B} 
  {D : P Value -> P (Comp (fset A))} 
  {K : P Value -> P A -> P (Comp B)}: 
  continuous D ->
  monotone D ->
  (forall v, continuous (fun x => K x v)) ->
  (forall v, monotone (fun x => K x v)) ->
  continuous (fun v => (BIND (D v) (K v))). 
Proof.
  intros IHD mD IHK mK.
  intros w F.
  eapply fset_induction with (f:= F). Unshelve. 3: eauto.
  - move=> SUB VW. destruct VW as [v vIn].
    have VW : valid w. econstructor; eauto.
    destruct (IHD w empty_fset ltac:(cbv; done) VW) as [D1 [IS1 [OS1 V1]]].
    exists D1.
    repeat split; eauto.
    cbv. done.
  - move=> a f IHF SUB VW. 
    rewrite union_mem in SUB.
    rewrite mem_singleton_eq in SUB.
    destruct IHF as [D1 [IS1 [OS1 V1]]]; auto.
    intros y yIn. eapply SUB. right. auto.
    have C: a ∈ BIND (D w)(K w). eapply SUB. left.  auto.
    destruct C as [u [k [uIn [h1 h2]]]].    
    unfold continuous in IHD.
    destruct (IHD w (singleton_fset u) ltac:(eauto) VW) as [D2 [IS2 [OS2 V2]]].
    rewrite mem_singleton_eq in OS2.
    destruct u.
    + simpl in h1. subst.
      exists (union_fset D1 D2).
      repeat rewrite union_mem.
      repeat rewrite mem_singleton_eq.
      repeat split; eauto.
      eapply union_left; auto.
      cbn.
      intros z zIn. 
      destruct zIn; try inversion H; subst.
      ++ exists c_wrong. exists k.
         repeat split.
         eapply mD. 2: eapply OS2; auto. eauto.
         intros x h. inversion h.
      ++ specialize (OS1 x H).
         eapply BIND_mono.
         3: eapply OS1.
         eapply mD. auto.
         intros x0 y yIn.
         eapply mK. 2: eapply yIn. auto.
    + have lemma:          
      forall l, 
         (forall a : fset A, Comp_In a (c_multi l) -> K w (mem a) (k a)) -> 
         exists D0, (mem D0 ⊆ w) /\
           (forall a : fset A, Comp_In a (c_multi l) -> K (mem D0) (mem a) (k a)) /\ valid_mem D0.
      { clear uIn D1 IS1 OS1 V1 h1 h2.
        induction l0; intros h2.
        ++ exists D2. 
           repeat split; eauto.
           intros a0 a0In.
           simpl in a0In. done.
        ++ destruct IHl0 as [D3 [IS3 [OS3 V3]]].
           { intros x xIn. apply h2. simpl. simpl in xIn. right. auto. }
           move: (h2 a0 ltac:(econstructor; eauto)) => Ka.
           unfold continuous in IHK.
           destruct (IHK (mem a0) w (singleton_fset (k a0)) ltac:(eauto) VW) as [D4 [IS4 [OS4 V4]]].
           exists (union_fset D2 (union_fset D3 D4)).
           repeat rewrite union_mem.
           repeat rewrite mem_singleton_eq in OS4.
           repeat split; eauto.
           eapply union_left; auto.  eapply union_left; auto.
           intros x xIn.           
           destruct xIn; subst.
           - eapply mK. 2: eapply OS4; eauto.
             right. right. auto.
           - eapply mK. 2: eapply OS3; eauto.
             right. left. auto.
      } 
      destruct (lemma l h2) as [D3 [IS3 [OS3 V3]]].
      exists (union_fset D1 (union_fset D2 D3)).
      repeat rewrite union_mem.
      rewrite mem_singleton_eq.
      repeat split; eauto.
      eapply union_left; auto.  eapply union_left; auto.
      intros y yIn. destruct yIn.
      ++ inversion H. subst a. inversion H. subst x.
         exists (c_multi l). exists k.
         repeat split; eauto.
         eapply mD. 2: eapply OS2; eauto. right. left. auto.
         intros x xIn.
         eapply (mK (mem x)). 2: eapply OS3; eauto.
         right. right. auto.
      ++ eapply BIND_mono. 3: eapply OS1; auto.
         eapply mD. left. auto.
         intros v z zIn. eapply mK. 2: eapply zIn. left. auto.
Qed.

Lemma RET_monotone  {A} {D : P Value -> P A } :
  monotone D -> monotone (fun v : P Value => RET (D v)).
Proof. intros mD x y S. eapply RET_mono; eauto. Qed.


Lemma RET_continuous {A} {D : P Value -> P A } :
  continuous D -> monotone D -> continuous (fun v : P Value => RET (D v)).
Proof.
  intros IHD mD.
  intros w F.
  eapply fset_induction with (f := F). Unshelve. 3: auto.
  - move=> SUB VW. 
    destruct VW as [v vIn].
    have VW : valid w. econstructor; eauto.
    destruct (IHD w empty_fset ltac:(cbv; done) VW) as [D1 [IS1 [OS1 V1]]].
    exists D1.
    repeat split; eauto.
    cbv. done.
  - move=> a f IHF. 
    repeat rewrite union_mem.
    move=> SUB VW.
    rewrite mem_singleton_eq in SUB.
    destruct IHF as [D1 [IS1 [OS1 V1]]]; auto.
    intros y yIn. eapply SUB. right. auto.
    have C: a ∈ RET (D w). eapply SUB. left.  auto.
    destruct a; try done.
    destruct l; try done.
    destruct l; try done.
    cbn in C.
    move: C => [C VL].
    unfold continuous in IHD.
    destruct (IHD w f0 ltac:(eauto) VW) as [D2 [IS2 [OS2 V2]]].
    exists (union_fset D1 D2).
    rewrite union_mem.
    rewrite mem_singleton_eq.
    repeat split; eauto.
    eapply union_left; eauto.
    intros y yIn. 
    destruct yIn.
    ++ inversion H.  subst.
       cbn. split; auto. intros z zIn. specialize (OS2 z zIn). 
       eapply mD. 2: eapply OS2. eauto.
    ++ specialize (OS1 x H).
       eapply RET_mono. 2: eapply OS1. auto.
Qed.

Ltac solve_continuous :=
  eauto using
   BIND_continuous,
   RET_continuous,
   CONS_continuous, 
   ID_continuous, 
   CONST_continuous,
   APPLY_continuous,
   ID_monotone,
   CONST_monotone,
   CONS_monotone,
   RET_monotone,
   BIND_monotone,
   APPLY_monotone.

Lemma RET_CONS_continuous1 {X} :
  continuous (fun v3 : P Value => RET (CONS v3 X)).
Proof.
  solve_continuous.
Qed.

Lemma RET_CONS_continuous2 {X} :
  continuous (fun v3 : P Value => RET (CONS X v3)).
Proof.
  solve_continuous.
Qed.  

Lemma BIND_CONS_continuous {X} :    
  continuous (fun v3 : P Value => BIND X (fun v4 : P Value => RET (CONS v3 v4))).
Proof.
  eapply BIND_continuous;
  solve_continuous.
Qed.
