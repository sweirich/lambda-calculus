Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.List.
Require Import lc.Env.
Require Import lc.SetsAsPredicates.
Import SetNotations.
Local Open Scope set_scope.
Require Import lc.Monad.
Import MonadNotation.
Open Scope monad_scope.
Require Import lc.Container.
Require Import lc.Scoped.

(* Definitions *)
Require Import lc.model_definitions.

(* Weakening & substitution for the definition of the denotation *)
Require Import lc.denot.

(* Consistency *)
Require Import lc.value_theory.

(* Validity *)
Require Import lc.valid_theory.

(* Validity *)
Require Import lc.congruence_theory.

Import EnvNotations.
Import LCNotations.
Local Open Scope tm.

(* ---- -------------------------------------- *)

(* k∈℘k *)
Lemma k_in_den_k : forall k, v_nat k ∈ NAT k.
Proof. intros. reflexivity. Qed.

Lemma k_in_den_k'_inv : forall k k', v_nat k ∈ NAT k' -> k = k'.
Proof. intros. inversion H. done. Qed.

Lemma v_in_den_k_inv :  forall v k, v ∈ NAT k -> v = v_nat k.
Proof. intros. destruct v; inversion H. done. Qed.


Lemma NAT_den {k} : NAT k ≃ ⌈ v_nat k ⌉.
split. intros x In. destruct x; try done. inversion In. subst. constructor.
intros x In. inversion In. cbn. auto. Qed.

Lemma den_list : forall i j D, D ⊆ LIST (NAT i :: NAT j :: nil) ->
                 forall x, x ∈ D -> x = v_list (v_nat i :: v_nat j :: nil).
Proof.
  intros.
  specialize (H x H0).
  destruct x; try done. 
  destruct l; try done; inversion H; subst; clear H.
  apply v_in_den_k_inv in H4. subst.
  inversion H6. subst. clear H6.
  apply v_in_den_k_inv in H2. subst.
  inversion H4. subst.
  reflexivity.
Qed.

Lemma ADD_APPLY {i j} : 
  ADD ▩ (LIST (NAT i :: NAT j :: nil)) ≃ NAT (i + j).
Proof.
  split.
  + intros w APP. inversion APP; subst; clear APP.
    all: cbn in H.
    all: try done.
    destruct w; try done.
    - destruct H as [i0 [j0 [h0 h1]]]. subst.
      move: (den_list _ _ _ H0 _ h0) => h1. inversion h1. subst. clear h1.
      eapply k_in_den_k.
    - assert False. eapply H.
      destruct V; try done. destruct H1. done.
      move: (den_list _ _ _ H0 v ltac:(auto)) => h1. subst. 
      eauto.
      done.
   + intros w wIn.
     apply v_in_den_k_inv in wIn. subst.
     eapply BETA with (V := v_list (v_nat i :: v_nat j :: nil) :: nil).
     - cbn. eauto.
     - intros x xIn. inversion xIn. subst.
       cbn. eauto using k_in_den_k.
       inversion H.
     - cbn. split. eauto. unfold In, mem. intro h. inversion h. 
       intro h. inversion h; done.
Qed.

Lemma CONS_ZERO1 {D1 D2} : (CONS D1 D2 ▩ NAT 0) ⊆ D1.
  intros w APP. inversion APP; try inversion H.
  + subst.
    apply v_in_den_k_inv in H0. inversion H0. subst.
    destruct VS; simpl in H1. done. inversion H1. subst.
    inversion H.
    auto.
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
  + intros w wInFX.
    have M: mem (cons w nil) ⊆ F X. 
    { intros d y. inversion y; subst. auto. done. }
    move: (Fcont X (cons w nil) M NEX) => 
    [ D [ DltX [ wInFD NED ]]].
    move: NEX => [ [x h0] h1].
    eapply BETA with (V:=D); eauto.
    repeat split; eauto.
Qed.

(* ---------------------------------------------------- *)

(* Nonempty environments *)

Lemma extend_nonempty_env {ρ x X} : 
  x `notin` dom ρ ->
  nonemptyT X -> 
  nonempty_env ρ -> nonempty_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX. eapply ForallT_cons; eauto. Qed.

#[export] Hint Resolve extend_nonempty_env : core.

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


(* Continuous ----------------------------------------- *)

(* creates an environment that maps each variable x to a singleton 
   set of some element in ρ x *)
Definition initial_finite_env (ρ : Rho) (NE : valid_env ρ) : Rho.
  induction NE. exact nil.
  destruct f as [[V _] _].
  exact (cons (x, ⌈ V ⌉) IHNE).
Defined.

Lemma initial_finite_dom : forall E NE, dom (initial_finite_env E NE) = dom E.
Proof.
  induction NE; simpl. auto.
  destruct f as [[v _] w].  simpl. congruence.
Qed. 

#[export] Hint Rewrite initial_finite_dom : rewr_list.

Lemma finite_singleton : forall v, finite ⌈ v ⌉.
Proof. intros v.  exists (cons v nil).
       repeat split; eauto. done. 
Qed.

#[export] Hint Resolve finite_singleton : core. 


Lemma initial_fin (ρ : Rho) (NE : valid_env ρ) :
  finite_env (initial_finite_env ρ NE).
Proof.
  induction NE.
  simpl. econstructor.
  simpl. destruct f as [[v _] w1 ].
  econstructor; eauto.
  rewrite initial_finite_dom. auto.
Qed.

#[global] Hint Resolve initial_fin : core. 


Lemma initial_fin_sub (ρ : Rho) (NE : valid_env ρ) :
  initial_finite_env ρ NE ⊆e ρ.
Proof.
  induction NE; simpl. econstructor.
  destruct f as [[v wpx] _].
  econstructor. auto.
  rewrite initial_finite_dom. auto.
  intros z y. inversion y. subst. unfold In. auto.
Qed.

#[global] Hint Resolve initial_fin_sub : core. 


(* single-env maps x to D and any other variable y to something in ρ y. *)
Definition single_env (x : atom) (D : P Value) (ρ : Rho) 
  (NE : valid_env ρ) : Rho :=
  update x D (initial_finite_env ρ NE).

  
Lemma single_fin { v x ρ NE } : 
  finite_env (single_env x ⌈ v ⌉ ρ NE).
Proof.
  induction NE; unfold finite_env; eauto.
  unfold single_env; econstructor.
  unfold single_env. simpl. 
  destruct f as [[v1 I1] v2].
  destruct (x == x0) eqn:EQ.
  + subst. rewrite update_eq_var. 
    econstructor.
    eapply initial_fin. simpl_env. auto. auto.
  + rewrite update_neq_var; eauto.
    econstructor; eauto.
    simpl_env. auto.
Qed.

#[global] Hint Resolve single_fin : core. 


Lemma single_sub { ρ x v } :
  forall (NE : valid_env ρ),
    v ∈ ρ ⋅ x 
  -> x `in` dom ρ
  -> (single_env x ⌈ v ⌉ ρ NE) ⊆e ρ.
Proof.
  intros NE.
  induction NE.
  all: intros vpe Indom. 
  + (* nil case *) auto. 
  + (* cons case *)
    unfold single_env in *.
    simpl. simpl_env in Indom.
    destruct f as [[w h1] h2]. simpl.
    simpl in vpe.
    destruct (x == x0).
    ++ subst. econstructor; eauto.
       simpl_env.  eauto.
       intros x h. inversion h. subst. auto.
    ++ econstructor; eauto. 
       eapply IHNE; eauto. fsetdec.
       simpl_env. auto.
       intros y h. inversion h. subst. unfold In. auto.
Qed.

#[export] Hint Resolve single_sub : core. 


(* v∈single[xv]x  *)
Lemma v_single_xvx {v x ρ NE} : 
  x `in` dom ρ ->
  v ∈ (single_env x ⌈ v ⌉ ρ NE ⋅ x).
Proof.
  unfold single_env.
  move: NE.
  induction NE; intro h. fsetdec.
  simpl. destruct f as [[w h1] h2]. simpl.
  destruct (x == x0) eqn:EQ. subst. simpl.
  rewrite eq_dec_refl. econstructor; eauto.
  simpl. rewrite EQ. simpl in h. eapply IHNE; auto. fsetdec.
Qed.  

#[export] Hint Resolve v_single_xvx : core. 



(* continuous-∈⇒⊆ *)
Lemma continuous_In_sub E ρ (NE : valid_env ρ) :
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


Lemma CONS_continuous {D E ρ}{w} :
    w ∈ (CONS (D ρ) (E ρ))
  -> continuous_env D ρ 
  -> continuous_env E ρ
  -> monotone_env D 
  -> monotone_env E
  -> exists ρ3 , 
    exists (pf : finite_env ρ3) , ρ3 ⊆e  ρ 
                             /\ (w ∈ (CONS (D ρ3) (E ρ3))).
Proof.  
  intros C. unfold CONS, In in C. destruct w.
  all: try done.
  destruct l. try done.
  move: C => [Dv El].
  intros IHD IHE mD mE.
  destruct (IHD v Dv) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
  destruct (IHE (v_list l) El) as 
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
  + destruct (IHD v_wrong H) as
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    exists ρ1. exists fρ1. split. auto.
    eapply FUNWRONG; auto.
  + destruct (IHE v_wrong H) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    exists ρ1. exists fρ1. split. auto.
    eapply ARGWRONG; auto.
  + destruct (IHD (V ↦ w) H) as 
      [ ρ1 [ fρ1 [ ρ1ρ VwDp1 ]]].
    destruct 
      (continuous_In_sub E ρ NE mE V)
      as [ ρ2 [ fρ2 [ ρ2ρ VEp2 ]]]; eauto.
    have S1: same_scope ρ1 ρ. eapply Forall2_same_scope; eauto.
    have S2: same_scope ρ2 ρ. eapply Forall2_same_scope; eauto.
    have SS: same_scope ρ1 ρ2. { transitivity ρ; auto. symmetry; auto. }
    exists (ρ1 ⊔e ρ2).
    repeat split.
  - eapply join_finite_env; eauto.
  - eapply join_lub; eauto.
  - have VwDp3 : V ↦ w ∈ D (ρ1 ⊔e ρ2).
    { eapply mD. 2: eapply VwDp1. 
      eapply join_sub_left. auto. }
    have VEρ3 : mem V ⊆ E (ρ1 ⊔e ρ2).
    { intros v vV. eapply mE.
      2: eapply VEp2; auto. 
      eapply join_sub_right.  auto. }
    eapply BETA with (V:=V); auto.
 + destruct (IHD (v_list VS)) as [ρ1 [F1 [h1 h2]]]; auto.
   destruct (IHE (v_nat k)) as [ρ2 [F2 [h3 h4]]]; auto.
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
Qed.



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
  -> (forall V, valid_mem V ->
          continuous_env E (x ~ mem V ++ ρ))
  -> monotone_env E
  -> exists ρ', exists (pf:finite_env ρ'),
            ρ' ⊆e ρ /\
            (v ∈ (Λ (fun D => E (x ~ D ++ ρ')))).
Proof.
  induction v.
  all: try solve [intros; cbv in H; done].
  - (* v is l ↦ v *)
    intros [ wEVρ [NW CL] ] IH mE.
    have VV: valid_mem l. unfold valid_mem. split; eauto.
    destruct (IH l ltac:(eauto) v wEVρ) as
      [ ρ' [ fρ' [ ρ'Vρ wEρ' ]]]. 
    inversion ρ'Vρ. subst. clear ρ'Vρ.
    inversion fρ'. subst. clear fρ'.
    exists E1. exists X.
    repeat split; eauto.
    eapply mE. 2: exact wEρ'.
    have SS: E1 ⊆e E1. eapply Reflexive_sub_env.  eapply Forall2_uniq1; eauto. 
    auto.
  - exists (initial_finite_env ρ NE).
    repeat split; eauto.
Qed.

(* ---------------------------------------------------------- *)

(* https://github.com/jsiek/denotational_semantics/blob/master/agda/ISWIMPValue.agda *)

Definition denot1 (t : tm) (ρ : Rho) : P Value.
  remember (size_tm t) as n.
  have GE: n >= size_tm t. subst. auto. clear Heqn.
  move: t GE ρ.
  induction (lt_wf n) as [n _ denot].
  Print tm.
  intros [ i | x | u | t | k | (* add *) | (* nil *) | t ] SZ; simpl in SZ.
  all: intros ρ.
  - exact ⌈ v_wrong ⌉.
  - exact (ρ ⋅ x).
  - move: (fresh_for (dom ρ \u fv_tm u)) => x.
    have F : P Value -> P Value.
    intro D.
    have LT: size_tm (u ^ x) < n. {  autorewrite with lngen; lia. }
    specialize (denot (size_tm (u ^ x)) LT (u ^ x) ltac:(auto) (x ~ D ++ ρ)).
    exact denot.
    exact (Λ F).
  - move: (denot (size_tm t) ltac:(lia) t ltac:(lia) ρ) => t'.
    move: (denot (size_tm u) ltac:(lia) u ltac:(lia) ρ) => u'.
    exact (t' ▩ u').
  - exact (NAT k). 
  - exact ADD.
  - exact NIL.    
  - move: (denot (size_tm t) ltac:(lia) t ltac:(lia) ρ) => t'.
    move: (denot (size_tm u) ltac:(lia) u ltac:(lia) ρ) => u'.
    exact (CONS t' u').
Defined. 

(* ------------------------------------ *)

(* denotational_semantics/agda/SemanticProperties.agda  *)

(* Note: sub_env forces ρ and ρ' to have the same domain *)


Lemma access_monotone {ρ ρ':Rho}{x} : ρ ⊆e ρ' -> ρ ⋅ x ⊆ ρ' ⋅ x.
Proof.
  induction 1. simpl. reflexivity.
  simpl. destruct (x == x0) eqn:E. auto.
  auto. 
Qed.

(*  forall ρ ρ', ρ ⊆e ρ' -> denot t ρ ⊆ denot t ρ'. *)
Lemma denot_monotone {t}: 
  monotone_env (denot t).
Proof.
  unfold monotone_env.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
 all: intros ρ ρ' S.
 all: autorewrite with denot.
 all: try solve [reflexivity].
  + eapply access_monotone; auto.
  + eapply APPLY_mono_sub; eauto.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    fsetdec.
    fsetdec.
    eapply Λ_ext_sub.
    intros X NE.
    eapply IH. fsetdec.
    eapply extend_sub_env; eauto. 
  + eapply CONS_mono_sub; eauto.
Qed.


(* ⟦⟧-monotone-one *)
Lemma denot_monotone_one : forall ρ t x, 
    uniq ρ -> x `notin` dom ρ ->
    monotone (fun D => denot t (x ~ D ++ ρ)).
Proof. 
  intros.
  unfold monotone. 
  intros D1 D2 sub.
  eapply denot_monotone; simpl; auto.
  econstructor; eauto.
Qed.
  
(* ⟦⟧-continuous *)
Lemma denot_continuous {t} : forall ρ,
    valid_env ρ
  -> continuous_env (denot t) ρ.
Proof.
  eapply tm_induction with (t := t);
  [move=>i|move=>x|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros ρ NE.
  all: intros v vIn.
  all: autorewrite with denot in vIn.
  all: try solve [ exists (initial_finite_env ρ NE);
    eexists; eauto] .
  + destruct (FSetDecideAuxiliary.dec_In x (dom ρ)).
    - exists (single_env x ⌈ v ⌉ ρ NE).
      exists (@single_fin v x ρ NE).
      split.
      ++ eapply single_sub; auto.
      ++ eapply v_single_xvx. auto. 
    - exists (initial_finite_env ρ NE).
      eexists; eauto. split. eauto.
      rewrite denot_var.
      rewrite access_fresh. simpl_env. auto.
      rewrite access_fresh in vIn. auto. done.
  + edestruct (APPLY_continuous NE vIn) as [ρ' [F SS]]; eauto.
    eapply denot_monotone.
    eapply denot_monotone.
    exists ρ'. exists F.
    rewrite denot_app. auto.
  + pick fresh x.
    rewrite (denot_abs x) in vIn. fsetdec.
    move: (@Lambda_continuous _ _ NE v x vIn) => h.    
    destruct h as [ρ' [Fρ' [S vvIn]]].
    ++ intros V NEV NW.
       move: (valid_nonempty_mem _ NEV) => [w h0]. 
       eapply IH; eauto.
    ++ eapply denot_monotone.
    ++ exists ρ'. exists Fρ'. 
       erewrite <- Forall2_dom in Fr. 2: eapply S.
       rewrite (denot_abs x). fsetdec.
       split; auto.
  + edestruct (CONS_continuous vIn) as [ρ' [F SS]]; eauto.
    eapply denot_monotone.
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

(* ------------------------------------------------------- *)

(* Soundness of reduction with respect to denotation *)
(* ISWIMPValue.agda *)

Ltac invert_value :=
  repeat match goal with 
    | [ H : value (_ _) |- _ ] => inversion H; clear H; subst
    | [ H : listvalue (_ _) |- _ ] => inversion H; clear H; subst
  end.


(* The denotation of syntactic values is valid. *)
Lemma denot_value_valid {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ 
  -> (value t -> valid (denot t ρ)) * 
      (listvalue t -> forall x, x ∈ (denot t ρ) -> { l & v_list l = x}).
Proof. 
  intros FV NEρ.
  induction t.
  all: split.
  all: intros vv.
  all: autorewrite with denot.
  all: try solve [ assert False; invert_value; done].
  + unfold nonempty_env in NEρ.
    eapply (@ForallT_access _ ⌈ v_wrong ⌉ _ _) in NEρ.
    2: instantiate (1:= x); auto.
    destruct NEρ. split; auto.
    simpl in FV. fsetdec.
  + pick fresh x.
    erewrite denot_abs with (x:=x); eauto.
    eapply valid_Λ.
  + eapply valid_NAT; eauto. 
  + eapply valid_ADD; eauto.
  + assert False. inversion vv. done.
  + eapply valid_NIL; eauto.
  + (* exists nil. cbv. econstructor. *)
    intros x In. inversion In. exists nil. reflexivity.
  + simpl in FV. 
    move: (IHt1 ltac:(fsetdec)) => [ih11 _].
    move: (IHt2 ltac:(fsetdec)) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [[v u] NW].
    move: (ih22 LV v u) => [ll ii].
    eapply valid_CONS; eauto. eapply ih11. invert_value. auto.
    subst. eauto.
(*
    move: (ih22 LV) => [l I].
    eapply valid_CONS; eauto. 
    eapply ih11. invert_value. auto. *)
  + simpl in FV. 
    move: (IHt1 ltac:(fsetdec)) => [ih11 _].
    move: (IHt2 ltac:(fsetdec)) => [ih21 ih22].
    have V2: value t2. invert_value. auto.
    have LV: listvalue t2. invert_value. auto.
    move: (ih21 V2) => [[v u] NW].
    move: (ih22 LV v u) => [ll ii].
    subst.
    intros x CC. 
    destruct x; try done.
    exists l. reflexivity.
(*
    have LV: listvalue t2. invert_value. auto.    
    move: (ih22 LV) => [l I].
    destruct ih11 as [[v1 I1] nw1]. invert_value. auto.
    exists (v1 :: l). 
    cbn. split. auto. auto. *)
Qed.     

Lemma value_nonempty {t}{ρ} : 
  fv_tm t [<=] dom ρ -> valid_env ρ -> value t -> valid (denot t ρ).
Proof. 
  intros.
  eapply denot_value_valid; eauto.
Qed. 

Lemma soundness: 
  forall t u, 
    full_reduction t u ->
    forall ρ,
    scoped t ρ ->
    scoped u ρ ->
    valid_env ρ ->
    denot t ρ ≃ denot u ρ.
Proof.
  intros t u RED. 
  induction RED; intros ρ SCt SCu NE.
  - (* beta *)
    destruct SCt as [FV U lc]. inversion lc. subst.
    simpl in FV.
    rewrite denot_app.
    pick fresh x.
    erewrite denot_abs with (x:=x).
    rewrite Λ_denot_APPLY_id.
    eapply value_nonempty; auto.
    fsetdec.
    auto.
    fsetdec.
    rewrite (subst_tm_intro x t v); auto.
    replace ρ with (nil ++ ρ) at 3.
    rewrite <- subst_denot with (ρ1 := nil). reflexivity.
    simpl_env.
    econstructor; eauto. 
    rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
    inversion H; eauto.
    econstructor; eauto. 
    fsetdec.
    reflexivity.
    fsetdec.
  - (* abs-cong *)
    pick fresh x.
    repeat erewrite denot_abs with (x:=x); try fsetdec.
    specialize (H0 x ltac:(auto)).
    eapply Λ_ext.
    intros X NEX.
    eapply H0.
    have F1 : x `notin` dom ρ \u fv_tm t. fsetdec.
    eapply (scoped_abs_inv _ x _ X _ F1 SCt).
    have F2 : x `notin` dom ρ \u fv_tm t'. fsetdec.
    eapply (scoped_abs_inv _ x _ X _ F2 SCu).
    eapply extend_valid_env.
    fsetdec.
    eauto.
    eauto.
  - have SC1: scoped t ρ. eapply scoped_app_inv1; eauto.
    have SC2: scoped t' ρ. eapply scoped_app_inv1; eauto.
    have SC3: scoped u ρ. eapply scoped_app_inv2; eauto.
    repeat rewrite denot_app.
    eapply APPLY_cong; eauto.
    reflexivity.
  - have SC1: scoped t ρ.  eapply scoped_app_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_app_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_app_inv2; eauto.
    repeat rewrite denot_app.
    eapply APPLY_cong; eauto.
    reflexivity.
  - repeat rewrite denot_tcons; eauto.
    eapply CONS_cong; eauto.
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped t' ρ.  eapply scoped_tcons_inv1; eauto.
    eapply IHRED; eauto.
    reflexivity.
  - repeat rewrite denot_tcons.
    have SC1: scoped t ρ.  eapply scoped_tcons_inv1; eauto.
    have SC2: scoped u ρ.  eapply scoped_tcons_inv2; eauto.
    have SC3: scoped u' ρ.  eapply scoped_tcons_inv2; eauto.
    rewrite IHRED; eauto.
    reflexivity.
  - autorewrite with denot.
    split. eapply CONS_ZERO1.

    destruct SCt. simpl in s.
    move: (@denot_value_valid v ρ ltac:(fsetdec) NE) => [h1 h2].
    move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [w1 w2].
    move: (h1 H) => [[vv rr] NW]. clear h1 h2.
    move: (w1 (sv_list _ H0)) => [[uu ss] NW1]. 
    move: (w2 H0 uu ss) => [ll tt]. subst.
    intros x Inx.
    eapply PROJ with (k:= 0) (VS := x :: ll).
    cbn. split; auto. constructor. simpl.
    reflexivity.
    
(*    intros x Inx.
    eapply PROJ with (VS := (x :: ll)) (k:= 0).
    cbn. split; auto. constructor. simpl.
    reflexivity. *)
  - autorewrite with denot.
    split.
    + intros x In. inversion In; clear In; try inversion H1; subst.
      inversion H2. subst. clear H2.
      destruct VS; simpl in H3. done.
      inversion H1.
      eapply PROJ; eauto. econstructor.
    + intros x In.
      destruct SCt. simpl in s.
      move: (@denot_value_valid v ρ ltac:(fsetdec) NE) => [h1 h2].
      move: (@denot_value_valid w ρ ltac:(fsetdec) NE) => [w1 w2].
      move: (h1 H) => [[vv rr] NW]. clear h1 h2.
      move: (w1 (sv_list _ H0)) => [[uu ss] NW2].
      move: (w2 H0) => mm.  
      inversion In; try done; subst.
      move: (mm _ H1) => [o OO]. done.
      inversion H2. subst.
      eapply PROJ. instantiate (1 := (vv :: VS)).
      econstructor; eauto.
      instantiate (1:= (1 + k0)). econstructor.
      simpl.
      auto.
  - autorewrite with denot.
Admitted.


(* --------------------------------------------------------------- *)

(* Example semantics *)


Definition tm_Id : tm := abs (var_b 0).

Lemma denot_Id {v} : (v <> v_wrong) -> (v :: nil ↦ v) ∈ denot tm_Id nil.
Proof.
  intro NE.
  unfold tm_Id.
  pick fresh x.
  rewrite (denot_abs x). simpl. auto.
  unfold Λ. unfold Ensembles.In.
  split. 2: { split. done. intro h. inversion h. done. done. }
  cbn.
  destruct (x == x); try done.
  cbn. left. auto.
Qed. 


Lemma denot_Id_inv : forall x ρ, x ∈ denot tm_Id ρ ->
                          forall w,  Consistent x (w :: nil ↦ w).
Proof.
  intros x ρ.
  unfold tm_Id. 
  pick fresh y.
  rewrite (denot_abs y); auto.
  intro h. unfold In in h. 
  unfold Λ in h.
  destruct x; try done.
  move: h => [h0 [h1 h2]].
  cbn in h0. rewrite eq_dec_refl in h0.
  intros w.
  destruct (dec_con x w). eauto.
  eapply c_map1.
  exists x. exists w. 
  repeat split; eauto.
  unfold List.In. eauto.
Qed.

Definition tm_Delta : tm := abs (app (var_b 0) (var_b 0)).


#[global] Hint Rewrite access_eq_var : lngen.

Lemma denot_Delta_inv :
  forall x, x ∈ denot tm_Delta nil -> 
       exists v w, Consistent x (((v :: nil ↦ w) :: v :: nil) ↦ w).
Proof.
  intro x.  unfold In, tm_Delta.
  pick fresh y.
  rewrite (denot_abs y); auto.
  cbn. rewrite eq_dec_refl.
  unfold Λ. destruct x; try done.
  move=> [h0 [h1 h2]].
  inversion h0; subst; try done.
  + exists (l ↦ x). exists x.
    eapply c_map2. reflexivity.
  + exists (l ↦ x). exists x.
    eapply c_map2. reflexivity.
  + cbn. intros.
    exists v_fun. exists v_fun. eauto.
Qed.

Lemma denot_Delta : forall (v w : Value), v <> v_wrong ->
    (((v :: nil ↦ w) :: v :: nil) ↦ w) ∈ denot tm_Delta nil.
Proof.
  intros v w NW.
  pick fresh x.
  unfold tm_Delta.
  rewrite (denot_abs x); auto.
  cbn. rewrite eq_dec_refl.
  split. 2: { unfold valid_mem. split. intro h. done. intro h.
              inversion h; try done. inversion H; try done. }
  cbv.
  eapply BETA with (V := v :: nil).
  unfold In. left. auto.
  rewrite -> mem_singleton. 
  intros x0 II. inversion II. subst. cbv. right. left. auto.
  unfold valid_mem.
  split; eauto.
  intro h. done. 
  intro h; inversion h; try done.
Qed.


Definition tm_Omega : tm := app tm_Delta tm_Delta.

Lemma denot_Omega : forall v, not (v ∈ denot tm_Omega nil).
Proof.
unfold tm_Omega.
rewrite denot_app.
intro v.
intro h.
inversion h; subst; clear h.
+ apply denot_Delta_inv in H.
  move: H => [v [w C]]. inversion C.
+ apply denot_Delta_inv in H.
  move: H => [v [w C]]. inversion C.
+ apply denot_Delta_inv in H.
  move: H => [v1 [w2 C]]. 
  inversion C; subst.
Admitted.

(* A term with an unbound variable has no value. *)
Definition tm_Wrong : tm := app (var_b 1) (var_b 0).

Lemma denot_Wrong : v_wrong ∈ denot tm_Wrong nil.
Proof.
  unfold tm_Wrong.
  rewrite denot_app.
  repeat rewrite denot_var_b.
  eapply FUNWRONG.
  auto.
Qed.  




(* Λ  \Lambda
   ▩  \squarecrossfill 
   ↦  \mapsto  
   ⤇ \Mapsto  
   ●  \CIRCLE 
   ⊆  \subseteq   (Included)
*)
