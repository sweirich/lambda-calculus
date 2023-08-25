(* 

The weakening and substitution properties for denot.
   
Lemma weaken_denot : forall t ρ2 ρ,
   fv_tm t [<=] dom ρ2 ->
   uniq (ρ ++ ρ2) ->
   denot t ρ2 = denot t (ρ ++ ρ2). 

Lemma subst_denot1 :
  forall (t : tm) (x : atom) (u : tm) (ρ : Env (P Value)),
    scoped t (x ~ denot u ρ ++ ρ) ->
    scoped u ρ ->
    denot t (x ~ denot u ρ ++ ρ) = denot (t [x ~> u]) ρ.

 *)


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.scoped.

Require Import structures.Structures.
Require Import denot.definitions.
Require Import denot.denot.

Import SetNotations.
Local Open Scope set_scope.
Import MonadNotation.
Open Scope monad_scope.

Import EnvNotations.
Import LCNotations.

Import Wf_nat.

Lemma weaken_access {x}{ρ1 ρ ρ2}:
  singleton x [<=] union (dom ρ1) (dom ρ2) ->
  uniq (ρ1 ++ ρ ++ ρ2) ->
  (ρ1 ++ ρ2) ⋅ x = (ρ1 ++ ρ ++ ρ2) ⋅ x.
Proof.
  intros FV U.
  destruct_uniq.
  move: (access_app_P ρ1 x) => [A1|A2].
  rewrite A1. rewrite A1. auto.
  move: (A2 ρ2) => [A21 A22].
  rewrite A22.
  move: (A2 (ρ ++ ρ2)) => [A31 A32].
  rewrite A32.
  rewrite access_app_fresh; auto.
  intro h.
  solve_uniq.
Qed.

Lemma weaken_denot1 : forall t ρ ρ1 ρ2, 
    fv_tm t [<=] dom (ρ1 ++ ρ2) ->
    uniq (ρ1 ++ ρ ++ ρ2) ->
    denot t (ρ1 ++ ρ2) = denot t (ρ1 ++ ρ ++ ρ2). 
Proof.
  intro t.
  eapply tm_induction with (t := t).
  1: move=>i. 
  2: move=>x.
  3: move=>t1 t2 IH1 IH2. 
  4: move=> u IH.
  8: move=> t1 t2 IH1 IH2.
  all: intros ρ ρ1 ρ2 FV U.
  all: simpl_env in FV; simpl in FV. 
  all: autorewrite with denot.
  all: try solve [reflexivity].
  + (* var *) 
    f_equal.
    eapply weaken_access; eauto.
  + (* app *)
    f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
    extensionality v1. f_equal.
    eapply IH2; simpl_env; eauto.
    fsetdec.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    simpl_env; fsetdec.
    simpl_env; fsetdec.
    f_equal. f_equal.
    extensionality D.
    rewrite <- app_assoc.
    erewrite IH; simpl_env; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl; eauto.
    fsetdec.
  + f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
    extensionality v1. 
    f_equal.
    eapply IH2; simpl_env; eauto.
    fsetdec.
Qed.

Lemma weaken_denot : forall t ρ2 ρ,
   fv_tm t [<=] dom ρ2 ->
   uniq (ρ ++ ρ2) ->
   denot t ρ2 = denot t (ρ ++ ρ2). 
Proof.
  intros.
  unfold denot.
  eapply weaken_denot1 with (ρ1 := nil); simpl; auto.
Qed.


Lemma weaken_denot_val : forall t ρ2 ρ,
   fv_tm t [<=] dom ρ2 ->
   uniq (ρ ++ ρ2) ->
   denot_val t ρ2 = denot_val t (ρ ++ ρ2). 
Proof.
  intros.
  induction t.
  all: autorewrite with denot.
  all: try reflexivity.
  + move: (@weaken_access x nil ρ ρ2) => WA. 
    eapply WA; eauto. simpl in H. fsetdec.
  + pick fresh x.
    repeat rewrite (denot_val_abs x); simpl_env; try fsetdec.
    f_equal.
    extensionality D.
    eapply weaken_denot1.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl; eauto.
    fsetdec.
    solve_uniq.
  + simpl in H.
    f_equal. 
    eapply IHt1; eauto. fsetdec.
    eapply IHt2; eauto. fsetdec.
Qed.


