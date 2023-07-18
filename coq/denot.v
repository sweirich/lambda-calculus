Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.

Require Import lc.List.
Require Import lc.Env.

Require Import lc.Sets.
Import SetNotations.
Local Open Scope set_scope.

Require Import lc.Monad.
Import MonadNotation.
Open Scope monad_scope.

Require Import lc.Container.

Require Import lc.Scoped.

Require Import lc.model_definitions.

Import EnvNotations.
Import LCNotations.

Import Wf_nat.

(* This cannot be part of the Env module because we need to know the type
   of the domain *)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x : list (atom * P Value) => dom x) in
  constr:(A \u B \u C \u D).


Lemma size_is_enough : forall n a, n >= size_tm a -> forall ρ, denot_n n a ρ = denot_n (size_tm a) a ρ.
Proof.
  intros n.
  induction (lt_wf n) as [n _ IH].
  intros a h ρ; destruct a; simpl in *.
  all: try destruct n; simpl; auto; try lia.
  all: f_equal.
  all: try rewrite IH; try lia; auto;
    try rewrite IH; try lia; auto.
  - extensionality D.
    remember (fresh_for (dom ρ \u fv_tm a)) as x.
    rewrite IH. lia.
    autorewrite with lngen. lia.
    autorewrite with lngen. auto.
Qed.

Definition denot (a : tm) := denot_n (size_tm a) a.

Lemma denot_var_b : forall x ρ, denot (var_b x) ρ = ⌈ v_wrong ⌉.
Proof.
  intros x ρ. reflexivity.
Qed.

Lemma denot_var : forall x ρ, denot (var_f x) ρ = ρ ⋅ x.
Proof.
  intros. reflexivity.
Qed.

Lemma denot_app : forall t u ρ, 
    denot (app t u) ρ = 
      (denot t ρ ▩ denot u ρ).
Proof. 
  intros.
  unfold denot. simpl.
  rewrite size_is_enough. lia. auto.
  rewrite size_is_enough. lia. auto.
Qed.

Lemma denot_lit : forall k ρ,  denot (lit k) ρ = NAT k.
Proof. intros. reflexivity. Qed. 

Lemma denot_add : forall ρ,  denot add ρ = ADD.
Proof. intros. reflexivity. Qed. 

Lemma denot_tnil : forall ρ,  denot tnil ρ = NIL.
Proof.  intros. reflexivity. Qed. 

Lemma denot_tcons : forall t u ρ, 
    denot (tcons t u) ρ = CONS (denot t ρ) (denot u ρ).
Proof. 
  intros.
  unfold denot. simpl.
  rewrite size_is_enough. lia. auto.
  rewrite size_is_enough. lia. auto.
Qed.


(* To compute the denotation of an abstraction, we need to first prove a
   renaming lemma. This lemma ensures that the names that we pick for the
   lambda-bound variables don't matter.  *)

Ltac name_binder x0 Frx0 := 
    match goal with 
      [ |- context[fresh_for ?ρ] ] => 
         remember (fresh_for ρ) as x0;
         move: (@fresh_for_fresh x0 ρ ltac:(auto)) => Frx0;
         simpl_env in Frx0
    end.    

Definition access_app_P := @access_app (P Value) ⌈ v_wrong ⌉.

(* Renaming property for denotations. *)

Lemma rename_denot_n : forall n t y w ρ1 ρ2 D, 
  w `notin` dom ρ1 -> 
  y `notin` dom ρ1 \u fv_tm t -> 
  denot_n n t (ρ1 ++ w ~ D ++ ρ2) = 
  denot_n n (t [w ~> var_f y]) (ρ1 ++ y ~ D ++ ρ2).
Proof. 
  induction n;
  intros t y w ρ1 ρ2 D Frw Fry; simpl. auto.
  destruct t; simpl; auto.
  all: simpl in Fry.
  + destruct (x == w).
    ++ subst. 
       simpl_env.       
       rewrite access_app_fresh; auto. 
       rewrite access_eq_var.
       rewrite access_app_fresh; auto. 
       rewrite access_eq_var. auto.
    ++ have NEx: x <> y. fsetdec.
       edestruct (@access_app_P ρ1 x).
       repeat rewrite H. auto.
       destruct (H (cons (w, D) ρ2)).
       rewrite H1. 
       destruct (H (cons (y, D) ρ2)).
       rewrite H3.
       rewrite access_neq_var. auto.
       rewrite access_neq_var. auto.
       auto.
  + f_equal.
    extensionality D0.
    name_binder x0 Frx0.
    name_binder y0 Fry0.

    pick fresh z.
    rewrite (subst_tm_intro z _ (var_f x0)). 
    auto. 
    rewrite (subst_tm_intro z _ (var_f y0)). 
    { autorewrite with lngen. simpl.
      clear Frx0 Fry0 Fry Frw. fsetdec. }
    replace (t [w ~> var_f y] ^ z) with ((t ^ z) [w ~> var_f y]).
    2: {
      rewrite subst_tm_open_tm_wrt_tm; auto.
      rewrite subst_neq_var. 
      fsetdec.
      auto.
    } 
    rewrite <- cons_app_assoc.

    replace (((x0, D0) :: ρ1) ++ (w, D) :: ρ2) with
      (nil ++ (x0 ~ D0) ++ (ρ1 ++ (w ~ D) ++ ρ2)). 2: { simpl_env; auto. }
    rewrite <- IHn; simpl_env; auto.
    2: { autorewrite with lngen. 
         clear Fry0 Frw Fry.
         simpl.
         fsetdec.
    }

    replace ((y0 ~ D0) ++ ρ1 ++ (y ~ D) ++ ρ2) with
      (nil ++ (y0 ~ D0) ++ (ρ1 ++ (y ~ D) ++ ρ2)). 2: { simpl_env; auto. }

    rewrite <- IHn; simpl_env; auto.
    2: { rewrite fv_tm_subst_tm_upper.            
         rewrite fv_tm_open_tm_wrt_tm_upper.
         simpl.
         clear Frx0 Frw Fry.
         rewrite <- fv_tm_subst_tm_lower in Fry0.
         fsetdec.
    }
    
    repeat rewrite <- (app_assoc _ (z ~ D0)).
    eapply IHn.
    simpl_env. { clear Fry0 Fry Frx0. fsetdec. }
    rewrite fv_tm_open_tm_wrt_tm_upper.
    simpl_env. simpl.

    clear Frx0 Fry0 Frw.
    simpl in Fry.
    fsetdec.
  + simpl_env.
    f_equal.
    apply IHn; simpl_env; auto.
    apply IHn; simpl_env; auto.
  + simpl_env.
    f_equal.
    apply IHn; simpl_env; auto.
    apply IHn; simpl_env; auto. 
Qed.


Lemma rename_open_denot : forall w y n t  ρ D, 
  w `notin` fv_tm t -> 
  y `notin` fv_tm t -> 
  denot_n n (t ^ w) (w ~ D ++ ρ) = 
  denot_n n (t ^ y) (y ~ D ++ ρ).
Proof. 
  intros.
  pick fresh z.
  rewrite (subst_tm_intro z _ (var_f w)). auto.
  rewrite (subst_tm_intro z _ (var_f y)). auto.
  rewrite_env (nil ++ w ~ D ++ ρ).
  rewrite <- rename_denot_n; simpl; auto.
  rewrite_env (nil ++ y ~ D ++ ρ).
  rewrite <- rename_denot_n; simpl; auto.
  rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
  rewrite fv_tm_open_tm_wrt_tm_upper. simpl. fsetdec.
Qed.  

Lemma denot_abs : forall x t ρ,
    x `notin` dom ρ \u fv_tm t ->
    denot (abs t) ρ = 
      Λ (fun D => denot (t ^ x) (x ~ D ++ ρ)).
Proof.
  intros.
  unfold denot. simpl.
  rewrite size_tm_open_tm_wrt_tm_var.
  f_equal.
  extensionality D.
  name_binder x0 Frx0.
  simpl_env. 
  rewrite -> (rename_open_denot x0 x); eauto.
Qed.


Create HintDb denot.
#[export] Hint Opaque denot : denot.
#[export] Hint Rewrite denot_var_b denot_var denot_app denot_lit 
  denot_add denot_tnil denot_tcons : denot.
(* no hint for abs, must pick fresh first *)

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
  + (* app *)
    f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
    eapply IH2; simpl_env; eauto.
    fsetdec.
  + pick fresh x.
    repeat rewrite (denot_abs x).
    simpl_env; fsetdec.
    simpl_env; fsetdec.
    f_equal.
    extensionality D.
    rewrite <- app_assoc.
    erewrite IH; simpl_env; eauto.
    rewrite fv_tm_open_tm_wrt_tm_upper; simpl; eauto.
    fsetdec.
  + f_equal.
    eapply IH1; simpl_env; eauto.
    fsetdec.
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

(* Scoping predicates *)

Lemma subst_denot : forall t x u ρ1 ρ2, 
    scoped t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) ->
    scoped u ρ2 ->
    denot t (ρ1 ++ x ~ (denot u ρ2) ++ ρ2) =
    denot (t [x ~> u]) (ρ1 ++ ρ2).
Proof.
  intro t.
  eapply tm_induction with (t := t);
  [move=>i|move=>y|move=>t1 t2 IH1 IH2|move=> t' IH|move=>k| | | move=> t1 t2 IH1 IH2].
  all: intros x u ρ1 ρ2 ST SU.
  all: simpl. 
  all: simpl_env. 
  all: autorewrite with denot.
  all: try solve [reflexivity].
  + destruct (y == x) eqn:EQ. subst.
    ++ have NI: x `notin` dom ρ1.
       { inversion ST. destruct_uniq. auto. }
       have D2: fv_tm u [<=] dom ρ2. 
       { inversion SU. auto. }
       have U2: uniq (ρ1 ++ ρ2). 
       { inversion ST. solve_uniq. }
       rewrite access_app_fresh; auto.       
       rewrite access_eq_var.
       apply weaken_denot; eauto.
    ++ repeat rewrite denot_var.
       destruct (access_app_P ρ1 y) as [h1 | h2].
       repeat rewrite h1. auto.
       move: (h2 ρ2) => [N1 ->]. 
       move: (h2 (x ~ denot u ρ2 ++ ρ2)) => [N3 ->].
       rewrite access_neq_var; auto.
  + move: (scoped_app_inv1 _ _ _ _ ST) => S1.
    move: (scoped_app_inv2 _ _ _ _ ST) => S2.
    f_equal.
    eapply IH1; eauto.
    eapply IH2; eauto.
  + have LCU: lc_tm u. inversion SU. auto.
    pick fresh z.
    specialize (IH z ltac:(auto) x u).
    simpl. simpl_env.
    repeat rewrite (denot_abs z).
    simpl_env. fsetdec.
    simpl_env. rewrite fv_tm_subst_tm_upper. fsetdec. 
    f_equal.
    extensionality D.
    have FZ: z `notin` (dom (ρ1 ++ x ~ denot u ρ2 ++ ρ2) \u fv_tm t').
    simpl_env. fsetdec.
    move: (scoped_abs_inv _ z t' D _ FZ ST) => h.
    rewrite <- app_assoc.
    rewrite IH; auto.
    rewrite subst_tm_open_tm_wrt_tm. eauto.
    rewrite subst_neq_var. auto.
    reflexivity.
  + move: (scoped_tcons_inv1 _ _ _ _ ST) => S1.
    move: (scoped_tcons_inv2 _ _ _ _ ST) => S2.
    f_equal.
    eapply IH1; eauto.
    eapply IH2; eauto.
Qed.

Lemma subst_denot1 :
  forall (t : tm) (x : atom) (u : tm) (ρ : Env (P Value)),
    scoped t (x ~ denot u ρ ++ ρ) 
    -> scoped u ρ 
    -> denot t (x ~ denot u ρ ++ ρ) = denot (t [x ~> u]) ρ.
Proof.
  intros. 
  eapply subst_denot with (ρ1 := nil); auto. 
Qed.
