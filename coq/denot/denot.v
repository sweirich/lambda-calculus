(* 

This module provides rewriting rules for the denotation function, so that users need never look 
at the fuel-based definition. These can be accessed by the "denot" Hint database for 
all syntactic forms except for abs.

Rewriting abstractions is not automatic because the new variable name must be provided.
  
Lemma denot_abs : forall x t ρ,
    x `notin` dom ρ \u fv_tm t ->
    denot (abs t) ρ = 
      RET2 (Λ (fun D => denot (t ^ x) (x ~ D ++ ρ))).

 *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.scoped.

Require Import structures.Structures.
Require Import denot.definitions.

Import SetNotations.
Local Open Scope set_scope.
Import MonadNotation.
Open Scope monad_scope.

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


Lemma size_is_enough_mutual : 
  forall n a, n >=  (size_tm a) -> 
         (forall ρ, denot_comp_n n a ρ = denot_comp_n (size_tm a) a ρ) /\
         (forall ρ, denot_val_n n a ρ = denot_val_n (size_tm a) a ρ).
Proof.
  intros n.
  induction (lt_wf n) as [n _ IH].

  intros a h; split; intros ρ; destruct a; simpl in *.

  all: try destruct n; simpl; auto; try lia.

  all: f_equal.
  all: try extensionality b.
  all: try (f_equal; extensionality a0).
  - remember (fresh_for (dom ρ \u fv_tm a)) as x.
    destruct (IH n ltac:(auto) (a ^ x)) as [IHC IHV].
    autorewrite with lngen. lia.
    rewrite IHC. 
    autorewrite with lngen. auto.
  - edestruct (IH n ltac:(lia) a1 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a1 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHC1. rewrite IHC2. auto. 
  - edestruct (IH n ltac:(lia) a2 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a2 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHC1. rewrite IHC2. auto.      
  - edestruct (IH n ltac:(lia) a1 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a1 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHC1. rewrite IHC2. auto. 
  - edestruct (IH n ltac:(lia) a2 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a2 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHC1. rewrite IHC2. auto.      
  - remember (fresh_for (dom ρ \u fv_tm a)) as x.
    destruct (IH n ltac:(auto) (a ^ x)) as [IHC IHV].
    autorewrite with lngen. lia.
    rewrite IHC. 
    autorewrite with lngen. auto.
  - edestruct (IH n ltac:(lia) a1 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a1 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHV1. rewrite IHV2. auto. 
  - edestruct (IH n ltac:(lia) a2 ltac:(lia)) as [IHC1 IHV1]. 
    edestruct (IH (size_tm a1 + size_tm a2) ltac:(lia) a2 ltac:(lia)) as [IHC2 IHV2]. 
    rewrite IHV1. rewrite IHV2. auto. 
Qed.

Lemma size_is_enough : 
  forall n a, n >=  (size_tm a) -> 
         (forall ρ, denot_comp_n n a ρ = denot_comp_n (size_tm a) a ρ).
Proof.
  intros.
  eapply size_is_enough_mutual. auto.
Qed.         

Lemma size_is_enough_val : 
  forall n a, n >=  (size_tm a) -> 
         (forall ρ, denot_val_n n a ρ = denot_val_n (size_tm a) a ρ).
Proof.
  intros.
  eapply size_is_enough_mutual. auto.
Qed.         


Local Hint Transparent denot.
Local Hint Transparent denot_val.


Lemma denot_var_b : forall x ρ, denot (var_b x) ρ = fun x => False.
Proof.
  intros x ρ.
  cbv. 
  extensionality b.
  f_equal.
Admitted.


Lemma denot_val_var : forall x ρ, denot_val (var_f x) ρ = ρ ⋅ x.
Proof.
  intros. reflexivity.
Qed.

Lemma denot_var : forall x ρ, denot (var_f x) ρ = RET (ρ ⋅ x).
Proof.
  intros. reflexivity.
Qed.




Lemma denot_app : forall t u ρ, 
    denot (app t u) ρ = 
      BIND (denot t ρ) (fun v1 =>
      BIND (denot u ρ) (fun v2 => 
      (v1 ▩ v2))).
Proof. 
  intros.
  unfold denot. simpl.
  f_equal.
  rewrite size_is_enough. lia. auto.
  extensionality v1.
  f_equal.
  rewrite size_is_enough. lia. auto.
Qed.

Lemma denot_lit : forall k ρ,  denot (lit k) ρ = RET (NAT k).
Proof. intros. reflexivity. Qed. 

Lemma denot_add : forall ρ,  denot add ρ = RET ADD.
Proof. intros. reflexivity. Qed. 

Lemma denot_tnil : forall ρ,  denot tnil ρ = RET NIL.
Proof.  intros. reflexivity. Qed. 

Lemma denot_tcons : forall t u ρ, 
    denot (tcons t u) ρ =
      BIND (denot t ρ) (fun v1 =>
      BIND (denot u ρ) (fun v2 =>
      RET (CONS v1 v2))).
Proof. 
  intros.
  unfold denot. simpl.
  f_equal.
  rewrite size_is_enough. lia. auto.
  extensionality v1. f_equal.
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

Definition access_app_P := @access_app (P Value) (fun x => False).

(* Renaming property for denotations. *)

Lemma rename_denot_n : forall n t y w ρ1 ρ2 D, 
  w `notin` dom ρ1 -> 
  y `notin` dom ρ1 \u fv_tm t -> 
  denot_comp_n n t (ρ1 ++ w ~ D ++ ρ2) = 
  denot_comp_n n (t [w ~> var_f y]) (ρ1 ++ y ~ D ++ ρ2).
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
    f_equal. 
    extensionality D1.
    rewrite <- cons_app_assoc.

    replace (((x0, D1) :: ρ1) ++ (w, D) :: ρ2) with
      (nil ++ (x0 ~ D1) ++ (ρ1 ++ (w ~ D) ++ ρ2)). 2: { simpl_env; auto. }
    rewrite <- IHn; simpl_env; auto.
    2: { autorewrite with lngen. 
         clear Fry0 Frw Fry.
         simpl.
         fsetdec.
    }

    replace ((y0 ~ D1) ++ ρ1 ++ (y ~ D) ++ ρ2) with
      (nil ++ (y0 ~ D1) ++ (ρ1 ++ (y ~ D) ++ ρ2)). 2: { simpl_env; auto. }

    rewrite <- IHn; simpl_env; auto.
    2: { rewrite fv_tm_subst_tm_upper.            
         rewrite fv_tm_open_tm_wrt_tm_upper.
         simpl.
         clear Frx0 Frw Fry.
         rewrite <- fv_tm_subst_tm_lower in Fry0.
         fsetdec.
    }
    
    repeat rewrite <- (app_assoc _ (z ~ D1)).
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
    extensionality v1.
    f_equal.
    apply IHn; simpl_env; auto.
  + simpl_env.
    f_equal.
    apply IHn; simpl_env; auto.
    extensionality v1. f_equal.
    apply IHn; simpl_env; auto. 
Qed.


Lemma rename_open_denot : forall w y n t  ρ D, 
  w `notin` fv_tm t -> 
  y `notin` fv_tm t -> 
  denot_comp_n n (t ^ w) (w ~ D ++ ρ) = 
  denot_comp_n n (t ^ y) (y ~ D ++ ρ).
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
      RET (Λ2 (fun D => denot (t ^ x) (x ~ D ++ ρ))).
Proof.
  intros.
  unfold denot. simpl.
  rewrite size_tm_open_tm_wrt_tm_var.
  f_equal. f_equal.
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



