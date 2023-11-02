(* ------------------------------------------------------------ *)
(* Scoping                                                      *)
(* ------------------------------------------------------------ *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export tactics.
Require Import structures.Env.

Import LCNotations.
Open Scope tm.

Section Scoped.

Variable A : Type.

Inductive scoped t (ρ : Env A) :=
  scoped_intro : 
    fv_tm t [<=] dom ρ -> uniq ρ -> lc_tm t -> scoped t ρ.

Lemma scoped_app : forall t1 t2 ρ,
    scoped t1 ρ -> scoped t2 ρ -> 
    scoped (app t1 t2) ρ.
Proof.
  intros. inversion H. inversion H0. econstructor; eauto.
  simpl. fsetdec.
Qed.

Lemma scoped_app_inv1 : forall t1 t2 ρ,
    scoped (app t1 t2) ρ ->
    scoped t1 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.

Lemma scoped_app_inv2 : forall t1 t2 ρ,
    scoped (app t1 t2) ρ ->
    scoped t2 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.


Lemma scoped_tcons : forall t1 t2 ρ,
    scoped t1 ρ -> scoped t2 ρ -> 
    scoped (tcons t1 t2) ρ.
Proof.
  intros. inversion H. inversion H0. econstructor; eauto.
  simpl. fsetdec.
Qed.

Lemma scoped_tcons_inv1 : forall t1 t2 ρ,
    scoped (tcons t1 t2) ρ ->
    scoped t1 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.

Lemma scoped_tcons_inv2 : forall t1 t2 ρ,
    scoped (tcons t1 t2) ρ ->
    scoped t2 ρ.
Proof.
  intros. inversion H.
  simpl in *. inversion H2.
  econstructor; eauto. 
  fsetdec.
Qed.

Lemma scoped_abs : forall x t1 D ρ, 
  x `notin` dom ρ \u fv_tm t1
  -> scoped (t1 ^ x) (x ~ D ++ ρ)
  -> scoped (abs t1) ρ.
Proof. 
  intros. destruct H0.
  simpl_env in s.
  rewrite <- fv_tm_open_tm_wrt_tm_lower in s.
  destruct_uniq.
  constructor. simpl. fsetdec.
  auto.
  eapply (lc_abs_exists x).
  auto.
Qed.

Lemma scoped_abs_inv : forall x t1 D ρ, 
  x `notin` dom ρ \u fv_tm t1
  -> scoped (abs t1) ρ
  -> scoped (t1 ^ x) (x ~ D ++ ρ).
Proof.
  intros.
  destruct H0. simpl in s. inversion l.
  econstructor; eauto.
  autorewrite with lngen.
  simpl_env.
  subst.
  simpl. fsetdec.
Qed.

(*
Lemma scoped_open_var : forall {x t ρ D},
   scoped t ρ ->
   x `notin` dom ρ ->
   scoped (t ^ x) (x ~ D ++ ρ).
Proof.
  intros.
  inversion H.
  econstructor.
  rewrite fv_tm_open_tm_wrt_tm_upper.
  simpl.
  fsetdec.
  solve_uniq.
*)

End Scoped.

Arguments scoped {_}.

#[export] Hint Constructors scoped : core.
