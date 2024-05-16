Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Coq.Relations.Relation_Definitions.
Require Import Lia.

Require Export lc.tactics.
Require Import lc.scoped.
Require Import structures.Structures.

Require Import verse.definitions.

Import SetNotations.
Local Open Scope set_scope.
Import MonadNotation.
Open Scope monad_scope.

Import EnvNotations.
Import LCNotations.

(* short proof tactic for goals of the form Sets.Forall success X *)
Ltac forall_success := 
  let x:= fresh in 
  intros x ?; destruct x; try done.


(* valid operators *)


Lemma valid_NIL : valid NIL.
Proof.
  unfold NIL, valid.
  econstructor; eauto.
Qed.

Lemma valid_CONS {x y z} : valid x -> valid y -> v_list z ∈ y -> valid (CONS x y).
Proof.
  intros [vx nx] [vl nl] In. unfold CONS.
  - exists (v_list (vx :: z)). cbv. eauto.
Qed. 

Lemma valid_NAT : forall k, valid (NAT k).
Proof.
  intros k. unfold NAT, valid. 
  exists (v_nat k); eauto. 
Qed.

Lemma valid_ADD : valid ADD.
Proof. 
  unfold ADD, valid.
Admitted.
(*
  exists ( (v_list (v_nat 0 :: v_nat 0 :: nil) :: nil) ↦ pure_Comp ((v_nat 0) :: nil)). 
  exists 0. exists 0. exists 0. repeat split; auto. 
Qed. *)

Lemma valid_Λ : forall F, valid (Λ F).
Proof. 
  intros F. 
  cbv.
  exists v_fun. auto. 
Qed.

 
Lemma valid_LIST : forall D, List.ForallT valid D -> valid (LIST D).
induction 1. 
auto.
exists (v_list nil); done. 
destruct IHX as [xs h].
destruct p as [y hy]. 
destruct xs; try done.
exists (v_list (y :: l0)). econstructor; eauto.
Qed.

