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

(* short proof tactic for goals of the form Sets.Forall success X *)
Ltac forall_success := 
  let x:= fresh in 
  intros x ?; destruct x; try done.


#[export] Hint Resolve Forall_mem : core.

(* valid sets are inhabited *)
Definition valid_is_nonempty {A} (V : P A) : valid V -> nonemptyT V := id.

#[export] Hint Immediate valid_is_nonempty : core.

Lemma valid_join : forall {A} ( v1 v2 : P A), 
    valid v1 -> 
    valid v2 ->
    valid (v1 ∪ v2).
Proof.
  intros A v1 v2 [x1 h1] [x2 h2].
  exists x1. eapply Union_introl; eauto.
Qed.


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
  exists (v_nat k); eauto. cbn. auto.
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

(* Valid environments *)

Lemma valid_nil : valid_env nil.
Proof. unfold valid_env. eauto. Qed.

#[export] Hint Resolve valid_nil : core.

Lemma extend_valid_env {ρ x X} : 
  x `notin` dom ρ ->
  valid X -> 
  valid_env ρ -> valid_env (x ~ X ++ ρ).
Proof. intros Fr NEP NEX.  eapply ForallT_cons; eauto. Qed.

#[export] Hint Resolve extend_valid_env : core.
