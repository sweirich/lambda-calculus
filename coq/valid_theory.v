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

Import EnvNotations.
Import LCNotations.

Lemma valid_mem_valid {V} : valid_mem V -> valid (mem V).
Proof.
  intros [V1 V2].
  destruct V; simpl in *. done.
  split. exists v. auto. eauto.
Qed.


(* valid sets are inhabited *)
Definition valid_is_nonempty V : valid V -> nonemptyT V := fst.

Lemma valid_nonempty_mem : forall V, 
      valid_mem V -> nonemptyT (mem V).
Proof. intros. eapply valid_is_nonempty.
       eapply valid_mem_valid; auto. Qed.

(* And do not contain wrong *)
Lemma valid_not_wrong {X} : valid X -> not (v_wrong ∈ X).
Proof. intros [x h1]; done. Qed.

Lemma valid_mem_nonnil {V} : valid_mem V -> V <> nil.
Proof. intros [h _]; auto. Qed.

Lemma valid_mem_not_wrong {V} : valid_mem V -> not (List.In v_wrong V).
Proof. intros [h j]; auto. Qed.


(* A finite, inhabited subset of a valid set is valid *)
Lemma valid_sub_valid_mem {D a} :
  D <> nil -> valid a -> mem D ⊆ a -> valid_mem D.
Proof.
  intros NE [V1 V2] S.
  inversion V1.
  split; auto.
Qed.

#[export] Hint Immediate valid_is_nonempty valid_nonempty_mem valid_not_wrong valid_mem_valid valid_mem_nonnil valid_mem_not_wrong valid_sub_valid_mem : core.

Lemma valid_join : forall v1 v2, 
    valid v1 -> 
    valid v2 ->
    valid (v1 ∪ v2).
Proof.
  intros v1 v2 [[x1 I1] h1] [[x2 I2] h2].
  split. 
  exists x1. eapply Union_introl; eauto.
  intro h. inversion h; subst; done.
Qed.


(* valid operators *)

Lemma valid_NIL : valid NIL.
Proof.
  unfold NIL, valid.
  split. econstructor; eauto. intro h; inversion h.
Qed.

Lemma valid_CONS {x y z} : valid x -> valid y -> v_list z ∈ y -> valid (CONS x y).
Proof.
  intros [[vx h1] nx] [[vl h2] nl] In. unfold CONS.
  split.
  - exists (v_list (vx :: z)). cbv. eauto.
  - intro h. inversion h.
Qed. 

Lemma valid_NAT : forall k, valid (NAT k).
Proof.
  intros k. unfold NAT, valid. split.
  exists (v_nat k); eauto. cbn. auto.
  intro h; inversion h.
Qed.

Lemma valid_ADD : valid ADD.
Proof. 
  unfold ADD, valid.
  split.
  exists ( (v_list (v_nat 0 :: v_nat 0 :: nil) :: nil) ↦ v_nat 0). 
  cbn.
  exists 0. exists 0. split.  auto. auto.
  intro h. inversion h.
Qed.

Lemma valid_Λ : forall F, valid (Λ F).
Proof. 
  intros F. 
  split. cbv.
  exists v_fun. auto. 
  unfold In. done.
Qed.

 
Lemma valid_LIST : forall D, ForallT valid D -> valid (LIST D).
induction 1. 
split; auto.
exists (v_list nil); done. 
destruct IHX as [[xs nin] h].
destruct p as [[y niny] hy]. 
destruct xs; try done.
split. 
exists (v_list (y :: l0)). econstructor; eauto.
eauto.
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
